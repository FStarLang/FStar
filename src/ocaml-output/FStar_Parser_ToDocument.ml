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
         (id1,uu____3513)) ->
          let uu____3516 =
            let uu____3517 =
              FStar_Util.char_at id1.FStar_Ident.idText (Prims.parse_int "0")
               in
            FStar_All.pipe_right uu____3517 FStar_Util.is_upper  in
          if uu____3516
          then
            let uu____3518 = p_qualifier FStar_Parser_AST.Assumption  in
            FStar_Pprint.op_Hat_Hat uu____3518 FStar_Pprint.space
          else p_qualifiers d.FStar_Parser_AST.quals
      | uu____3520 -> p_qualifiers d.FStar_Parser_AST.quals  in
    let uu____3525 = FStar_Pprint.optional p_fsdoc d.FStar_Parser_AST.doc  in
    let uu____3526 =
      let uu____3527 = p_attributes d.FStar_Parser_AST.attrs  in
      let uu____3528 =
        let uu____3529 = p_rawDecl d  in
        FStar_Pprint.op_Hat_Hat qualifiers uu____3529  in
      FStar_Pprint.op_Hat_Hat uu____3527 uu____3528  in
    FStar_Pprint.op_Hat_Hat uu____3525 uu____3526

and (p_attributes : FStar_Parser_AST.attributes_ -> FStar_Pprint.document) =
  fun attrs  ->
    match attrs with
    | [] -> FStar_Pprint.empty
    | uu____3531 ->
        let uu____3532 =
          let uu____3533 = str "@ "  in
          let uu____3534 =
            let uu____3535 =
              let uu____3536 =
                let uu____3537 =
                  let uu____3538 = FStar_List.map p_atomicTerm attrs  in
                  FStar_Pprint.flow break1 uu____3538  in
                FStar_Pprint.op_Hat_Hat uu____3537 FStar_Pprint.rbracket  in
              FStar_Pprint.align uu____3536  in
            FStar_Pprint.op_Hat_Hat uu____3535 FStar_Pprint.hardline  in
          FStar_Pprint.op_Hat_Hat uu____3533 uu____3534  in
        FStar_Pprint.op_Hat_Hat FStar_Pprint.lbracket uu____3532

and (p_fsdoc : FStar_Parser_AST.fsdoc -> FStar_Pprint.document) =
  fun uu____3541  ->
    match uu____3541 with
    | (doc1,kwd_args) ->
        let kwd_args_doc =
          match kwd_args with
          | [] -> FStar_Pprint.empty
          | kwd_args1 ->
              let process_kwd_arg uu____3575 =
                match uu____3575 with
                | (kwd,arg) ->
                    let uu____3582 = str "@"  in
                    let uu____3583 =
                      let uu____3584 = str kwd  in
                      let uu____3585 =
                        let uu____3586 = str arg  in
                        FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____3586
                         in
                      FStar_Pprint.op_Hat_Hat uu____3584 uu____3585  in
                    FStar_Pprint.op_Hat_Hat uu____3582 uu____3583
                 in
              let uu____3587 =
                let uu____3588 =
                  FStar_Pprint.separate_map FStar_Pprint.hardline
                    process_kwd_arg kwd_args1
                   in
                FStar_Pprint.op_Hat_Hat uu____3588 FStar_Pprint.hardline  in
              FStar_Pprint.op_Hat_Hat FStar_Pprint.hardline uu____3587
           in
        let uu____3593 =
          let uu____3594 =
            let uu____3595 =
              let uu____3596 =
                let uu____3597 = str doc1  in
                let uu____3598 =
                  let uu____3599 =
                    let uu____3600 =
                      FStar_Pprint.op_Hat_Hat FStar_Pprint.rparen
                        FStar_Pprint.hardline
                       in
                    FStar_Pprint.op_Hat_Hat FStar_Pprint.star uu____3600  in
                  FStar_Pprint.op_Hat_Hat kwd_args_doc uu____3599  in
                FStar_Pprint.op_Hat_Hat uu____3597 uu____3598  in
              FStar_Pprint.op_Hat_Hat FStar_Pprint.star uu____3596  in
            FStar_Pprint.op_Hat_Hat FStar_Pprint.star uu____3595  in
          FStar_Pprint.op_Hat_Hat FStar_Pprint.lparen uu____3594  in
        FStar_Pprint.op_Hat_Hat FStar_Pprint.hardline uu____3593

and (p_justSig : FStar_Parser_AST.decl -> FStar_Pprint.document) =
  fun d  ->
    match d.FStar_Parser_AST.d with
    | FStar_Parser_AST.Val (lid,t) ->
        let uu____3604 =
          let uu____3605 = str "val"  in
          let uu____3606 =
            let uu____3607 =
              let uu____3608 = p_lident lid  in
              let uu____3609 =
                FStar_Pprint.op_Hat_Hat FStar_Pprint.space FStar_Pprint.colon
                 in
              FStar_Pprint.op_Hat_Hat uu____3608 uu____3609  in
            FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____3607  in
          FStar_Pprint.op_Hat_Hat uu____3605 uu____3606  in
        let uu____3610 = p_typ false false t  in
        FStar_Pprint.op_Hat_Hat uu____3604 uu____3610
    | FStar_Parser_AST.TopLevelLet (uu____3611,lbs) ->
        FStar_Pprint.separate_map FStar_Pprint.hardline
          (fun lb  ->
             let uu____3636 =
               let uu____3637 = str "let"  in p_letlhs uu____3637 lb  in
             FStar_Pprint.group uu____3636) lbs
    | uu____3638 -> FStar_Pprint.empty

and (p_rawDecl : FStar_Parser_AST.decl -> FStar_Pprint.document) =
  fun d  ->
    match d.FStar_Parser_AST.d with
    | FStar_Parser_AST.Open uid ->
        let uu____3641 =
          let uu____3642 = str "open"  in
          let uu____3643 = p_quident uid  in
          FStar_Pprint.op_Hat_Slash_Hat uu____3642 uu____3643  in
        FStar_Pprint.group uu____3641
    | FStar_Parser_AST.Include uid ->
        let uu____3645 =
          let uu____3646 = str "include"  in
          let uu____3647 = p_quident uid  in
          FStar_Pprint.op_Hat_Slash_Hat uu____3646 uu____3647  in
        FStar_Pprint.group uu____3645
    | FStar_Parser_AST.ModuleAbbrev (uid1,uid2) ->
        let uu____3650 =
          let uu____3651 = str "module"  in
          let uu____3652 =
            let uu____3653 =
              let uu____3654 = p_uident uid1  in
              let uu____3655 =
                FStar_Pprint.op_Hat_Hat FStar_Pprint.space
                  FStar_Pprint.equals
                 in
              FStar_Pprint.op_Hat_Hat uu____3654 uu____3655  in
            FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____3653  in
          FStar_Pprint.op_Hat_Hat uu____3651 uu____3652  in
        let uu____3656 = p_quident uid2  in
        op_Hat_Slash_Plus_Hat uu____3650 uu____3656
    | FStar_Parser_AST.TopLevelModule uid ->
        let uu____3658 =
          let uu____3659 = str "module"  in
          let uu____3660 =
            let uu____3661 = p_quident uid  in
            FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____3661  in
          FStar_Pprint.op_Hat_Hat uu____3659 uu____3660  in
        FStar_Pprint.group uu____3658
    | FStar_Parser_AST.Tycon
        (true
         ,(FStar_Parser_AST.TyconAbbrev
           (uid,tpars,FStar_Pervasives_Native.None ,t),FStar_Pervasives_Native.None
           )::[])
        ->
        let effect_prefix_doc =
          let uu____3694 = str "effect"  in
          let uu____3695 =
            let uu____3696 = p_uident uid  in
            FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____3696  in
          FStar_Pprint.op_Hat_Hat uu____3694 uu____3695  in
        let uu____3697 =
          let uu____3698 = p_typars tpars  in
          FStar_Pprint.surround (Prims.parse_int "2") (Prims.parse_int "1")
            effect_prefix_doc uu____3698 FStar_Pprint.equals
           in
        let uu____3699 = p_typ false false t  in
        op_Hat_Slash_Plus_Hat uu____3697 uu____3699
    | FStar_Parser_AST.Tycon (false ,tcdefs) ->
        let uu____3717 =
          let uu____3718 = str "type"  in
          let uu____3719 = FStar_List.hd tcdefs  in
          p_fsdocTypeDeclPairs uu____3718 uu____3719  in
        let uu____3732 =
          let uu____3733 = FStar_List.tl tcdefs  in
          FStar_All.pipe_left
            (FStar_Pprint.concat_map
               (fun x  ->
                  let uu____3771 =
                    let uu____3772 = str "and"  in
                    p_fsdocTypeDeclPairs uu____3772 x  in
                  FStar_Pprint.op_Hat_Hat break1 uu____3771)) uu____3733
           in
        FStar_Pprint.op_Hat_Hat uu____3717 uu____3732
    | FStar_Parser_AST.TopLevelLet (q,lbs) ->
        let let_doc =
          let uu____3788 = str "let"  in
          let uu____3789 = p_letqualifier q  in
          FStar_Pprint.op_Hat_Hat uu____3788 uu____3789  in
        let uu____3790 = str "and"  in
        separate_map_with_comments_kw let_doc uu____3790 p_letbinding lbs
          (fun uu____3798  ->
             match uu____3798 with
             | (p,t) ->
                 FStar_Range.union_ranges p.FStar_Parser_AST.prange
                   t.FStar_Parser_AST.range)
    | FStar_Parser_AST.Val (lid,t) ->
        let uu____3807 = str "val"  in
        let uu____3808 =
          let uu____3809 =
            let uu____3810 = p_lident lid  in
            let uu____3811 =
              let uu____3812 =
                let uu____3813 =
                  let uu____3814 = p_typ false false t  in
                  FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____3814  in
                FStar_Pprint.op_Hat_Hat FStar_Pprint.colon uu____3813  in
              FStar_Pprint.group uu____3812  in
            FStar_Pprint.op_Hat_Hat uu____3810 uu____3811  in
          FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____3809  in
        FStar_Pprint.op_Hat_Hat uu____3807 uu____3808
    | FStar_Parser_AST.Assume (id1,t) ->
        let decl_keyword =
          let uu____3818 =
            let uu____3819 =
              FStar_Util.char_at id1.FStar_Ident.idText (Prims.parse_int "0")
               in
            FStar_All.pipe_right uu____3819 FStar_Util.is_upper  in
          if uu____3818
          then FStar_Pprint.empty
          else
            (let uu____3821 = str "val"  in
             FStar_Pprint.op_Hat_Hat uu____3821 FStar_Pprint.space)
           in
        let uu____3822 =
          let uu____3823 = p_ident id1  in
          let uu____3824 =
            let uu____3825 =
              let uu____3826 =
                let uu____3827 = p_typ false false t  in
                FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____3827  in
              FStar_Pprint.op_Hat_Hat FStar_Pprint.colon uu____3826  in
            FStar_Pprint.group uu____3825  in
          FStar_Pprint.op_Hat_Hat uu____3823 uu____3824  in
        FStar_Pprint.op_Hat_Hat decl_keyword uu____3822
    | FStar_Parser_AST.Exception (uid,t_opt) ->
        let uu____3834 = str "exception"  in
        let uu____3835 =
          let uu____3836 =
            let uu____3837 = p_uident uid  in
            let uu____3838 =
              FStar_Pprint.optional
                (fun t  ->
                   let uu____3842 =
                     let uu____3843 = str "of"  in
                     let uu____3844 = p_typ false false t  in
                     op_Hat_Slash_Plus_Hat uu____3843 uu____3844  in
                   FStar_Pprint.op_Hat_Hat break1 uu____3842) t_opt
               in
            FStar_Pprint.op_Hat_Hat uu____3837 uu____3838  in
          FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____3836  in
        FStar_Pprint.op_Hat_Hat uu____3834 uu____3835
    | FStar_Parser_AST.NewEffect ne ->
        let uu____3846 = str "new_effect"  in
        let uu____3847 =
          let uu____3848 = p_newEffect ne  in
          FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____3848  in
        FStar_Pprint.op_Hat_Hat uu____3846 uu____3847
    | FStar_Parser_AST.SubEffect se ->
        let uu____3850 = str "sub_effect"  in
        let uu____3851 =
          let uu____3852 = p_subEffect se  in
          FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____3852  in
        FStar_Pprint.op_Hat_Hat uu____3850 uu____3851
    | FStar_Parser_AST.Pragma p -> p_pragma p
    | FStar_Parser_AST.Fsdoc doc1 ->
        let uu____3855 = p_fsdoc doc1  in
        FStar_Pprint.op_Hat_Hat uu____3855 FStar_Pprint.hardline
    | FStar_Parser_AST.Main uu____3856 ->
        failwith "*Main declaration* : Is that really still in use ??"
    | FStar_Parser_AST.Tycon (true ,uu____3857) ->
        failwith
          "Effect abbreviation is expected to be defined by an abbreviation"
    | FStar_Parser_AST.Splice t ->
        let uu____3875 = str "%splice"  in
        let uu____3876 =
          let uu____3877 = p_term false false t  in
          FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____3877  in
        FStar_Pprint.op_Hat_Hat uu____3875 uu____3876

and (p_pragma : FStar_Parser_AST.pragma -> FStar_Pprint.document) =
  fun uu___53_3878  ->
    match uu___53_3878 with
    | FStar_Parser_AST.SetOptions s ->
        let uu____3880 = str "#set-options"  in
        let uu____3881 =
          let uu____3882 =
            let uu____3883 = str s  in FStar_Pprint.dquotes uu____3883  in
          FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____3882  in
        FStar_Pprint.op_Hat_Hat uu____3880 uu____3881
    | FStar_Parser_AST.ResetOptions s_opt ->
        let uu____3887 = str "#reset-options"  in
        let uu____3888 =
          FStar_Pprint.optional
            (fun s  ->
               let uu____3892 =
                 let uu____3893 = str s  in FStar_Pprint.dquotes uu____3893
                  in
               FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____3892) s_opt
           in
        FStar_Pprint.op_Hat_Hat uu____3887 uu____3888
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
    fun uu____3918  ->
      match uu____3918 with
      | (typedecl,fsdoc_opt) ->
          let uu____3931 = p_typeDecl (kw, fsdoc_opt) typedecl  in
          (match uu____3931 with
           | (decl,body) ->
               let uu____3946 = body ()  in
               FStar_Pprint.op_Hat_Hat decl uu____3946)

and (p_typeDecl :
  (FStar_Pprint.document,FStar_Parser_AST.fsdoc
                           FStar_Pervasives_Native.option)
    FStar_Pervasives_Native.tuple2 ->
    FStar_Parser_AST.tycon ->
      (FStar_Pprint.document,Prims.unit -> FStar_Pprint.document)
        FStar_Pervasives_Native.tuple2)
  =
  fun pre  ->
    fun uu___54_3948  ->
      match uu___54_3948 with
      | FStar_Parser_AST.TyconAbstract (lid,bs,typ_opt) ->
          let empty' uu____3975 = FStar_Pprint.empty  in
          let uu____3976 = p_typeDeclPrefix pre false lid bs typ_opt  in
          (uu____3976, empty')
      | FStar_Parser_AST.TyconAbbrev (lid,bs,typ_opt,t) ->
          let f uu____3994 =
            let uu____3995 = p_typ false false t  in jump2 uu____3995  in
          let uu____3996 = p_typeDeclPrefix pre true lid bs typ_opt  in
          (uu____3996, f)
      | FStar_Parser_AST.TyconRecord (lid,bs,typ_opt,record_field_decls) ->
          let p_recordFieldAndComments ps uu____4045 =
            match uu____4045 with
            | (lid1,t,doc_opt) ->
                let uu____4061 =
                  FStar_Range.extend_to_end_of_line t.FStar_Parser_AST.range
                   in
                with_comment (p_recordFieldDecl ps) (lid1, t, doc_opt)
                  uu____4061
             in
          let p_fields uu____4075 =
            let uu____4076 =
              let uu____4077 =
                let uu____4078 =
                  FStar_Pprint.op_Hat_Hat FStar_Pprint.semi break1  in
                separate_map_last uu____4078 p_recordFieldAndComments
                  record_field_decls
                 in
              braces_with_nesting uu____4077  in
            FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____4076  in
          let uu____4087 = p_typeDeclPrefix pre true lid bs typ_opt  in
          (uu____4087, p_fields)
      | FStar_Parser_AST.TyconVariant (lid,bs,typ_opt,ct_decls) ->
          let p_constructorBranchAndComments uu____4145 =
            match uu____4145 with
            | (uid,t_opt,doc_opt,use_of) ->
                let range =
                  let uu____4171 =
                    let uu____4172 =
                      FStar_Util.map_opt t_opt
                        (fun t  -> t.FStar_Parser_AST.range)
                       in
                    FStar_Util.dflt uid.FStar_Ident.idRange uu____4172  in
                  FStar_Range.extend_to_end_of_line uu____4171  in
                with_comment p_constructorBranch
                  (uid, t_opt, doc_opt, use_of) range
             in
          let datacon_doc uu____4196 =
            FStar_Pprint.separate_map FStar_Pprint.hardline
              p_constructorBranchAndComments ct_decls
             in
          let uu____4209 = p_typeDeclPrefix pre true lid bs typ_opt  in
          (uu____4209,
            ((fun uu____4214  ->
                let uu____4215 = datacon_doc ()  in jump2 uu____4215)))

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
  fun uu____4216  ->
    fun eq1  ->
      fun lid  ->
        fun bs  ->
          fun typ_opt  ->
            match uu____4216 with
            | (kw,fsdoc_opt) ->
                let maybe_with_fsdoc cont =
                  let lid_doc = p_ident lid  in
                  let kw_lid =
                    let uu____4248 = FStar_Pprint.op_Hat_Slash_Hat kw lid_doc
                       in
                    FStar_Pprint.group uu____4248  in
                  match fsdoc_opt with
                  | FStar_Pervasives_Native.None  -> cont kw_lid
                  | FStar_Pervasives_Native.Some fsdoc ->
                      let uu____4250 =
                        let uu____4253 =
                          let uu____4256 = p_fsdoc fsdoc  in
                          let uu____4257 =
                            let uu____4260 = cont lid_doc  in [uu____4260]
                             in
                          uu____4256 :: uu____4257  in
                        kw :: uu____4253  in
                      FStar_Pprint.separate FStar_Pprint.hardline uu____4250
                   in
                let typ =
                  let maybe_eq =
                    if eq1 then FStar_Pprint.equals else FStar_Pprint.empty
                     in
                  match typ_opt with
                  | FStar_Pervasives_Native.None  -> maybe_eq
                  | FStar_Pervasives_Native.Some t ->
                      let uu____4265 =
                        let uu____4266 =
                          let uu____4267 = p_typ false false t  in
                          FStar_Pprint.op_Hat_Slash_Hat uu____4267 maybe_eq
                           in
                        FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____4266
                         in
                      FStar_Pprint.op_Hat_Hat FStar_Pprint.colon uu____4265
                   in
                if bs = []
                then maybe_with_fsdoc (fun n1  -> prefix2 n1 typ)
                else
                  (let binders = p_binders_list true bs  in
                   maybe_with_fsdoc
                     (fun n1  ->
                        let uu____4282 =
                          let uu____4283 = FStar_Pprint.flow break1 binders
                             in
                          prefix2 n1 uu____4283  in
                        prefix2 uu____4282 typ))

and (p_recordFieldDecl :
  Prims.bool ->
    (FStar_Ident.ident,FStar_Parser_AST.term,FStar_Parser_AST.fsdoc
                                               FStar_Pervasives_Native.option)
      FStar_Pervasives_Native.tuple3 -> FStar_Pprint.document)
  =
  fun ps  ->
    fun uu____4285  ->
      match uu____4285 with
      | (lid,t,doc_opt) ->
          let uu____4301 =
            let uu____4302 = FStar_Pprint.optional p_fsdoc doc_opt  in
            let uu____4303 =
              let uu____4304 = p_lident lid  in
              let uu____4305 =
                let uu____4306 = p_typ ps false t  in
                FStar_Pprint.op_Hat_Hat FStar_Pprint.colon uu____4306  in
              FStar_Pprint.op_Hat_Hat uu____4304 uu____4305  in
            FStar_Pprint.op_Hat_Hat uu____4302 uu____4303  in
          FStar_Pprint.group uu____4301

and (p_constructorBranch :
  (FStar_Ident.ident,FStar_Parser_AST.term FStar_Pervasives_Native.option,
    FStar_Parser_AST.fsdoc FStar_Pervasives_Native.option,Prims.bool)
    FStar_Pervasives_Native.tuple4 -> FStar_Pprint.document)
  =
  fun uu____4307  ->
    match uu____4307 with
    | (uid,t_opt,doc_opt,use_of) ->
        let sep = if use_of then str "of" else FStar_Pprint.colon  in
        let uid_doc =
          let uu____4335 =
            let uu____4336 =
              let uu____4337 = p_uident uid  in
              FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____4337  in
            FStar_Pprint.op_Hat_Hat FStar_Pprint.bar uu____4336  in
          FStar_Pprint.group uu____4335  in
        let uu____4338 = FStar_Pprint.optional p_fsdoc doc_opt  in
        let uu____4339 =
          default_or_map uid_doc
            (fun t  ->
               let uu____4343 =
                 let uu____4344 =
                   let uu____4345 =
                     let uu____4346 =
                       let uu____4347 = p_typ false false t  in
                       FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____4347
                        in
                     FStar_Pprint.op_Hat_Hat sep uu____4346  in
                   FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____4345  in
                 FStar_Pprint.op_Hat_Hat uid_doc uu____4344  in
               FStar_Pprint.group uu____4343) t_opt
           in
        FStar_Pprint.op_Hat_Hat uu____4338 uu____4339

and (p_letlhs :
  FStar_Pprint.document ->
    (FStar_Parser_AST.pattern,FStar_Parser_AST.term)
      FStar_Pervasives_Native.tuple2 -> FStar_Pprint.document)
  =
  fun kw  ->
    fun uu____4349  ->
      match uu____4349 with
      | (pat,uu____4355) ->
          let uu____4356 =
            match pat.FStar_Parser_AST.pat with
            | FStar_Parser_AST.PatAscribed
                (pat1,(t,FStar_Pervasives_Native.None )) ->
                let uu____4375 =
                  let uu____4376 =
                    let uu____4377 =
                      let uu____4378 = p_tmArrow p_tmNoEq t  in
                      FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____4378
                       in
                    FStar_Pprint.op_Hat_Hat FStar_Pprint.colon uu____4377  in
                  FStar_Pprint.group uu____4376  in
                (pat1, uu____4375)
            | FStar_Parser_AST.PatAscribed
                (pat1,(t,FStar_Pervasives_Native.Some tac)) ->
                let uu____4390 =
                  let uu____4391 =
                    let uu____4392 =
                      let uu____4393 =
                        let uu____4394 = p_tmArrow p_tmNoEq t  in
                        FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____4394
                         in
                      FStar_Pprint.op_Hat_Hat FStar_Pprint.colon uu____4393
                       in
                    FStar_Pprint.group uu____4392  in
                  let uu____4395 =
                    let uu____4396 =
                      let uu____4397 = str "by"  in
                      let uu____4398 =
                        let uu____4399 = p_atomicTerm tac  in
                        FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____4399
                         in
                      FStar_Pprint.op_Hat_Hat uu____4397 uu____4398  in
                    FStar_Pprint.group uu____4396  in
                  FStar_Pprint.op_Hat_Hat uu____4391 uu____4395  in
                (pat1, uu____4390)
            | uu____4400 -> (pat, FStar_Pprint.empty)  in
          (match uu____4356 with
           | (pat1,ascr_doc) ->
               (match pat1.FStar_Parser_AST.pat with
                | FStar_Parser_AST.PatApp
                    ({
                       FStar_Parser_AST.pat = FStar_Parser_AST.PatVar
                         (x,uu____4404);
                       FStar_Parser_AST.prange = uu____4405;_},pats)
                    ->
                    let uu____4415 =
                      let uu____4416 =
                        let uu____4417 =
                          let uu____4418 = p_lident x  in
                          FStar_Pprint.op_Hat_Slash_Hat kw uu____4418  in
                        FStar_Pprint.group uu____4417  in
                      let uu____4419 =
                        FStar_Pprint.flow_map break1 p_atomicPattern pats  in
                      prefix2 uu____4416 uu____4419  in
                    prefix2_nonempty uu____4415 ascr_doc
                | uu____4420 ->
                    let uu____4421 =
                      let uu____4422 =
                        let uu____4423 =
                          let uu____4424 = p_tuplePattern pat1  in
                          FStar_Pprint.op_Hat_Slash_Hat kw uu____4424  in
                        FStar_Pprint.group uu____4423  in
                      FStar_Pprint.op_Hat_Hat uu____4422 ascr_doc  in
                    FStar_Pprint.group uu____4421))

and (p_letbinding :
  FStar_Pprint.document ->
    (FStar_Parser_AST.pattern,FStar_Parser_AST.term)
      FStar_Pervasives_Native.tuple2 -> FStar_Pprint.document)
  =
  fun kw  ->
    fun uu____4426  ->
      match uu____4426 with
      | (pat,e) ->
          let doc_pat = p_letlhs kw (pat, e)  in
          let doc_expr = p_term false false e  in
          let uu____4435 =
            let uu____4436 =
              FStar_Pprint.op_Hat_Slash_Hat FStar_Pprint.equals doc_expr  in
            FStar_Pprint.op_Hat_Slash_Hat doc_pat uu____4436  in
          let uu____4437 =
            let uu____4438 =
              let uu____4439 =
                let uu____4440 =
                  let uu____4441 = jump2 doc_expr  in
                  FStar_Pprint.op_Hat_Hat FStar_Pprint.equals uu____4441  in
                FStar_Pprint.group uu____4440  in
              FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____4439  in
            FStar_Pprint.op_Hat_Hat doc_pat uu____4438  in
          FStar_Pprint.ifflat uu____4435 uu____4437

and (p_newEffect : FStar_Parser_AST.effect_decl -> FStar_Pprint.document) =
  fun uu___55_4442  ->
    match uu___55_4442 with
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
        let uu____4467 = p_uident uid  in
        let uu____4468 = p_binders true bs  in
        let uu____4469 =
          let uu____4470 = p_simpleTerm false false t  in
          prefix2 FStar_Pprint.equals uu____4470  in
        FStar_Pprint.surround (Prims.parse_int "2") (Prims.parse_int "1")
          uu____4467 uu____4468 uu____4469

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
          let uu____4479 =
            let uu____4480 =
              let uu____4481 =
                let uu____4482 = p_uident uid  in
                let uu____4483 = p_binders true bs  in
                let uu____4484 =
                  let uu____4485 = p_typ false false t  in
                  prefix2 FStar_Pprint.colon uu____4485  in
                FStar_Pprint.surround (Prims.parse_int "2")
                  (Prims.parse_int "1") uu____4482 uu____4483 uu____4484
                 in
              FStar_Pprint.group uu____4481  in
            let uu____4486 =
              let uu____4487 = str "with"  in
              let uu____4488 =
                separate_break_map_last FStar_Pprint.semi p_effectDecl
                  eff_decls
                 in
              prefix2 uu____4487 uu____4488  in
            FStar_Pprint.op_Hat_Slash_Hat uu____4480 uu____4486  in
          braces_with_nesting uu____4479

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
          let uu____4519 =
            let uu____4520 = p_lident lid  in
            let uu____4521 =
              FStar_Pprint.op_Hat_Hat FStar_Pprint.space FStar_Pprint.equals
               in
            FStar_Pprint.op_Hat_Hat uu____4520 uu____4521  in
          let uu____4522 = p_simpleTerm ps false e  in
          prefix2 uu____4519 uu____4522
      | uu____4523 ->
          let uu____4524 =
            let uu____4525 = FStar_Parser_AST.decl_to_string d  in
            FStar_Util.format1
              "Not a declaration of an effect member... or at least I hope so : %s"
              uu____4525
             in
          failwith uu____4524

and (p_subEffect : FStar_Parser_AST.lift -> FStar_Pprint.document) =
  fun lift  ->
    let lift_op_doc =
      let lifts =
        match lift.FStar_Parser_AST.lift_op with
        | FStar_Parser_AST.NonReifiableLift t -> [("lift_wp", t)]
        | FStar_Parser_AST.ReifiableLift (t1,t2) ->
            [("lift_wp", t1); ("lift", t2)]
        | FStar_Parser_AST.LiftForFree t -> [("lift", t)]  in
      let p_lift ps uu____4583 =
        match uu____4583 with
        | (kwd,t) ->
            let uu____4590 =
              let uu____4591 = str kwd  in
              let uu____4592 =
                FStar_Pprint.op_Hat_Hat FStar_Pprint.space
                  FStar_Pprint.equals
                 in
              FStar_Pprint.op_Hat_Hat uu____4591 uu____4592  in
            let uu____4593 = p_simpleTerm ps false t  in
            prefix2 uu____4590 uu____4593
         in
      separate_break_map_last FStar_Pprint.semi p_lift lifts  in
    let uu____4598 =
      let uu____4599 =
        let uu____4600 = p_quident lift.FStar_Parser_AST.msource  in
        let uu____4601 =
          let uu____4602 = str "~>"  in
          FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____4602  in
        FStar_Pprint.op_Hat_Hat uu____4600 uu____4601  in
      let uu____4603 = p_quident lift.FStar_Parser_AST.mdest  in
      prefix2 uu____4599 uu____4603  in
    let uu____4604 =
      let uu____4605 = braces_with_nesting lift_op_doc  in
      FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____4605  in
    FStar_Pprint.op_Hat_Hat uu____4598 uu____4604

and (p_qualifier : FStar_Parser_AST.qualifier -> FStar_Pprint.document) =
  fun uu___56_4606  ->
    match uu___56_4606 with
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
    | uu____4608 ->
        let uu____4609 =
          let uu____4610 = FStar_List.map p_qualifier qs  in
          FStar_Pprint.flow break1 uu____4610  in
        FStar_Pprint.op_Hat_Hat uu____4609 FStar_Pprint.hardline

and (p_letqualifier :
  FStar_Parser_AST.let_qualifier -> FStar_Pprint.document) =
  fun uu___57_4613  ->
    match uu___57_4613 with
    | FStar_Parser_AST.Rec  ->
        let uu____4614 = str "rec"  in
        FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____4614
    | FStar_Parser_AST.Mutable  ->
        let uu____4615 = str "mutable"  in
        FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____4615
    | FStar_Parser_AST.NoLetQualifier  -> FStar_Pprint.empty

and (p_aqual : FStar_Parser_AST.arg_qualifier -> FStar_Pprint.document) =
  fun uu___58_4616  ->
    match uu___58_4616 with
    | FStar_Parser_AST.Implicit  -> str "#"
    | FStar_Parser_AST.Equality  -> str "$"

and (p_disjunctivePattern :
  FStar_Parser_AST.pattern -> FStar_Pprint.document) =
  fun p  ->
    match p.FStar_Parser_AST.pat with
    | FStar_Parser_AST.PatOr pats ->
        let uu____4621 =
          let uu____4622 =
            let uu____4623 =
              FStar_Pprint.op_Hat_Hat FStar_Pprint.bar FStar_Pprint.space  in
            FStar_Pprint.op_Hat_Hat break1 uu____4623  in
          FStar_Pprint.separate_map uu____4622 p_tuplePattern pats  in
        FStar_Pprint.group uu____4621
    | uu____4624 -> p_tuplePattern p

and (p_tuplePattern : FStar_Parser_AST.pattern -> FStar_Pprint.document) =
  fun p  ->
    match p.FStar_Parser_AST.pat with
    | FStar_Parser_AST.PatTuple (pats,false ) ->
        let uu____4631 =
          let uu____4632 = FStar_Pprint.op_Hat_Hat FStar_Pprint.comma break1
             in
          FStar_Pprint.separate_map uu____4632 p_constructorPattern pats  in
        FStar_Pprint.group uu____4631
    | uu____4633 -> p_constructorPattern p

and (p_constructorPattern :
  FStar_Parser_AST.pattern -> FStar_Pprint.document) =
  fun p  ->
    match p.FStar_Parser_AST.pat with
    | FStar_Parser_AST.PatApp
        ({ FStar_Parser_AST.pat = FStar_Parser_AST.PatName maybe_cons_lid;
           FStar_Parser_AST.prange = uu____4636;_},hd1::tl1::[])
        when
        FStar_Ident.lid_equals maybe_cons_lid FStar_Parser_Const.cons_lid ->
        let uu____4641 =
          FStar_Pprint.op_Hat_Hat FStar_Pprint.colon FStar_Pprint.colon  in
        let uu____4642 = p_constructorPattern hd1  in
        let uu____4643 = p_constructorPattern tl1  in
        infix0 uu____4641 uu____4642 uu____4643
    | FStar_Parser_AST.PatApp
        ({ FStar_Parser_AST.pat = FStar_Parser_AST.PatName uid;
           FStar_Parser_AST.prange = uu____4645;_},pats)
        ->
        let uu____4651 = p_quident uid  in
        let uu____4652 =
          FStar_Pprint.separate_map break1 p_atomicPattern pats  in
        prefix2 uu____4651 uu____4652
    | uu____4653 -> p_atomicPattern p

and (p_atomicPattern : FStar_Parser_AST.pattern -> FStar_Pprint.document) =
  fun p  ->
    match p.FStar_Parser_AST.pat with
    | FStar_Parser_AST.PatAscribed (pat,(t,FStar_Pervasives_Native.None )) ->
        (match ((pat.FStar_Parser_AST.pat), (t.FStar_Parser_AST.tm)) with
         | (FStar_Parser_AST.PatVar (lid,aqual),FStar_Parser_AST.Refine
            ({ FStar_Parser_AST.b = FStar_Parser_AST.Annotated (lid',t1);
               FStar_Parser_AST.brange = uu____4669;
               FStar_Parser_AST.blevel = uu____4670;
               FStar_Parser_AST.aqual = uu____4671;_},phi))
             when lid.FStar_Ident.idText = lid'.FStar_Ident.idText ->
             let uu____4677 =
               let uu____4678 = p_ident lid  in
               p_refinement aqual uu____4678 t1 phi  in
             soft_parens_with_nesting uu____4677
         | (FStar_Parser_AST.PatWild ,FStar_Parser_AST.Refine
            ({ FStar_Parser_AST.b = FStar_Parser_AST.NoName t1;
               FStar_Parser_AST.brange = uu____4680;
               FStar_Parser_AST.blevel = uu____4681;
               FStar_Parser_AST.aqual = uu____4682;_},phi))
             ->
             let uu____4684 =
               p_refinement FStar_Pervasives_Native.None
                 FStar_Pprint.underscore t1 phi
                in
             soft_parens_with_nesting uu____4684
         | uu____4685 ->
             let uu____4690 =
               let uu____4691 = p_tuplePattern pat  in
               let uu____4692 =
                 let uu____4693 = p_tmEqNoRefinement t  in
                 FStar_Pprint.op_Hat_Slash_Hat FStar_Pprint.colon uu____4693
                  in
               FStar_Pprint.op_Hat_Hat uu____4691 uu____4692  in
             soft_parens_with_nesting uu____4690)
    | FStar_Parser_AST.PatList pats ->
        let uu____4697 =
          separate_break_map FStar_Pprint.semi p_tuplePattern pats  in
        FStar_Pprint.surround (Prims.parse_int "2") (Prims.parse_int "0")
          FStar_Pprint.lbracket uu____4697 FStar_Pprint.rbracket
    | FStar_Parser_AST.PatRecord pats ->
        let p_recordFieldPat uu____4712 =
          match uu____4712 with
          | (lid,pat) ->
              let uu____4719 = p_qlident lid  in
              let uu____4720 = p_tuplePattern pat  in
              infix2 FStar_Pprint.equals uu____4719 uu____4720
           in
        let uu____4721 =
          separate_break_map FStar_Pprint.semi p_recordFieldPat pats  in
        soft_braces_with_nesting uu____4721
    | FStar_Parser_AST.PatTuple (pats,true ) ->
        let uu____4731 =
          FStar_Pprint.op_Hat_Hat FStar_Pprint.lparen FStar_Pprint.bar  in
        let uu____4732 =
          separate_break_map FStar_Pprint.comma p_constructorPattern pats  in
        let uu____4733 =
          FStar_Pprint.op_Hat_Hat FStar_Pprint.bar FStar_Pprint.rparen  in
        FStar_Pprint.surround (Prims.parse_int "2") (Prims.parse_int "1")
          uu____4731 uu____4732 uu____4733
    | FStar_Parser_AST.PatTvar (tv,arg_qualifier_opt) -> p_tvar tv
    | FStar_Parser_AST.PatOp op ->
        let uu____4744 =
          let uu____4745 =
            let uu____4746 = str (FStar_Ident.text_of_id op)  in
            let uu____4747 =
              FStar_Pprint.op_Hat_Hat FStar_Pprint.space FStar_Pprint.rparen
               in
            FStar_Pprint.op_Hat_Hat uu____4746 uu____4747  in
          FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____4745  in
        FStar_Pprint.op_Hat_Hat FStar_Pprint.lparen uu____4744
    | FStar_Parser_AST.PatWild  -> FStar_Pprint.underscore
    | FStar_Parser_AST.PatConst c -> p_constant c
    | FStar_Parser_AST.PatVar (lid,aqual) ->
        let uu____4755 = FStar_Pprint.optional p_aqual aqual  in
        let uu____4756 = p_lident lid  in
        FStar_Pprint.op_Hat_Hat uu____4755 uu____4756
    | FStar_Parser_AST.PatName uid -> p_quident uid
    | FStar_Parser_AST.PatOr uu____4758 -> failwith "Inner or pattern !"
    | FStar_Parser_AST.PatApp
        ({ FStar_Parser_AST.pat = FStar_Parser_AST.PatName uu____4761;
           FStar_Parser_AST.prange = uu____4762;_},uu____4763)
        ->
        let uu____4768 = p_tuplePattern p  in
        soft_parens_with_nesting uu____4768
    | FStar_Parser_AST.PatTuple (uu____4769,false ) ->
        let uu____4774 = p_tuplePattern p  in
        soft_parens_with_nesting uu____4774
    | uu____4775 ->
        let uu____4776 =
          let uu____4777 = FStar_Parser_AST.pat_to_string p  in
          FStar_Util.format1 "Invalid pattern %s" uu____4777  in
        failwith uu____4776

and (p_binder :
  Prims.bool -> FStar_Parser_AST.binder -> FStar_Pprint.document) =
  fun is_atomic  ->
    fun b  ->
      match b.FStar_Parser_AST.b with
      | FStar_Parser_AST.Variable lid ->
          let uu____4781 =
            FStar_Pprint.optional p_aqual b.FStar_Parser_AST.aqual  in
          let uu____4782 = p_lident lid  in
          FStar_Pprint.op_Hat_Hat uu____4781 uu____4782
      | FStar_Parser_AST.TVariable lid -> p_lident lid
      | FStar_Parser_AST.Annotated (lid,t) ->
          let doc1 =
            match t.FStar_Parser_AST.tm with
            | FStar_Parser_AST.Refine
                ({ FStar_Parser_AST.b = FStar_Parser_AST.Annotated (lid',t1);
                   FStar_Parser_AST.brange = uu____4789;
                   FStar_Parser_AST.blevel = uu____4790;
                   FStar_Parser_AST.aqual = uu____4791;_},phi)
                when lid.FStar_Ident.idText = lid'.FStar_Ident.idText ->
                let uu____4793 = p_ident lid  in
                p_refinement b.FStar_Parser_AST.aqual uu____4793 t1 phi
            | uu____4794 ->
                let uu____4795 =
                  FStar_Pprint.optional p_aqual b.FStar_Parser_AST.aqual  in
                let uu____4796 =
                  let uu____4797 = p_lident lid  in
                  let uu____4798 =
                    let uu____4799 = p_tmFormula t  in
                    FStar_Pprint.op_Hat_Slash_Hat FStar_Pprint.colon
                      uu____4799
                     in
                  FStar_Pprint.op_Hat_Hat uu____4797 uu____4798  in
                FStar_Pprint.op_Hat_Hat uu____4795 uu____4796
             in
          if is_atomic
          then
            let uu____4800 =
              let uu____4801 =
                FStar_Pprint.op_Hat_Hat doc1 FStar_Pprint.rparen  in
              FStar_Pprint.op_Hat_Hat FStar_Pprint.lparen uu____4801  in
            FStar_Pprint.group uu____4800
          else FStar_Pprint.group doc1
      | FStar_Parser_AST.TAnnotated uu____4803 ->
          failwith "Is this still used ?"
      | FStar_Parser_AST.NoName t ->
          (match t.FStar_Parser_AST.tm with
           | FStar_Parser_AST.Refine
               ({ FStar_Parser_AST.b = FStar_Parser_AST.NoName t1;
                  FStar_Parser_AST.brange = uu____4810;
                  FStar_Parser_AST.blevel = uu____4811;
                  FStar_Parser_AST.aqual = uu____4812;_},phi)
               ->
               if is_atomic
               then
                 let uu____4814 =
                   let uu____4815 =
                     let uu____4816 =
                       p_refinement b.FStar_Parser_AST.aqual
                         FStar_Pprint.underscore t1 phi
                        in
                     FStar_Pprint.op_Hat_Hat uu____4816 FStar_Pprint.rparen
                      in
                   FStar_Pprint.op_Hat_Hat FStar_Pprint.lparen uu____4815  in
                 FStar_Pprint.group uu____4814
               else
                 (let uu____4818 =
                    p_refinement b.FStar_Parser_AST.aqual
                      FStar_Pprint.underscore t1 phi
                     in
                  FStar_Pprint.group uu____4818)
           | uu____4819 -> if is_atomic then p_atomicTerm t else p_appTerm t)

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
            | FStar_Parser_AST.Construct uu____4828 -> false
            | FStar_Parser_AST.App uu____4839 -> false
            | FStar_Parser_AST.Op uu____4846 -> false
            | uu____4853 -> true  in
          let phi1 = p_noSeqTerm false false phi  in
          let jump_break =
            if is_t_atomic
            then (Prims.parse_int "0")
            else (Prims.parse_int "1")  in
          let uu____4857 =
            let uu____4858 = FStar_Pprint.optional p_aqual aqual_opt  in
            let uu____4859 =
              FStar_Pprint.op_Hat_Hat binder FStar_Pprint.colon  in
            FStar_Pprint.op_Hat_Hat uu____4858 uu____4859  in
          let uu____4860 =
            let uu____4861 = p_appTerm t  in
            let uu____4862 =
              let uu____4863 =
                let uu____4864 =
                  let uu____4865 = soft_braces_with_nesting_tight phi1  in
                  let uu____4866 = soft_braces_with_nesting phi1  in
                  FStar_Pprint.ifflat uu____4865 uu____4866  in
                FStar_Pprint.group uu____4864  in
              FStar_Pprint.jump (Prims.parse_int "2") jump_break uu____4863
               in
            FStar_Pprint.op_Hat_Hat uu____4861 uu____4862  in
          FStar_Pprint.op_Hat_Slash_Hat uu____4857 uu____4860

and (p_binders_list :
  Prims.bool ->
    FStar_Parser_AST.binder Prims.list -> FStar_Pprint.document Prims.list)
  = fun is_atomic  -> fun bs  -> FStar_List.map (p_binder is_atomic) bs

and (p_binders :
  Prims.bool -> FStar_Parser_AST.binder Prims.list -> FStar_Pprint.document)
  =
  fun is_atomic  ->
    fun bs  ->
      let uu____4877 = p_binders_list is_atomic bs  in
      separate_or_flow break1 uu____4877

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
            let uu____4898 =
              let uu____4899 =
                let uu____4900 = p_noSeqTerm true false e1  in
                FStar_Pprint.op_Hat_Hat uu____4900 FStar_Pprint.semi  in
              FStar_Pprint.group uu____4899  in
            let uu____4901 = p_term ps pb e2  in
            FStar_Pprint.op_Hat_Slash_Hat uu____4898 uu____4901
        | FStar_Parser_AST.Bind (x,e1,e2) ->
            let uu____4905 =
              let uu____4906 =
                let uu____4907 =
                  let uu____4908 = p_lident x  in
                  let uu____4909 =
                    FStar_Pprint.op_Hat_Hat FStar_Pprint.space
                      FStar_Pprint.long_left_arrow
                     in
                  FStar_Pprint.op_Hat_Hat uu____4908 uu____4909  in
                let uu____4910 =
                  let uu____4911 = p_noSeqTerm true false e1  in
                  let uu____4912 =
                    FStar_Pprint.op_Hat_Hat FStar_Pprint.space
                      FStar_Pprint.semi
                     in
                  FStar_Pprint.op_Hat_Hat uu____4911 uu____4912  in
                op_Hat_Slash_Plus_Hat uu____4907 uu____4910  in
              FStar_Pprint.group uu____4906  in
            let uu____4913 = p_term ps pb e2  in
            FStar_Pprint.op_Hat_Slash_Hat uu____4905 uu____4913
        | uu____4914 ->
            let uu____4915 = p_noSeqTerm ps pb e  in
            FStar_Pprint.group uu____4915

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
            let uu____4926 =
              let uu____4927 = p_tmIff e1  in
              let uu____4928 =
                let uu____4929 =
                  let uu____4930 = p_typ ps pb t  in
                  FStar_Pprint.op_Hat_Slash_Hat FStar_Pprint.colon uu____4930
                   in
                FStar_Pprint.op_Hat_Hat FStar_Pprint.langle uu____4929  in
              FStar_Pprint.op_Hat_Slash_Hat uu____4927 uu____4928  in
            FStar_Pprint.group uu____4926
        | FStar_Parser_AST.Ascribed (e1,t,FStar_Pervasives_Native.Some tac)
            ->
            let uu____4936 =
              let uu____4937 = p_tmIff e1  in
              let uu____4938 =
                let uu____4939 =
                  let uu____4940 =
                    let uu____4941 = p_typ false false t  in
                    let uu____4942 =
                      let uu____4943 = str "by"  in
                      let uu____4944 = p_typ ps pb tac  in
                      FStar_Pprint.op_Hat_Slash_Hat uu____4943 uu____4944  in
                    FStar_Pprint.op_Hat_Slash_Hat uu____4941 uu____4942  in
                  FStar_Pprint.op_Hat_Slash_Hat FStar_Pprint.colon uu____4940
                   in
                FStar_Pprint.op_Hat_Hat FStar_Pprint.langle uu____4939  in
              FStar_Pprint.op_Hat_Slash_Hat uu____4937 uu____4938  in
            FStar_Pprint.group uu____4936
        | FStar_Parser_AST.Op
            ({ FStar_Ident.idText = ".()<-";
               FStar_Ident.idRange = uu____4945;_},e1::e2::e3::[])
            ->
            let uu____4951 =
              let uu____4952 =
                let uu____4953 =
                  let uu____4954 = p_atomicTermNotQUident e1  in
                  let uu____4955 =
                    let uu____4956 =
                      let uu____4957 =
                        let uu____4958 = p_term false false e2  in
                        soft_parens_with_nesting uu____4958  in
                      let uu____4959 =
                        FStar_Pprint.op_Hat_Hat FStar_Pprint.space
                          FStar_Pprint.larrow
                         in
                      FStar_Pprint.op_Hat_Hat uu____4957 uu____4959  in
                    FStar_Pprint.op_Hat_Hat FStar_Pprint.dot uu____4956  in
                  FStar_Pprint.op_Hat_Hat uu____4954 uu____4955  in
                FStar_Pprint.group uu____4953  in
              let uu____4960 =
                let uu____4961 = p_noSeqTerm ps pb e3  in jump2 uu____4961
                 in
              FStar_Pprint.op_Hat_Hat uu____4952 uu____4960  in
            FStar_Pprint.group uu____4951
        | FStar_Parser_AST.Op
            ({ FStar_Ident.idText = ".[]<-";
               FStar_Ident.idRange = uu____4962;_},e1::e2::e3::[])
            ->
            let uu____4968 =
              let uu____4969 =
                let uu____4970 =
                  let uu____4971 = p_atomicTermNotQUident e1  in
                  let uu____4972 =
                    let uu____4973 =
                      let uu____4974 =
                        let uu____4975 = p_term false false e2  in
                        soft_brackets_with_nesting uu____4975  in
                      let uu____4976 =
                        FStar_Pprint.op_Hat_Hat FStar_Pprint.space
                          FStar_Pprint.larrow
                         in
                      FStar_Pprint.op_Hat_Hat uu____4974 uu____4976  in
                    FStar_Pprint.op_Hat_Hat FStar_Pprint.dot uu____4973  in
                  FStar_Pprint.op_Hat_Hat uu____4971 uu____4972  in
                FStar_Pprint.group uu____4970  in
              let uu____4977 =
                let uu____4978 = p_noSeqTerm ps pb e3  in jump2 uu____4978
                 in
              FStar_Pprint.op_Hat_Hat uu____4969 uu____4977  in
            FStar_Pprint.group uu____4968
        | FStar_Parser_AST.Requires (e1,wtf) ->
            let uu____4988 =
              let uu____4989 = str "requires"  in
              let uu____4990 = p_typ ps pb e1  in
              FStar_Pprint.op_Hat_Slash_Hat uu____4989 uu____4990  in
            FStar_Pprint.group uu____4988
        | FStar_Parser_AST.Ensures (e1,wtf) ->
            let uu____5000 =
              let uu____5001 = str "ensures"  in
              let uu____5002 = p_typ ps pb e1  in
              FStar_Pprint.op_Hat_Slash_Hat uu____5001 uu____5002  in
            FStar_Pprint.group uu____5000
        | FStar_Parser_AST.Attributes es ->
            let uu____5006 =
              let uu____5007 = str "attributes"  in
              let uu____5008 =
                FStar_Pprint.separate_map break1 p_atomicTerm es  in
              FStar_Pprint.op_Hat_Slash_Hat uu____5007 uu____5008  in
            FStar_Pprint.group uu____5006
        | FStar_Parser_AST.If (e1,e2,e3) ->
            if is_unit e3
            then
              let uu____5012 =
                let uu____5013 =
                  let uu____5014 = str "if"  in
                  let uu____5015 = p_noSeqTerm false false e1  in
                  op_Hat_Slash_Plus_Hat uu____5014 uu____5015  in
                let uu____5016 =
                  let uu____5017 = str "then"  in
                  let uu____5018 = p_noSeqTerm ps pb e2  in
                  op_Hat_Slash_Plus_Hat uu____5017 uu____5018  in
                FStar_Pprint.op_Hat_Slash_Hat uu____5013 uu____5016  in
              FStar_Pprint.group uu____5012
            else
              (let e2_doc =
                 match e2.FStar_Parser_AST.tm with
                 | FStar_Parser_AST.If (uu____5021,uu____5022,e31) when
                     is_unit e31 ->
                     let uu____5024 = p_noSeqTerm false false e2  in
                     soft_parens_with_nesting uu____5024
                 | uu____5025 -> p_noSeqTerm false false e2  in
               let uu____5026 =
                 let uu____5027 =
                   let uu____5028 = str "if"  in
                   let uu____5029 = p_noSeqTerm false false e1  in
                   op_Hat_Slash_Plus_Hat uu____5028 uu____5029  in
                 let uu____5030 =
                   let uu____5031 =
                     let uu____5032 = str "then"  in
                     op_Hat_Slash_Plus_Hat uu____5032 e2_doc  in
                   let uu____5033 =
                     let uu____5034 = str "else"  in
                     let uu____5035 = p_noSeqTerm ps pb e3  in
                     op_Hat_Slash_Plus_Hat uu____5034 uu____5035  in
                   FStar_Pprint.op_Hat_Slash_Hat uu____5031 uu____5033  in
                 FStar_Pprint.op_Hat_Slash_Hat uu____5027 uu____5030  in
               FStar_Pprint.group uu____5026)
        | FStar_Parser_AST.TryWith (e1,branches) ->
            let uu____5058 =
              let uu____5059 =
                let uu____5060 =
                  let uu____5061 = str "try"  in
                  let uu____5062 = p_noSeqTerm false false e1  in
                  prefix2 uu____5061 uu____5062  in
                let uu____5063 =
                  let uu____5064 = str "with"  in
                  let uu____5065 =
                    separate_map_last FStar_Pprint.hardline p_patternBranch
                      branches
                     in
                  FStar_Pprint.op_Hat_Slash_Hat uu____5064 uu____5065  in
                FStar_Pprint.op_Hat_Slash_Hat uu____5060 uu____5063  in
              FStar_Pprint.group uu____5059  in
            let uu____5074 = paren_if (ps || pb)  in uu____5074 uu____5058
        | FStar_Parser_AST.Match (e1,branches) ->
            let uu____5099 =
              let uu____5100 =
                let uu____5101 =
                  let uu____5102 = str "match"  in
                  let uu____5103 = p_noSeqTerm false false e1  in
                  let uu____5104 = str "with"  in
                  FStar_Pprint.surround (Prims.parse_int "2")
                    (Prims.parse_int "1") uu____5102 uu____5103 uu____5104
                   in
                let uu____5105 =
                  separate_map_last FStar_Pprint.hardline p_patternBranch
                    branches
                   in
                FStar_Pprint.op_Hat_Slash_Hat uu____5101 uu____5105  in
              FStar_Pprint.group uu____5100  in
            let uu____5114 = paren_if (ps || pb)  in uu____5114 uu____5099
        | FStar_Parser_AST.LetOpen (uid,e1) ->
            let uu____5119 =
              let uu____5120 =
                let uu____5121 =
                  let uu____5122 = str "let open"  in
                  let uu____5123 = p_quident uid  in
                  let uu____5124 = str "in"  in
                  FStar_Pprint.surround (Prims.parse_int "2")
                    (Prims.parse_int "1") uu____5122 uu____5123 uu____5124
                   in
                let uu____5125 = p_term false pb e1  in
                FStar_Pprint.op_Hat_Slash_Hat uu____5121 uu____5125  in
              FStar_Pprint.group uu____5120  in
            let uu____5126 = paren_if ps  in uu____5126 uu____5119
        | FStar_Parser_AST.Let (q,lbs,e1) ->
            let p_lb q1 uu____5182 is_last =
              match uu____5182 with
              | (a,(pat,e2)) ->
                  let attrs = p_attrs_opt a  in
                  let doc_let_or_and =
                    match q1 with
                    | FStar_Pervasives_Native.Some (FStar_Parser_AST.Rec ) ->
                        let uu____5215 =
                          let uu____5216 = str "let"  in
                          let uu____5217 = str "rec"  in
                          FStar_Pprint.op_Hat_Slash_Hat uu____5216 uu____5217
                           in
                        FStar_Pprint.group uu____5215
                    | FStar_Pervasives_Native.Some
                        (FStar_Parser_AST.NoLetQualifier ) -> str "let"
                    | uu____5218 -> str "and"  in
                  let doc_pat = p_letlhs doc_let_or_and (pat, e2)  in
                  let doc_expr = p_term false false e2  in
                  let uu____5223 =
                    if is_last
                    then
                      let uu____5224 =
                        FStar_Pprint.flow break1
                          [doc_pat; FStar_Pprint.equals]
                         in
                      let uu____5225 = str "in"  in
                      FStar_Pprint.surround (Prims.parse_int "2")
                        (Prims.parse_int "1") uu____5224 doc_expr uu____5225
                    else
                      (let uu____5227 =
                         FStar_Pprint.flow break1
                           [doc_pat; FStar_Pprint.equals; doc_expr]
                          in
                       FStar_Pprint.hang (Prims.parse_int "2") uu____5227)
                     in
                  FStar_Pprint.op_Hat_Hat attrs uu____5223
               in
            let l = FStar_List.length lbs  in
            let lbs_docs =
              FStar_List.mapi
                (fun i  ->
                   fun lb  ->
                     if i = (Prims.parse_int "0")
                     then
                       let uu____5273 =
                         p_lb (FStar_Pervasives_Native.Some q) lb
                           (i = (l - (Prims.parse_int "1")))
                          in
                       FStar_Pprint.group uu____5273
                     else
                       (let uu____5281 =
                          p_lb FStar_Pervasives_Native.None lb
                            (i = (l - (Prims.parse_int "1")))
                           in
                        FStar_Pprint.group uu____5281)) lbs
               in
            let lbs_doc =
              let uu____5289 = FStar_Pprint.separate break1 lbs_docs  in
              FStar_Pprint.group uu____5289  in
            let uu____5290 =
              let uu____5291 =
                let uu____5292 =
                  let uu____5293 = p_term false pb e1  in
                  FStar_Pprint.op_Hat_Hat FStar_Pprint.hardline uu____5293
                   in
                FStar_Pprint.op_Hat_Hat lbs_doc uu____5292  in
              FStar_Pprint.group uu____5291  in
            let uu____5294 = paren_if ps  in uu____5294 uu____5290
        | FStar_Parser_AST.Abs
            ({ FStar_Parser_AST.pat = FStar_Parser_AST.PatVar (x,typ_opt);
               FStar_Parser_AST.prange = uu____5299;_}::[],{
                                                             FStar_Parser_AST.tm
                                                               =
                                                               FStar_Parser_AST.Match
                                                               (maybe_x,branches);
                                                             FStar_Parser_AST.range
                                                               = uu____5302;
                                                             FStar_Parser_AST.level
                                                               = uu____5303;_})
            when matches_var maybe_x x ->
            let uu____5330 =
              let uu____5331 =
                let uu____5332 = str "function"  in
                let uu____5333 =
                  separate_map_last FStar_Pprint.hardline p_patternBranch
                    branches
                   in
                FStar_Pprint.op_Hat_Slash_Hat uu____5332 uu____5333  in
              FStar_Pprint.group uu____5331  in
            let uu____5342 = paren_if (ps || pb)  in uu____5342 uu____5330
        | FStar_Parser_AST.Quote (e1,FStar_Parser_AST.Dynamic ) ->
            let uu____5346 =
              let uu____5347 = str "quote"  in
              let uu____5348 = p_noSeqTerm ps pb e1  in
              FStar_Pprint.op_Hat_Slash_Hat uu____5347 uu____5348  in
            FStar_Pprint.group uu____5346
        | FStar_Parser_AST.Quote (e1,FStar_Parser_AST.Static ) ->
            let uu____5350 =
              let uu____5351 = str "`"  in
              let uu____5352 = p_noSeqTerm ps pb e1  in
              FStar_Pprint.op_Hat_Hat uu____5351 uu____5352  in
            FStar_Pprint.group uu____5350
        | FStar_Parser_AST.VQuote e1 ->
            let uu____5354 =
              let uu____5355 = str "%`"  in
              let uu____5356 = p_noSeqTerm ps pb e1  in
              FStar_Pprint.op_Hat_Hat uu____5355 uu____5356  in
            FStar_Pprint.group uu____5354
        | uu____5357 -> p_typ ps pb e

and (p_attrs_opt :
  FStar_Parser_AST.term Prims.list FStar_Pervasives_Native.option ->
    FStar_Pprint.document)
  =
  fun uu___59_5358  ->
    match uu___59_5358 with
    | FStar_Pervasives_Native.None  -> FStar_Pprint.empty
    | FStar_Pervasives_Native.Some terms ->
        let uu____5370 =
          let uu____5371 = str "[@"  in
          let uu____5372 =
            let uu____5373 =
              FStar_Pprint.separate_map break1 p_atomicTerm terms  in
            let uu____5374 = str "]"  in
            FStar_Pprint.op_Hat_Slash_Hat uu____5373 uu____5374  in
          FStar_Pprint.op_Hat_Slash_Hat uu____5371 uu____5372  in
        FStar_Pprint.group uu____5370

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
                 let uu____5400 =
                   let uu____5401 =
                     let uu____5402 = p_quantifier e  in
                     FStar_Pprint.op_Hat_Hat uu____5402 FStar_Pprint.space
                      in
                   FStar_Pprint.soft_surround (Prims.parse_int "2")
                     (Prims.parse_int "0") uu____5401 binders_doc
                     FStar_Pprint.dot
                    in
                 prefix2 uu____5400 term_doc
             | pats ->
                 let uu____5408 =
                   let uu____5409 =
                     let uu____5410 =
                       let uu____5411 =
                         let uu____5412 = p_quantifier e  in
                         FStar_Pprint.op_Hat_Hat uu____5412
                           FStar_Pprint.space
                          in
                       FStar_Pprint.soft_surround (Prims.parse_int "2")
                         (Prims.parse_int "0") uu____5411 binders_doc
                         FStar_Pprint.dot
                        in
                     let uu____5413 = p_trigger trigger  in
                     prefix2 uu____5410 uu____5413  in
                   FStar_Pprint.group uu____5409  in
                 prefix2 uu____5408 term_doc)
        | FStar_Parser_AST.QExists (bs,trigger,e1) ->
            let binders_doc = p_binders true bs  in
            let term_doc = p_noSeqTerm ps pb e1  in
            (match trigger with
             | [] ->
                 let uu____5433 =
                   let uu____5434 =
                     let uu____5435 = p_quantifier e  in
                     FStar_Pprint.op_Hat_Hat uu____5435 FStar_Pprint.space
                      in
                   FStar_Pprint.soft_surround (Prims.parse_int "2")
                     (Prims.parse_int "0") uu____5434 binders_doc
                     FStar_Pprint.dot
                    in
                 prefix2 uu____5433 term_doc
             | pats ->
                 let uu____5441 =
                   let uu____5442 =
                     let uu____5443 =
                       let uu____5444 =
                         let uu____5445 = p_quantifier e  in
                         FStar_Pprint.op_Hat_Hat uu____5445
                           FStar_Pprint.space
                          in
                       FStar_Pprint.soft_surround (Prims.parse_int "2")
                         (Prims.parse_int "0") uu____5444 binders_doc
                         FStar_Pprint.dot
                        in
                     let uu____5446 = p_trigger trigger  in
                     prefix2 uu____5443 uu____5446  in
                   FStar_Pprint.group uu____5442  in
                 prefix2 uu____5441 term_doc)
        | uu____5447 -> p_simpleTerm ps pb e

and (p_quantifier : FStar_Parser_AST.term -> FStar_Pprint.document) =
  fun e  ->
    match e.FStar_Parser_AST.tm with
    | FStar_Parser_AST.QForall uu____5449 -> str "forall"
    | FStar_Parser_AST.QExists uu____5462 -> str "exists"
    | uu____5475 ->
        failwith "Imposible : p_quantifier called on a non-quantifier term"

and (p_trigger :
  FStar_Parser_AST.term Prims.list Prims.list -> FStar_Pprint.document) =
  fun uu___60_5476  ->
    match uu___60_5476 with
    | [] -> FStar_Pprint.empty
    | pats ->
        let uu____5488 =
          let uu____5489 =
            let uu____5490 =
              let uu____5491 = str "pattern"  in
              let uu____5492 =
                let uu____5493 =
                  let uu____5494 = p_disjunctivePats pats  in
                  jump2 uu____5494  in
                FStar_Pprint.op_Hat_Hat uu____5493 FStar_Pprint.rbrace  in
              FStar_Pprint.op_Hat_Slash_Hat uu____5491 uu____5492  in
            FStar_Pprint.op_Hat_Hat FStar_Pprint.colon uu____5490  in
          FStar_Pprint.op_Hat_Hat FStar_Pprint.lbrace uu____5489  in
        FStar_Pprint.group uu____5488

and (p_disjunctivePats :
  FStar_Parser_AST.term Prims.list Prims.list -> FStar_Pprint.document) =
  fun pats  ->
    let uu____5500 = str "\\/"  in
    FStar_Pprint.separate_map uu____5500 p_conjunctivePats pats

and (p_conjunctivePats :
  FStar_Parser_AST.term Prims.list -> FStar_Pprint.document) =
  fun pats  ->
    let uu____5506 =
      let uu____5507 = FStar_Pprint.op_Hat_Hat FStar_Pprint.semi break1  in
      FStar_Pprint.separate_map uu____5507 p_appTerm pats  in
    FStar_Pprint.group uu____5506

and (p_simpleTerm :
  Prims.bool -> Prims.bool -> FStar_Parser_AST.term -> FStar_Pprint.document)
  =
  fun ps  ->
    fun pb  ->
      fun e  ->
        match e.FStar_Parser_AST.tm with
        | FStar_Parser_AST.Abs (pats,e1) ->
            let uu____5517 =
              let uu____5518 =
                let uu____5519 = str "fun"  in
                let uu____5520 =
                  let uu____5521 =
                    FStar_Pprint.separate_map break1 p_atomicPattern pats  in
                  FStar_Pprint.op_Hat_Slash_Hat uu____5521
                    FStar_Pprint.rarrow
                   in
                op_Hat_Slash_Plus_Hat uu____5519 uu____5520  in
              let uu____5522 = p_term false pb e1  in
              op_Hat_Slash_Plus_Hat uu____5518 uu____5522  in
            let uu____5523 = paren_if ps  in uu____5523 uu____5517
        | uu____5526 -> p_tmIff e

and (p_maybeFocusArrow : Prims.bool -> FStar_Pprint.document) =
  fun b  -> if b then str "~>" else FStar_Pprint.rarrow

and (p_patternBranch :
  Prims.bool ->
    (FStar_Parser_AST.pattern,FStar_Parser_AST.term
                                FStar_Pervasives_Native.option,FStar_Parser_AST.term)
      FStar_Pervasives_Native.tuple3 -> FStar_Pprint.document)
  =
  fun pb  ->
    fun uu____5530  ->
      match uu____5530 with
      | (pat,when_opt,e) ->
          let one_pattern_branch p =
            let branch =
              match when_opt with
              | FStar_Pervasives_Native.None  ->
                  let uu____5551 =
                    let uu____5552 =
                      let uu____5553 =
                        let uu____5554 = p_tuplePattern p  in
                        let uu____5555 =
                          FStar_Pprint.op_Hat_Hat FStar_Pprint.space
                            FStar_Pprint.rarrow
                           in
                        FStar_Pprint.op_Hat_Hat uu____5554 uu____5555  in
                      FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____5553
                       in
                    FStar_Pprint.op_Hat_Hat FStar_Pprint.bar uu____5552  in
                  FStar_Pprint.group uu____5551
              | FStar_Pervasives_Native.Some f ->
                  let uu____5557 =
                    let uu____5558 =
                      let uu____5559 =
                        let uu____5560 =
                          let uu____5561 =
                            let uu____5562 = p_tuplePattern p  in
                            let uu____5563 = str "when"  in
                            FStar_Pprint.op_Hat_Slash_Hat uu____5562
                              uu____5563
                             in
                          FStar_Pprint.group uu____5561  in
                        let uu____5564 =
                          let uu____5565 =
                            let uu____5568 = p_tmFormula f  in
                            [uu____5568; FStar_Pprint.rarrow]  in
                          FStar_Pprint.flow break1 uu____5565  in
                        FStar_Pprint.op_Hat_Slash_Hat uu____5560 uu____5564
                         in
                      FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____5559
                       in
                    FStar_Pprint.op_Hat_Hat FStar_Pprint.bar uu____5558  in
                  FStar_Pprint.hang (Prims.parse_int "2") uu____5557
               in
            let uu____5569 =
              let uu____5570 = p_term false pb e  in
              op_Hat_Slash_Plus_Hat branch uu____5570  in
            FStar_Pprint.group uu____5569  in
          (match pat.FStar_Parser_AST.pat with
           | FStar_Parser_AST.PatOr pats ->
               (match FStar_List.rev pats with
                | hd1::tl1 ->
                    let last_pat_branch = one_pattern_branch hd1  in
                    let uu____5579 =
                      let uu____5580 =
                        let uu____5581 =
                          let uu____5582 =
                            let uu____5583 =
                              let uu____5584 =
                                FStar_Pprint.op_Hat_Hat FStar_Pprint.bar
                                  FStar_Pprint.space
                                 in
                              FStar_Pprint.op_Hat_Hat break1 uu____5584  in
                            FStar_Pprint.separate_map uu____5583
                              p_tuplePattern (FStar_List.rev tl1)
                             in
                          FStar_Pprint.op_Hat_Slash_Hat uu____5582
                            last_pat_branch
                           in
                        FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____5581
                         in
                      FStar_Pprint.op_Hat_Hat FStar_Pprint.bar uu____5580  in
                    FStar_Pprint.group uu____5579
                | [] ->
                    failwith "Impossible: disjunctive pattern can't be empty")
           | uu____5585 -> one_pattern_branch pat)

and (p_tmIff : FStar_Parser_AST.term -> FStar_Pprint.document) =
  fun e  ->
    match e.FStar_Parser_AST.tm with
    | FStar_Parser_AST.Op
        ({ FStar_Ident.idText = "<==>"; FStar_Ident.idRange = uu____5587;_},e1::e2::[])
        ->
        let uu____5592 = str "<==>"  in
        let uu____5593 = p_tmImplies e1  in
        let uu____5594 = p_tmIff e2  in
        infix0 uu____5592 uu____5593 uu____5594
    | uu____5595 -> p_tmImplies e

and (p_tmImplies : FStar_Parser_AST.term -> FStar_Pprint.document) =
  fun e  ->
    match e.FStar_Parser_AST.tm with
    | FStar_Parser_AST.Op
        ({ FStar_Ident.idText = "==>"; FStar_Ident.idRange = uu____5597;_},e1::e2::[])
        ->
        let uu____5602 = str "==>"  in
        let uu____5603 = p_tmArrow p_tmFormula e1  in
        let uu____5604 = p_tmImplies e2  in
        infix0 uu____5602 uu____5603 uu____5604
    | uu____5605 -> p_tmArrow p_tmFormula e

and (p_tmArrow :
  (FStar_Parser_AST.term -> FStar_Pprint.document) ->
    FStar_Parser_AST.term -> FStar_Pprint.document)
  =
  fun p_Tm  ->
    fun e  ->
      let terms = p_tmArrow' p_Tm e  in
      let uu____5613 =
        FStar_List.splitAt
          ((FStar_List.length terms) - (Prims.parse_int "1")) terms
         in
      match uu____5613 with
      | (terms',last1) ->
          let last_op =
            if (FStar_List.length terms) > (Prims.parse_int "1")
            then
              FStar_Pprint.op_Hat_Hat FStar_Pprint.space FStar_Pprint.rarrow
            else FStar_Pprint.empty  in
          (match FStar_List.length terms with
           | _0_31 when _0_31 = (Prims.parse_int "1") -> FStar_List.hd terms
           | uu____5634 ->
               let uu____5635 =
                 let uu____5636 =
                   let uu____5637 =
                     let uu____5638 =
                       FStar_Pprint.op_Hat_Hat FStar_Pprint.rarrow break1  in
                     FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____5638
                      in
                   FStar_Pprint.separate uu____5637 terms  in
                 let uu____5639 =
                   let uu____5640 =
                     let uu____5641 =
                       let uu____5642 =
                         let uu____5643 =
                           let uu____5644 =
                             let uu____5645 =
                               FStar_Pprint.op_Hat_Hat FStar_Pprint.rarrow
                                 break1
                                in
                             FStar_Pprint.op_Hat_Hat FStar_Pprint.space
                               uu____5645
                              in
                           FStar_Pprint.separate uu____5644 terms'  in
                         FStar_Pprint.op_Hat_Hat uu____5643 last_op  in
                       let uu____5646 =
                         let uu____5647 =
                           let uu____5648 =
                             let uu____5649 =
                               let uu____5650 =
                                 FStar_Pprint.op_Hat_Hat FStar_Pprint.rarrow
                                   break1
                                  in
                               FStar_Pprint.op_Hat_Hat FStar_Pprint.space
                                 uu____5650
                                in
                             FStar_Pprint.separate uu____5649 terms'  in
                           FStar_Pprint.op_Hat_Hat uu____5648 last_op  in
                         jump2 uu____5647  in
                       FStar_Pprint.ifflat uu____5642 uu____5646  in
                     FStar_Pprint.group uu____5641  in
                   let uu____5651 = FStar_List.hd last1  in
                   prefix2 uu____5640 uu____5651  in
                 FStar_Pprint.ifflat uu____5636 uu____5639  in
               FStar_Pprint.group uu____5635)

and (p_tmArrow' :
  (FStar_Parser_AST.term -> FStar_Pprint.document) ->
    FStar_Parser_AST.term -> FStar_Pprint.document Prims.list)
  =
  fun p_Tm  ->
    fun e  ->
      match e.FStar_Parser_AST.tm with
      | FStar_Parser_AST.Product (bs,tgt) ->
          let uu____5664 = FStar_List.map (fun b  -> p_binder false b) bs  in
          let uu____5669 = p_tmArrow' p_Tm tgt  in
          FStar_List.append uu____5664 uu____5669
      | uu____5672 -> let uu____5673 = p_Tm e  in [uu____5673]

and (p_tmFormula : FStar_Parser_AST.term -> FStar_Pprint.document) =
  fun e  ->
    let conj =
      let uu____5676 =
        let uu____5677 = str "/\\"  in
        FStar_Pprint.op_Hat_Hat uu____5677 break1  in
      FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____5676  in
    let disj =
      let uu____5679 =
        let uu____5680 = str "\\/"  in
        FStar_Pprint.op_Hat_Hat uu____5680 break1  in
      FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____5679  in
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
        ({ FStar_Ident.idText = "\\/"; FStar_Ident.idRange = uu____5699;_},e1::e2::[])
        ->
        let uu____5704 = p_tmDisjunction e1  in
        let uu____5709 = let uu____5714 = p_tmConjunction e2  in [uu____5714]
           in
        FStar_List.append uu____5704 uu____5709
    | uu____5723 -> let uu____5724 = p_tmConjunction e  in [uu____5724]

and (p_tmConjunction :
  FStar_Parser_AST.term -> FStar_Pprint.document Prims.list) =
  fun e  ->
    match e.FStar_Parser_AST.tm with
    | FStar_Parser_AST.Op
        ({ FStar_Ident.idText = "/\\"; FStar_Ident.idRange = uu____5734;_},e1::e2::[])
        ->
        let uu____5739 = p_tmConjunction e1  in
        let uu____5742 = let uu____5745 = p_tmTuple e2  in [uu____5745]  in
        FStar_List.append uu____5739 uu____5742
    | uu____5746 -> let uu____5747 = p_tmTuple e  in [uu____5747]

and (p_tmTuple : FStar_Parser_AST.term -> FStar_Pprint.document) =
  fun e  -> with_comment p_tmTuple' e e.FStar_Parser_AST.range

and (p_tmTuple' : FStar_Parser_AST.term -> FStar_Pprint.document) =
  fun e  ->
    match e.FStar_Parser_AST.tm with
    | FStar_Parser_AST.Construct (lid,args) when is_tuple_constructor lid ->
        let uu____5764 = FStar_Pprint.op_Hat_Hat FStar_Pprint.comma break1
           in
        FStar_Pprint.separate_map uu____5764
          (fun uu____5772  ->
             match uu____5772 with | (e1,uu____5778) -> p_tmEq e1) args
    | uu____5779 -> p_tmEq e

and (paren_if_gt :
  Prims.int -> Prims.int -> FStar_Pprint.document -> FStar_Pprint.document) =
  fun curr  ->
    fun mine  ->
      fun doc1  ->
        if mine <= curr
        then doc1
        else
          (let uu____5784 =
             let uu____5785 =
               FStar_Pprint.op_Hat_Hat doc1 FStar_Pprint.rparen  in
             FStar_Pprint.op_Hat_Hat FStar_Pprint.lparen uu____5785  in
           FStar_Pprint.group uu____5784)

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
            let uu____5848 = levels op1  in
            (match uu____5848 with
             | (left1,mine,right1) ->
                 let uu____5858 =
                   let uu____5859 = FStar_All.pipe_left str op1  in
                   let uu____5860 = p_tmEqWith' p_X left1 e1  in
                   let uu____5861 = p_tmEqWith' p_X right1 e2  in
                   infix0 uu____5859 uu____5860 uu____5861  in
                 paren_if_gt curr mine uu____5858)
        | FStar_Parser_AST.Op
            ({ FStar_Ident.idText = ":="; FStar_Ident.idRange = uu____5862;_},e1::e2::[])
            ->
            let uu____5867 =
              let uu____5868 = p_tmEqWith p_X e1  in
              let uu____5869 =
                let uu____5870 =
                  let uu____5871 =
                    let uu____5872 = p_tmEqWith p_X e2  in
                    op_Hat_Slash_Plus_Hat FStar_Pprint.equals uu____5872  in
                  FStar_Pprint.op_Hat_Hat FStar_Pprint.colon uu____5871  in
                FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____5870  in
              FStar_Pprint.op_Hat_Hat uu____5868 uu____5869  in
            FStar_Pprint.group uu____5867
        | FStar_Parser_AST.Op
            ({ FStar_Ident.idText = "-"; FStar_Ident.idRange = uu____5873;_},e1::[])
            ->
            let uu____5877 = levels "-"  in
            (match uu____5877 with
             | (left1,mine,right1) ->
                 let uu____5887 = p_tmEqWith' p_X mine e1  in
                 FStar_Pprint.op_Hat_Slash_Hat FStar_Pprint.minus uu____5887)
        | uu____5888 -> p_tmNoEqWith p_X e

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
            (lid,(e1,uu____5959)::(e2,uu____5961)::[]) when
            (FStar_Ident.lid_equals lid FStar_Parser_Const.cons_lid) &&
              (let uu____5981 = is_list e  in Prims.op_Negation uu____5981)
            ->
            let op = "::"  in
            let uu____5983 = levels op  in
            (match uu____5983 with
             | (left1,mine,right1) ->
                 let uu____5993 =
                   let uu____5994 = str op  in
                   let uu____5995 = p_tmNoEqWith' p_X left1 e1  in
                   let uu____5996 = p_tmNoEqWith' p_X right1 e2  in
                   infix0 uu____5994 uu____5995 uu____5996  in
                 paren_if_gt curr mine uu____5993)
        | FStar_Parser_AST.Sum (binders,res) ->
            let op = "&"  in
            let uu____6004 = levels op  in
            (match uu____6004 with
             | (left1,mine,right1) ->
                 let p_dsumfst b =
                   let uu____6018 = p_binder false b  in
                   let uu____6019 =
                     let uu____6020 =
                       let uu____6021 = str op  in
                       FStar_Pprint.op_Hat_Hat uu____6021 break1  in
                     FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____6020
                      in
                   FStar_Pprint.op_Hat_Hat uu____6018 uu____6019  in
                 let uu____6022 =
                   let uu____6023 = FStar_Pprint.concat_map p_dsumfst binders
                      in
                   let uu____6024 = p_tmNoEqWith' p_X right1 res  in
                   FStar_Pprint.op_Hat_Hat uu____6023 uu____6024  in
                 paren_if_gt curr mine uu____6022)
        | FStar_Parser_AST.Op (op,e1::e2::[]) when is_operatorInfix34 op ->
            let op1 = FStar_Ident.text_of_id op  in
            let uu____6031 = levels op1  in
            (match uu____6031 with
             | (left1,mine,right1) ->
                 let uu____6041 =
                   let uu____6042 = str op1  in
                   let uu____6043 = p_tmNoEqWith' p_X left1 e1  in
                   let uu____6044 = p_tmNoEqWith' p_X right1 e2  in
                   infix0 uu____6042 uu____6043 uu____6044  in
                 paren_if_gt curr mine uu____6041)
        | FStar_Parser_AST.Record (with_opt,record_fields) ->
            let uu____6063 =
              let uu____6064 =
                default_or_map FStar_Pprint.empty p_with_clause with_opt  in
              let uu____6065 =
                let uu____6066 =
                  FStar_Pprint.op_Hat_Hat FStar_Pprint.semi break1  in
                separate_map_last uu____6066 p_simpleDef record_fields  in
              FStar_Pprint.op_Hat_Hat uu____6064 uu____6065  in
            braces_with_nesting uu____6063
        | FStar_Parser_AST.Op
            ({ FStar_Ident.idText = "~"; FStar_Ident.idRange = uu____6071;_},e1::[])
            ->
            let uu____6075 =
              let uu____6076 = str "~"  in
              let uu____6077 = p_atomicTerm e1  in
              FStar_Pprint.op_Hat_Hat uu____6076 uu____6077  in
            FStar_Pprint.group uu____6075
        | uu____6078 -> p_X e

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
        let uu____6085 =
          let uu____6086 = p_lidentOrUnderscore lid  in
          let uu____6087 =
            let uu____6088 = p_appTerm e1  in
            FStar_Pprint.op_Hat_Slash_Hat FStar_Pprint.colon uu____6088  in
          FStar_Pprint.op_Hat_Slash_Hat uu____6086 uu____6087  in
        FStar_Pprint.group uu____6085
    | FStar_Parser_AST.Refine (b,phi) -> p_refinedBinder b phi
    | uu____6091 -> p_appTerm e

and (p_with_clause : FStar_Parser_AST.term -> FStar_Pprint.document) =
  fun e  ->
    let uu____6093 = p_appTerm e  in
    let uu____6094 =
      let uu____6095 =
        let uu____6096 = str "with"  in
        FStar_Pprint.op_Hat_Hat uu____6096 break1  in
      FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____6095  in
    FStar_Pprint.op_Hat_Hat uu____6093 uu____6094

and (p_refinedBinder :
  FStar_Parser_AST.binder -> FStar_Parser_AST.term -> FStar_Pprint.document)
  =
  fun b  ->
    fun phi  ->
      match b.FStar_Parser_AST.b with
      | FStar_Parser_AST.Annotated (lid,t) ->
          let uu____6101 = p_lident lid  in
          p_refinement b.FStar_Parser_AST.aqual uu____6101 t phi
      | FStar_Parser_AST.TAnnotated uu____6102 ->
          failwith "Is this still used ?"
      | FStar_Parser_AST.Variable uu____6107 ->
          let uu____6108 =
            let uu____6109 = FStar_Parser_AST.binder_to_string b  in
            FStar_Util.format1
              "Imposible : a refined binder ought to be annotated %s"
              uu____6109
             in
          failwith uu____6108
      | FStar_Parser_AST.TVariable uu____6110 ->
          let uu____6111 =
            let uu____6112 = FStar_Parser_AST.binder_to_string b  in
            FStar_Util.format1
              "Imposible : a refined binder ought to be annotated %s"
              uu____6112
             in
          failwith uu____6111
      | FStar_Parser_AST.NoName uu____6113 ->
          let uu____6114 =
            let uu____6115 = FStar_Parser_AST.binder_to_string b  in
            FStar_Util.format1
              "Imposible : a refined binder ought to be annotated %s"
              uu____6115
             in
          failwith uu____6114

and (p_simpleDef :
  Prims.bool ->
    (FStar_Ident.lid,FStar_Parser_AST.term) FStar_Pervasives_Native.tuple2 ->
      FStar_Pprint.document)
  =
  fun ps  ->
    fun uu____6117  ->
      match uu____6117 with
      | (lid,e) ->
          let uu____6124 =
            let uu____6125 = p_qlident lid  in
            let uu____6126 =
              let uu____6127 = p_noSeqTerm ps false e  in
              FStar_Pprint.op_Hat_Slash_Hat FStar_Pprint.equals uu____6127
               in
            FStar_Pprint.op_Hat_Slash_Hat uu____6125 uu____6126  in
          FStar_Pprint.group uu____6124

and (p_appTerm : FStar_Parser_AST.term -> FStar_Pprint.document) =
  fun e  ->
    match e.FStar_Parser_AST.tm with
    | FStar_Parser_AST.App uu____6129 when is_general_application e ->
        let uu____6136 = head_and_args e  in
        (match uu____6136 with
         | (head1,args) ->
             let uu____6161 =
               let uu____6172 = FStar_ST.op_Bang should_print_fs_typ_app  in
               if uu____6172
               then
                 let uu____6202 =
                   FStar_Util.take
                     (fun uu____6226  ->
                        match uu____6226 with
                        | (uu____6231,aq) -> aq = FStar_Parser_AST.FsTypApp)
                     args
                    in
                 match uu____6202 with
                 | (fs_typ_args,args1) ->
                     let uu____6269 =
                       let uu____6270 = p_indexingTerm head1  in
                       let uu____6271 =
                         let uu____6272 =
                           FStar_Pprint.op_Hat_Hat FStar_Pprint.comma break1
                            in
                         soft_surround_map_or_flow (Prims.parse_int "2")
                           (Prims.parse_int "0") FStar_Pprint.empty
                           FStar_Pprint.langle uu____6272 FStar_Pprint.rangle
                           p_fsTypArg fs_typ_args
                          in
                       FStar_Pprint.op_Hat_Hat uu____6270 uu____6271  in
                     (uu____6269, args1)
               else
                 (let uu____6284 = p_indexingTerm head1  in
                  (uu____6284, args))
                in
             (match uu____6161 with
              | (head_doc,args1) ->
                  let uu____6305 =
                    let uu____6306 =
                      FStar_Pprint.op_Hat_Hat head_doc FStar_Pprint.space  in
                    soft_surround_map_or_flow (Prims.parse_int "2")
                      (Prims.parse_int "0") head_doc uu____6306 break1
                      FStar_Pprint.empty p_argTerm args1
                     in
                  FStar_Pprint.group uu____6305))
    | FStar_Parser_AST.Construct (lid,args) when
        (is_general_construction e) &&
          (let uu____6326 = is_dtuple_constructor lid  in
           Prims.op_Negation uu____6326)
        ->
        (match args with
         | [] -> p_quident lid
         | arg::[] ->
             let uu____6344 =
               let uu____6345 = p_quident lid  in
               let uu____6346 = p_argTerm arg  in
               FStar_Pprint.op_Hat_Slash_Hat uu____6345 uu____6346  in
             FStar_Pprint.group uu____6344
         | hd1::tl1 ->
             let uu____6363 =
               let uu____6364 =
                 let uu____6365 =
                   let uu____6366 = p_quident lid  in
                   let uu____6367 = p_argTerm hd1  in
                   prefix2 uu____6366 uu____6367  in
                 FStar_Pprint.group uu____6365  in
               let uu____6368 =
                 let uu____6369 =
                   FStar_Pprint.separate_map break1 p_argTerm tl1  in
                 jump2 uu____6369  in
               FStar_Pprint.op_Hat_Hat uu____6364 uu____6368  in
             FStar_Pprint.group uu____6363)
    | uu____6374 -> p_indexingTerm e

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
         (let uu____6383 = p_indexingTerm e  in
          FStar_Pprint.surround (Prims.parse_int "2") (Prims.parse_int "1")
            FStar_Pprint.langle uu____6383 FStar_Pprint.rangle))
    | (e,FStar_Parser_AST.Hash ) ->
        let uu____6385 = str "#"  in
        let uu____6386 = p_indexingTerm e  in
        FStar_Pprint.op_Hat_Hat uu____6385 uu____6386
    | (e,FStar_Parser_AST.Nothing ) -> p_indexingTerm e

and (p_fsTypArg :
  (FStar_Parser_AST.term,FStar_Parser_AST.imp) FStar_Pervasives_Native.tuple2
    -> FStar_Pprint.document)
  =
  fun uu____6388  ->
    match uu____6388 with | (e,uu____6394) -> p_indexingTerm e

and (p_indexingTerm_aux :
  (FStar_Parser_AST.term -> FStar_Pprint.document) ->
    FStar_Parser_AST.term -> FStar_Pprint.document)
  =
  fun exit1  ->
    fun e  ->
      match e.FStar_Parser_AST.tm with
      | FStar_Parser_AST.Op
          ({ FStar_Ident.idText = ".()"; FStar_Ident.idRange = uu____6399;_},e1::e2::[])
          ->
          let uu____6404 =
            let uu____6405 = p_indexingTerm_aux p_atomicTermNotQUident e1  in
            let uu____6406 =
              let uu____6407 =
                let uu____6408 = p_term false false e2  in
                soft_parens_with_nesting uu____6408  in
              FStar_Pprint.op_Hat_Hat FStar_Pprint.dot uu____6407  in
            FStar_Pprint.op_Hat_Hat uu____6405 uu____6406  in
          FStar_Pprint.group uu____6404
      | FStar_Parser_AST.Op
          ({ FStar_Ident.idText = ".[]"; FStar_Ident.idRange = uu____6409;_},e1::e2::[])
          ->
          let uu____6414 =
            let uu____6415 = p_indexingTerm_aux p_atomicTermNotQUident e1  in
            let uu____6416 =
              let uu____6417 =
                let uu____6418 = p_term false false e2  in
                soft_brackets_with_nesting uu____6418  in
              FStar_Pprint.op_Hat_Hat FStar_Pprint.dot uu____6417  in
            FStar_Pprint.op_Hat_Hat uu____6415 uu____6416  in
          FStar_Pprint.group uu____6414
      | uu____6419 -> exit1 e

and (p_indexingTerm : FStar_Parser_AST.term -> FStar_Pprint.document) =
  fun e  -> p_indexingTerm_aux p_atomicTerm e

and (p_atomicTerm : FStar_Parser_AST.term -> FStar_Pprint.document) =
  fun e  ->
    match e.FStar_Parser_AST.tm with
    | FStar_Parser_AST.LetOpen (lid,e1) ->
        let uu____6424 = p_quident lid  in
        let uu____6425 =
          let uu____6426 =
            let uu____6427 = p_term false false e1  in
            soft_parens_with_nesting uu____6427  in
          FStar_Pprint.op_Hat_Hat FStar_Pprint.dot uu____6426  in
        FStar_Pprint.op_Hat_Hat uu____6424 uu____6425
    | FStar_Parser_AST.Name lid -> p_quident lid
    | FStar_Parser_AST.Op (op,e1::[]) when is_general_prefix_op op ->
        let uu____6433 = str (FStar_Ident.text_of_id op)  in
        let uu____6434 = p_atomicTerm e1  in
        FStar_Pprint.op_Hat_Hat uu____6433 uu____6434
    | uu____6435 -> p_atomicTermNotQUident e

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
         | uu____6442 -> p_constant c)
    | FStar_Parser_AST.Name lid when
        FStar_Ident.lid_equals lid FStar_Parser_Const.true_lid -> str "True"
    | FStar_Parser_AST.Name lid when
        FStar_Ident.lid_equals lid FStar_Parser_Const.false_lid ->
        str "False"
    | FStar_Parser_AST.Op (op,e1::[]) when is_general_prefix_op op ->
        let uu____6449 = str (FStar_Ident.text_of_id op)  in
        let uu____6450 = p_atomicTermNotQUident e1  in
        FStar_Pprint.op_Hat_Hat uu____6449 uu____6450
    | FStar_Parser_AST.Op (op,[]) ->
        let uu____6454 =
          let uu____6455 =
            let uu____6456 = str (FStar_Ident.text_of_id op)  in
            let uu____6457 =
              FStar_Pprint.op_Hat_Hat FStar_Pprint.space FStar_Pprint.rparen
               in
            FStar_Pprint.op_Hat_Hat uu____6456 uu____6457  in
          FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____6455  in
        FStar_Pprint.op_Hat_Hat FStar_Pprint.lparen uu____6454
    | FStar_Parser_AST.Construct (lid,args) when is_dtuple_constructor lid ->
        let uu____6472 =
          FStar_Pprint.op_Hat_Hat FStar_Pprint.lparen FStar_Pprint.bar  in
        let uu____6473 =
          let uu____6474 = FStar_Pprint.op_Hat_Hat FStar_Pprint.comma break1
             in
          let uu____6475 = FStar_List.map FStar_Pervasives_Native.fst args
             in
          FStar_Pprint.separate_map uu____6474 p_tmEq uu____6475  in
        let uu____6482 =
          FStar_Pprint.op_Hat_Hat FStar_Pprint.bar FStar_Pprint.rparen  in
        FStar_Pprint.surround (Prims.parse_int "2") (Prims.parse_int "1")
          uu____6472 uu____6473 uu____6482
    | FStar_Parser_AST.Project (e1,lid) ->
        let uu____6485 =
          let uu____6486 = p_atomicTermNotQUident e1  in
          let uu____6487 =
            let uu____6488 = p_qlident lid  in
            FStar_Pprint.op_Hat_Hat FStar_Pprint.dot uu____6488  in
          FStar_Pprint.prefix (Prims.parse_int "2") (Prims.parse_int "0")
            uu____6486 uu____6487
           in
        FStar_Pprint.group uu____6485
    | uu____6489 -> p_projectionLHS e

and (p_projectionLHS : FStar_Parser_AST.term -> FStar_Pprint.document) =
  fun e  ->
    match e.FStar_Parser_AST.tm with
    | FStar_Parser_AST.Var lid -> p_qlident lid
    | FStar_Parser_AST.Projector (constr_lid,field_lid) ->
        let uu____6494 = p_quident constr_lid  in
        let uu____6495 =
          let uu____6496 =
            let uu____6497 = p_lident field_lid  in
            FStar_Pprint.op_Hat_Hat FStar_Pprint.dot uu____6497  in
          FStar_Pprint.op_Hat_Hat FStar_Pprint.qmark uu____6496  in
        FStar_Pprint.op_Hat_Hat uu____6494 uu____6495
    | FStar_Parser_AST.Discrim constr_lid ->
        let uu____6499 = p_quident constr_lid  in
        FStar_Pprint.op_Hat_Hat uu____6499 FStar_Pprint.qmark
    | FStar_Parser_AST.Paren e1 ->
        let uu____6501 = p_term false false e1  in
        soft_parens_with_nesting uu____6501
    | uu____6502 when is_array e ->
        let es = extract_from_list e  in
        let uu____6506 =
          FStar_Pprint.op_Hat_Hat FStar_Pprint.lbracket FStar_Pprint.bar  in
        let uu____6507 =
          let uu____6508 = FStar_Pprint.op_Hat_Hat FStar_Pprint.semi break1
             in
          separate_map_or_flow_last uu____6508
            (fun ps  -> p_noSeqTerm ps false) es
           in
        let uu____6511 =
          FStar_Pprint.op_Hat_Hat FStar_Pprint.bar FStar_Pprint.rbracket  in
        FStar_Pprint.surround (Prims.parse_int "2") (Prims.parse_int "0")
          uu____6506 uu____6507 uu____6511
    | uu____6512 when is_list e ->
        let uu____6513 =
          let uu____6514 = FStar_Pprint.op_Hat_Hat FStar_Pprint.semi break1
             in
          let uu____6515 = extract_from_list e  in
          separate_map_or_flow_last uu____6514
            (fun ps  -> p_noSeqTerm ps false) uu____6515
           in
        FStar_Pprint.surround (Prims.parse_int "2") (Prims.parse_int "0")
          FStar_Pprint.lbracket uu____6513 FStar_Pprint.rbracket
    | uu____6520 when is_lex_list e ->
        let uu____6521 =
          FStar_Pprint.op_Hat_Hat FStar_Pprint.percent FStar_Pprint.lbracket
           in
        let uu____6522 =
          let uu____6523 = FStar_Pprint.op_Hat_Hat FStar_Pprint.semi break1
             in
          let uu____6524 = extract_from_list e  in
          separate_map_or_flow_last uu____6523
            (fun ps  -> p_noSeqTerm ps false) uu____6524
           in
        FStar_Pprint.surround (Prims.parse_int "2") (Prims.parse_int "1")
          uu____6521 uu____6522 FStar_Pprint.rbracket
    | uu____6529 when is_ref_set e ->
        let es = extract_from_ref_set e  in
        let uu____6533 =
          FStar_Pprint.op_Hat_Hat FStar_Pprint.bang FStar_Pprint.lbrace  in
        let uu____6534 =
          let uu____6535 = FStar_Pprint.op_Hat_Hat FStar_Pprint.comma break1
             in
          separate_map_or_flow uu____6535 p_appTerm es  in
        FStar_Pprint.surround (Prims.parse_int "2") (Prims.parse_int "0")
          uu____6533 uu____6534 FStar_Pprint.rbrace
    | FStar_Parser_AST.Labeled (e1,s,b) ->
        let uu____6539 = str (Prims.strcat "(*" (Prims.strcat s "*)"))  in
        let uu____6540 = p_term false false e1  in
        FStar_Pprint.op_Hat_Slash_Hat uu____6539 uu____6540
    | FStar_Parser_AST.Op (op,args) when
        let uu____6547 = handleable_op op args  in
        Prims.op_Negation uu____6547 ->
        let uu____6548 =
          let uu____6549 =
            let uu____6550 =
              let uu____6551 =
                let uu____6552 =
                  FStar_Util.string_of_int (FStar_List.length args)  in
                Prims.strcat uu____6552
                  " arguments couldn't be handled by the pretty printer"
                 in
              Prims.strcat " with " uu____6551  in
            Prims.strcat (FStar_Ident.text_of_id op) uu____6550  in
          Prims.strcat "Operation " uu____6549  in
        failwith uu____6548
    | FStar_Parser_AST.Uvar uu____6553 ->
        failwith "Unexpected universe variable out of universe context"
    | FStar_Parser_AST.Wild  ->
        let uu____6554 = p_term false false e  in
        soft_parens_with_nesting uu____6554
    | FStar_Parser_AST.Const uu____6555 ->
        let uu____6556 = p_term false false e  in
        soft_parens_with_nesting uu____6556
    | FStar_Parser_AST.Op uu____6557 ->
        let uu____6564 = p_term false false e  in
        soft_parens_with_nesting uu____6564
    | FStar_Parser_AST.Tvar uu____6565 ->
        let uu____6566 = p_term false false e  in
        soft_parens_with_nesting uu____6566
    | FStar_Parser_AST.Var uu____6567 ->
        let uu____6568 = p_term false false e  in
        soft_parens_with_nesting uu____6568
    | FStar_Parser_AST.Name uu____6569 ->
        let uu____6570 = p_term false false e  in
        soft_parens_with_nesting uu____6570
    | FStar_Parser_AST.Construct uu____6571 ->
        let uu____6582 = p_term false false e  in
        soft_parens_with_nesting uu____6582
    | FStar_Parser_AST.Abs uu____6583 ->
        let uu____6590 = p_term false false e  in
        soft_parens_with_nesting uu____6590
    | FStar_Parser_AST.App uu____6591 ->
        let uu____6598 = p_term false false e  in
        soft_parens_with_nesting uu____6598
    | FStar_Parser_AST.Let uu____6599 ->
        let uu____6620 = p_term false false e  in
        soft_parens_with_nesting uu____6620
    | FStar_Parser_AST.LetOpen uu____6621 ->
        let uu____6626 = p_term false false e  in
        soft_parens_with_nesting uu____6626
    | FStar_Parser_AST.Seq uu____6627 ->
        let uu____6632 = p_term false false e  in
        soft_parens_with_nesting uu____6632
    | FStar_Parser_AST.Bind uu____6633 ->
        let uu____6640 = p_term false false e  in
        soft_parens_with_nesting uu____6640
    | FStar_Parser_AST.If uu____6641 ->
        let uu____6648 = p_term false false e  in
        soft_parens_with_nesting uu____6648
    | FStar_Parser_AST.Match uu____6649 ->
        let uu____6664 = p_term false false e  in
        soft_parens_with_nesting uu____6664
    | FStar_Parser_AST.TryWith uu____6665 ->
        let uu____6680 = p_term false false e  in
        soft_parens_with_nesting uu____6680
    | FStar_Parser_AST.Ascribed uu____6681 ->
        let uu____6690 = p_term false false e  in
        soft_parens_with_nesting uu____6690
    | FStar_Parser_AST.Record uu____6691 ->
        let uu____6704 = p_term false false e  in
        soft_parens_with_nesting uu____6704
    | FStar_Parser_AST.Project uu____6705 ->
        let uu____6710 = p_term false false e  in
        soft_parens_with_nesting uu____6710
    | FStar_Parser_AST.Product uu____6711 ->
        let uu____6718 = p_term false false e  in
        soft_parens_with_nesting uu____6718
    | FStar_Parser_AST.Sum uu____6719 ->
        let uu____6726 = p_term false false e  in
        soft_parens_with_nesting uu____6726
    | FStar_Parser_AST.QForall uu____6727 ->
        let uu____6740 = p_term false false e  in
        soft_parens_with_nesting uu____6740
    | FStar_Parser_AST.QExists uu____6741 ->
        let uu____6754 = p_term false false e  in
        soft_parens_with_nesting uu____6754
    | FStar_Parser_AST.Refine uu____6755 ->
        let uu____6760 = p_term false false e  in
        soft_parens_with_nesting uu____6760
    | FStar_Parser_AST.NamedTyp uu____6761 ->
        let uu____6766 = p_term false false e  in
        soft_parens_with_nesting uu____6766
    | FStar_Parser_AST.Requires uu____6767 ->
        let uu____6774 = p_term false false e  in
        soft_parens_with_nesting uu____6774
    | FStar_Parser_AST.Ensures uu____6775 ->
        let uu____6782 = p_term false false e  in
        soft_parens_with_nesting uu____6782
    | FStar_Parser_AST.Attributes uu____6783 ->
        let uu____6786 = p_term false false e  in
        soft_parens_with_nesting uu____6786
    | FStar_Parser_AST.Quote uu____6787 ->
        let uu____6792 = p_term false false e  in
        soft_parens_with_nesting uu____6792
    | FStar_Parser_AST.VQuote uu____6793 ->
        let uu____6794 = p_term false false e  in
        soft_parens_with_nesting uu____6794

and (p_constant : FStar_Const.sconst -> FStar_Pprint.document) =
  fun uu___63_6795  ->
    match uu___63_6795 with
    | FStar_Const.Const_effect  -> str "Effect"
    | FStar_Const.Const_unit  -> str "()"
    | FStar_Const.Const_bool b -> FStar_Pprint.doc_of_bool b
    | FStar_Const.Const_float x -> str (FStar_Util.string_of_float x)
    | FStar_Const.Const_char x ->
        let uu____6799 = FStar_Pprint.doc_of_char x  in
        FStar_Pprint.squotes uu____6799
    | FStar_Const.Const_string (s,uu____6801) ->
        let uu____6802 = str s  in FStar_Pprint.dquotes uu____6802
    | FStar_Const.Const_bytearray (bytes,uu____6804) ->
        let uu____6809 =
          let uu____6810 = str (FStar_Util.string_of_bytes bytes)  in
          FStar_Pprint.dquotes uu____6810  in
        let uu____6811 = str "B"  in
        FStar_Pprint.op_Hat_Hat uu____6809 uu____6811
    | FStar_Const.Const_int (repr,sign_width_opt) ->
        let signedness uu___61_6829 =
          match uu___61_6829 with
          | FStar_Const.Unsigned  -> str "u"
          | FStar_Const.Signed  -> FStar_Pprint.empty  in
        let width uu___62_6833 =
          match uu___62_6833 with
          | FStar_Const.Int8  -> str "y"
          | FStar_Const.Int16  -> str "s"
          | FStar_Const.Int32  -> str "l"
          | FStar_Const.Int64  -> str "L"  in
        let ending =
          default_or_map FStar_Pprint.empty
            (fun uu____6844  ->
               match uu____6844 with
               | (s,w) ->
                   let uu____6851 = signedness s  in
                   let uu____6852 = width w  in
                   FStar_Pprint.op_Hat_Hat uu____6851 uu____6852)
            sign_width_opt
           in
        let uu____6853 = str repr  in
        FStar_Pprint.op_Hat_Hat uu____6853 ending
    | FStar_Const.Const_range_of  -> str "range_of"
    | FStar_Const.Const_set_range_of  -> str "set_range_of"
    | FStar_Const.Const_range r ->
        let uu____6855 = FStar_Range.string_of_range r  in str uu____6855
    | FStar_Const.Const_reify  -> str "reify"
    | FStar_Const.Const_reflect lid ->
        let uu____6857 = p_quident lid  in
        let uu____6858 =
          let uu____6859 =
            let uu____6860 = str "reflect"  in
            FStar_Pprint.op_Hat_Hat FStar_Pprint.dot uu____6860  in
          FStar_Pprint.op_Hat_Hat FStar_Pprint.qmark uu____6859  in
        FStar_Pprint.op_Hat_Hat uu____6857 uu____6858

and (p_universe : FStar_Parser_AST.term -> FStar_Pprint.document) =
  fun u  ->
    let uu____6862 = str "u#"  in
    let uu____6863 = p_atomicUniverse u  in
    FStar_Pprint.op_Hat_Hat uu____6862 uu____6863

and (p_universeFrom : FStar_Parser_AST.term -> FStar_Pprint.document) =
  fun u  ->
    match u.FStar_Parser_AST.tm with
    | FStar_Parser_AST.Op
        ({ FStar_Ident.idText = "+"; FStar_Ident.idRange = uu____6865;_},u1::u2::[])
        ->
        let uu____6870 =
          let uu____6871 = p_universeFrom u1  in
          let uu____6872 =
            let uu____6873 = p_universeFrom u2  in
            FStar_Pprint.op_Hat_Slash_Hat FStar_Pprint.plus uu____6873  in
          FStar_Pprint.op_Hat_Slash_Hat uu____6871 uu____6872  in
        FStar_Pprint.group uu____6870
    | FStar_Parser_AST.App uu____6874 ->
        let uu____6881 = head_and_args u  in
        (match uu____6881 with
         | (head1,args) ->
             (match head1.FStar_Parser_AST.tm with
              | FStar_Parser_AST.Var maybe_max_lid when
                  FStar_Ident.lid_equals maybe_max_lid
                    FStar_Parser_Const.max_lid
                  ->
                  let uu____6907 =
                    let uu____6908 = p_qlident FStar_Parser_Const.max_lid  in
                    let uu____6909 =
                      FStar_Pprint.separate_map FStar_Pprint.space
                        (fun uu____6917  ->
                           match uu____6917 with
                           | (u1,uu____6923) -> p_atomicUniverse u1) args
                       in
                    op_Hat_Slash_Plus_Hat uu____6908 uu____6909  in
                  FStar_Pprint.group uu____6907
              | uu____6924 ->
                  let uu____6925 =
                    let uu____6926 = FStar_Parser_AST.term_to_string u  in
                    FStar_Util.format1 "Invalid term in universe context %s"
                      uu____6926
                     in
                  failwith uu____6925))
    | uu____6927 -> p_atomicUniverse u

and (p_atomicUniverse : FStar_Parser_AST.term -> FStar_Pprint.document) =
  fun u  ->
    match u.FStar_Parser_AST.tm with
    | FStar_Parser_AST.Wild  -> FStar_Pprint.underscore
    | FStar_Parser_AST.Const (FStar_Const.Const_int (r,sw)) ->
        p_constant (FStar_Const.Const_int (r, sw))
    | FStar_Parser_AST.Uvar id1 -> str (FStar_Ident.text_of_id id1)
    | FStar_Parser_AST.Paren u1 ->
        let uu____6951 = p_universeFrom u1  in
        soft_parens_with_nesting uu____6951
    | FStar_Parser_AST.Op
        ({ FStar_Ident.idText = "+"; FStar_Ident.idRange = uu____6952;_},uu____6953::uu____6954::[])
        ->
        let uu____6957 = p_universeFrom u  in
        soft_parens_with_nesting uu____6957
    | FStar_Parser_AST.App uu____6958 ->
        let uu____6965 = p_universeFrom u  in
        soft_parens_with_nesting uu____6965
    | uu____6966 ->
        let uu____6967 =
          let uu____6968 = FStar_Parser_AST.term_to_string u  in
          FStar_Util.format1 "Invalid term in universe context %s" uu____6968
           in
        failwith uu____6967

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
       | FStar_Parser_AST.Module (uu____7008,decls) -> FStar_Pprint.empty
       | FStar_Parser_AST.Interface (uu____7014,decls,uu____7016) ->
           FStar_Pprint.empty
        in
     FStar_ST.op_Colon_Equals should_print_fs_typ_app false; res)
  
let (comments_to_document :
  (Prims.string,FStar_Range.range) FStar_Pervasives_Native.tuple2 Prims.list
    -> FStar_Pprint.document)
  =
  fun comments  ->
    FStar_Pprint.separate_map FStar_Pprint.hardline
      (fun uu____7063  ->
         match uu____7063 with | (comment,range) -> str comment) comments
  
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
        | FStar_Parser_AST.Module (uu____7103,decls) -> decls
        | FStar_Parser_AST.Interface (uu____7109,decls,uu____7111) -> decls
         in
      FStar_ST.op_Colon_Equals should_print_fs_typ_app false;
      (match decls with
       | [] -> (FStar_Pprint.empty, comments)
       | d::ds ->
           let uu____7156 =
             match ds with
             | {
                 FStar_Parser_AST.d = FStar_Parser_AST.Pragma
                   (FStar_Parser_AST.LightOff );
                 FStar_Parser_AST.drange = uu____7169;
                 FStar_Parser_AST.doc = uu____7170;
                 FStar_Parser_AST.quals = uu____7171;
                 FStar_Parser_AST.attrs = uu____7172;_}::uu____7173 ->
                 let d0 = FStar_List.hd ds  in
                 let uu____7179 =
                   let uu____7182 =
                     let uu____7185 = FStar_List.tl ds  in d :: uu____7185
                      in
                   d0 :: uu____7182  in
                 (uu____7179, (d0.FStar_Parser_AST.drange))
             | uu____7190 -> ((d :: ds), (d.FStar_Parser_AST.drange))  in
           (match uu____7156 with
            | (decls1,first_range) ->
                let extract_decl_range d1 = d1.FStar_Parser_AST.drange  in
                (FStar_ST.op_Colon_Equals comment_stack comments;
                 (let initial_comment =
                    let uu____7248 = FStar_Range.start_of_range first_range
                       in
                    place_comments_until_pos (Prims.parse_int "0")
                      (Prims.parse_int "1") uu____7248 FStar_Pprint.empty
                     in
                  let doc1 =
                    separate_map_with_comments FStar_Pprint.empty
                      FStar_Pprint.empty decl_to_document decls1
                      extract_decl_range
                     in
                  let comments1 = FStar_ST.op_Bang comment_stack  in
                  FStar_ST.op_Colon_Equals comment_stack [];
                  FStar_ST.op_Colon_Equals should_print_fs_typ_app false;
                  (let uu____7344 =
                     FStar_Pprint.op_Hat_Hat initial_comment doc1  in
                   (uu____7344, comments1))))))
  