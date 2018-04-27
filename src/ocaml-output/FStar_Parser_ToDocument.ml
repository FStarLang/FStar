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
let (surround_maybe_empty :
  Prims.int ->
    Prims.int ->
      FStar_Pprint.document ->
        FStar_Pprint.document ->
          FStar_Pprint.document -> FStar_Pprint.document)
  =
  fun n1  ->
    fun b  ->
      fun doc1  ->
        fun doc2  ->
          fun doc3  ->
            if doc2 = FStar_Pprint.empty
            then
              let uu____499 = FStar_Pprint.op_Hat_Slash_Hat doc1 doc3  in
              FStar_Pprint.group uu____499
            else FStar_Pprint.surround n1 b doc1 doc2 doc3
  
let soft_surround_separate_map :
  'Auu____510 .
    Prims.int ->
      Prims.int ->
        FStar_Pprint.document ->
          FStar_Pprint.document ->
            FStar_Pprint.document ->
              FStar_Pprint.document ->
                ('Auu____510 -> FStar_Pprint.document) ->
                  'Auu____510 Prims.list -> FStar_Pprint.document
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
                    (let uu____555 = FStar_Pprint.separate_map sep f xs  in
                     FStar_Pprint.soft_surround n1 b opening uu____555
                       closing)
  
let soft_surround_map_or_flow :
  'Auu____565 .
    Prims.int ->
      Prims.int ->
        FStar_Pprint.document ->
          FStar_Pprint.document ->
            FStar_Pprint.document ->
              FStar_Pprint.document ->
                ('Auu____565 -> FStar_Pprint.document) ->
                  'Auu____565 Prims.list -> FStar_Pprint.document
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
                    (let uu____610 = separate_map_or_flow sep f xs  in
                     FStar_Pprint.soft_surround n1 b opening uu____610
                       closing)
  
let (doc_of_fsdoc :
  (Prims.string,(Prims.string,Prims.string) FStar_Pervasives_Native.tuple2
                  Prims.list)
    FStar_Pervasives_Native.tuple2 -> FStar_Pprint.document)
  =
  fun uu____623  ->
    match uu____623 with
    | (comment,keywords) ->
        let uu____648 =
          let uu____649 =
            let uu____652 = str comment  in
            let uu____653 =
              let uu____656 =
                let uu____659 =
                  FStar_Pprint.separate_map FStar_Pprint.comma
                    (fun uu____668  ->
                       match uu____668 with
                       | (k,v1) ->
                           let uu____675 =
                             let uu____678 = str k  in
                             let uu____679 =
                               let uu____682 =
                                 let uu____685 = str v1  in [uu____685]  in
                               FStar_Pprint.rarrow :: uu____682  in
                             uu____678 :: uu____679  in
                           FStar_Pprint.concat uu____675) keywords
                   in
                [uu____659]  in
              FStar_Pprint.space :: uu____656  in
            uu____652 :: uu____653  in
          FStar_Pprint.concat uu____649  in
        FStar_Pprint.group uu____648
  
let (is_unit : FStar_Parser_AST.term -> Prims.bool) =
  fun e  ->
    match e.FStar_Parser_AST.tm with
    | FStar_Parser_AST.Const (FStar_Const.Const_unit ) -> true
    | uu____689 -> false
  
let (matches_var : FStar_Parser_AST.term -> FStar_Ident.ident -> Prims.bool)
  =
  fun t  ->
    fun x  ->
      match t.FStar_Parser_AST.tm with
      | FStar_Parser_AST.Var y ->
          let uu____697 = FStar_Ident.text_of_lid y  in
          x.FStar_Ident.idText = uu____697
      | uu____698 -> false
  
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
        | FStar_Parser_AST.Construct (lid,uu____727::(e2,uu____729)::[]) ->
            (FStar_Ident.lid_equals lid cons_lid1) && (aux e2)
        | uu____752 -> false  in
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
    | FStar_Parser_AST.Construct (uu____764,[]) -> []
    | FStar_Parser_AST.Construct
        (uu____775,(e1,FStar_Parser_AST.Nothing )::(e2,FStar_Parser_AST.Nothing
                                                    )::[])
        -> let uu____796 = extract_from_list e2  in e1 :: uu____796
    | uu____799 ->
        let uu____800 =
          let uu____801 = FStar_Parser_AST.term_to_string e  in
          FStar_Util.format1 "Not a list %s" uu____801  in
        failwith uu____800
  
let (is_array : FStar_Parser_AST.term -> Prims.bool) =
  fun e  ->
    match e.FStar_Parser_AST.tm with
    | FStar_Parser_AST.App
        ({ FStar_Parser_AST.tm = FStar_Parser_AST.Var lid;
           FStar_Parser_AST.range = uu____808;
           FStar_Parser_AST.level = uu____809;_},l,FStar_Parser_AST.Nothing
         )
        ->
        (FStar_Ident.lid_equals lid FStar_Parser_Const.array_mk_array_lid) &&
          (is_list l)
    | uu____811 -> false
  
let rec (is_ref_set : FStar_Parser_AST.term -> Prims.bool) =
  fun e  ->
    match e.FStar_Parser_AST.tm with
    | FStar_Parser_AST.Var maybe_empty_lid ->
        FStar_Ident.lid_equals maybe_empty_lid FStar_Parser_Const.set_empty
    | FStar_Parser_AST.App
        ({ FStar_Parser_AST.tm = FStar_Parser_AST.Var maybe_singleton_lid;
           FStar_Parser_AST.range = uu____817;
           FStar_Parser_AST.level = uu____818;_},{
                                                   FStar_Parser_AST.tm =
                                                     FStar_Parser_AST.App
                                                     ({
                                                        FStar_Parser_AST.tm =
                                                          FStar_Parser_AST.Var
                                                          maybe_addr_of_lid;
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
                FStar_Parser_AST.range = uu____826;
                FStar_Parser_AST.level = uu____827;_},e1,FStar_Parser_AST.Nothing
              );
           FStar_Parser_AST.range = uu____829;
           FStar_Parser_AST.level = uu____830;_},e2,FStar_Parser_AST.Nothing
         )
        ->
        ((FStar_Ident.lid_equals maybe_union_lid FStar_Parser_Const.set_union)
           && (is_ref_set e1))
          && (is_ref_set e2)
    | uu____832 -> false
  
let rec (extract_from_ref_set :
  FStar_Parser_AST.term -> FStar_Parser_AST.term Prims.list) =
  fun e  ->
    match e.FStar_Parser_AST.tm with
    | FStar_Parser_AST.Var uu____840 -> []
    | FStar_Parser_AST.App
        ({ FStar_Parser_AST.tm = FStar_Parser_AST.Var uu____841;
           FStar_Parser_AST.range = uu____842;
           FStar_Parser_AST.level = uu____843;_},{
                                                   FStar_Parser_AST.tm =
                                                     FStar_Parser_AST.App
                                                     ({
                                                        FStar_Parser_AST.tm =
                                                          FStar_Parser_AST.Var
                                                          uu____844;
                                                        FStar_Parser_AST.range
                                                          = uu____845;
                                                        FStar_Parser_AST.level
                                                          = uu____846;_},e1,FStar_Parser_AST.Nothing
                                                      );
                                                   FStar_Parser_AST.range =
                                                     uu____848;
                                                   FStar_Parser_AST.level =
                                                     uu____849;_},FStar_Parser_AST.Nothing
         )
        -> [e1]
    | FStar_Parser_AST.App
        ({
           FStar_Parser_AST.tm = FStar_Parser_AST.App
             ({ FStar_Parser_AST.tm = FStar_Parser_AST.Var uu____850;
                FStar_Parser_AST.range = uu____851;
                FStar_Parser_AST.level = uu____852;_},e1,FStar_Parser_AST.Nothing
              );
           FStar_Parser_AST.range = uu____854;
           FStar_Parser_AST.level = uu____855;_},e2,FStar_Parser_AST.Nothing
         )
        ->
        let uu____857 = extract_from_ref_set e1  in
        let uu____860 = extract_from_ref_set e2  in
        FStar_List.append uu____857 uu____860
    | uu____863 ->
        let uu____864 =
          let uu____865 = FStar_Parser_AST.term_to_string e  in
          FStar_Util.format1 "Not a ref set %s" uu____865  in
        failwith uu____864
  
let (is_general_application : FStar_Parser_AST.term -> Prims.bool) =
  fun e  ->
    let uu____871 = (is_array e) || (is_ref_set e)  in
    Prims.op_Negation uu____871
  
let (is_general_construction : FStar_Parser_AST.term -> Prims.bool) =
  fun e  ->
    let uu____875 = (is_list e) || (is_lex_list e)  in
    Prims.op_Negation uu____875
  
let (is_general_prefix_op : FStar_Ident.ident -> Prims.bool) =
  fun op  ->
    let op_starting_char =
      let uu____880 = FStar_Ident.text_of_id op  in
      FStar_Util.char_at uu____880 (Prims.parse_int "0")  in
    ((op_starting_char = 33) || (op_starting_char = 63)) ||
      ((op_starting_char = 126) &&
         (let uu____885 = FStar_Ident.text_of_id op  in uu____885 <> "~"))
  
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
      | uu____945 -> (e1, acc)  in
    aux e []
  
type associativity =
  | Left 
  | Right 
  | NonAssoc [@@deriving show]
let (uu___is_Left : associativity -> Prims.bool) =
  fun projectee  -> match projectee with | Left  -> true | uu____959 -> false 
let (uu___is_Right : associativity -> Prims.bool) =
  fun projectee  ->
    match projectee with | Right  -> true | uu____963 -> false
  
let (uu___is_NonAssoc : associativity -> Prims.bool) =
  fun projectee  ->
    match projectee with | NonAssoc  -> true | uu____967 -> false
  
type token = (FStar_Char.char,Prims.string) FStar_Util.either[@@deriving
                                                               show]
type associativity_level =
  (associativity,token Prims.list) FStar_Pervasives_Native.tuple2[@@deriving
                                                                   show]
let (token_to_string :
  (FStar_BaseTypes.char,Prims.string) FStar_Util.either -> Prims.string) =
  fun uu___53_985  ->
    match uu___53_985 with
    | FStar_Util.Inl c -> Prims.strcat (FStar_Util.string_of_char c) ".*"
    | FStar_Util.Inr s -> s
  
let (matches_token :
  Prims.string ->
    (FStar_Char.char,Prims.string) FStar_Util.either -> Prims.bool)
  =
  fun s  ->
    fun uu___54_1002  ->
      match uu___54_1002 with
      | FStar_Util.Inl c ->
          let uu____1011 = FStar_String.get s (Prims.parse_int "0")  in
          uu____1011 = c
      | FStar_Util.Inr s' -> s = s'
  
let matches_level :
  'Auu____1019 .
    Prims.string ->
      ('Auu____1019,(FStar_Char.char,Prims.string) FStar_Util.either
                      Prims.list)
        FStar_Pervasives_Native.tuple2 -> Prims.bool
  =
  fun s  ->
    fun uu____1038  ->
      match uu____1038 with
      | (assoc_levels,tokens) ->
          let uu____1066 = FStar_List.tryFind (matches_token s) tokens  in
          uu____1066 <> FStar_Pervasives_Native.None
  
let opinfix4 :
  'Auu____1092 .
    Prims.unit ->
      (associativity,('Auu____1092,Prims.string) FStar_Util.either Prims.list)
        FStar_Pervasives_Native.tuple2
  = fun uu____1103  -> (Right, [FStar_Util.Inr "**"]) 
let opinfix3 :
  'Auu____1119 .
    Prims.unit ->
      (associativity,(FStar_Char.char,'Auu____1119) FStar_Util.either
                       Prims.list)
        FStar_Pervasives_Native.tuple2
  =
  fun uu____1131  ->
    (Left, [FStar_Util.Inl 42; FStar_Util.Inl 47; FStar_Util.Inl 37])
  
let opinfix2 :
  'Auu____1166 .
    Prims.unit ->
      (associativity,(FStar_Char.char,'Auu____1166) FStar_Util.either
                       Prims.list)
        FStar_Pervasives_Native.tuple2
  = fun uu____1178  -> (Left, [FStar_Util.Inl 43; FStar_Util.Inl 45]) 
let minus_lvl :
  'Auu____1206 .
    Prims.unit ->
      (associativity,('Auu____1206,Prims.string) FStar_Util.either Prims.list)
        FStar_Pervasives_Native.tuple2
  = fun uu____1217  -> (Left, [FStar_Util.Inr "-"]) 
let opinfix1 :
  'Auu____1233 .
    Prims.unit ->
      (associativity,(FStar_Char.char,'Auu____1233) FStar_Util.either
                       Prims.list)
        FStar_Pervasives_Native.tuple2
  = fun uu____1245  -> (Right, [FStar_Util.Inl 64; FStar_Util.Inl 94]) 
let pipe_right :
  'Auu____1273 .
    Prims.unit ->
      (associativity,('Auu____1273,Prims.string) FStar_Util.either Prims.list)
        FStar_Pervasives_Native.tuple2
  = fun uu____1284  -> (Left, [FStar_Util.Inr "|>"]) 
let opinfix0d :
  'Auu____1300 .
    Prims.unit ->
      (associativity,(FStar_Char.char,'Auu____1300) FStar_Util.either
                       Prims.list)
        FStar_Pervasives_Native.tuple2
  = fun uu____1312  -> (Left, [FStar_Util.Inl 36]) 
let opinfix0c :
  'Auu____1333 .
    Prims.unit ->
      (associativity,(FStar_Char.char,'Auu____1333) FStar_Util.either
                       Prims.list)
        FStar_Pervasives_Native.tuple2
  =
  fun uu____1345  ->
    (Left, [FStar_Util.Inl 61; FStar_Util.Inl 60; FStar_Util.Inl 62])
  
let equal :
  'Auu____1380 .
    Prims.unit ->
      (associativity,('Auu____1380,Prims.string) FStar_Util.either Prims.list)
        FStar_Pervasives_Native.tuple2
  = fun uu____1391  -> (Left, [FStar_Util.Inr "="]) 
let opinfix0b :
  'Auu____1407 .
    Prims.unit ->
      (associativity,(FStar_Char.char,'Auu____1407) FStar_Util.either
                       Prims.list)
        FStar_Pervasives_Native.tuple2
  = fun uu____1419  -> (Left, [FStar_Util.Inl 38]) 
let opinfix0a :
  'Auu____1440 .
    Prims.unit ->
      (associativity,(FStar_Char.char,'Auu____1440) FStar_Util.either
                       Prims.list)
        FStar_Pervasives_Native.tuple2
  = fun uu____1452  -> (Left, [FStar_Util.Inl 124]) 
let colon_equals :
  'Auu____1473 .
    Prims.unit ->
      (associativity,('Auu____1473,Prims.string) FStar_Util.either Prims.list)
        FStar_Pervasives_Native.tuple2
  = fun uu____1484  -> (NonAssoc, [FStar_Util.Inr ":="]) 
let amp :
  'Auu____1500 .
    Prims.unit ->
      (associativity,('Auu____1500,Prims.string) FStar_Util.either Prims.list)
        FStar_Pervasives_Native.tuple2
  = fun uu____1511  -> (Right, [FStar_Util.Inr "&"]) 
let colon_colon :
  'Auu____1527 .
    Prims.unit ->
      (associativity,('Auu____1527,Prims.string) FStar_Util.either Prims.list)
        FStar_Pervasives_Native.tuple2
  = fun uu____1538  -> (Right, [FStar_Util.Inr "::"]) 
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
  let levels_from_associativity l uu___55_1745 =
    match uu___55_1745 with
    | Left  -> (l, l, (l - (Prims.parse_int "1")))
    | Right  -> ((l - (Prims.parse_int "1")), l, l)
    | NonAssoc  ->
        ((l - (Prims.parse_int "1")), l, (l - (Prims.parse_int "1")))
     in
  FStar_List.mapi
    (fun i  ->
       fun uu____1785  ->
         match uu____1785 with
         | (assoc1,tokens) -> ((levels_from_associativity i assoc1), tokens))
    level_associativity_spec
  
let (assign_levels :
  associativity_level Prims.list ->
    Prims.string ->
      (Prims.int,Prims.int,Prims.int) FStar_Pervasives_Native.tuple3)
  =
  fun token_associativity_spec  ->
    fun s  ->
      let uu____1865 = FStar_List.tryFind (matches_level s) level_table  in
      match uu____1865 with
      | FStar_Pervasives_Native.Some (assoc_levels,uu____1915) ->
          assoc_levels
      | uu____1959 -> failwith (Prims.strcat "Unrecognized operator " s)
  
let (max : Prims.int -> Prims.int -> Prims.int) =
  fun k1  -> fun k2  -> if k1 > k2 then k1 else k2 
let max_level :
  'Auu____1994 .
    ('Auu____1994,(FStar_Char.char,Prims.string) FStar_Util.either Prims.list)
      FStar_Pervasives_Native.tuple2 Prims.list -> Prims.int
  =
  fun l  ->
    let find_level_and_max n1 level =
      let uu____2054 =
        FStar_List.tryFind
          (fun uu____2094  ->
             match uu____2094 with
             | (uu____2112,tokens) ->
                 tokens = (FStar_Pervasives_Native.snd level)) level_table
         in
      match uu____2054 with
      | FStar_Pervasives_Native.Some ((uu____2154,l1,uu____2156),uu____2157)
          -> max n1 l1
      | FStar_Pervasives_Native.None  ->
          let uu____2212 =
            let uu____2213 =
              let uu____2214 =
                FStar_List.map token_to_string
                  (FStar_Pervasives_Native.snd level)
                 in
              FStar_String.concat "," uu____2214  in
            FStar_Util.format1 "Undefined associativity level %s" uu____2213
             in
          failwith uu____2212
       in
    FStar_List.fold_left find_level_and_max (Prims.parse_int "0") l
  
let (levels :
  Prims.string ->
    (Prims.int,Prims.int,Prims.int) FStar_Pervasives_Native.tuple3)
  =
  fun op  ->
    let uu____2248 = assign_levels level_associativity_spec op  in
    match uu____2248 with
    | (left1,mine,right1) ->
        if op = "*"
        then ((left1 - (Prims.parse_int "1")), mine, right1)
        else (left1, mine, right1)
  
let operatorInfix0ad12 :
  'Auu____2272 .
    Prims.unit ->
      (associativity,(FStar_Char.char,'Auu____2272) FStar_Util.either
                       Prims.list)
        FStar_Pervasives_Native.tuple2 Prims.list
  =
  fun uu____2286  ->
    [opinfix0a ();
    opinfix0b ();
    opinfix0c ();
    opinfix0d ();
    opinfix1 ();
    opinfix2 ()]
  
let (is_operatorInfix0ad12 : FStar_Ident.ident -> Prims.bool) =
  fun op  ->
    let uu____2367 =
      let uu____2381 =
        let uu____2395 = FStar_Ident.text_of_id op  in
        FStar_All.pipe_left matches_level uu____2395  in
      FStar_List.tryFind uu____2381 (operatorInfix0ad12 ())  in
    uu____2367 <> FStar_Pervasives_Native.None
  
let (is_operatorInfix34 : FStar_Ident.ident -> Prims.bool) =
  let opinfix34 = [opinfix3 (); opinfix4 ()]  in
  fun op  ->
    let uu____2495 =
      let uu____2509 =
        let uu____2523 = FStar_Ident.text_of_id op  in
        FStar_All.pipe_left matches_level uu____2523  in
      FStar_List.tryFind uu____2509 opinfix34  in
    uu____2495 <> FStar_Pervasives_Native.None
  
let (handleable_args_length : FStar_Ident.ident -> Prims.int) =
  fun op  ->
    let op_s = FStar_Ident.text_of_id op  in
    let uu____2576 =
      (is_general_prefix_op op) || (FStar_List.mem op_s ["-"; "~"])  in
    if uu____2576
    then (Prims.parse_int "1")
    else
      (let uu____2578 =
         ((is_operatorInfix0ad12 op) || (is_operatorInfix34 op)) ||
           (FStar_List.mem op_s
              ["<==>"; "==>"; "\\/"; "/\\"; "="; "|>"; ":="; ".()"; ".[]"])
          in
       if uu____2578
       then (Prims.parse_int "2")
       else
         if FStar_List.mem op_s [".()<-"; ".[]<-"]
         then (Prims.parse_int "3")
         else (Prims.parse_int "0"))
  
let handleable_op :
  'Auu____2584 . FStar_Ident.ident -> 'Auu____2584 Prims.list -> Prims.bool =
  fun op  ->
    fun args  ->
      match FStar_List.length args with
      | _0_27 when _0_27 = (Prims.parse_int "0") -> true
      | _0_28 when _0_28 = (Prims.parse_int "1") ->
          (is_general_prefix_op op) ||
            (let uu____2598 = FStar_Ident.text_of_id op  in
             FStar_List.mem uu____2598 ["-"; "~"])
      | _0_29 when _0_29 = (Prims.parse_int "2") ->
          ((is_operatorInfix0ad12 op) || (is_operatorInfix34 op)) ||
            (let uu____2600 = FStar_Ident.text_of_id op  in
             FStar_List.mem uu____2600
               ["<==>"; "==>"; "\\/"; "/\\"; "="; "|>"; ":="; ".()"; ".[]"])
      | _0_30 when _0_30 = (Prims.parse_int "3") ->
          let uu____2601 = FStar_Ident.text_of_id op  in
          FStar_List.mem uu____2601 [".()<-"; ".[]<-"]
      | uu____2602 -> false
  
let (comment_stack :
  (Prims.string,FStar_Range.range) FStar_Pervasives_Native.tuple2 Prims.list
    FStar_ST.ref)
  = FStar_Util.mk_ref [] 
let with_comment :
  'Auu____2636 .
    ('Auu____2636 -> FStar_Pprint.document) ->
      'Auu____2636 -> FStar_Range.range -> FStar_Pprint.document
  =
  fun printer  ->
    fun tm  ->
      fun tmrange  ->
        let rec comments_before_pos acc print_pos lookahead_pos =
          let uu____2668 = FStar_ST.op_Bang comment_stack  in
          match uu____2668 with
          | [] -> (acc, false)
          | (comment,crange)::cs ->
              let uu____2727 = FStar_Range.range_before_pos crange print_pos
                 in
              if uu____2727
              then
                (FStar_ST.op_Colon_Equals comment_stack cs;
                 (let uu____2764 =
                    let uu____2765 =
                      let uu____2766 = str comment  in
                      FStar_Pprint.op_Hat_Hat uu____2766
                        FStar_Pprint.hardline
                       in
                    FStar_Pprint.op_Hat_Hat acc uu____2765  in
                  comments_before_pos uu____2764 print_pos lookahead_pos))
              else
                (let uu____2768 =
                   FStar_Range.range_before_pos crange lookahead_pos  in
                 (acc, uu____2768))
           in
        let uu____2769 =
          let uu____2774 =
            let uu____2775 = FStar_Range.start_of_range tmrange  in
            FStar_Range.end_of_line uu____2775  in
          let uu____2776 = FStar_Range.end_of_range tmrange  in
          comments_before_pos FStar_Pprint.empty uu____2774 uu____2776  in
        match uu____2769 with
        | (comments,has_lookahead) ->
            let printed_e = printer tm  in
            let comments1 =
              if has_lookahead
              then
                let pos = FStar_Range.end_of_range tmrange  in
                let uu____2782 = comments_before_pos comments pos pos  in
                FStar_Pervasives_Native.fst uu____2782
              else comments  in
            let uu____2788 = FStar_Pprint.op_Hat_Hat comments1 printed_e  in
            FStar_Pprint.group uu____2788
  
let rec (place_comments_until_pos :
  Prims.int ->
    Prims.int ->
      FStar_Range.pos -> FStar_Pprint.document -> FStar_Pprint.document)
  =
  fun k  ->
    fun lbegin  ->
      fun pos_end  ->
        fun doc1  ->
          let uu____2801 = FStar_ST.op_Bang comment_stack  in
          match uu____2801 with
          | (comment,crange)::cs when
              FStar_Range.range_before_pos crange pos_end ->
              (FStar_ST.op_Colon_Equals comment_stack cs;
               (let lnum =
                  let uu____2885 =
                    let uu____2886 =
                      let uu____2887 = FStar_Range.start_of_range crange  in
                      FStar_Range.line_of_pos uu____2887  in
                    uu____2886 - lbegin  in
                  max k uu____2885  in
                let lnum1 = Prims.min (Prims.parse_int "2") lnum  in
                let doc2 =
                  let uu____2890 =
                    let uu____2891 =
                      FStar_Pprint.repeat lnum1 FStar_Pprint.hardline  in
                    let uu____2892 = str comment  in
                    FStar_Pprint.op_Hat_Hat uu____2891 uu____2892  in
                  FStar_Pprint.op_Hat_Hat doc1 uu____2890  in
                let uu____2893 =
                  let uu____2894 = FStar_Range.end_of_range crange  in
                  FStar_Range.line_of_pos uu____2894  in
                place_comments_until_pos (Prims.parse_int "1") uu____2893
                  pos_end doc2))
          | uu____2895 ->
              if doc1 = FStar_Pprint.empty
              then FStar_Pprint.empty
              else
                (let lnum =
                   let uu____2904 =
                     let uu____2905 = FStar_Range.line_of_pos pos_end  in
                     uu____2905 - lbegin  in
                   max (Prims.parse_int "1") uu____2904  in
                 let lnum1 = Prims.min (Prims.parse_int "2") lnum  in
                 let uu____2907 =
                   FStar_Pprint.repeat lnum1 FStar_Pprint.hardline  in
                 FStar_Pprint.op_Hat_Hat doc1 uu____2907)
  
let separate_map_with_comments :
  'Auu____2914 .
    FStar_Pprint.document ->
      FStar_Pprint.document ->
        ('Auu____2914 -> FStar_Pprint.document) ->
          'Auu____2914 Prims.list ->
            ('Auu____2914 -> FStar_Range.range) -> FStar_Pprint.document
  =
  fun prefix1  ->
    fun sep  ->
      fun f  ->
        fun xs  ->
          fun extract_range  ->
            let fold_fun uu____2962 x =
              match uu____2962 with
              | (last_line,doc1) ->
                  let r = extract_range x  in
                  let doc2 =
                    let uu____2976 = FStar_Range.start_of_range r  in
                    place_comments_until_pos (Prims.parse_int "1") last_line
                      uu____2976 doc1
                     in
                  let uu____2977 =
                    let uu____2978 = FStar_Range.end_of_range r  in
                    FStar_Range.line_of_pos uu____2978  in
                  let uu____2979 =
                    let uu____2980 =
                      let uu____2981 = f x  in
                      FStar_Pprint.op_Hat_Hat sep uu____2981  in
                    FStar_Pprint.op_Hat_Hat doc2 uu____2980  in
                  (uu____2977, uu____2979)
               in
            let uu____2982 =
              let uu____2989 = FStar_List.hd xs  in
              let uu____2990 = FStar_List.tl xs  in (uu____2989, uu____2990)
               in
            match uu____2982 with
            | (x,xs1) ->
                let init1 =
                  let uu____3006 =
                    let uu____3007 =
                      let uu____3008 = extract_range x  in
                      FStar_Range.end_of_range uu____3008  in
                    FStar_Range.line_of_pos uu____3007  in
                  let uu____3009 =
                    let uu____3010 = f x  in
                    FStar_Pprint.op_Hat_Hat prefix1 uu____3010  in
                  (uu____3006, uu____3009)  in
                let uu____3011 = FStar_List.fold_left fold_fun init1 xs1  in
                FStar_Pervasives_Native.snd uu____3011
  
let separate_map_with_comments_kw :
  'Auu____3027 'Auu____3028 .
    'Auu____3027 ->
      'Auu____3027 ->
        ('Auu____3027 -> 'Auu____3028 -> FStar_Pprint.document) ->
          'Auu____3028 Prims.list ->
            ('Auu____3028 -> FStar_Range.range) -> FStar_Pprint.document
  =
  fun prefix1  ->
    fun sep  ->
      fun f  ->
        fun xs  ->
          fun extract_range  ->
            let fold_fun uu____3081 x =
              match uu____3081 with
              | (last_line,doc1) ->
                  let r = extract_range x  in
                  let doc2 =
                    let uu____3095 = FStar_Range.start_of_range r  in
                    place_comments_until_pos (Prims.parse_int "1") last_line
                      uu____3095 doc1
                     in
                  let uu____3096 =
                    let uu____3097 = FStar_Range.end_of_range r  in
                    FStar_Range.line_of_pos uu____3097  in
                  let uu____3098 =
                    let uu____3099 = f sep x  in
                    FStar_Pprint.op_Hat_Hat doc2 uu____3099  in
                  (uu____3096, uu____3098)
               in
            let uu____3100 =
              let uu____3107 = FStar_List.hd xs  in
              let uu____3108 = FStar_List.tl xs  in (uu____3107, uu____3108)
               in
            match uu____3100 with
            | (x,xs1) ->
                let init1 =
                  let uu____3124 =
                    let uu____3125 =
                      let uu____3126 = extract_range x  in
                      FStar_Range.end_of_range uu____3126  in
                    FStar_Range.line_of_pos uu____3125  in
                  let uu____3127 = f prefix1 x  in (uu____3124, uu____3127)
                   in
                let uu____3128 = FStar_List.fold_left fold_fun init1 xs1  in
                FStar_Pervasives_Native.snd uu____3128
  
let rec (p_decl : FStar_Parser_AST.decl -> FStar_Pprint.document) =
  fun d  ->
    let qualifiers =
      match ((d.FStar_Parser_AST.quals), (d.FStar_Parser_AST.d)) with
      | ((FStar_Parser_AST.Assumption )::[],FStar_Parser_AST.Assume
         (id1,uu____3556)) ->
          let uu____3559 =
            let uu____3560 =
              FStar_Util.char_at id1.FStar_Ident.idText (Prims.parse_int "0")
               in
            FStar_All.pipe_right uu____3560 FStar_Util.is_upper  in
          if uu____3559
          then
            let uu____3561 = p_qualifier FStar_Parser_AST.Assumption  in
            FStar_Pprint.op_Hat_Hat uu____3561 FStar_Pprint.space
          else p_qualifiers d.FStar_Parser_AST.quals
      | uu____3563 -> p_qualifiers d.FStar_Parser_AST.quals  in
    let uu____3568 = FStar_Pprint.optional p_fsdoc d.FStar_Parser_AST.doc  in
    let uu____3569 =
      let uu____3570 = p_attributes d.FStar_Parser_AST.attrs  in
      let uu____3571 =
        let uu____3572 = p_rawDecl d  in
        FStar_Pprint.op_Hat_Hat qualifiers uu____3572  in
      FStar_Pprint.op_Hat_Hat uu____3570 uu____3571  in
    FStar_Pprint.op_Hat_Hat uu____3568 uu____3569

and (p_attributes : FStar_Parser_AST.attributes_ -> FStar_Pprint.document) =
  fun attrs  ->
    match attrs with
    | [] -> FStar_Pprint.empty
    | uu____3574 ->
        let uu____3575 =
          let uu____3576 = str "@ "  in
          let uu____3577 =
            let uu____3578 =
              let uu____3579 =
                let uu____3580 =
                  let uu____3581 = FStar_List.map p_atomicTerm attrs  in
                  FStar_Pprint.flow break1 uu____3581  in
                FStar_Pprint.op_Hat_Hat uu____3580 FStar_Pprint.rbracket  in
              FStar_Pprint.align uu____3579  in
            FStar_Pprint.op_Hat_Hat uu____3578 FStar_Pprint.hardline  in
          FStar_Pprint.op_Hat_Hat uu____3576 uu____3577  in
        FStar_Pprint.op_Hat_Hat FStar_Pprint.lbracket uu____3575

and (p_fsdoc : FStar_Parser_AST.fsdoc -> FStar_Pprint.document) =
  fun uu____3584  ->
    match uu____3584 with
    | (doc1,kwd_args) ->
        let kwd_args_doc =
          match kwd_args with
          | [] -> FStar_Pprint.empty
          | kwd_args1 ->
              let process_kwd_arg uu____3618 =
                match uu____3618 with
                | (kwd,arg) ->
                    let uu____3625 = str "@"  in
                    let uu____3626 =
                      let uu____3627 = str kwd  in
                      let uu____3628 =
                        let uu____3629 = str arg  in
                        FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____3629
                         in
                      FStar_Pprint.op_Hat_Hat uu____3627 uu____3628  in
                    FStar_Pprint.op_Hat_Hat uu____3625 uu____3626
                 in
              let uu____3630 =
                let uu____3631 =
                  FStar_Pprint.separate_map FStar_Pprint.hardline
                    process_kwd_arg kwd_args1
                   in
                FStar_Pprint.op_Hat_Hat uu____3631 FStar_Pprint.hardline  in
              FStar_Pprint.op_Hat_Hat FStar_Pprint.hardline uu____3630
           in
        let uu____3636 =
          let uu____3637 =
            let uu____3638 =
              let uu____3639 =
                let uu____3640 = str doc1  in
                let uu____3641 =
                  let uu____3642 =
                    let uu____3643 =
                      FStar_Pprint.op_Hat_Hat FStar_Pprint.rparen
                        FStar_Pprint.hardline
                       in
                    FStar_Pprint.op_Hat_Hat FStar_Pprint.star uu____3643  in
                  FStar_Pprint.op_Hat_Hat kwd_args_doc uu____3642  in
                FStar_Pprint.op_Hat_Hat uu____3640 uu____3641  in
              FStar_Pprint.op_Hat_Hat FStar_Pprint.star uu____3639  in
            FStar_Pprint.op_Hat_Hat FStar_Pprint.star uu____3638  in
          FStar_Pprint.op_Hat_Hat FStar_Pprint.lparen uu____3637  in
        FStar_Pprint.op_Hat_Hat FStar_Pprint.hardline uu____3636

and (p_justSig : FStar_Parser_AST.decl -> FStar_Pprint.document) =
  fun d  ->
    match d.FStar_Parser_AST.d with
    | FStar_Parser_AST.Val (lid,t) ->
        let uu____3647 =
          let uu____3648 = str "val"  in
          let uu____3649 =
            let uu____3650 =
              let uu____3651 = p_lident lid  in
              let uu____3652 =
                FStar_Pprint.op_Hat_Hat FStar_Pprint.space FStar_Pprint.colon
                 in
              FStar_Pprint.op_Hat_Hat uu____3651 uu____3652  in
            FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____3650  in
          FStar_Pprint.op_Hat_Hat uu____3648 uu____3649  in
        let uu____3653 = p_typ false false t  in
        FStar_Pprint.op_Hat_Hat uu____3647 uu____3653
    | FStar_Parser_AST.TopLevelLet (uu____3654,lbs) ->
        FStar_Pprint.separate_map FStar_Pprint.hardline
          (fun lb  ->
             let uu____3679 =
               let uu____3680 = str "let"  in p_letlhs uu____3680 lb  in
             FStar_Pprint.group uu____3679) lbs
    | uu____3681 -> FStar_Pprint.empty

and (p_list :
  (FStar_Ident.ident -> FStar_Pprint.document) ->
    FStar_Pprint.document ->
      FStar_Ident.ident Prims.list -> FStar_Pprint.document)
  =
  fun f  ->
    fun sep  ->
      fun l  ->
        let rec p_list' uu___56_3694 =
          match uu___56_3694 with
          | [] -> FStar_Pprint.empty
          | x::[] -> f x
          | x::xs ->
              let uu____3702 = f x  in
              let uu____3703 =
                let uu____3704 = p_list' xs  in
                FStar_Pprint.op_Hat_Hat sep uu____3704  in
              FStar_Pprint.op_Hat_Hat uu____3702 uu____3703
           in
        let uu____3705 = str "["  in
        let uu____3706 =
          let uu____3707 = p_list' l  in
          let uu____3708 = str "]"  in
          FStar_Pprint.op_Hat_Hat uu____3707 uu____3708  in
        FStar_Pprint.op_Hat_Hat uu____3705 uu____3706

and (p_rawDecl : FStar_Parser_AST.decl -> FStar_Pprint.document) =
  fun d  ->
    match d.FStar_Parser_AST.d with
    | FStar_Parser_AST.Open uid ->
        let uu____3711 =
          let uu____3712 = str "open"  in
          let uu____3713 = p_quident uid  in
          FStar_Pprint.op_Hat_Slash_Hat uu____3712 uu____3713  in
        FStar_Pprint.group uu____3711
    | FStar_Parser_AST.Include uid ->
        let uu____3715 =
          let uu____3716 = str "include"  in
          let uu____3717 = p_quident uid  in
          FStar_Pprint.op_Hat_Slash_Hat uu____3716 uu____3717  in
        FStar_Pprint.group uu____3715
    | FStar_Parser_AST.ModuleAbbrev (uid1,uid2) ->
        let uu____3720 =
          let uu____3721 = str "module"  in
          let uu____3722 =
            let uu____3723 =
              let uu____3724 = p_uident uid1  in
              let uu____3725 =
                FStar_Pprint.op_Hat_Hat FStar_Pprint.space
                  FStar_Pprint.equals
                 in
              FStar_Pprint.op_Hat_Hat uu____3724 uu____3725  in
            FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____3723  in
          FStar_Pprint.op_Hat_Hat uu____3721 uu____3722  in
        let uu____3726 = p_quident uid2  in
        op_Hat_Slash_Plus_Hat uu____3720 uu____3726
    | FStar_Parser_AST.TopLevelModule uid ->
        let uu____3728 =
          let uu____3729 = str "module"  in
          let uu____3730 =
            let uu____3731 = p_quident uid  in
            FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____3731  in
          FStar_Pprint.op_Hat_Hat uu____3729 uu____3730  in
        FStar_Pprint.group uu____3728
    | FStar_Parser_AST.Tycon
        (true
         ,(FStar_Parser_AST.TyconAbbrev
           (uid,tpars,FStar_Pervasives_Native.None ,t),FStar_Pervasives_Native.None
           )::[])
        ->
        let effect_prefix_doc =
          let uu____3764 = str "effect"  in
          let uu____3765 =
            let uu____3766 = p_uident uid  in
            FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____3766  in
          FStar_Pprint.op_Hat_Hat uu____3764 uu____3765  in
        let uu____3767 =
          let uu____3768 = p_typars tpars  in
          FStar_Pprint.surround (Prims.parse_int "2") (Prims.parse_int "1")
            effect_prefix_doc uu____3768 FStar_Pprint.equals
           in
        let uu____3769 = p_typ false false t  in
        op_Hat_Slash_Plus_Hat uu____3767 uu____3769
    | FStar_Parser_AST.Tycon (false ,tcdefs) ->
        let uu____3787 =
          let uu____3788 = str "type"  in
          let uu____3789 = FStar_List.hd tcdefs  in
          p_fsdocTypeDeclPairs uu____3788 uu____3789  in
        let uu____3802 =
          let uu____3803 = FStar_List.tl tcdefs  in
          FStar_All.pipe_left
            (FStar_Pprint.concat_map
               (fun x  ->
                  let uu____3841 =
                    let uu____3842 = str "and"  in
                    p_fsdocTypeDeclPairs uu____3842 x  in
                  FStar_Pprint.op_Hat_Hat break1 uu____3841)) uu____3803
           in
        FStar_Pprint.op_Hat_Hat uu____3787 uu____3802
    | FStar_Parser_AST.TopLevelLet (q,lbs) ->
        let let_doc =
          let uu____3858 = str "let"  in
          let uu____3859 = p_letqualifier q  in
          FStar_Pprint.op_Hat_Hat uu____3858 uu____3859  in
        let uu____3860 = str "and"  in
        separate_map_with_comments_kw let_doc uu____3860 p_letbinding lbs
          (fun uu____3868  ->
             match uu____3868 with
             | (p,t) ->
                 FStar_Range.union_ranges p.FStar_Parser_AST.prange
                   t.FStar_Parser_AST.range)
    | FStar_Parser_AST.Val (lid,t) ->
        let uu____3877 = str "val"  in
        let uu____3878 =
          let uu____3879 =
            let uu____3880 = p_lident lid  in
            let uu____3881 =
              let uu____3882 =
                let uu____3883 =
                  let uu____3884 = p_typ false false t  in
                  FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____3884  in
                FStar_Pprint.op_Hat_Hat FStar_Pprint.colon uu____3883  in
              FStar_Pprint.group uu____3882  in
            FStar_Pprint.op_Hat_Hat uu____3880 uu____3881  in
          FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____3879  in
        FStar_Pprint.op_Hat_Hat uu____3877 uu____3878
    | FStar_Parser_AST.Assume (id1,t) ->
        let decl_keyword =
          let uu____3888 =
            let uu____3889 =
              FStar_Util.char_at id1.FStar_Ident.idText (Prims.parse_int "0")
               in
            FStar_All.pipe_right uu____3889 FStar_Util.is_upper  in
          if uu____3888
          then FStar_Pprint.empty
          else
            (let uu____3891 = str "val"  in
             FStar_Pprint.op_Hat_Hat uu____3891 FStar_Pprint.space)
           in
        let uu____3892 =
          let uu____3893 = p_ident id1  in
          let uu____3894 =
            let uu____3895 =
              let uu____3896 =
                let uu____3897 = p_typ false false t  in
                FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____3897  in
              FStar_Pprint.op_Hat_Hat FStar_Pprint.colon uu____3896  in
            FStar_Pprint.group uu____3895  in
          FStar_Pprint.op_Hat_Hat uu____3893 uu____3894  in
        FStar_Pprint.op_Hat_Hat decl_keyword uu____3892
    | FStar_Parser_AST.Exception (uid,t_opt) ->
        let uu____3904 = str "exception"  in
        let uu____3905 =
          let uu____3906 =
            let uu____3907 = p_uident uid  in
            let uu____3908 =
              FStar_Pprint.optional
                (fun t  ->
                   let uu____3912 =
                     let uu____3913 = str "of"  in
                     let uu____3914 = p_typ false false t  in
                     op_Hat_Slash_Plus_Hat uu____3913 uu____3914  in
                   FStar_Pprint.op_Hat_Hat break1 uu____3912) t_opt
               in
            FStar_Pprint.op_Hat_Hat uu____3907 uu____3908  in
          FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____3906  in
        FStar_Pprint.op_Hat_Hat uu____3904 uu____3905
    | FStar_Parser_AST.NewEffect ne ->
        let uu____3916 = str "new_effect"  in
        let uu____3917 =
          let uu____3918 = p_newEffect ne  in
          FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____3918  in
        FStar_Pprint.op_Hat_Hat uu____3916 uu____3917
    | FStar_Parser_AST.SubEffect se ->
        let uu____3920 = str "sub_effect"  in
        let uu____3921 =
          let uu____3922 = p_subEffect se  in
          FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____3922  in
        FStar_Pprint.op_Hat_Hat uu____3920 uu____3921
    | FStar_Parser_AST.Pragma p -> p_pragma p
    | FStar_Parser_AST.Fsdoc doc1 ->
        let uu____3925 = p_fsdoc doc1  in
        FStar_Pprint.op_Hat_Hat uu____3925 FStar_Pprint.hardline
    | FStar_Parser_AST.Main uu____3926 ->
        failwith "*Main declaration* : Is that really still in use ??"
    | FStar_Parser_AST.Tycon (true ,uu____3927) ->
        failwith
          "Effect abbreviation is expected to be defined by an abbreviation"
    | FStar_Parser_AST.Splice (ids,t) ->
        let uu____3950 = str "%splice"  in
        let uu____3951 =
          let uu____3952 =
            let uu____3953 = str ";"  in p_list p_uident uu____3953 ids  in
          let uu____3954 =
            let uu____3955 = p_term false false t  in
            FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____3955  in
          FStar_Pprint.op_Hat_Hat uu____3952 uu____3954  in
        FStar_Pprint.op_Hat_Hat uu____3950 uu____3951

and (p_pragma : FStar_Parser_AST.pragma -> FStar_Pprint.document) =
  fun uu___57_3956  ->
    match uu___57_3956 with
    | FStar_Parser_AST.SetOptions s ->
        let uu____3958 = str "#set-options"  in
        let uu____3959 =
          let uu____3960 =
            let uu____3961 = str s  in FStar_Pprint.dquotes uu____3961  in
          FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____3960  in
        FStar_Pprint.op_Hat_Hat uu____3958 uu____3959
    | FStar_Parser_AST.ResetOptions s_opt ->
        let uu____3965 = str "#reset-options"  in
        let uu____3966 =
          FStar_Pprint.optional
            (fun s  ->
               let uu____3970 =
                 let uu____3971 = str s  in FStar_Pprint.dquotes uu____3971
                  in
               FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____3970) s_opt
           in
        FStar_Pprint.op_Hat_Hat uu____3965 uu____3966
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
    fun uu____3996  ->
      match uu____3996 with
      | (typedecl,fsdoc_opt) ->
          let uu____4009 = p_typeDecl (kw, fsdoc_opt) typedecl  in
          (match uu____4009 with
           | (decl,body) ->
               let uu____4024 = body ()  in
               FStar_Pprint.op_Hat_Hat decl uu____4024)

and (p_typeDecl :
  (FStar_Pprint.document,FStar_Parser_AST.fsdoc
                           FStar_Pervasives_Native.option)
    FStar_Pervasives_Native.tuple2 ->
    FStar_Parser_AST.tycon ->
      (FStar_Pprint.document,Prims.unit -> FStar_Pprint.document)
        FStar_Pervasives_Native.tuple2)
  =
  fun pre  ->
    fun uu___58_4026  ->
      match uu___58_4026 with
      | FStar_Parser_AST.TyconAbstract (lid,bs,typ_opt) ->
          let empty' uu____4053 = FStar_Pprint.empty  in
          let uu____4054 = p_typeDeclPrefix pre false lid bs typ_opt  in
          (uu____4054, empty')
      | FStar_Parser_AST.TyconAbbrev (lid,bs,typ_opt,t) ->
          let f uu____4072 =
            let uu____4073 = p_typ false false t  in jump2 uu____4073  in
          let uu____4074 = p_typeDeclPrefix pre true lid bs typ_opt  in
          (uu____4074, f)
      | FStar_Parser_AST.TyconRecord (lid,bs,typ_opt,record_field_decls) ->
          let p_recordFieldAndComments ps uu____4123 =
            match uu____4123 with
            | (lid1,t,doc_opt) ->
                let uu____4139 =
                  FStar_Range.extend_to_end_of_line t.FStar_Parser_AST.range
                   in
                with_comment (p_recordFieldDecl ps) (lid1, t, doc_opt)
                  uu____4139
             in
          let p_fields uu____4153 =
            let uu____4154 =
              let uu____4155 =
                let uu____4156 =
                  FStar_Pprint.op_Hat_Hat FStar_Pprint.semi break1  in
                separate_map_last uu____4156 p_recordFieldAndComments
                  record_field_decls
                 in
              braces_with_nesting uu____4155  in
            FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____4154  in
          let uu____4165 = p_typeDeclPrefix pre true lid bs typ_opt  in
          (uu____4165, p_fields)
      | FStar_Parser_AST.TyconVariant (lid,bs,typ_opt,ct_decls) ->
          let p_constructorBranchAndComments uu____4223 =
            match uu____4223 with
            | (uid,t_opt,doc_opt,use_of) ->
                let range =
                  let uu____4249 =
                    let uu____4250 =
                      FStar_Util.map_opt t_opt
                        (fun t  -> t.FStar_Parser_AST.range)
                       in
                    FStar_Util.dflt uid.FStar_Ident.idRange uu____4250  in
                  FStar_Range.extend_to_end_of_line uu____4249  in
                with_comment p_constructorBranch
                  (uid, t_opt, doc_opt, use_of) range
             in
          let datacon_doc uu____4274 =
            FStar_Pprint.separate_map FStar_Pprint.hardline
              p_constructorBranchAndComments ct_decls
             in
          let uu____4287 = p_typeDeclPrefix pre true lid bs typ_opt  in
          (uu____4287,
            ((fun uu____4292  ->
                let uu____4293 = datacon_doc ()  in jump2 uu____4293)))

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
  fun uu____4294  ->
    fun eq1  ->
      fun lid  ->
        fun bs  ->
          fun typ_opt  ->
            match uu____4294 with
            | (kw,fsdoc_opt) ->
                let maybe_with_fsdoc cont =
                  let lid_doc = p_ident lid  in
                  let kw_lid =
                    let uu____4326 = FStar_Pprint.op_Hat_Slash_Hat kw lid_doc
                       in
                    FStar_Pprint.group uu____4326  in
                  match fsdoc_opt with
                  | FStar_Pervasives_Native.None  -> cont kw_lid
                  | FStar_Pervasives_Native.Some fsdoc ->
                      let uu____4328 =
                        let uu____4331 =
                          let uu____4334 = p_fsdoc fsdoc  in
                          let uu____4335 =
                            let uu____4338 = cont lid_doc  in [uu____4338]
                             in
                          uu____4334 :: uu____4335  in
                        kw :: uu____4331  in
                      FStar_Pprint.separate FStar_Pprint.hardline uu____4328
                   in
                let typ =
                  let maybe_eq =
                    if eq1 then FStar_Pprint.equals else FStar_Pprint.empty
                     in
                  match typ_opt with
                  | FStar_Pervasives_Native.None  -> maybe_eq
                  | FStar_Pervasives_Native.Some t ->
                      let uu____4343 =
                        let uu____4344 =
                          let uu____4345 = p_typ false false t  in
                          FStar_Pprint.op_Hat_Slash_Hat uu____4345 maybe_eq
                           in
                        FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____4344
                         in
                      FStar_Pprint.op_Hat_Hat FStar_Pprint.colon uu____4343
                   in
                if bs = []
                then maybe_with_fsdoc (fun n1  -> prefix2 n1 typ)
                else
                  (let binders = p_binders_list true bs  in
                   maybe_with_fsdoc
                     (fun n1  ->
                        let uu____4360 =
                          let uu____4361 = FStar_Pprint.flow break1 binders
                             in
                          prefix2 n1 uu____4361  in
                        prefix2 uu____4360 typ))

and (p_recordFieldDecl :
  Prims.bool ->
    (FStar_Ident.ident,FStar_Parser_AST.term,FStar_Parser_AST.fsdoc
                                               FStar_Pervasives_Native.option)
      FStar_Pervasives_Native.tuple3 -> FStar_Pprint.document)
  =
  fun ps  ->
    fun uu____4363  ->
      match uu____4363 with
      | (lid,t,doc_opt) ->
          let uu____4379 =
            let uu____4380 = FStar_Pprint.optional p_fsdoc doc_opt  in
            let uu____4381 =
              let uu____4382 = p_lident lid  in
              let uu____4383 =
                let uu____4384 = p_typ ps false t  in
                FStar_Pprint.op_Hat_Hat FStar_Pprint.colon uu____4384  in
              FStar_Pprint.op_Hat_Hat uu____4382 uu____4383  in
            FStar_Pprint.op_Hat_Hat uu____4380 uu____4381  in
          FStar_Pprint.group uu____4379

and (p_constructorBranch :
  (FStar_Ident.ident,FStar_Parser_AST.term FStar_Pervasives_Native.option,
    FStar_Parser_AST.fsdoc FStar_Pervasives_Native.option,Prims.bool)
    FStar_Pervasives_Native.tuple4 -> FStar_Pprint.document)
  =
  fun uu____4385  ->
    match uu____4385 with
    | (uid,t_opt,doc_opt,use_of) ->
        let sep = if use_of then str "of" else FStar_Pprint.colon  in
        let uid_doc =
          let uu____4413 =
            let uu____4414 =
              let uu____4415 = p_uident uid  in
              FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____4415  in
            FStar_Pprint.op_Hat_Hat FStar_Pprint.bar uu____4414  in
          FStar_Pprint.group uu____4413  in
        let uu____4416 = FStar_Pprint.optional p_fsdoc doc_opt  in
        let uu____4417 =
          default_or_map uid_doc
            (fun t  ->
               let uu____4421 =
                 let uu____4422 =
                   let uu____4423 =
                     let uu____4424 =
                       let uu____4425 = p_typ false false t  in
                       FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____4425
                        in
                     FStar_Pprint.op_Hat_Hat sep uu____4424  in
                   FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____4423  in
                 FStar_Pprint.op_Hat_Hat uid_doc uu____4422  in
               FStar_Pprint.group uu____4421) t_opt
           in
        FStar_Pprint.op_Hat_Hat uu____4416 uu____4417

and (p_letlhs :
  FStar_Pprint.document ->
    (FStar_Parser_AST.pattern,FStar_Parser_AST.term)
      FStar_Pervasives_Native.tuple2 -> FStar_Pprint.document)
  =
  fun kw  ->
    fun uu____4427  ->
      match uu____4427 with
      | (pat,uu____4433) ->
          let uu____4434 =
            match pat.FStar_Parser_AST.pat with
            | FStar_Parser_AST.PatAscribed
                (pat1,(t,FStar_Pervasives_Native.None )) ->
                let uu____4453 =
                  let uu____4454 =
                    let uu____4455 =
                      let uu____4456 = p_tmArrow p_tmNoEq t  in
                      FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____4456
                       in
                    FStar_Pprint.op_Hat_Hat FStar_Pprint.colon uu____4455  in
                  FStar_Pprint.group uu____4454  in
                (pat1, uu____4453)
            | FStar_Parser_AST.PatAscribed
                (pat1,(t,FStar_Pervasives_Native.Some tac)) ->
                let uu____4468 =
                  let uu____4469 =
                    let uu____4470 =
                      let uu____4471 =
                        let uu____4472 = p_tmArrow p_tmNoEq t  in
                        FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____4472
                         in
                      FStar_Pprint.op_Hat_Hat FStar_Pprint.colon uu____4471
                       in
                    FStar_Pprint.group uu____4470  in
                  let uu____4473 =
                    let uu____4474 =
                      let uu____4475 = str "by"  in
                      let uu____4476 =
                        let uu____4477 = p_atomicTerm tac  in
                        FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____4477
                         in
                      FStar_Pprint.op_Hat_Hat uu____4475 uu____4476  in
                    FStar_Pprint.group uu____4474  in
                  FStar_Pprint.op_Hat_Hat uu____4469 uu____4473  in
                (pat1, uu____4468)
            | uu____4478 -> (pat, FStar_Pprint.empty)  in
          (match uu____4434 with
           | (pat1,ascr_doc) ->
               (match pat1.FStar_Parser_AST.pat with
                | FStar_Parser_AST.PatApp
                    ({
                       FStar_Parser_AST.pat = FStar_Parser_AST.PatVar
                         (x,uu____4482);
                       FStar_Parser_AST.prange = uu____4483;_},pats)
                    ->
                    let uu____4493 =
                      let uu____4494 =
                        let uu____4495 =
                          let uu____4496 = p_lident x  in
                          FStar_Pprint.op_Hat_Slash_Hat kw uu____4496  in
                        FStar_Pprint.group uu____4495  in
                      let uu____4497 =
                        FStar_Pprint.flow_map break1 p_atomicPattern pats  in
                      prefix2 uu____4494 uu____4497  in
                    prefix2_nonempty uu____4493 ascr_doc
                | uu____4498 ->
                    let uu____4499 =
                      let uu____4500 =
                        let uu____4501 =
                          let uu____4502 = p_tuplePattern pat1  in
                          FStar_Pprint.op_Hat_Slash_Hat kw uu____4502  in
                        FStar_Pprint.group uu____4501  in
                      FStar_Pprint.op_Hat_Hat uu____4500 ascr_doc  in
                    FStar_Pprint.group uu____4499))

and (p_letbinding :
  FStar_Pprint.document ->
    (FStar_Parser_AST.pattern,FStar_Parser_AST.term)
      FStar_Pervasives_Native.tuple2 -> FStar_Pprint.document)
  =
  fun kw  ->
    fun uu____4504  ->
      match uu____4504 with
      | (pat,e) ->
          let doc_pat = p_letlhs kw (pat, e)  in
          let doc_expr = p_term false false e  in
          let uu____4513 =
            let uu____4514 =
              FStar_Pprint.op_Hat_Slash_Hat FStar_Pprint.equals doc_expr  in
            FStar_Pprint.op_Hat_Slash_Hat doc_pat uu____4514  in
          let uu____4515 =
            let uu____4516 =
              let uu____4517 =
                let uu____4518 =
                  let uu____4519 = jump2 doc_expr  in
                  FStar_Pprint.op_Hat_Hat FStar_Pprint.equals uu____4519  in
                FStar_Pprint.group uu____4518  in
              FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____4517  in
            FStar_Pprint.op_Hat_Hat doc_pat uu____4516  in
          FStar_Pprint.ifflat uu____4513 uu____4515

and (p_newEffect : FStar_Parser_AST.effect_decl -> FStar_Pprint.document) =
  fun uu___59_4520  ->
    match uu___59_4520 with
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
        let uu____4545 = p_uident uid  in
        let uu____4546 = p_binders true bs  in
        let uu____4547 =
          let uu____4548 = p_simpleTerm false false t  in
          prefix2 FStar_Pprint.equals uu____4548  in
        surround_maybe_empty (Prims.parse_int "2") (Prims.parse_int "1")
          uu____4545 uu____4546 uu____4547

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
          let binders = p_binders true bs  in
          let uu____4558 =
            let uu____4559 =
              let uu____4560 =
                let uu____4561 = p_uident uid  in
                let uu____4562 = p_binders true bs  in
                let uu____4563 =
                  let uu____4564 = p_typ false false t  in
                  prefix2 FStar_Pprint.colon uu____4564  in
                surround_maybe_empty (Prims.parse_int "2")
                  (Prims.parse_int "1") uu____4561 uu____4562 uu____4563
                 in
              FStar_Pprint.group uu____4560  in
            let uu____4565 =
              let uu____4566 = str "with"  in
              let uu____4567 =
                let uu____4568 =
                  let uu____4569 =
                    let uu____4570 =
                      let uu____4571 =
                        let uu____4572 =
                          FStar_Pprint.op_Hat_Hat FStar_Pprint.semi
                            FStar_Pprint.space
                           in
                        FStar_Pprint.op_Hat_Hat FStar_Pprint.hardline
                          uu____4572
                         in
                      separate_map_last uu____4571 p_effectDecl eff_decls  in
                    FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____4570  in
                  FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____4569  in
                FStar_Pprint.op_Hat_Hat FStar_Pprint.hardline uu____4568  in
              FStar_Pprint.op_Hat_Hat uu____4566 uu____4567  in
            FStar_Pprint.op_Hat_Slash_Hat uu____4559 uu____4565  in
          braces_with_nesting uu____4558

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
          let uu____4603 =
            let uu____4604 = p_lident lid  in
            let uu____4605 =
              FStar_Pprint.op_Hat_Hat FStar_Pprint.space FStar_Pprint.equals
               in
            FStar_Pprint.op_Hat_Hat uu____4604 uu____4605  in
          let uu____4606 = p_simpleTerm ps false e  in
          prefix2 uu____4603 uu____4606
      | uu____4607 ->
          let uu____4608 =
            let uu____4609 = FStar_Parser_AST.decl_to_string d  in
            FStar_Util.format1
              "Not a declaration of an effect member... or at least I hope so : %s"
              uu____4609
             in
          failwith uu____4608

and (p_subEffect : FStar_Parser_AST.lift -> FStar_Pprint.document) =
  fun lift  ->
    let lift_op_doc =
      let lifts =
        match lift.FStar_Parser_AST.lift_op with
        | FStar_Parser_AST.NonReifiableLift t -> [("lift_wp", t)]
        | FStar_Parser_AST.ReifiableLift (t1,t2) ->
            [("lift_wp", t1); ("lift", t2)]
        | FStar_Parser_AST.LiftForFree t -> [("lift", t)]  in
      let p_lift ps uu____4667 =
        match uu____4667 with
        | (kwd,t) ->
            let uu____4674 =
              let uu____4675 = str kwd  in
              let uu____4676 =
                FStar_Pprint.op_Hat_Hat FStar_Pprint.space
                  FStar_Pprint.equals
                 in
              FStar_Pprint.op_Hat_Hat uu____4675 uu____4676  in
            let uu____4677 = p_simpleTerm ps false t  in
            prefix2 uu____4674 uu____4677
         in
      separate_break_map_last FStar_Pprint.semi p_lift lifts  in
    let uu____4682 =
      let uu____4683 =
        let uu____4684 = p_quident lift.FStar_Parser_AST.msource  in
        let uu____4685 =
          let uu____4686 = str "~>"  in
          FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____4686  in
        FStar_Pprint.op_Hat_Hat uu____4684 uu____4685  in
      let uu____4687 = p_quident lift.FStar_Parser_AST.mdest  in
      prefix2 uu____4683 uu____4687  in
    let uu____4688 =
      let uu____4689 = braces_with_nesting lift_op_doc  in
      FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____4689  in
    FStar_Pprint.op_Hat_Hat uu____4682 uu____4688

and (p_qualifier : FStar_Parser_AST.qualifier -> FStar_Pprint.document) =
  fun uu___60_4690  ->
    match uu___60_4690 with
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
    | uu____4692 ->
        let uu____4693 =
          let uu____4694 = FStar_List.map p_qualifier qs  in
          FStar_Pprint.flow break1 uu____4694  in
        FStar_Pprint.op_Hat_Hat uu____4693 FStar_Pprint.hardline

and (p_letqualifier :
  FStar_Parser_AST.let_qualifier -> FStar_Pprint.document) =
  fun uu___61_4697  ->
    match uu___61_4697 with
    | FStar_Parser_AST.Rec  ->
        let uu____4698 = str "rec"  in
        FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____4698
    | FStar_Parser_AST.Mutable  ->
        let uu____4699 = str "mutable"  in
        FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____4699
    | FStar_Parser_AST.NoLetQualifier  -> FStar_Pprint.empty

and (p_aqual : FStar_Parser_AST.arg_qualifier -> FStar_Pprint.document) =
  fun uu___62_4700  ->
    match uu___62_4700 with
    | FStar_Parser_AST.Implicit  -> str "#"
    | FStar_Parser_AST.Equality  -> str "$"

and (p_disjunctivePattern :
  FStar_Parser_AST.pattern -> FStar_Pprint.document) =
  fun p  ->
    match p.FStar_Parser_AST.pat with
    | FStar_Parser_AST.PatOr pats ->
        let uu____4705 =
          let uu____4706 =
            let uu____4707 =
              FStar_Pprint.op_Hat_Hat FStar_Pprint.bar FStar_Pprint.space  in
            FStar_Pprint.op_Hat_Hat break1 uu____4707  in
          FStar_Pprint.separate_map uu____4706 p_tuplePattern pats  in
        FStar_Pprint.group uu____4705
    | uu____4708 -> p_tuplePattern p

and (p_tuplePattern : FStar_Parser_AST.pattern -> FStar_Pprint.document) =
  fun p  ->
    match p.FStar_Parser_AST.pat with
    | FStar_Parser_AST.PatTuple (pats,false ) ->
        let uu____4715 =
          let uu____4716 = FStar_Pprint.op_Hat_Hat FStar_Pprint.comma break1
             in
          FStar_Pprint.separate_map uu____4716 p_constructorPattern pats  in
        FStar_Pprint.group uu____4715
    | uu____4717 -> p_constructorPattern p

and (p_constructorPattern :
  FStar_Parser_AST.pattern -> FStar_Pprint.document) =
  fun p  ->
    match p.FStar_Parser_AST.pat with
    | FStar_Parser_AST.PatApp
        ({ FStar_Parser_AST.pat = FStar_Parser_AST.PatName maybe_cons_lid;
           FStar_Parser_AST.prange = uu____4720;_},hd1::tl1::[])
        when
        FStar_Ident.lid_equals maybe_cons_lid FStar_Parser_Const.cons_lid ->
        let uu____4725 =
          FStar_Pprint.op_Hat_Hat FStar_Pprint.colon FStar_Pprint.colon  in
        let uu____4726 = p_constructorPattern hd1  in
        let uu____4727 = p_constructorPattern tl1  in
        infix0 uu____4725 uu____4726 uu____4727
    | FStar_Parser_AST.PatApp
        ({ FStar_Parser_AST.pat = FStar_Parser_AST.PatName uid;
           FStar_Parser_AST.prange = uu____4729;_},pats)
        ->
        let uu____4735 = p_quident uid  in
        let uu____4736 =
          FStar_Pprint.separate_map break1 p_atomicPattern pats  in
        prefix2 uu____4735 uu____4736
    | uu____4737 -> p_atomicPattern p

and (p_atomicPattern : FStar_Parser_AST.pattern -> FStar_Pprint.document) =
  fun p  ->
    match p.FStar_Parser_AST.pat with
    | FStar_Parser_AST.PatAscribed (pat,(t,FStar_Pervasives_Native.None )) ->
        (match ((pat.FStar_Parser_AST.pat), (t.FStar_Parser_AST.tm)) with
         | (FStar_Parser_AST.PatVar (lid,aqual),FStar_Parser_AST.Refine
            ({ FStar_Parser_AST.b = FStar_Parser_AST.Annotated (lid',t1);
               FStar_Parser_AST.brange = uu____4753;
               FStar_Parser_AST.blevel = uu____4754;
               FStar_Parser_AST.aqual = uu____4755;_},phi))
             when lid.FStar_Ident.idText = lid'.FStar_Ident.idText ->
             let uu____4761 =
               let uu____4762 = p_ident lid  in
               p_refinement aqual uu____4762 t1 phi  in
             soft_parens_with_nesting uu____4761
         | (FStar_Parser_AST.PatWild ,FStar_Parser_AST.Refine
            ({ FStar_Parser_AST.b = FStar_Parser_AST.NoName t1;
               FStar_Parser_AST.brange = uu____4764;
               FStar_Parser_AST.blevel = uu____4765;
               FStar_Parser_AST.aqual = uu____4766;_},phi))
             ->
             let uu____4768 =
               p_refinement FStar_Pervasives_Native.None
                 FStar_Pprint.underscore t1 phi
                in
             soft_parens_with_nesting uu____4768
         | uu____4769 ->
             let uu____4774 =
               let uu____4775 = p_tuplePattern pat  in
               let uu____4776 =
                 let uu____4777 = p_tmEqNoRefinement t  in
                 FStar_Pprint.op_Hat_Slash_Hat FStar_Pprint.colon uu____4777
                  in
               FStar_Pprint.op_Hat_Hat uu____4775 uu____4776  in
             soft_parens_with_nesting uu____4774)
    | FStar_Parser_AST.PatList pats ->
        let uu____4781 =
          separate_break_map FStar_Pprint.semi p_tuplePattern pats  in
        FStar_Pprint.surround (Prims.parse_int "2") (Prims.parse_int "0")
          FStar_Pprint.lbracket uu____4781 FStar_Pprint.rbracket
    | FStar_Parser_AST.PatRecord pats ->
        let p_recordFieldPat uu____4796 =
          match uu____4796 with
          | (lid,pat) ->
              let uu____4803 = p_qlident lid  in
              let uu____4804 = p_tuplePattern pat  in
              infix2 FStar_Pprint.equals uu____4803 uu____4804
           in
        let uu____4805 =
          separate_break_map FStar_Pprint.semi p_recordFieldPat pats  in
        soft_braces_with_nesting uu____4805
    | FStar_Parser_AST.PatTuple (pats,true ) ->
        let uu____4815 =
          FStar_Pprint.op_Hat_Hat FStar_Pprint.lparen FStar_Pprint.bar  in
        let uu____4816 =
          separate_break_map FStar_Pprint.comma p_constructorPattern pats  in
        let uu____4817 =
          FStar_Pprint.op_Hat_Hat FStar_Pprint.bar FStar_Pprint.rparen  in
        FStar_Pprint.surround (Prims.parse_int "2") (Prims.parse_int "1")
          uu____4815 uu____4816 uu____4817
    | FStar_Parser_AST.PatTvar (tv,arg_qualifier_opt) -> p_tvar tv
    | FStar_Parser_AST.PatOp op ->
        let uu____4828 =
          let uu____4829 =
            let uu____4830 =
              let uu____4831 = FStar_Ident.text_of_id op  in str uu____4831
               in
            let uu____4832 =
              FStar_Pprint.op_Hat_Hat FStar_Pprint.space FStar_Pprint.rparen
               in
            FStar_Pprint.op_Hat_Hat uu____4830 uu____4832  in
          FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____4829  in
        FStar_Pprint.op_Hat_Hat FStar_Pprint.lparen uu____4828
    | FStar_Parser_AST.PatWild  -> FStar_Pprint.underscore
    | FStar_Parser_AST.PatConst c -> p_constant c
    | FStar_Parser_AST.PatVar (lid,aqual) ->
        let uu____4840 = FStar_Pprint.optional p_aqual aqual  in
        let uu____4841 = p_lident lid  in
        FStar_Pprint.op_Hat_Hat uu____4840 uu____4841
    | FStar_Parser_AST.PatName uid -> p_quident uid
    | FStar_Parser_AST.PatOr uu____4843 -> failwith "Inner or pattern !"
    | FStar_Parser_AST.PatApp
        ({ FStar_Parser_AST.pat = FStar_Parser_AST.PatName uu____4846;
           FStar_Parser_AST.prange = uu____4847;_},uu____4848)
        ->
        let uu____4853 = p_tuplePattern p  in
        soft_parens_with_nesting uu____4853
    | FStar_Parser_AST.PatTuple (uu____4854,false ) ->
        let uu____4859 = p_tuplePattern p  in
        soft_parens_with_nesting uu____4859
    | uu____4860 ->
        let uu____4861 =
          let uu____4862 = FStar_Parser_AST.pat_to_string p  in
          FStar_Util.format1 "Invalid pattern %s" uu____4862  in
        failwith uu____4861

and (p_binder :
  Prims.bool -> FStar_Parser_AST.binder -> FStar_Pprint.document) =
  fun is_atomic  ->
    fun b  ->
      match b.FStar_Parser_AST.b with
      | FStar_Parser_AST.Variable lid ->
          let uu____4866 =
            FStar_Pprint.optional p_aqual b.FStar_Parser_AST.aqual  in
          let uu____4867 = p_lident lid  in
          FStar_Pprint.op_Hat_Hat uu____4866 uu____4867
      | FStar_Parser_AST.TVariable lid -> p_lident lid
      | FStar_Parser_AST.Annotated (lid,t) ->
          let doc1 =
            match t.FStar_Parser_AST.tm with
            | FStar_Parser_AST.Refine
                ({ FStar_Parser_AST.b = FStar_Parser_AST.Annotated (lid',t1);
                   FStar_Parser_AST.brange = uu____4874;
                   FStar_Parser_AST.blevel = uu____4875;
                   FStar_Parser_AST.aqual = uu____4876;_},phi)
                when lid.FStar_Ident.idText = lid'.FStar_Ident.idText ->
                let uu____4878 = p_lident lid  in
                p_refinement b.FStar_Parser_AST.aqual uu____4878 t1 phi
            | uu____4879 ->
                let uu____4880 =
                  FStar_Pprint.optional p_aqual b.FStar_Parser_AST.aqual  in
                let uu____4881 =
                  let uu____4882 = p_lident lid  in
                  let uu____4883 =
                    let uu____4884 = p_tmFormula t  in
                    FStar_Pprint.op_Hat_Slash_Hat FStar_Pprint.colon
                      uu____4884
                     in
                  FStar_Pprint.op_Hat_Hat uu____4882 uu____4883  in
                FStar_Pprint.op_Hat_Hat uu____4880 uu____4881
             in
          if is_atomic
          then
            let uu____4885 =
              let uu____4886 =
                FStar_Pprint.op_Hat_Hat doc1 FStar_Pprint.rparen  in
              FStar_Pprint.op_Hat_Hat FStar_Pprint.lparen uu____4886  in
            FStar_Pprint.group uu____4885
          else FStar_Pprint.group doc1
      | FStar_Parser_AST.TAnnotated uu____4888 ->
          failwith "Is this still used ?"
      | FStar_Parser_AST.NoName t ->
          (match t.FStar_Parser_AST.tm with
           | FStar_Parser_AST.Refine
               ({ FStar_Parser_AST.b = FStar_Parser_AST.NoName t1;
                  FStar_Parser_AST.brange = uu____4895;
                  FStar_Parser_AST.blevel = uu____4896;
                  FStar_Parser_AST.aqual = uu____4897;_},phi)
               ->
               if is_atomic
               then
                 let uu____4899 =
                   let uu____4900 =
                     let uu____4901 =
                       p_refinement b.FStar_Parser_AST.aqual
                         FStar_Pprint.underscore t1 phi
                        in
                     FStar_Pprint.op_Hat_Hat uu____4901 FStar_Pprint.rparen
                      in
                   FStar_Pprint.op_Hat_Hat FStar_Pprint.lparen uu____4900  in
                 FStar_Pprint.group uu____4899
               else
                 (let uu____4903 =
                    p_refinement b.FStar_Parser_AST.aqual
                      FStar_Pprint.underscore t1 phi
                     in
                  FStar_Pprint.group uu____4903)
           | uu____4904 -> if is_atomic then p_atomicTerm t else p_appTerm t)

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
            | FStar_Parser_AST.Construct uu____4913 -> false
            | FStar_Parser_AST.App uu____4924 -> false
            | FStar_Parser_AST.Op uu____4931 -> false
            | uu____4938 -> true  in
          let phi1 = p_noSeqTerm false false phi  in
          let jump_break =
            if is_t_atomic
            then (Prims.parse_int "0")
            else (Prims.parse_int "1")  in
          let uu____4942 =
            let uu____4943 = FStar_Pprint.optional p_aqual aqual_opt  in
            let uu____4944 =
              FStar_Pprint.op_Hat_Hat binder FStar_Pprint.colon  in
            FStar_Pprint.op_Hat_Hat uu____4943 uu____4944  in
          let uu____4945 =
            let uu____4946 = p_appTerm t  in
            let uu____4947 =
              let uu____4948 =
                let uu____4949 =
                  let uu____4950 = soft_braces_with_nesting_tight phi1  in
                  let uu____4951 = soft_braces_with_nesting phi1  in
                  FStar_Pprint.ifflat uu____4950 uu____4951  in
                FStar_Pprint.group uu____4949  in
              FStar_Pprint.jump (Prims.parse_int "2") jump_break uu____4948
               in
            FStar_Pprint.op_Hat_Hat uu____4946 uu____4947  in
          FStar_Pprint.op_Hat_Slash_Hat uu____4942 uu____4945

and (p_binders_list :
  Prims.bool ->
    FStar_Parser_AST.binder Prims.list -> FStar_Pprint.document Prims.list)
  = fun is_atomic  -> fun bs  -> FStar_List.map (p_binder is_atomic) bs

and (p_binders :
  Prims.bool -> FStar_Parser_AST.binder Prims.list -> FStar_Pprint.document)
  =
  fun is_atomic  ->
    fun bs  ->
      let uu____4962 = p_binders_list is_atomic bs  in
      separate_or_flow break1 uu____4962

and (text_of_id_or_underscore : FStar_Ident.ident -> FStar_Pprint.document) =
  fun lid  ->
    if
      FStar_Util.starts_with lid.FStar_Ident.idText
        FStar_Ident.reserved_prefix
    then FStar_Pprint.underscore
    else (let uu____4967 = FStar_Ident.text_of_id lid  in str uu____4967)

and (text_of_lid_or_underscore : FStar_Ident.lident -> FStar_Pprint.document)
  =
  fun lid  ->
    if
      FStar_Util.starts_with (lid.FStar_Ident.ident).FStar_Ident.idText
        FStar_Ident.reserved_prefix
    then FStar_Pprint.underscore
    else (let uu____4970 = FStar_Ident.text_of_lid lid  in str uu____4970)

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
            let uu____4987 =
              let uu____4988 =
                let uu____4989 = p_noSeqTerm true false e1  in
                FStar_Pprint.op_Hat_Hat uu____4989 FStar_Pprint.semi  in
              FStar_Pprint.group uu____4988  in
            let uu____4990 = p_term ps pb e2  in
            FStar_Pprint.op_Hat_Slash_Hat uu____4987 uu____4990
        | FStar_Parser_AST.Bind (x,e1,e2) ->
            let uu____4994 =
              let uu____4995 =
                let uu____4996 =
                  let uu____4997 = p_lident x  in
                  let uu____4998 =
                    FStar_Pprint.op_Hat_Hat FStar_Pprint.space
                      FStar_Pprint.long_left_arrow
                     in
                  FStar_Pprint.op_Hat_Hat uu____4997 uu____4998  in
                let uu____4999 =
                  let uu____5000 = p_noSeqTerm true false e1  in
                  let uu____5001 =
                    FStar_Pprint.op_Hat_Hat FStar_Pprint.space
                      FStar_Pprint.semi
                     in
                  FStar_Pprint.op_Hat_Hat uu____5000 uu____5001  in
                op_Hat_Slash_Plus_Hat uu____4996 uu____4999  in
              FStar_Pprint.group uu____4995  in
            let uu____5002 = p_term ps pb e2  in
            FStar_Pprint.op_Hat_Slash_Hat uu____4994 uu____5002
        | uu____5003 ->
            let uu____5004 = p_noSeqTerm ps pb e  in
            FStar_Pprint.group uu____5004

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
            let uu____5015 =
              let uu____5016 = p_tmIff e1  in
              let uu____5017 =
                let uu____5018 =
                  let uu____5019 = p_typ ps pb t  in
                  FStar_Pprint.op_Hat_Slash_Hat FStar_Pprint.colon uu____5019
                   in
                FStar_Pprint.op_Hat_Hat FStar_Pprint.langle uu____5018  in
              FStar_Pprint.op_Hat_Slash_Hat uu____5016 uu____5017  in
            FStar_Pprint.group uu____5015
        | FStar_Parser_AST.Ascribed (e1,t,FStar_Pervasives_Native.Some tac)
            ->
            let uu____5025 =
              let uu____5026 = p_tmIff e1  in
              let uu____5027 =
                let uu____5028 =
                  let uu____5029 =
                    let uu____5030 = p_typ false false t  in
                    let uu____5031 =
                      let uu____5032 = str "by"  in
                      let uu____5033 = p_typ ps pb tac  in
                      FStar_Pprint.op_Hat_Slash_Hat uu____5032 uu____5033  in
                    FStar_Pprint.op_Hat_Slash_Hat uu____5030 uu____5031  in
                  FStar_Pprint.op_Hat_Slash_Hat FStar_Pprint.colon uu____5029
                   in
                FStar_Pprint.op_Hat_Hat FStar_Pprint.langle uu____5028  in
              FStar_Pprint.op_Hat_Slash_Hat uu____5026 uu____5027  in
            FStar_Pprint.group uu____5025
        | FStar_Parser_AST.Op
            ({ FStar_Ident.idText = ".()<-";
               FStar_Ident.idRange = uu____5034;_},e1::e2::e3::[])
            ->
            let uu____5040 =
              let uu____5041 =
                let uu____5042 =
                  let uu____5043 = p_atomicTermNotQUident e1  in
                  let uu____5044 =
                    let uu____5045 =
                      let uu____5046 =
                        let uu____5047 = p_term false false e2  in
                        soft_parens_with_nesting uu____5047  in
                      let uu____5048 =
                        FStar_Pprint.op_Hat_Hat FStar_Pprint.space
                          FStar_Pprint.larrow
                         in
                      FStar_Pprint.op_Hat_Hat uu____5046 uu____5048  in
                    FStar_Pprint.op_Hat_Hat FStar_Pprint.dot uu____5045  in
                  FStar_Pprint.op_Hat_Hat uu____5043 uu____5044  in
                FStar_Pprint.group uu____5042  in
              let uu____5049 =
                let uu____5050 = p_noSeqTerm ps pb e3  in jump2 uu____5050
                 in
              FStar_Pprint.op_Hat_Hat uu____5041 uu____5049  in
            FStar_Pprint.group uu____5040
        | FStar_Parser_AST.Op
            ({ FStar_Ident.idText = ".[]<-";
               FStar_Ident.idRange = uu____5051;_},e1::e2::e3::[])
            ->
            let uu____5057 =
              let uu____5058 =
                let uu____5059 =
                  let uu____5060 = p_atomicTermNotQUident e1  in
                  let uu____5061 =
                    let uu____5062 =
                      let uu____5063 =
                        let uu____5064 = p_term false false e2  in
                        soft_brackets_with_nesting uu____5064  in
                      let uu____5065 =
                        FStar_Pprint.op_Hat_Hat FStar_Pprint.space
                          FStar_Pprint.larrow
                         in
                      FStar_Pprint.op_Hat_Hat uu____5063 uu____5065  in
                    FStar_Pprint.op_Hat_Hat FStar_Pprint.dot uu____5062  in
                  FStar_Pprint.op_Hat_Hat uu____5060 uu____5061  in
                FStar_Pprint.group uu____5059  in
              let uu____5066 =
                let uu____5067 = p_noSeqTerm ps pb e3  in jump2 uu____5067
                 in
              FStar_Pprint.op_Hat_Hat uu____5058 uu____5066  in
            FStar_Pprint.group uu____5057
        | FStar_Parser_AST.Requires (e1,wtf) ->
            let uu____5077 =
              let uu____5078 = str "requires"  in
              let uu____5079 = p_typ ps pb e1  in
              FStar_Pprint.op_Hat_Slash_Hat uu____5078 uu____5079  in
            FStar_Pprint.group uu____5077
        | FStar_Parser_AST.Ensures (e1,wtf) ->
            let uu____5089 =
              let uu____5090 = str "ensures"  in
              let uu____5091 = p_typ ps pb e1  in
              FStar_Pprint.op_Hat_Slash_Hat uu____5090 uu____5091  in
            FStar_Pprint.group uu____5089
        | FStar_Parser_AST.Attributes es ->
            let uu____5095 =
              let uu____5096 = str "attributes"  in
              let uu____5097 =
                FStar_Pprint.separate_map break1 p_atomicTerm es  in
              FStar_Pprint.op_Hat_Slash_Hat uu____5096 uu____5097  in
            FStar_Pprint.group uu____5095
        | FStar_Parser_AST.If (e1,e2,e3) ->
            if is_unit e3
            then
              let uu____5101 =
                let uu____5102 =
                  let uu____5103 = str "if"  in
                  let uu____5104 = p_noSeqTerm false false e1  in
                  op_Hat_Slash_Plus_Hat uu____5103 uu____5104  in
                let uu____5105 =
                  let uu____5106 = str "then"  in
                  let uu____5107 = p_noSeqTerm ps pb e2  in
                  op_Hat_Slash_Plus_Hat uu____5106 uu____5107  in
                FStar_Pprint.op_Hat_Slash_Hat uu____5102 uu____5105  in
              FStar_Pprint.group uu____5101
            else
              (let e2_doc =
                 match e2.FStar_Parser_AST.tm with
                 | FStar_Parser_AST.If (uu____5110,uu____5111,e31) when
                     is_unit e31 ->
                     let uu____5113 = p_noSeqTerm false false e2  in
                     soft_parens_with_nesting uu____5113
                 | uu____5114 -> p_noSeqTerm false false e2  in
               let uu____5115 =
                 let uu____5116 =
                   let uu____5117 = str "if"  in
                   let uu____5118 = p_noSeqTerm false false e1  in
                   op_Hat_Slash_Plus_Hat uu____5117 uu____5118  in
                 let uu____5119 =
                   let uu____5120 =
                     let uu____5121 = str "then"  in
                     op_Hat_Slash_Plus_Hat uu____5121 e2_doc  in
                   let uu____5122 =
                     let uu____5123 = str "else"  in
                     let uu____5124 = p_noSeqTerm ps pb e3  in
                     op_Hat_Slash_Plus_Hat uu____5123 uu____5124  in
                   FStar_Pprint.op_Hat_Slash_Hat uu____5120 uu____5122  in
                 FStar_Pprint.op_Hat_Slash_Hat uu____5116 uu____5119  in
               FStar_Pprint.group uu____5115)
        | FStar_Parser_AST.TryWith (e1,branches) ->
            let uu____5147 =
              let uu____5148 =
                let uu____5149 =
                  let uu____5150 = str "try"  in
                  let uu____5151 = p_noSeqTerm false false e1  in
                  prefix2 uu____5150 uu____5151  in
                let uu____5152 =
                  let uu____5153 = str "with"  in
                  let uu____5154 =
                    separate_map_last FStar_Pprint.hardline p_patternBranch
                      branches
                     in
                  FStar_Pprint.op_Hat_Slash_Hat uu____5153 uu____5154  in
                FStar_Pprint.op_Hat_Slash_Hat uu____5149 uu____5152  in
              FStar_Pprint.group uu____5148  in
            let uu____5163 = paren_if (ps || pb)  in uu____5163 uu____5147
        | FStar_Parser_AST.Match (e1,branches) ->
            let uu____5188 =
              let uu____5189 =
                let uu____5190 =
                  let uu____5191 = str "match"  in
                  let uu____5192 = p_noSeqTerm false false e1  in
                  let uu____5193 = str "with"  in
                  FStar_Pprint.surround (Prims.parse_int "2")
                    (Prims.parse_int "1") uu____5191 uu____5192 uu____5193
                   in
                let uu____5194 =
                  separate_map_last FStar_Pprint.hardline p_patternBranch
                    branches
                   in
                FStar_Pprint.op_Hat_Slash_Hat uu____5190 uu____5194  in
              FStar_Pprint.group uu____5189  in
            let uu____5203 = paren_if (ps || pb)  in uu____5203 uu____5188
        | FStar_Parser_AST.LetOpen (uid,e1) ->
            let uu____5208 =
              let uu____5209 =
                let uu____5210 =
                  let uu____5211 = str "let open"  in
                  let uu____5212 = p_quident uid  in
                  let uu____5213 = str "in"  in
                  FStar_Pprint.surround (Prims.parse_int "2")
                    (Prims.parse_int "1") uu____5211 uu____5212 uu____5213
                   in
                let uu____5214 = p_term false pb e1  in
                FStar_Pprint.op_Hat_Slash_Hat uu____5210 uu____5214  in
              FStar_Pprint.group uu____5209  in
            let uu____5215 = paren_if ps  in uu____5215 uu____5208
        | FStar_Parser_AST.Let (q,lbs,e1) ->
            let p_lb q1 uu____5271 is_last =
              match uu____5271 with
              | (a,(pat,e2)) ->
                  let attrs = p_attrs_opt a  in
                  let doc_let_or_and =
                    match q1 with
                    | FStar_Pervasives_Native.Some (FStar_Parser_AST.Rec ) ->
                        let uu____5304 =
                          let uu____5305 = str "let"  in
                          let uu____5306 = str "rec"  in
                          FStar_Pprint.op_Hat_Slash_Hat uu____5305 uu____5306
                           in
                        FStar_Pprint.group uu____5304
                    | FStar_Pervasives_Native.Some
                        (FStar_Parser_AST.NoLetQualifier ) -> str "let"
                    | uu____5307 -> str "and"  in
                  let doc_pat = p_letlhs doc_let_or_and (pat, e2)  in
                  let doc_expr = p_term false false e2  in
                  let uu____5312 =
                    if is_last
                    then
                      let uu____5313 =
                        FStar_Pprint.flow break1
                          [doc_pat; FStar_Pprint.equals]
                         in
                      let uu____5314 = str "in"  in
                      FStar_Pprint.surround (Prims.parse_int "2")
                        (Prims.parse_int "1") uu____5313 doc_expr uu____5314
                    else
                      (let uu____5316 =
                         FStar_Pprint.flow break1
                           [doc_pat; FStar_Pprint.equals; doc_expr]
                          in
                       FStar_Pprint.hang (Prims.parse_int "2") uu____5316)
                     in
                  FStar_Pprint.op_Hat_Hat attrs uu____5312
               in
            let l = FStar_List.length lbs  in
            let lbs_docs =
              FStar_List.mapi
                (fun i  ->
                   fun lb  ->
                     if i = (Prims.parse_int "0")
                     then
                       let uu____5362 =
                         p_lb (FStar_Pervasives_Native.Some q) lb
                           (i = (l - (Prims.parse_int "1")))
                          in
                       FStar_Pprint.group uu____5362
                     else
                       (let uu____5370 =
                          p_lb FStar_Pervasives_Native.None lb
                            (i = (l - (Prims.parse_int "1")))
                           in
                        FStar_Pprint.group uu____5370)) lbs
               in
            let lbs_doc =
              let uu____5378 = FStar_Pprint.separate break1 lbs_docs  in
              FStar_Pprint.group uu____5378  in
            let uu____5379 =
              let uu____5380 =
                let uu____5381 =
                  let uu____5382 = p_term false pb e1  in
                  FStar_Pprint.op_Hat_Hat FStar_Pprint.hardline uu____5382
                   in
                FStar_Pprint.op_Hat_Hat lbs_doc uu____5381  in
              FStar_Pprint.group uu____5380  in
            let uu____5383 = paren_if ps  in uu____5383 uu____5379
        | FStar_Parser_AST.Abs
            ({ FStar_Parser_AST.pat = FStar_Parser_AST.PatVar (x,typ_opt);
               FStar_Parser_AST.prange = uu____5388;_}::[],{
                                                             FStar_Parser_AST.tm
                                                               =
                                                               FStar_Parser_AST.Match
                                                               (maybe_x,branches);
                                                             FStar_Parser_AST.range
                                                               = uu____5391;
                                                             FStar_Parser_AST.level
                                                               = uu____5392;_})
            when matches_var maybe_x x ->
            let uu____5419 =
              let uu____5420 =
                let uu____5421 = str "function"  in
                let uu____5422 =
                  separate_map_last FStar_Pprint.hardline p_patternBranch
                    branches
                   in
                FStar_Pprint.op_Hat_Slash_Hat uu____5421 uu____5422  in
              FStar_Pprint.group uu____5420  in
            let uu____5431 = paren_if (ps || pb)  in uu____5431 uu____5419
        | FStar_Parser_AST.Quote (e1,FStar_Parser_AST.Dynamic ) ->
            let uu____5435 =
              let uu____5436 = str "quote"  in
              let uu____5437 = p_noSeqTerm ps pb e1  in
              FStar_Pprint.op_Hat_Slash_Hat uu____5436 uu____5437  in
            FStar_Pprint.group uu____5435
        | FStar_Parser_AST.Quote (e1,FStar_Parser_AST.Static ) ->
            let uu____5439 =
              let uu____5440 = str "`"  in
              let uu____5441 = p_noSeqTerm ps pb e1  in
              FStar_Pprint.op_Hat_Hat uu____5440 uu____5441  in
            FStar_Pprint.group uu____5439
        | FStar_Parser_AST.VQuote e1 ->
            let uu____5443 =
              let uu____5444 = str "%`"  in
              let uu____5445 = p_noSeqTerm ps pb e1  in
              FStar_Pprint.op_Hat_Hat uu____5444 uu____5445  in
            FStar_Pprint.group uu____5443
        | FStar_Parser_AST.Antiquote (false ,e1) ->
            let uu____5447 =
              let uu____5448 = str "`#"  in
              let uu____5449 = p_noSeqTerm ps pb e1  in
              FStar_Pprint.op_Hat_Hat uu____5448 uu____5449  in
            FStar_Pprint.group uu____5447
        | FStar_Parser_AST.Antiquote (true ,e1) ->
            let uu____5451 =
              let uu____5452 = str "`@"  in
              let uu____5453 = p_noSeqTerm ps pb e1  in
              FStar_Pprint.op_Hat_Hat uu____5452 uu____5453  in
            FStar_Pprint.group uu____5451
        | uu____5454 -> p_typ ps pb e

and (p_attrs_opt :
  FStar_Parser_AST.term Prims.list FStar_Pervasives_Native.option ->
    FStar_Pprint.document)
  =
  fun uu___63_5455  ->
    match uu___63_5455 with
    | FStar_Pervasives_Native.None  -> FStar_Pprint.empty
    | FStar_Pervasives_Native.Some terms ->
        let uu____5467 =
          let uu____5468 = str "[@"  in
          let uu____5469 =
            let uu____5470 =
              FStar_Pprint.separate_map break1 p_atomicTerm terms  in
            let uu____5471 = str "]"  in
            FStar_Pprint.op_Hat_Slash_Hat uu____5470 uu____5471  in
          FStar_Pprint.op_Hat_Slash_Hat uu____5468 uu____5469  in
        FStar_Pprint.group uu____5467

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
                 let uu____5497 =
                   let uu____5498 =
                     let uu____5499 = p_quantifier e  in
                     FStar_Pprint.op_Hat_Hat uu____5499 FStar_Pprint.space
                      in
                   FStar_Pprint.soft_surround (Prims.parse_int "2")
                     (Prims.parse_int "0") uu____5498 binders_doc
                     FStar_Pprint.dot
                    in
                 prefix2 uu____5497 term_doc
             | pats ->
                 let uu____5505 =
                   let uu____5506 =
                     let uu____5507 =
                       let uu____5508 =
                         let uu____5509 = p_quantifier e  in
                         FStar_Pprint.op_Hat_Hat uu____5509
                           FStar_Pprint.space
                          in
                       FStar_Pprint.soft_surround (Prims.parse_int "2")
                         (Prims.parse_int "0") uu____5508 binders_doc
                         FStar_Pprint.dot
                        in
                     let uu____5510 = p_trigger trigger  in
                     prefix2 uu____5507 uu____5510  in
                   FStar_Pprint.group uu____5506  in
                 prefix2 uu____5505 term_doc)
        | FStar_Parser_AST.QExists (bs,trigger,e1) ->
            let binders_doc = p_binders true bs  in
            let term_doc = p_noSeqTerm ps pb e1  in
            (match trigger with
             | [] ->
                 let uu____5530 =
                   let uu____5531 =
                     let uu____5532 = p_quantifier e  in
                     FStar_Pprint.op_Hat_Hat uu____5532 FStar_Pprint.space
                      in
                   FStar_Pprint.soft_surround (Prims.parse_int "2")
                     (Prims.parse_int "0") uu____5531 binders_doc
                     FStar_Pprint.dot
                    in
                 prefix2 uu____5530 term_doc
             | pats ->
                 let uu____5538 =
                   let uu____5539 =
                     let uu____5540 =
                       let uu____5541 =
                         let uu____5542 = p_quantifier e  in
                         FStar_Pprint.op_Hat_Hat uu____5542
                           FStar_Pprint.space
                          in
                       FStar_Pprint.soft_surround (Prims.parse_int "2")
                         (Prims.parse_int "0") uu____5541 binders_doc
                         FStar_Pprint.dot
                        in
                     let uu____5543 = p_trigger trigger  in
                     prefix2 uu____5540 uu____5543  in
                   FStar_Pprint.group uu____5539  in
                 prefix2 uu____5538 term_doc)
        | uu____5544 -> p_simpleTerm ps pb e

and (p_quantifier : FStar_Parser_AST.term -> FStar_Pprint.document) =
  fun e  ->
    match e.FStar_Parser_AST.tm with
    | FStar_Parser_AST.QForall uu____5546 -> str "forall"
    | FStar_Parser_AST.QExists uu____5559 -> str "exists"
    | uu____5572 ->
        failwith "Imposible : p_quantifier called on a non-quantifier term"

and (p_trigger :
  FStar_Parser_AST.term Prims.list Prims.list -> FStar_Pprint.document) =
  fun uu___64_5573  ->
    match uu___64_5573 with
    | [] -> FStar_Pprint.empty
    | pats ->
        let uu____5585 =
          let uu____5586 =
            let uu____5587 =
              let uu____5588 = str "pattern"  in
              let uu____5589 =
                let uu____5590 =
                  let uu____5591 = p_disjunctivePats pats  in
                  FStar_Pprint.jump (Prims.parse_int "2")
                    (Prims.parse_int "0") uu____5591
                   in
                FStar_Pprint.op_Hat_Hat uu____5590 FStar_Pprint.rbrace  in
              FStar_Pprint.op_Hat_Slash_Hat uu____5588 uu____5589  in
            FStar_Pprint.op_Hat_Hat FStar_Pprint.colon uu____5587  in
          FStar_Pprint.op_Hat_Hat FStar_Pprint.lbrace uu____5586  in
        FStar_Pprint.group uu____5585

and (p_disjunctivePats :
  FStar_Parser_AST.term Prims.list Prims.list -> FStar_Pprint.document) =
  fun pats  ->
    let uu____5597 = str "\\/"  in
    FStar_Pprint.separate_map uu____5597 p_conjunctivePats pats

and (p_conjunctivePats :
  FStar_Parser_AST.term Prims.list -> FStar_Pprint.document) =
  fun pats  ->
    let uu____5603 =
      let uu____5604 = FStar_Pprint.op_Hat_Hat FStar_Pprint.semi break1  in
      FStar_Pprint.separate_map uu____5604 p_appTerm pats  in
    FStar_Pprint.group uu____5603

and (p_simpleTerm :
  Prims.bool -> Prims.bool -> FStar_Parser_AST.term -> FStar_Pprint.document)
  =
  fun ps  ->
    fun pb  ->
      fun e  ->
        match e.FStar_Parser_AST.tm with
        | FStar_Parser_AST.Abs (pats,e1) ->
            let uu____5614 =
              let uu____5615 =
                let uu____5616 = str "fun"  in
                let uu____5617 =
                  let uu____5618 =
                    FStar_Pprint.separate_map break1 p_atomicPattern pats  in
                  FStar_Pprint.op_Hat_Slash_Hat uu____5618
                    FStar_Pprint.rarrow
                   in
                op_Hat_Slash_Plus_Hat uu____5616 uu____5617  in
              let uu____5619 = p_term false pb e1  in
              op_Hat_Slash_Plus_Hat uu____5615 uu____5619  in
            let uu____5620 = paren_if ps  in uu____5620 uu____5614
        | uu____5623 -> p_tmIff e

and (p_maybeFocusArrow : Prims.bool -> FStar_Pprint.document) =
  fun b  -> if b then str "~>" else FStar_Pprint.rarrow

and (p_patternBranch :
  Prims.bool ->
    (FStar_Parser_AST.pattern,FStar_Parser_AST.term
                                FStar_Pervasives_Native.option,FStar_Parser_AST.term)
      FStar_Pervasives_Native.tuple3 -> FStar_Pprint.document)
  =
  fun pb  ->
    fun uu____5627  ->
      match uu____5627 with
      | (pat,when_opt,e) ->
          let one_pattern_branch p =
            let branch =
              match when_opt with
              | FStar_Pervasives_Native.None  ->
                  let uu____5648 =
                    let uu____5649 =
                      let uu____5650 =
                        let uu____5651 = p_tuplePattern p  in
                        let uu____5652 =
                          FStar_Pprint.op_Hat_Hat FStar_Pprint.space
                            FStar_Pprint.rarrow
                           in
                        FStar_Pprint.op_Hat_Hat uu____5651 uu____5652  in
                      FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____5650
                       in
                    FStar_Pprint.op_Hat_Hat FStar_Pprint.bar uu____5649  in
                  FStar_Pprint.group uu____5648
              | FStar_Pervasives_Native.Some f ->
                  let uu____5654 =
                    let uu____5655 =
                      let uu____5656 =
                        let uu____5657 =
                          let uu____5658 =
                            let uu____5659 = p_tuplePattern p  in
                            let uu____5660 = str "when"  in
                            FStar_Pprint.op_Hat_Slash_Hat uu____5659
                              uu____5660
                             in
                          FStar_Pprint.group uu____5658  in
                        let uu____5661 =
                          let uu____5662 =
                            let uu____5665 = p_tmFormula f  in
                            [uu____5665; FStar_Pprint.rarrow]  in
                          FStar_Pprint.flow break1 uu____5662  in
                        FStar_Pprint.op_Hat_Slash_Hat uu____5657 uu____5661
                         in
                      FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____5656
                       in
                    FStar_Pprint.op_Hat_Hat FStar_Pprint.bar uu____5655  in
                  FStar_Pprint.hang (Prims.parse_int "2") uu____5654
               in
            let uu____5666 =
              let uu____5667 = p_term false pb e  in
              op_Hat_Slash_Plus_Hat branch uu____5667  in
            FStar_Pprint.group uu____5666  in
          (match pat.FStar_Parser_AST.pat with
           | FStar_Parser_AST.PatOr pats ->
               (match FStar_List.rev pats with
                | hd1::tl1 ->
                    let last_pat_branch = one_pattern_branch hd1  in
                    let uu____5676 =
                      let uu____5677 =
                        let uu____5678 =
                          let uu____5679 =
                            let uu____5680 =
                              let uu____5681 =
                                FStar_Pprint.op_Hat_Hat FStar_Pprint.bar
                                  FStar_Pprint.space
                                 in
                              FStar_Pprint.op_Hat_Hat break1 uu____5681  in
                            FStar_Pprint.separate_map uu____5680
                              p_tuplePattern (FStar_List.rev tl1)
                             in
                          FStar_Pprint.op_Hat_Slash_Hat uu____5679
                            last_pat_branch
                           in
                        FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____5678
                         in
                      FStar_Pprint.op_Hat_Hat FStar_Pprint.bar uu____5677  in
                    FStar_Pprint.group uu____5676
                | [] ->
                    failwith "Impossible: disjunctive pattern can't be empty")
           | uu____5682 -> one_pattern_branch pat)

and (p_tmIff : FStar_Parser_AST.term -> FStar_Pprint.document) =
  fun e  ->
    match e.FStar_Parser_AST.tm with
    | FStar_Parser_AST.Op
        ({ FStar_Ident.idText = "<==>"; FStar_Ident.idRange = uu____5684;_},e1::e2::[])
        ->
        let uu____5689 = str "<==>"  in
        let uu____5690 = p_tmImplies e1  in
        let uu____5691 = p_tmIff e2  in
        infix0 uu____5689 uu____5690 uu____5691
    | uu____5692 -> p_tmImplies e

and (p_tmImplies : FStar_Parser_AST.term -> FStar_Pprint.document) =
  fun e  ->
    match e.FStar_Parser_AST.tm with
    | FStar_Parser_AST.Op
        ({ FStar_Ident.idText = "==>"; FStar_Ident.idRange = uu____5694;_},e1::e2::[])
        ->
        let uu____5699 = str "==>"  in
        let uu____5700 = p_tmArrow p_tmFormula e1  in
        let uu____5701 = p_tmImplies e2  in
        infix0 uu____5699 uu____5700 uu____5701
    | uu____5702 -> p_tmArrow p_tmFormula e

and (p_tmArrow :
  (FStar_Parser_AST.term -> FStar_Pprint.document) ->
    FStar_Parser_AST.term -> FStar_Pprint.document)
  =
  fun p_Tm  ->
    fun e  ->
      let terms = p_tmArrow' p_Tm e  in
      let uu____5710 =
        FStar_List.splitAt
          ((FStar_List.length terms) - (Prims.parse_int "1")) terms
         in
      match uu____5710 with
      | (terms',last1) ->
          let last_op =
            if (FStar_List.length terms) > (Prims.parse_int "1")
            then
              FStar_Pprint.op_Hat_Hat FStar_Pprint.space FStar_Pprint.rarrow
            else FStar_Pprint.empty  in
          (match FStar_List.length terms with
           | _0_31 when _0_31 = (Prims.parse_int "1") -> FStar_List.hd terms
           | uu____5731 ->
               let uu____5732 =
                 let uu____5733 =
                   let uu____5734 =
                     let uu____5735 =
                       FStar_Pprint.op_Hat_Hat FStar_Pprint.rarrow break1  in
                     FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____5735
                      in
                   FStar_Pprint.separate uu____5734 terms  in
                 let uu____5736 =
                   let uu____5737 =
                     let uu____5738 =
                       let uu____5739 =
                         let uu____5740 =
                           let uu____5741 =
                             let uu____5742 =
                               FStar_Pprint.op_Hat_Hat FStar_Pprint.rarrow
                                 break1
                                in
                             FStar_Pprint.op_Hat_Hat FStar_Pprint.space
                               uu____5742
                              in
                           FStar_Pprint.separate uu____5741 terms'  in
                         FStar_Pprint.op_Hat_Hat uu____5740 last_op  in
                       let uu____5743 =
                         let uu____5744 =
                           let uu____5745 =
                             let uu____5746 =
                               let uu____5747 =
                                 FStar_Pprint.op_Hat_Hat FStar_Pprint.rarrow
                                   break1
                                  in
                               FStar_Pprint.op_Hat_Hat FStar_Pprint.space
                                 uu____5747
                                in
                             FStar_Pprint.separate uu____5746 terms'  in
                           FStar_Pprint.op_Hat_Hat uu____5745 last_op  in
                         jump2 uu____5744  in
                       FStar_Pprint.ifflat uu____5739 uu____5743  in
                     FStar_Pprint.group uu____5738  in
                   let uu____5748 = FStar_List.hd last1  in
                   prefix2 uu____5737 uu____5748  in
                 FStar_Pprint.ifflat uu____5733 uu____5736  in
               FStar_Pprint.group uu____5732)

and (p_tmArrow' :
  (FStar_Parser_AST.term -> FStar_Pprint.document) ->
    FStar_Parser_AST.term -> FStar_Pprint.document Prims.list)
  =
  fun p_Tm  ->
    fun e  ->
      match e.FStar_Parser_AST.tm with
      | FStar_Parser_AST.Product (bs,tgt) ->
          let uu____5761 = FStar_List.map (fun b  -> p_binder false b) bs  in
          let uu____5766 = p_tmArrow' p_Tm tgt  in
          FStar_List.append uu____5761 uu____5766
      | uu____5769 -> let uu____5770 = p_Tm e  in [uu____5770]

and (p_tmFormula : FStar_Parser_AST.term -> FStar_Pprint.document) =
  fun e  ->
    let conj =
      let uu____5773 =
        let uu____5774 = str "/\\"  in
        FStar_Pprint.op_Hat_Hat uu____5774 break1  in
      FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____5773  in
    let disj =
      let uu____5776 =
        let uu____5777 = str "\\/"  in
        FStar_Pprint.op_Hat_Hat uu____5777 break1  in
      FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____5776  in
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
        ({ FStar_Ident.idText = "\\/"; FStar_Ident.idRange = uu____5796;_},e1::e2::[])
        ->
        let uu____5801 = p_tmDisjunction e1  in
        let uu____5806 = let uu____5811 = p_tmConjunction e2  in [uu____5811]
           in
        FStar_List.append uu____5801 uu____5806
    | uu____5820 -> let uu____5821 = p_tmConjunction e  in [uu____5821]

and (p_tmConjunction :
  FStar_Parser_AST.term -> FStar_Pprint.document Prims.list) =
  fun e  ->
    match e.FStar_Parser_AST.tm with
    | FStar_Parser_AST.Op
        ({ FStar_Ident.idText = "/\\"; FStar_Ident.idRange = uu____5831;_},e1::e2::[])
        ->
        let uu____5836 = p_tmConjunction e1  in
        let uu____5839 = let uu____5842 = p_tmTuple e2  in [uu____5842]  in
        FStar_List.append uu____5836 uu____5839
    | uu____5843 -> let uu____5844 = p_tmTuple e  in [uu____5844]

and (p_tmTuple : FStar_Parser_AST.term -> FStar_Pprint.document) =
  fun e  -> with_comment p_tmTuple' e e.FStar_Parser_AST.range

and (p_tmTuple' : FStar_Parser_AST.term -> FStar_Pprint.document) =
  fun e  ->
    match e.FStar_Parser_AST.tm with
    | FStar_Parser_AST.Construct (lid,args) when is_tuple_constructor lid ->
        let uu____5861 = FStar_Pprint.op_Hat_Hat FStar_Pprint.comma break1
           in
        FStar_Pprint.separate_map uu____5861
          (fun uu____5869  ->
             match uu____5869 with | (e1,uu____5875) -> p_tmEq e1) args
    | uu____5876 -> p_tmEq e

and (paren_if_gt :
  Prims.int -> Prims.int -> FStar_Pprint.document -> FStar_Pprint.document) =
  fun curr  ->
    fun mine  ->
      fun doc1  ->
        if mine <= curr
        then doc1
        else
          (let uu____5881 =
             let uu____5882 =
               FStar_Pprint.op_Hat_Hat doc1 FStar_Pprint.rparen  in
             FStar_Pprint.op_Hat_Hat FStar_Pprint.lparen uu____5882  in
           FStar_Pprint.group uu____5881)

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
               (let uu____5945 = FStar_Ident.text_of_id op  in
                uu____5945 = "="))
              ||
              (let uu____5947 = FStar_Ident.text_of_id op  in
               uu____5947 = "|>")
            ->
            let op1 = FStar_Ident.text_of_id op  in
            let uu____5949 = levels op1  in
            (match uu____5949 with
             | (left1,mine,right1) ->
                 let uu____5959 =
                   let uu____5960 = FStar_All.pipe_left str op1  in
                   let uu____5961 = p_tmEqWith' p_X left1 e1  in
                   let uu____5962 = p_tmEqWith' p_X right1 e2  in
                   infix0 uu____5960 uu____5961 uu____5962  in
                 paren_if_gt curr mine uu____5959)
        | FStar_Parser_AST.Op
            ({ FStar_Ident.idText = ":="; FStar_Ident.idRange = uu____5963;_},e1::e2::[])
            ->
            let uu____5968 =
              let uu____5969 = p_tmEqWith p_X e1  in
              let uu____5970 =
                let uu____5971 =
                  let uu____5972 =
                    let uu____5973 = p_tmEqWith p_X e2  in
                    op_Hat_Slash_Plus_Hat FStar_Pprint.equals uu____5973  in
                  FStar_Pprint.op_Hat_Hat FStar_Pprint.colon uu____5972  in
                FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____5971  in
              FStar_Pprint.op_Hat_Hat uu____5969 uu____5970  in
            FStar_Pprint.group uu____5968
        | FStar_Parser_AST.Op
            ({ FStar_Ident.idText = "-"; FStar_Ident.idRange = uu____5974;_},e1::[])
            ->
            let uu____5978 = levels "-"  in
            (match uu____5978 with
             | (left1,mine,right1) ->
                 let uu____5988 = p_tmEqWith' p_X mine e1  in
                 FStar_Pprint.op_Hat_Slash_Hat FStar_Pprint.minus uu____5988)
        | uu____5989 -> p_tmNoEqWith p_X e

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
              (lid,(e1,uu____6061)::(e2,uu____6063)::[]) when
              (FStar_Ident.lid_equals lid FStar_Parser_Const.cons_lid) &&
                (let uu____6083 = is_list e  in Prims.op_Negation uu____6083)
              ->
              let op = "::"  in
              let uu____6085 = levels op  in
              (match uu____6085 with
               | (left1,mine,right1) ->
                   let uu____6095 =
                     let uu____6096 = str op  in
                     let uu____6097 = p_tmNoEqWith' false p_X left1 e1  in
                     let uu____6098 = p_tmNoEqWith' false p_X right1 e2  in
                     infix0 uu____6096 uu____6097 uu____6098  in
                   paren_if_gt curr mine uu____6095)
          | FStar_Parser_AST.Sum (binders,res) ->
              let op = "&"  in
              let uu____6106 = levels op  in
              (match uu____6106 with
               | (left1,mine,right1) ->
                   let p_dsumfst b =
                     let uu____6120 = p_binder false b  in
                     let uu____6121 =
                       let uu____6122 =
                         let uu____6123 = str op  in
                         FStar_Pprint.op_Hat_Hat uu____6123 break1  in
                       FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____6122
                        in
                     FStar_Pprint.op_Hat_Hat uu____6120 uu____6121  in
                   let uu____6124 =
                     let uu____6125 =
                       FStar_Pprint.concat_map p_dsumfst binders  in
                     let uu____6126 = p_tmNoEqWith' false p_X right1 res  in
                     FStar_Pprint.op_Hat_Hat uu____6125 uu____6126  in
                   paren_if_gt curr mine uu____6124)
          | FStar_Parser_AST.Op
              ({ FStar_Ident.idText = "*";
                 FStar_Ident.idRange = uu____6127;_},e1::e2::[])
              ->
              let op = "*"  in
              let uu____6133 = levels op  in
              (match uu____6133 with
               | (left1,mine,right1) ->
                   if inside_tuple
                   then
                     let uu____6143 = str op  in
                     let uu____6144 = p_tmNoEqWith' true p_X left1 e1  in
                     let uu____6145 = p_tmNoEqWith' true p_X right1 e2  in
                     infix0 uu____6143 uu____6144 uu____6145
                   else
                     (let uu____6146 =
                        let uu____6147 = str op  in
                        let uu____6148 = p_tmNoEqWith' true p_X left1 e1  in
                        let uu____6149 = p_tmNoEqWith' true p_X right1 e2  in
                        infix0 uu____6147 uu____6148 uu____6149  in
                      paren_if_gt curr mine uu____6146))
          | FStar_Parser_AST.Op (op,e1::e2::[]) when is_operatorInfix34 op ->
              let op1 = FStar_Ident.text_of_id op  in
              let uu____6156 = levels op1  in
              (match uu____6156 with
               | (left1,mine,right1) ->
                   let uu____6166 =
                     let uu____6167 = str op1  in
                     let uu____6168 = p_tmNoEqWith' false p_X left1 e1  in
                     let uu____6169 = p_tmNoEqWith' false p_X right1 e2  in
                     infix0 uu____6167 uu____6168 uu____6169  in
                   paren_if_gt curr mine uu____6166)
          | FStar_Parser_AST.Record (with_opt,record_fields) ->
              let uu____6188 =
                let uu____6189 =
                  default_or_map FStar_Pprint.empty p_with_clause with_opt
                   in
                let uu____6190 =
                  let uu____6191 =
                    FStar_Pprint.op_Hat_Hat FStar_Pprint.semi break1  in
                  separate_map_last uu____6191 p_simpleDef record_fields  in
                FStar_Pprint.op_Hat_Hat uu____6189 uu____6190  in
              braces_with_nesting uu____6188
          | FStar_Parser_AST.Op
              ({ FStar_Ident.idText = "~";
                 FStar_Ident.idRange = uu____6196;_},e1::[])
              ->
              let uu____6200 =
                let uu____6201 = str "~"  in
                let uu____6202 = p_atomicTerm e1  in
                FStar_Pprint.op_Hat_Hat uu____6201 uu____6202  in
              FStar_Pprint.group uu____6200
          | FStar_Parser_AST.Paren p when inside_tuple ->
              (match p.FStar_Parser_AST.tm with
               | FStar_Parser_AST.Op
                   ({ FStar_Ident.idText = "*";
                      FStar_Ident.idRange = uu____6204;_},e1::e2::[])
                   ->
                   let op = "*"  in
                   let uu____6210 = levels op  in
                   (match uu____6210 with
                    | (left1,mine,right1) ->
                        let uu____6220 =
                          let uu____6221 = str op  in
                          let uu____6222 = p_tmNoEqWith' true p_X left1 e1
                             in
                          let uu____6223 = p_tmNoEqWith' true p_X right1 e2
                             in
                          infix0 uu____6221 uu____6222 uu____6223  in
                        paren_if_gt curr mine uu____6220)
               | uu____6224 -> p_X e)
          | uu____6225 -> p_X e

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
        let uu____6232 =
          let uu____6233 = p_lident lid  in
          let uu____6234 =
            let uu____6235 = p_appTerm e1  in
            FStar_Pprint.op_Hat_Slash_Hat FStar_Pprint.colon uu____6235  in
          FStar_Pprint.op_Hat_Slash_Hat uu____6233 uu____6234  in
        FStar_Pprint.group uu____6232
    | FStar_Parser_AST.Refine (b,phi) -> p_refinedBinder b phi
    | uu____6238 -> p_appTerm e

and (p_with_clause : FStar_Parser_AST.term -> FStar_Pprint.document) =
  fun e  ->
    let uu____6240 = p_appTerm e  in
    let uu____6241 =
      let uu____6242 =
        let uu____6243 = str "with"  in
        FStar_Pprint.op_Hat_Hat uu____6243 break1  in
      FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____6242  in
    FStar_Pprint.op_Hat_Hat uu____6240 uu____6241

and (p_refinedBinder :
  FStar_Parser_AST.binder -> FStar_Parser_AST.term -> FStar_Pprint.document)
  =
  fun b  ->
    fun phi  ->
      match b.FStar_Parser_AST.b with
      | FStar_Parser_AST.Annotated (lid,t) ->
          let uu____6248 = p_lident lid  in
          p_refinement b.FStar_Parser_AST.aqual uu____6248 t phi
      | FStar_Parser_AST.TAnnotated uu____6249 ->
          failwith "Is this still used ?"
      | FStar_Parser_AST.Variable uu____6254 ->
          let uu____6255 =
            let uu____6256 = FStar_Parser_AST.binder_to_string b  in
            FStar_Util.format1
              "Imposible : a refined binder ought to be annotated %s"
              uu____6256
             in
          failwith uu____6255
      | FStar_Parser_AST.TVariable uu____6257 ->
          let uu____6258 =
            let uu____6259 = FStar_Parser_AST.binder_to_string b  in
            FStar_Util.format1
              "Imposible : a refined binder ought to be annotated %s"
              uu____6259
             in
          failwith uu____6258
      | FStar_Parser_AST.NoName uu____6260 ->
          let uu____6261 =
            let uu____6262 = FStar_Parser_AST.binder_to_string b  in
            FStar_Util.format1
              "Imposible : a refined binder ought to be annotated %s"
              uu____6262
             in
          failwith uu____6261

and (p_simpleDef :
  Prims.bool ->
    (FStar_Ident.lid,FStar_Parser_AST.term) FStar_Pervasives_Native.tuple2 ->
      FStar_Pprint.document)
  =
  fun ps  ->
    fun uu____6264  ->
      match uu____6264 with
      | (lid,e) ->
          let uu____6271 =
            let uu____6272 = p_qlident lid  in
            let uu____6273 =
              let uu____6274 = p_noSeqTerm ps false e  in
              FStar_Pprint.op_Hat_Slash_Hat FStar_Pprint.equals uu____6274
               in
            FStar_Pprint.op_Hat_Slash_Hat uu____6272 uu____6273  in
          FStar_Pprint.group uu____6271

and (p_appTerm : FStar_Parser_AST.term -> FStar_Pprint.document) =
  fun e  ->
    match e.FStar_Parser_AST.tm with
    | FStar_Parser_AST.App uu____6276 when is_general_application e ->
        let uu____6283 = head_and_args e  in
        (match uu____6283 with
         | (head1,args) ->
             let uu____6308 =
               let uu____6319 = FStar_ST.op_Bang should_print_fs_typ_app  in
               if uu____6319
               then
                 let uu____6349 =
                   FStar_Util.take
                     (fun uu____6373  ->
                        match uu____6373 with
                        | (uu____6378,aq) -> aq = FStar_Parser_AST.FsTypApp)
                     args
                    in
                 match uu____6349 with
                 | (fs_typ_args,args1) ->
                     let uu____6416 =
                       let uu____6417 = p_indexingTerm head1  in
                       let uu____6418 =
                         let uu____6419 =
                           FStar_Pprint.op_Hat_Hat FStar_Pprint.comma break1
                            in
                         soft_surround_map_or_flow (Prims.parse_int "2")
                           (Prims.parse_int "0") FStar_Pprint.empty
                           FStar_Pprint.langle uu____6419 FStar_Pprint.rangle
                           p_fsTypArg fs_typ_args
                          in
                       FStar_Pprint.op_Hat_Hat uu____6417 uu____6418  in
                     (uu____6416, args1)
               else
                 (let uu____6431 = p_indexingTerm head1  in
                  (uu____6431, args))
                in
             (match uu____6308 with
              | (head_doc,args1) ->
                  let uu____6452 =
                    let uu____6453 =
                      FStar_Pprint.op_Hat_Hat head_doc FStar_Pprint.space  in
                    soft_surround_map_or_flow (Prims.parse_int "2")
                      (Prims.parse_int "0") head_doc uu____6453 break1
                      FStar_Pprint.empty p_argTerm args1
                     in
                  FStar_Pprint.group uu____6452))
    | FStar_Parser_AST.Construct (lid,args) when
        (is_general_construction e) &&
          (let uu____6473 = is_dtuple_constructor lid  in
           Prims.op_Negation uu____6473)
        ->
        (match args with
         | [] -> p_quident lid
         | arg::[] ->
             let uu____6491 =
               let uu____6492 = p_quident lid  in
               let uu____6493 = p_argTerm arg  in
               FStar_Pprint.op_Hat_Slash_Hat uu____6492 uu____6493  in
             FStar_Pprint.group uu____6491
         | hd1::tl1 ->
             let uu____6510 =
               let uu____6511 =
                 let uu____6512 =
                   let uu____6513 = p_quident lid  in
                   let uu____6514 = p_argTerm hd1  in
                   prefix2 uu____6513 uu____6514  in
                 FStar_Pprint.group uu____6512  in
               let uu____6515 =
                 let uu____6516 =
                   FStar_Pprint.separate_map break1 p_argTerm tl1  in
                 jump2 uu____6516  in
               FStar_Pprint.op_Hat_Hat uu____6511 uu____6515  in
             FStar_Pprint.group uu____6510)
    | uu____6521 -> p_indexingTerm e

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
         (let uu____6530 = p_indexingTerm e  in
          FStar_Pprint.surround (Prims.parse_int "2") (Prims.parse_int "1")
            FStar_Pprint.langle uu____6530 FStar_Pprint.rangle))
    | (e,FStar_Parser_AST.Hash ) ->
        let uu____6532 = str "#"  in
        let uu____6533 = p_indexingTerm e  in
        FStar_Pprint.op_Hat_Hat uu____6532 uu____6533
    | (e,FStar_Parser_AST.Nothing ) -> p_indexingTerm e

and (p_fsTypArg :
  (FStar_Parser_AST.term,FStar_Parser_AST.imp) FStar_Pervasives_Native.tuple2
    -> FStar_Pprint.document)
  =
  fun uu____6535  ->
    match uu____6535 with | (e,uu____6541) -> p_indexingTerm e

and (p_indexingTerm_aux :
  (FStar_Parser_AST.term -> FStar_Pprint.document) ->
    FStar_Parser_AST.term -> FStar_Pprint.document)
  =
  fun exit1  ->
    fun e  ->
      match e.FStar_Parser_AST.tm with
      | FStar_Parser_AST.Op
          ({ FStar_Ident.idText = ".()"; FStar_Ident.idRange = uu____6546;_},e1::e2::[])
          ->
          let uu____6551 =
            let uu____6552 = p_indexingTerm_aux p_atomicTermNotQUident e1  in
            let uu____6553 =
              let uu____6554 =
                let uu____6555 = p_term false false e2  in
                soft_parens_with_nesting uu____6555  in
              FStar_Pprint.op_Hat_Hat FStar_Pprint.dot uu____6554  in
            FStar_Pprint.op_Hat_Hat uu____6552 uu____6553  in
          FStar_Pprint.group uu____6551
      | FStar_Parser_AST.Op
          ({ FStar_Ident.idText = ".[]"; FStar_Ident.idRange = uu____6556;_},e1::e2::[])
          ->
          let uu____6561 =
            let uu____6562 = p_indexingTerm_aux p_atomicTermNotQUident e1  in
            let uu____6563 =
              let uu____6564 =
                let uu____6565 = p_term false false e2  in
                soft_brackets_with_nesting uu____6565  in
              FStar_Pprint.op_Hat_Hat FStar_Pprint.dot uu____6564  in
            FStar_Pprint.op_Hat_Hat uu____6562 uu____6563  in
          FStar_Pprint.group uu____6561
      | uu____6566 -> exit1 e

and (p_indexingTerm : FStar_Parser_AST.term -> FStar_Pprint.document) =
  fun e  -> p_indexingTerm_aux p_atomicTerm e

and (p_atomicTerm : FStar_Parser_AST.term -> FStar_Pprint.document) =
  fun e  ->
    match e.FStar_Parser_AST.tm with
    | FStar_Parser_AST.LetOpen (lid,e1) ->
        let uu____6571 = p_quident lid  in
        let uu____6572 =
          let uu____6573 =
            let uu____6574 = p_term false false e1  in
            soft_parens_with_nesting uu____6574  in
          FStar_Pprint.op_Hat_Hat FStar_Pprint.dot uu____6573  in
        FStar_Pprint.op_Hat_Hat uu____6571 uu____6572
    | FStar_Parser_AST.Name lid -> p_quident lid
    | FStar_Parser_AST.Op (op,e1::[]) when is_general_prefix_op op ->
        let uu____6580 =
          let uu____6581 = FStar_Ident.text_of_id op  in str uu____6581  in
        let uu____6582 = p_atomicTerm e1  in
        FStar_Pprint.op_Hat_Hat uu____6580 uu____6582
    | uu____6583 -> p_atomicTermNotQUident e

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
         | uu____6590 -> p_constant c)
    | FStar_Parser_AST.Name lid when
        FStar_Ident.lid_equals lid FStar_Parser_Const.true_lid -> str "True"
    | FStar_Parser_AST.Name lid when
        FStar_Ident.lid_equals lid FStar_Parser_Const.false_lid ->
        str "False"
    | FStar_Parser_AST.Op (op,e1::[]) when is_general_prefix_op op ->
        let uu____6597 =
          let uu____6598 = FStar_Ident.text_of_id op  in str uu____6598  in
        let uu____6599 = p_atomicTermNotQUident e1  in
        FStar_Pprint.op_Hat_Hat uu____6597 uu____6599
    | FStar_Parser_AST.Op (op,[]) ->
        let uu____6603 =
          let uu____6604 =
            let uu____6605 =
              let uu____6606 = FStar_Ident.text_of_id op  in str uu____6606
               in
            let uu____6607 =
              FStar_Pprint.op_Hat_Hat FStar_Pprint.space FStar_Pprint.rparen
               in
            FStar_Pprint.op_Hat_Hat uu____6605 uu____6607  in
          FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____6604  in
        FStar_Pprint.op_Hat_Hat FStar_Pprint.lparen uu____6603
    | FStar_Parser_AST.Construct (lid,args) when is_dtuple_constructor lid ->
        let uu____6622 =
          FStar_Pprint.op_Hat_Hat FStar_Pprint.lparen FStar_Pprint.bar  in
        let uu____6623 =
          let uu____6624 = FStar_Pprint.op_Hat_Hat FStar_Pprint.comma break1
             in
          let uu____6625 = FStar_List.map FStar_Pervasives_Native.fst args
             in
          FStar_Pprint.separate_map uu____6624 p_tmEq uu____6625  in
        let uu____6632 =
          FStar_Pprint.op_Hat_Hat FStar_Pprint.bar FStar_Pprint.rparen  in
        FStar_Pprint.surround (Prims.parse_int "2") (Prims.parse_int "1")
          uu____6622 uu____6623 uu____6632
    | FStar_Parser_AST.Project (e1,lid) ->
        let uu____6635 =
          let uu____6636 = p_atomicTermNotQUident e1  in
          let uu____6637 =
            let uu____6638 = p_qlident lid  in
            FStar_Pprint.op_Hat_Hat FStar_Pprint.dot uu____6638  in
          FStar_Pprint.prefix (Prims.parse_int "2") (Prims.parse_int "0")
            uu____6636 uu____6637
           in
        FStar_Pprint.group uu____6635
    | uu____6639 -> p_projectionLHS e

and (p_projectionLHS : FStar_Parser_AST.term -> FStar_Pprint.document) =
  fun e  ->
    match e.FStar_Parser_AST.tm with
    | FStar_Parser_AST.Var lid -> p_qlident lid
    | FStar_Parser_AST.Projector (constr_lid,field_lid) ->
        let uu____6644 = p_quident constr_lid  in
        let uu____6645 =
          let uu____6646 =
            let uu____6647 = p_lident field_lid  in
            FStar_Pprint.op_Hat_Hat FStar_Pprint.dot uu____6647  in
          FStar_Pprint.op_Hat_Hat FStar_Pprint.qmark uu____6646  in
        FStar_Pprint.op_Hat_Hat uu____6644 uu____6645
    | FStar_Parser_AST.Discrim constr_lid ->
        let uu____6649 = p_quident constr_lid  in
        FStar_Pprint.op_Hat_Hat uu____6649 FStar_Pprint.qmark
    | FStar_Parser_AST.Paren e1 ->
        let uu____6651 = p_term false false e1  in
        soft_parens_with_nesting uu____6651
    | uu____6652 when is_array e ->
        let es = extract_from_list e  in
        let uu____6656 =
          FStar_Pprint.op_Hat_Hat FStar_Pprint.lbracket FStar_Pprint.bar  in
        let uu____6657 =
          let uu____6658 = FStar_Pprint.op_Hat_Hat FStar_Pprint.semi break1
             in
          separate_map_or_flow_last uu____6658
            (fun ps  -> p_noSeqTerm ps false) es
           in
        let uu____6661 =
          FStar_Pprint.op_Hat_Hat FStar_Pprint.bar FStar_Pprint.rbracket  in
        FStar_Pprint.surround (Prims.parse_int "2") (Prims.parse_int "0")
          uu____6656 uu____6657 uu____6661
    | uu____6662 when is_list e ->
        let uu____6663 =
          let uu____6664 = FStar_Pprint.op_Hat_Hat FStar_Pprint.semi break1
             in
          let uu____6665 = extract_from_list e  in
          separate_map_or_flow_last uu____6664
            (fun ps  -> p_noSeqTerm ps false) uu____6665
           in
        FStar_Pprint.surround (Prims.parse_int "2") (Prims.parse_int "0")
          FStar_Pprint.lbracket uu____6663 FStar_Pprint.rbracket
    | uu____6670 when is_lex_list e ->
        let uu____6671 =
          FStar_Pprint.op_Hat_Hat FStar_Pprint.percent FStar_Pprint.lbracket
           in
        let uu____6672 =
          let uu____6673 = FStar_Pprint.op_Hat_Hat FStar_Pprint.semi break1
             in
          let uu____6674 = extract_from_list e  in
          separate_map_or_flow_last uu____6673
            (fun ps  -> p_noSeqTerm ps false) uu____6674
           in
        FStar_Pprint.surround (Prims.parse_int "2") (Prims.parse_int "1")
          uu____6671 uu____6672 FStar_Pprint.rbracket
    | uu____6679 when is_ref_set e ->
        let es = extract_from_ref_set e  in
        let uu____6683 =
          FStar_Pprint.op_Hat_Hat FStar_Pprint.bang FStar_Pprint.lbrace  in
        let uu____6684 =
          let uu____6685 = FStar_Pprint.op_Hat_Hat FStar_Pprint.comma break1
             in
          separate_map_or_flow uu____6685 p_appTerm es  in
        FStar_Pprint.surround (Prims.parse_int "2") (Prims.parse_int "0")
          uu____6683 uu____6684 FStar_Pprint.rbrace
    | FStar_Parser_AST.Labeled (e1,s,b) ->
        let uu____6689 = str (Prims.strcat "(*" (Prims.strcat s "*)"))  in
        let uu____6690 = p_term false false e1  in
        FStar_Pprint.op_Hat_Slash_Hat uu____6689 uu____6690
    | FStar_Parser_AST.Op (op,args) when
        let uu____6697 = handleable_op op args  in
        Prims.op_Negation uu____6697 ->
        let uu____6698 =
          let uu____6699 =
            let uu____6700 = FStar_Ident.text_of_id op  in
            let uu____6701 =
              let uu____6702 =
                let uu____6703 =
                  FStar_Util.string_of_int (FStar_List.length args)  in
                Prims.strcat uu____6703
                  " arguments couldn't be handled by the pretty printer"
                 in
              Prims.strcat " with " uu____6702  in
            Prims.strcat uu____6700 uu____6701  in
          Prims.strcat "Operation " uu____6699  in
        failwith uu____6698
    | FStar_Parser_AST.Uvar uu____6704 ->
        failwith "Unexpected universe variable out of universe context"
    | FStar_Parser_AST.Wild  ->
        let uu____6705 = p_term false false e  in
        soft_parens_with_nesting uu____6705
    | FStar_Parser_AST.Const uu____6706 ->
        let uu____6707 = p_term false false e  in
        soft_parens_with_nesting uu____6707
    | FStar_Parser_AST.Op uu____6708 ->
        let uu____6715 = p_term false false e  in
        soft_parens_with_nesting uu____6715
    | FStar_Parser_AST.Tvar uu____6716 ->
        let uu____6717 = p_term false false e  in
        soft_parens_with_nesting uu____6717
    | FStar_Parser_AST.Var uu____6718 ->
        let uu____6719 = p_term false false e  in
        soft_parens_with_nesting uu____6719
    | FStar_Parser_AST.Name uu____6720 ->
        let uu____6721 = p_term false false e  in
        soft_parens_with_nesting uu____6721
    | FStar_Parser_AST.Construct uu____6722 ->
        let uu____6733 = p_term false false e  in
        soft_parens_with_nesting uu____6733
    | FStar_Parser_AST.Abs uu____6734 ->
        let uu____6741 = p_term false false e  in
        soft_parens_with_nesting uu____6741
    | FStar_Parser_AST.App uu____6742 ->
        let uu____6749 = p_term false false e  in
        soft_parens_with_nesting uu____6749
    | FStar_Parser_AST.Let uu____6750 ->
        let uu____6771 = p_term false false e  in
        soft_parens_with_nesting uu____6771
    | FStar_Parser_AST.LetOpen uu____6772 ->
        let uu____6777 = p_term false false e  in
        soft_parens_with_nesting uu____6777
    | FStar_Parser_AST.Seq uu____6778 ->
        let uu____6783 = p_term false false e  in
        soft_parens_with_nesting uu____6783
    | FStar_Parser_AST.Bind uu____6784 ->
        let uu____6791 = p_term false false e  in
        soft_parens_with_nesting uu____6791
    | FStar_Parser_AST.If uu____6792 ->
        let uu____6799 = p_term false false e  in
        soft_parens_with_nesting uu____6799
    | FStar_Parser_AST.Match uu____6800 ->
        let uu____6815 = p_term false false e  in
        soft_parens_with_nesting uu____6815
    | FStar_Parser_AST.TryWith uu____6816 ->
        let uu____6831 = p_term false false e  in
        soft_parens_with_nesting uu____6831
    | FStar_Parser_AST.Ascribed uu____6832 ->
        let uu____6841 = p_term false false e  in
        soft_parens_with_nesting uu____6841
    | FStar_Parser_AST.Record uu____6842 ->
        let uu____6855 = p_term false false e  in
        soft_parens_with_nesting uu____6855
    | FStar_Parser_AST.Project uu____6856 ->
        let uu____6861 = p_term false false e  in
        soft_parens_with_nesting uu____6861
    | FStar_Parser_AST.Product uu____6862 ->
        let uu____6869 = p_term false false e  in
        soft_parens_with_nesting uu____6869
    | FStar_Parser_AST.Sum uu____6870 ->
        let uu____6877 = p_term false false e  in
        soft_parens_with_nesting uu____6877
    | FStar_Parser_AST.QForall uu____6878 ->
        let uu____6891 = p_term false false e  in
        soft_parens_with_nesting uu____6891
    | FStar_Parser_AST.QExists uu____6892 ->
        let uu____6905 = p_term false false e  in
        soft_parens_with_nesting uu____6905
    | FStar_Parser_AST.Refine uu____6906 ->
        let uu____6911 = p_term false false e  in
        soft_parens_with_nesting uu____6911
    | FStar_Parser_AST.NamedTyp uu____6912 ->
        let uu____6917 = p_term false false e  in
        soft_parens_with_nesting uu____6917
    | FStar_Parser_AST.Requires uu____6918 ->
        let uu____6925 = p_term false false e  in
        soft_parens_with_nesting uu____6925
    | FStar_Parser_AST.Ensures uu____6926 ->
        let uu____6933 = p_term false false e  in
        soft_parens_with_nesting uu____6933
    | FStar_Parser_AST.Attributes uu____6934 ->
        let uu____6937 = p_term false false e  in
        soft_parens_with_nesting uu____6937
    | FStar_Parser_AST.Quote uu____6938 ->
        let uu____6943 = p_term false false e  in
        soft_parens_with_nesting uu____6943
    | FStar_Parser_AST.VQuote uu____6944 ->
        let uu____6945 = p_term false false e  in
        soft_parens_with_nesting uu____6945
    | FStar_Parser_AST.Antiquote uu____6946 ->
        let uu____6951 = p_term false false e  in
        soft_parens_with_nesting uu____6951

and (p_constant : FStar_Const.sconst -> FStar_Pprint.document) =
  fun uu___67_6952  ->
    match uu___67_6952 with
    | FStar_Const.Const_effect  -> str "Effect"
    | FStar_Const.Const_unit  -> str "()"
    | FStar_Const.Const_bool b -> FStar_Pprint.doc_of_bool b
    | FStar_Const.Const_float x -> str (FStar_Util.string_of_float x)
    | FStar_Const.Const_char x -> FStar_Pprint.doc_of_char x
    | FStar_Const.Const_string (s,uu____6957) ->
        let uu____6958 = str s  in FStar_Pprint.dquotes uu____6958
    | FStar_Const.Const_bytearray (bytes,uu____6960) ->
        let uu____6965 =
          let uu____6966 = str (FStar_Util.string_of_bytes bytes)  in
          FStar_Pprint.dquotes uu____6966  in
        let uu____6967 = str "B"  in
        FStar_Pprint.op_Hat_Hat uu____6965 uu____6967
    | FStar_Const.Const_int (repr,sign_width_opt) ->
        let signedness uu___65_6985 =
          match uu___65_6985 with
          | FStar_Const.Unsigned  -> str "u"
          | FStar_Const.Signed  -> FStar_Pprint.empty  in
        let width uu___66_6989 =
          match uu___66_6989 with
          | FStar_Const.Int8  -> str "y"
          | FStar_Const.Int16  -> str "s"
          | FStar_Const.Int32  -> str "l"
          | FStar_Const.Int64  -> str "L"  in
        let ending =
          default_or_map FStar_Pprint.empty
            (fun uu____7000  ->
               match uu____7000 with
               | (s,w) ->
                   let uu____7007 = signedness s  in
                   let uu____7008 = width w  in
                   FStar_Pprint.op_Hat_Hat uu____7007 uu____7008)
            sign_width_opt
           in
        let uu____7009 = str repr  in
        FStar_Pprint.op_Hat_Hat uu____7009 ending
    | FStar_Const.Const_range_of  -> str "range_of"
    | FStar_Const.Const_set_range_of  -> str "set_range_of"
    | FStar_Const.Const_range r ->
        let uu____7011 = FStar_Range.string_of_range r  in str uu____7011
    | FStar_Const.Const_reify  -> str "reify"
    | FStar_Const.Const_reflect lid ->
        let uu____7013 = p_quident lid  in
        let uu____7014 =
          let uu____7015 =
            let uu____7016 = str "reflect"  in
            FStar_Pprint.op_Hat_Hat FStar_Pprint.dot uu____7016  in
          FStar_Pprint.op_Hat_Hat FStar_Pprint.qmark uu____7015  in
        FStar_Pprint.op_Hat_Hat uu____7013 uu____7014

and (p_universe : FStar_Parser_AST.term -> FStar_Pprint.document) =
  fun u  ->
    let uu____7018 = str "u#"  in
    let uu____7019 = p_atomicUniverse u  in
    FStar_Pprint.op_Hat_Hat uu____7018 uu____7019

and (p_universeFrom : FStar_Parser_AST.term -> FStar_Pprint.document) =
  fun u  ->
    match u.FStar_Parser_AST.tm with
    | FStar_Parser_AST.Op
        ({ FStar_Ident.idText = "+"; FStar_Ident.idRange = uu____7021;_},u1::u2::[])
        ->
        let uu____7026 =
          let uu____7027 = p_universeFrom u1  in
          let uu____7028 =
            let uu____7029 = p_universeFrom u2  in
            FStar_Pprint.op_Hat_Slash_Hat FStar_Pprint.plus uu____7029  in
          FStar_Pprint.op_Hat_Slash_Hat uu____7027 uu____7028  in
        FStar_Pprint.group uu____7026
    | FStar_Parser_AST.App uu____7030 ->
        let uu____7037 = head_and_args u  in
        (match uu____7037 with
         | (head1,args) ->
             (match head1.FStar_Parser_AST.tm with
              | FStar_Parser_AST.Var maybe_max_lid when
                  FStar_Ident.lid_equals maybe_max_lid
                    FStar_Parser_Const.max_lid
                  ->
                  let uu____7063 =
                    let uu____7064 = p_qlident FStar_Parser_Const.max_lid  in
                    let uu____7065 =
                      FStar_Pprint.separate_map FStar_Pprint.space
                        (fun uu____7073  ->
                           match uu____7073 with
                           | (u1,uu____7079) -> p_atomicUniverse u1) args
                       in
                    op_Hat_Slash_Plus_Hat uu____7064 uu____7065  in
                  FStar_Pprint.group uu____7063
              | uu____7080 ->
                  let uu____7081 =
                    let uu____7082 = FStar_Parser_AST.term_to_string u  in
                    FStar_Util.format1 "Invalid term in universe context %s"
                      uu____7082
                     in
                  failwith uu____7081))
    | uu____7083 -> p_atomicUniverse u

and (p_atomicUniverse : FStar_Parser_AST.term -> FStar_Pprint.document) =
  fun u  ->
    match u.FStar_Parser_AST.tm with
    | FStar_Parser_AST.Wild  -> FStar_Pprint.underscore
    | FStar_Parser_AST.Const (FStar_Const.Const_int (r,sw)) ->
        p_constant (FStar_Const.Const_int (r, sw))
    | FStar_Parser_AST.Uvar id1 ->
        let uu____7106 = FStar_Ident.text_of_id id1  in str uu____7106
    | FStar_Parser_AST.Paren u1 ->
        let uu____7108 = p_universeFrom u1  in
        soft_parens_with_nesting uu____7108
    | FStar_Parser_AST.Op
        ({ FStar_Ident.idText = "+"; FStar_Ident.idRange = uu____7109;_},uu____7110::uu____7111::[])
        ->
        let uu____7114 = p_universeFrom u  in
        soft_parens_with_nesting uu____7114
    | FStar_Parser_AST.App uu____7115 ->
        let uu____7122 = p_universeFrom u  in
        soft_parens_with_nesting uu____7122
    | uu____7123 ->
        let uu____7124 =
          let uu____7125 = FStar_Parser_AST.term_to_string u  in
          FStar_Util.format1 "Invalid term in universe context %s" uu____7125
           in
        failwith uu____7124

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
       | FStar_Parser_AST.Module (uu____7165,decls) ->
           let uu____7171 =
             FStar_All.pipe_right decls (FStar_List.map decl_to_document)  in
           FStar_All.pipe_right uu____7171
             (FStar_Pprint.separate FStar_Pprint.hardline)
       | FStar_Parser_AST.Interface (uu____7180,decls,uu____7182) ->
           let uu____7187 =
             FStar_All.pipe_right decls (FStar_List.map decl_to_document)  in
           FStar_All.pipe_right uu____7187
             (FStar_Pprint.separate FStar_Pprint.hardline)
        in
     FStar_ST.op_Colon_Equals should_print_fs_typ_app false; res)
  
let (comments_to_document :
  (Prims.string,FStar_Range.range) FStar_Pervasives_Native.tuple2 Prims.list
    -> FStar_Pprint.document)
  =
  fun comments  ->
    FStar_Pprint.separate_map FStar_Pprint.hardline
      (fun uu____7238  ->
         match uu____7238 with | (comment,range) -> str comment) comments
  
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
        | FStar_Parser_AST.Module (uu____7278,decls) -> decls
        | FStar_Parser_AST.Interface (uu____7284,decls,uu____7286) -> decls
         in
      FStar_ST.op_Colon_Equals should_print_fs_typ_app false;
      (match decls with
       | [] -> (FStar_Pprint.empty, comments)
       | d::ds ->
           let uu____7331 =
             match ds with
             | {
                 FStar_Parser_AST.d = FStar_Parser_AST.Pragma
                   (FStar_Parser_AST.LightOff );
                 FStar_Parser_AST.drange = uu____7344;
                 FStar_Parser_AST.doc = uu____7345;
                 FStar_Parser_AST.quals = uu____7346;
                 FStar_Parser_AST.attrs = uu____7347;_}::uu____7348 ->
                 let d0 = FStar_List.hd ds  in
                 let uu____7354 =
                   let uu____7357 =
                     let uu____7360 = FStar_List.tl ds  in d :: uu____7360
                      in
                   d0 :: uu____7357  in
                 (uu____7354, (d0.FStar_Parser_AST.drange))
             | uu____7365 -> ((d :: ds), (d.FStar_Parser_AST.drange))  in
           (match uu____7331 with
            | (decls1,first_range) ->
                let extract_decl_range d1 = d1.FStar_Parser_AST.drange  in
                (FStar_ST.op_Colon_Equals comment_stack comments;
                 (let initial_comment =
                    let uu____7423 = FStar_Range.start_of_range first_range
                       in
                    place_comments_until_pos (Prims.parse_int "0")
                      (Prims.parse_int "1") uu____7423 FStar_Pprint.empty
                     in
                  let doc1 =
                    separate_map_with_comments FStar_Pprint.empty
                      FStar_Pprint.empty decl_to_document decls1
                      extract_decl_range
                     in
                  let comments1 = FStar_ST.op_Bang comment_stack  in
                  FStar_ST.op_Colon_Equals comment_stack [];
                  FStar_ST.op_Colon_Equals should_print_fs_typ_app false;
                  (let uu____7519 =
                     FStar_Pprint.op_Hat_Hat initial_comment doc1  in
                   (uu____7519, comments1))))))
  