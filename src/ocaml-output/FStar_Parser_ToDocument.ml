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
          x.FStar_Ident.idText = (FStar_Ident.text_of_lid y)
      | uu____697 -> false
  
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
        | FStar_Parser_AST.Construct (lid,uu____726::(e2,uu____728)::[]) ->
            (FStar_Ident.lid_equals lid cons_lid1) && (aux e2)
        | uu____751 -> false  in
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
    | FStar_Parser_AST.Construct (uu____763,[]) -> []
    | FStar_Parser_AST.Construct
        (uu____774,(e1,FStar_Parser_AST.Nothing )::(e2,FStar_Parser_AST.Nothing
                                                    )::[])
        -> let uu____795 = extract_from_list e2  in e1 :: uu____795
    | uu____798 ->
        let uu____799 =
          let uu____800 = FStar_Parser_AST.term_to_string e  in
          FStar_Util.format1 "Not a list %s" uu____800  in
        failwith uu____799
  
let (is_array : FStar_Parser_AST.term -> Prims.bool) =
  fun e  ->
    match e.FStar_Parser_AST.tm with
    | FStar_Parser_AST.App
        ({ FStar_Parser_AST.tm = FStar_Parser_AST.Var lid;
           FStar_Parser_AST.range = uu____807;
           FStar_Parser_AST.level = uu____808;_},l,FStar_Parser_AST.Nothing
         )
        ->
        (FStar_Ident.lid_equals lid FStar_Parser_Const.array_mk_array_lid) &&
          (is_list l)
    | uu____810 -> false
  
let rec (is_ref_set : FStar_Parser_AST.term -> Prims.bool) =
  fun e  ->
    match e.FStar_Parser_AST.tm with
    | FStar_Parser_AST.Var maybe_empty_lid ->
        FStar_Ident.lid_equals maybe_empty_lid FStar_Parser_Const.set_empty
    | FStar_Parser_AST.App
        ({ FStar_Parser_AST.tm = FStar_Parser_AST.Var maybe_singleton_lid;
           FStar_Parser_AST.range = uu____816;
           FStar_Parser_AST.level = uu____817;_},{
                                                   FStar_Parser_AST.tm =
                                                     FStar_Parser_AST.App
                                                     ({
                                                        FStar_Parser_AST.tm =
                                                          FStar_Parser_AST.Var
                                                          maybe_addr_of_lid;
                                                        FStar_Parser_AST.range
                                                          = uu____819;
                                                        FStar_Parser_AST.level
                                                          = uu____820;_},e1,FStar_Parser_AST.Nothing
                                                      );
                                                   FStar_Parser_AST.range =
                                                     uu____822;
                                                   FStar_Parser_AST.level =
                                                     uu____823;_},FStar_Parser_AST.Nothing
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
                FStar_Parser_AST.range = uu____825;
                FStar_Parser_AST.level = uu____826;_},e1,FStar_Parser_AST.Nothing
              );
           FStar_Parser_AST.range = uu____828;
           FStar_Parser_AST.level = uu____829;_},e2,FStar_Parser_AST.Nothing
         )
        ->
        ((FStar_Ident.lid_equals maybe_union_lid FStar_Parser_Const.set_union)
           && (is_ref_set e1))
          && (is_ref_set e2)
    | uu____831 -> false
  
let rec (extract_from_ref_set :
  FStar_Parser_AST.term -> FStar_Parser_AST.term Prims.list) =
  fun e  ->
    match e.FStar_Parser_AST.tm with
    | FStar_Parser_AST.Var uu____839 -> []
    | FStar_Parser_AST.App
        ({ FStar_Parser_AST.tm = FStar_Parser_AST.Var uu____840;
           FStar_Parser_AST.range = uu____841;
           FStar_Parser_AST.level = uu____842;_},{
                                                   FStar_Parser_AST.tm =
                                                     FStar_Parser_AST.App
                                                     ({
                                                        FStar_Parser_AST.tm =
                                                          FStar_Parser_AST.Var
                                                          uu____843;
                                                        FStar_Parser_AST.range
                                                          = uu____844;
                                                        FStar_Parser_AST.level
                                                          = uu____845;_},e1,FStar_Parser_AST.Nothing
                                                      );
                                                   FStar_Parser_AST.range =
                                                     uu____847;
                                                   FStar_Parser_AST.level =
                                                     uu____848;_},FStar_Parser_AST.Nothing
         )
        -> [e1]
    | FStar_Parser_AST.App
        ({
           FStar_Parser_AST.tm = FStar_Parser_AST.App
             ({ FStar_Parser_AST.tm = FStar_Parser_AST.Var uu____849;
                FStar_Parser_AST.range = uu____850;
                FStar_Parser_AST.level = uu____851;_},e1,FStar_Parser_AST.Nothing
              );
           FStar_Parser_AST.range = uu____853;
           FStar_Parser_AST.level = uu____854;_},e2,FStar_Parser_AST.Nothing
         )
        ->
        let uu____856 = extract_from_ref_set e1  in
        let uu____859 = extract_from_ref_set e2  in
        FStar_List.append uu____856 uu____859
    | uu____862 ->
        let uu____863 =
          let uu____864 = FStar_Parser_AST.term_to_string e  in
          FStar_Util.format1 "Not a ref set %s" uu____864  in
        failwith uu____863
  
let (is_general_application : FStar_Parser_AST.term -> Prims.bool) =
  fun e  ->
    let uu____870 = (is_array e) || (is_ref_set e)  in
    Prims.op_Negation uu____870
  
let (is_general_construction : FStar_Parser_AST.term -> Prims.bool) =
  fun e  ->
    let uu____874 = (is_list e) || (is_lex_list e)  in
    Prims.op_Negation uu____874
  
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
      | uu____941 -> (e1, acc)  in
    aux e []
  
type associativity =
  | Left 
  | Right 
  | NonAssoc [@@deriving show]
let (uu___is_Left : associativity -> Prims.bool) =
  fun projectee  -> match projectee with | Left  -> true | uu____955 -> false 
let (uu___is_Right : associativity -> Prims.bool) =
  fun projectee  ->
    match projectee with | Right  -> true | uu____959 -> false
  
let (uu___is_NonAssoc : associativity -> Prims.bool) =
  fun projectee  ->
    match projectee with | NonAssoc  -> true | uu____963 -> false
  
type token = (FStar_Char.char,Prims.string) FStar_Util.either[@@deriving
                                                               show]
type associativity_level =
  (associativity,token Prims.list) FStar_Pervasives_Native.tuple2[@@deriving
                                                                   show]
let (token_to_string :
  (FStar_BaseTypes.char,Prims.string) FStar_Util.either -> Prims.string) =
  fun uu___50_981  ->
    match uu___50_981 with
    | FStar_Util.Inl c -> Prims.strcat (FStar_Util.string_of_char c) ".*"
    | FStar_Util.Inr s -> s
  
let (matches_token :
  Prims.string ->
    (FStar_Char.char,Prims.string) FStar_Util.either -> Prims.bool)
  =
  fun s  ->
    fun uu___51_998  ->
      match uu___51_998 with
      | FStar_Util.Inl c ->
          let uu____1007 = FStar_String.get s (Prims.parse_int "0")  in
          uu____1007 = c
      | FStar_Util.Inr s' -> s = s'
  
let matches_level :
  'Auu____1015 .
    Prims.string ->
      ('Auu____1015,(FStar_Char.char,Prims.string) FStar_Util.either
                      Prims.list)
        FStar_Pervasives_Native.tuple2 -> Prims.bool
  =
  fun s  ->
    fun uu____1034  ->
      match uu____1034 with
      | (assoc_levels,tokens) ->
          let uu____1062 = FStar_List.tryFind (matches_token s) tokens  in
          uu____1062 <> FStar_Pervasives_Native.None
  
let opinfix4 :
  'Auu____1088 .
    Prims.unit ->
      (associativity,('Auu____1088,Prims.string) FStar_Util.either Prims.list)
        FStar_Pervasives_Native.tuple2
  = fun uu____1099  -> (Right, [FStar_Util.Inr "**"]) 
let opinfix3 :
  'Auu____1115 .
    Prims.unit ->
      (associativity,(FStar_Char.char,'Auu____1115) FStar_Util.either
                       Prims.list)
        FStar_Pervasives_Native.tuple2
  =
  fun uu____1127  ->
    (Left, [FStar_Util.Inl 42; FStar_Util.Inl 47; FStar_Util.Inl 37])
  
let opinfix2 :
  'Auu____1162 .
    Prims.unit ->
      (associativity,(FStar_Char.char,'Auu____1162) FStar_Util.either
                       Prims.list)
        FStar_Pervasives_Native.tuple2
  = fun uu____1174  -> (Left, [FStar_Util.Inl 43; FStar_Util.Inl 45]) 
let minus_lvl :
  'Auu____1202 .
    Prims.unit ->
      (associativity,('Auu____1202,Prims.string) FStar_Util.either Prims.list)
        FStar_Pervasives_Native.tuple2
  = fun uu____1213  -> (Left, [FStar_Util.Inr "-"]) 
let opinfix1 :
  'Auu____1229 .
    Prims.unit ->
      (associativity,(FStar_Char.char,'Auu____1229) FStar_Util.either
                       Prims.list)
        FStar_Pervasives_Native.tuple2
  = fun uu____1241  -> (Right, [FStar_Util.Inl 64; FStar_Util.Inl 94]) 
let pipe_right :
  'Auu____1269 .
    Prims.unit ->
      (associativity,('Auu____1269,Prims.string) FStar_Util.either Prims.list)
        FStar_Pervasives_Native.tuple2
  = fun uu____1280  -> (Left, [FStar_Util.Inr "|>"]) 
let opinfix0d :
  'Auu____1296 .
    Prims.unit ->
      (associativity,(FStar_Char.char,'Auu____1296) FStar_Util.either
                       Prims.list)
        FStar_Pervasives_Native.tuple2
  = fun uu____1308  -> (Left, [FStar_Util.Inl 36]) 
let opinfix0c :
  'Auu____1329 .
    Prims.unit ->
      (associativity,(FStar_Char.char,'Auu____1329) FStar_Util.either
                       Prims.list)
        FStar_Pervasives_Native.tuple2
  =
  fun uu____1341  ->
    (Left, [FStar_Util.Inl 61; FStar_Util.Inl 60; FStar_Util.Inl 62])
  
let equal :
  'Auu____1376 .
    Prims.unit ->
      (associativity,('Auu____1376,Prims.string) FStar_Util.either Prims.list)
        FStar_Pervasives_Native.tuple2
  = fun uu____1387  -> (Left, [FStar_Util.Inr "="]) 
let opinfix0b :
  'Auu____1403 .
    Prims.unit ->
      (associativity,(FStar_Char.char,'Auu____1403) FStar_Util.either
                       Prims.list)
        FStar_Pervasives_Native.tuple2
  = fun uu____1415  -> (Left, [FStar_Util.Inl 38]) 
let opinfix0a :
  'Auu____1436 .
    Prims.unit ->
      (associativity,(FStar_Char.char,'Auu____1436) FStar_Util.either
                       Prims.list)
        FStar_Pervasives_Native.tuple2
  = fun uu____1448  -> (Left, [FStar_Util.Inl 124]) 
let colon_equals :
  'Auu____1469 .
    Prims.unit ->
      (associativity,('Auu____1469,Prims.string) FStar_Util.either Prims.list)
        FStar_Pervasives_Native.tuple2
  = fun uu____1480  -> (NonAssoc, [FStar_Util.Inr ":="]) 
let amp :
  'Auu____1496 .
    Prims.unit ->
      (associativity,('Auu____1496,Prims.string) FStar_Util.either Prims.list)
        FStar_Pervasives_Native.tuple2
  = fun uu____1507  -> (Right, [FStar_Util.Inr "&"]) 
let colon_colon :
  'Auu____1523 .
    Prims.unit ->
      (associativity,('Auu____1523,Prims.string) FStar_Util.either Prims.list)
        FStar_Pervasives_Native.tuple2
  = fun uu____1534  -> (Right, [FStar_Util.Inr "::"]) 
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
  let levels_from_associativity l uu___52_1741 =
    match uu___52_1741 with
    | Left  -> (l, l, (l - (Prims.parse_int "1")))
    | Right  -> ((l - (Prims.parse_int "1")), l, l)
    | NonAssoc  ->
        ((l - (Prims.parse_int "1")), l, (l - (Prims.parse_int "1")))
     in
  FStar_List.mapi
    (fun i  ->
       fun uu____1781  ->
         match uu____1781 with
         | (assoc1,tokens) -> ((levels_from_associativity i assoc1), tokens))
    level_associativity_spec
  
let (assign_levels :
  associativity_level Prims.list ->
    Prims.string ->
      (Prims.int,Prims.int,Prims.int) FStar_Pervasives_Native.tuple3)
  =
  fun token_associativity_spec  ->
    fun s  ->
      let uu____1861 = FStar_List.tryFind (matches_level s) level_table  in
      match uu____1861 with
      | FStar_Pervasives_Native.Some (assoc_levels,uu____1911) ->
          assoc_levels
      | uu____1955 -> failwith (Prims.strcat "Unrecognized operator " s)
  
let (max : Prims.int -> Prims.int -> Prims.int) =
  fun k1  -> fun k2  -> if k1 > k2 then k1 else k2 
let max_level :
  'Auu____1990 .
    ('Auu____1990,(FStar_Char.char,Prims.string) FStar_Util.either Prims.list)
      FStar_Pervasives_Native.tuple2 Prims.list -> Prims.int
  =
  fun l  ->
    let find_level_and_max n1 level =
      let uu____2050 =
        FStar_List.tryFind
          (fun uu____2090  ->
             match uu____2090 with
             | (uu____2108,tokens) ->
                 tokens = (FStar_Pervasives_Native.snd level)) level_table
         in
      match uu____2050 with
      | FStar_Pervasives_Native.Some ((uu____2150,l1,uu____2152),uu____2153)
          -> max n1 l1
      | FStar_Pervasives_Native.None  ->
          let uu____2208 =
            let uu____2209 =
              let uu____2210 =
                FStar_List.map token_to_string
                  (FStar_Pervasives_Native.snd level)
                 in
              FStar_String.concat "," uu____2210  in
            FStar_Util.format1 "Undefined associativity level %s" uu____2209
             in
          failwith uu____2208
       in
    FStar_List.fold_left find_level_and_max (Prims.parse_int "0") l
  
let (levels :
  Prims.string ->
    (Prims.int,Prims.int,Prims.int) FStar_Pervasives_Native.tuple3)
  =
  fun op  ->
    let uu____2244 = assign_levels level_associativity_spec op  in
    match uu____2244 with
    | (left1,mine,right1) ->
        if op = "*"
        then ((left1 - (Prims.parse_int "1")), mine, right1)
        else (left1, mine, right1)
  
let operatorInfix0ad12 :
  'Auu____2268 .
    Prims.unit ->
      (associativity,(FStar_Char.char,'Auu____2268) FStar_Util.either
                       Prims.list)
        FStar_Pervasives_Native.tuple2 Prims.list
  =
  fun uu____2282  ->
    [opinfix0a ();
    opinfix0b ();
    opinfix0c ();
    opinfix0d ();
    opinfix1 ();
    opinfix2 ()]
  
let (is_operatorInfix0ad12 : FStar_Ident.ident -> Prims.bool) =
  fun op  ->
    let uu____2363 =
      let uu____2377 =
        FStar_All.pipe_left matches_level (FStar_Ident.text_of_id op)  in
      FStar_List.tryFind uu____2377 (operatorInfix0ad12 ())  in
    uu____2363 <> FStar_Pervasives_Native.None
  
let (is_operatorInfix34 : FStar_Ident.ident -> Prims.bool) =
  let opinfix34 = [opinfix3 (); opinfix4 ()]  in
  fun op  ->
    let uu____2490 =
      let uu____2504 =
        FStar_All.pipe_left matches_level (FStar_Ident.text_of_id op)  in
      FStar_List.tryFind uu____2504 opinfix34  in
    uu____2490 <> FStar_Pervasives_Native.None
  
let (handleable_args_length : FStar_Ident.ident -> Prims.int) =
  fun op  ->
    let op_s = FStar_Ident.text_of_id op  in
    let uu____2570 =
      (is_general_prefix_op op) || (FStar_List.mem op_s ["-"; "~"])  in
    if uu____2570
    then (Prims.parse_int "1")
    else
      (let uu____2572 =
         ((is_operatorInfix0ad12 op) || (is_operatorInfix34 op)) ||
           (FStar_List.mem op_s
              ["<==>"; "==>"; "\\/"; "/\\"; "="; "|>"; ":="; ".()"; ".[]"])
          in
       if uu____2572
       then (Prims.parse_int "2")
       else
         if FStar_List.mem op_s [".()<-"; ".[]<-"]
         then (Prims.parse_int "3")
         else (Prims.parse_int "0"))
  
let handleable_op :
  'Auu____2578 . FStar_Ident.ident -> 'Auu____2578 Prims.list -> Prims.bool =
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
      | uu____2591 -> false
  
let (comment_stack :
  (Prims.string,FStar_Range.range) FStar_Pervasives_Native.tuple2 Prims.list
    FStar_ST.ref)
  = FStar_Util.mk_ref [] 
let with_comment :
  'Auu____2625 .
    ('Auu____2625 -> FStar_Pprint.document) ->
      'Auu____2625 -> FStar_Range.range -> FStar_Pprint.document
  =
  fun printer  ->
    fun tm  ->
      fun tmrange  ->
        let rec comments_before_pos acc print_pos lookahead_pos =
          let uu____2657 = FStar_ST.op_Bang comment_stack  in
          match uu____2657 with
          | [] -> (acc, false)
          | (comment,crange)::cs ->
              let uu____2716 = FStar_Range.range_before_pos crange print_pos
                 in
              if uu____2716
              then
                (FStar_ST.op_Colon_Equals comment_stack cs;
                 (let uu____2753 =
                    let uu____2754 =
                      let uu____2755 = str comment  in
                      FStar_Pprint.op_Hat_Hat uu____2755
                        FStar_Pprint.hardline
                       in
                    FStar_Pprint.op_Hat_Hat acc uu____2754  in
                  comments_before_pos uu____2753 print_pos lookahead_pos))
              else
                (let uu____2757 =
                   FStar_Range.range_before_pos crange lookahead_pos  in
                 (acc, uu____2757))
           in
        let uu____2758 =
          let uu____2763 =
            let uu____2764 = FStar_Range.start_of_range tmrange  in
            FStar_Range.end_of_line uu____2764  in
          let uu____2765 = FStar_Range.end_of_range tmrange  in
          comments_before_pos FStar_Pprint.empty uu____2763 uu____2765  in
        match uu____2758 with
        | (comments,has_lookahead) ->
            let printed_e = printer tm  in
            let comments1 =
              if has_lookahead
              then
                let pos = FStar_Range.end_of_range tmrange  in
                let uu____2771 = comments_before_pos comments pos pos  in
                FStar_Pervasives_Native.fst uu____2771
              else comments  in
            let uu____2777 = FStar_Pprint.op_Hat_Hat comments1 printed_e  in
            FStar_Pprint.group uu____2777
  
let rec (place_comments_until_pos :
  Prims.int ->
    Prims.int ->
      FStar_Range.pos -> FStar_Pprint.document -> FStar_Pprint.document)
  =
  fun k  ->
    fun lbegin  ->
      fun pos_end  ->
        fun doc1  ->
          let uu____2790 = FStar_ST.op_Bang comment_stack  in
          match uu____2790 with
          | (comment,crange)::cs when
              FStar_Range.range_before_pos crange pos_end ->
              (FStar_ST.op_Colon_Equals comment_stack cs;
               (let lnum =
                  let uu____2874 =
                    let uu____2875 =
                      let uu____2876 = FStar_Range.start_of_range crange  in
                      FStar_Range.line_of_pos uu____2876  in
                    uu____2875 - lbegin  in
                  max k uu____2874  in
                let lnum1 = Prims.min (Prims.parse_int "2") lnum  in
                let doc2 =
                  let uu____2879 =
                    let uu____2880 =
                      FStar_Pprint.repeat lnum1 FStar_Pprint.hardline  in
                    let uu____2881 = str comment  in
                    FStar_Pprint.op_Hat_Hat uu____2880 uu____2881  in
                  FStar_Pprint.op_Hat_Hat doc1 uu____2879  in
                let uu____2882 =
                  let uu____2883 = FStar_Range.end_of_range crange  in
                  FStar_Range.line_of_pos uu____2883  in
                place_comments_until_pos (Prims.parse_int "1") uu____2882
                  pos_end doc2))
          | uu____2884 ->
              if doc1 = FStar_Pprint.empty
              then FStar_Pprint.empty
              else
                (let lnum =
                   let uu____2893 =
                     let uu____2894 = FStar_Range.line_of_pos pos_end  in
                     uu____2894 - lbegin  in
                   max (Prims.parse_int "1") uu____2893  in
                 let lnum1 = Prims.min (Prims.parse_int "2") lnum  in
                 let uu____2896 =
                   FStar_Pprint.repeat lnum1 FStar_Pprint.hardline  in
                 FStar_Pprint.op_Hat_Hat doc1 uu____2896)
  
let separate_map_with_comments :
  'Auu____2903 .
    FStar_Pprint.document ->
      FStar_Pprint.document ->
        ('Auu____2903 -> FStar_Pprint.document) ->
          'Auu____2903 Prims.list ->
            ('Auu____2903 -> FStar_Range.range) -> FStar_Pprint.document
  =
  fun prefix1  ->
    fun sep  ->
      fun f  ->
        fun xs  ->
          fun extract_range  ->
            let fold_fun uu____2951 x =
              match uu____2951 with
              | (last_line,doc1) ->
                  let r = extract_range x  in
                  let doc2 =
                    let uu____2965 = FStar_Range.start_of_range r  in
                    place_comments_until_pos (Prims.parse_int "1") last_line
                      uu____2965 doc1
                     in
                  let uu____2966 =
                    let uu____2967 = FStar_Range.end_of_range r  in
                    FStar_Range.line_of_pos uu____2967  in
                  let uu____2968 =
                    let uu____2969 =
                      let uu____2970 = f x  in
                      FStar_Pprint.op_Hat_Hat sep uu____2970  in
                    FStar_Pprint.op_Hat_Hat doc2 uu____2969  in
                  (uu____2966, uu____2968)
               in
            let uu____2971 =
              let uu____2978 = FStar_List.hd xs  in
              let uu____2979 = FStar_List.tl xs  in (uu____2978, uu____2979)
               in
            match uu____2971 with
            | (x,xs1) ->
                let init1 =
                  let uu____2995 =
                    let uu____2996 =
                      let uu____2997 = extract_range x  in
                      FStar_Range.end_of_range uu____2997  in
                    FStar_Range.line_of_pos uu____2996  in
                  let uu____2998 =
                    let uu____2999 = f x  in
                    FStar_Pprint.op_Hat_Hat prefix1 uu____2999  in
                  (uu____2995, uu____2998)  in
                let uu____3000 = FStar_List.fold_left fold_fun init1 xs1  in
                FStar_Pervasives_Native.snd uu____3000
  
let separate_map_with_comments_kw :
  'Auu____3016 'Auu____3017 .
    'Auu____3016 ->
      'Auu____3016 ->
        ('Auu____3016 -> 'Auu____3017 -> FStar_Pprint.document) ->
          'Auu____3017 Prims.list ->
            ('Auu____3017 -> FStar_Range.range) -> FStar_Pprint.document
  =
  fun prefix1  ->
    fun sep  ->
      fun f  ->
        fun xs  ->
          fun extract_range  ->
            let fold_fun uu____3070 x =
              match uu____3070 with
              | (last_line,doc1) ->
                  let r = extract_range x  in
                  let doc2 =
                    let uu____3084 = FStar_Range.start_of_range r  in
                    place_comments_until_pos (Prims.parse_int "1") last_line
                      uu____3084 doc1
                     in
                  let uu____3085 =
                    let uu____3086 = FStar_Range.end_of_range r  in
                    FStar_Range.line_of_pos uu____3086  in
                  let uu____3087 =
                    let uu____3088 = f sep x  in
                    FStar_Pprint.op_Hat_Hat doc2 uu____3088  in
                  (uu____3085, uu____3087)
               in
            let uu____3089 =
              let uu____3096 = FStar_List.hd xs  in
              let uu____3097 = FStar_List.tl xs  in (uu____3096, uu____3097)
               in
            match uu____3089 with
            | (x,xs1) ->
                let init1 =
                  let uu____3113 =
                    let uu____3114 =
                      let uu____3115 = extract_range x  in
                      FStar_Range.end_of_range uu____3115  in
                    FStar_Range.line_of_pos uu____3114  in
                  let uu____3116 = f prefix1 x  in (uu____3113, uu____3116)
                   in
                let uu____3117 = FStar_List.fold_left fold_fun init1 xs1  in
                FStar_Pervasives_Native.snd uu____3117
  
let rec (p_decl : FStar_Parser_AST.decl -> FStar_Pprint.document) =
  fun d  ->
    let qualifiers =
      match ((d.FStar_Parser_AST.quals), (d.FStar_Parser_AST.d)) with
      | ((FStar_Parser_AST.Assumption )::[],FStar_Parser_AST.Assume
         (id1,uu____3534)) ->
          let uu____3537 =
            let uu____3538 =
              FStar_Util.char_at id1.FStar_Ident.idText (Prims.parse_int "0")
               in
            FStar_All.pipe_right uu____3538 FStar_Util.is_upper  in
          if uu____3537
          then
            let uu____3539 = p_qualifier FStar_Parser_AST.Assumption  in
            FStar_Pprint.op_Hat_Hat uu____3539 FStar_Pprint.space
          else p_qualifiers d.FStar_Parser_AST.quals
      | uu____3541 -> p_qualifiers d.FStar_Parser_AST.quals  in
    let uu____3546 = FStar_Pprint.optional p_fsdoc d.FStar_Parser_AST.doc  in
    let uu____3547 =
      let uu____3548 = p_attributes d.FStar_Parser_AST.attrs  in
      let uu____3549 =
        let uu____3550 = p_rawDecl d  in
        FStar_Pprint.op_Hat_Hat qualifiers uu____3550  in
      FStar_Pprint.op_Hat_Hat uu____3548 uu____3549  in
    FStar_Pprint.op_Hat_Hat uu____3546 uu____3547

and (p_attributes : FStar_Parser_AST.attributes_ -> FStar_Pprint.document) =
  fun attrs  ->
    match attrs with
    | [] -> FStar_Pprint.empty
    | uu____3552 ->
        let uu____3553 =
          let uu____3554 = str "@ "  in
          let uu____3555 =
            let uu____3556 =
              let uu____3557 =
                let uu____3558 =
                  let uu____3559 = FStar_List.map p_atomicTerm attrs  in
                  FStar_Pprint.flow break1 uu____3559  in
                FStar_Pprint.op_Hat_Hat uu____3558 FStar_Pprint.rbracket  in
              FStar_Pprint.align uu____3557  in
            FStar_Pprint.op_Hat_Hat uu____3556 FStar_Pprint.hardline  in
          FStar_Pprint.op_Hat_Hat uu____3554 uu____3555  in
        FStar_Pprint.op_Hat_Hat FStar_Pprint.lbracket uu____3553

and (p_fsdoc : FStar_Parser_AST.fsdoc -> FStar_Pprint.document) =
  fun uu____3562  ->
    match uu____3562 with
    | (doc1,kwd_args) ->
        let kwd_args_doc =
          match kwd_args with
          | [] -> FStar_Pprint.empty
          | kwd_args1 ->
              let process_kwd_arg uu____3596 =
                match uu____3596 with
                | (kwd,arg) ->
                    let uu____3603 = str "@"  in
                    let uu____3604 =
                      let uu____3605 = str kwd  in
                      let uu____3606 =
                        let uu____3607 = str arg  in
                        FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____3607
                         in
                      FStar_Pprint.op_Hat_Hat uu____3605 uu____3606  in
                    FStar_Pprint.op_Hat_Hat uu____3603 uu____3604
                 in
              let uu____3608 =
                let uu____3609 =
                  FStar_Pprint.separate_map FStar_Pprint.hardline
                    process_kwd_arg kwd_args1
                   in
                FStar_Pprint.op_Hat_Hat uu____3609 FStar_Pprint.hardline  in
              FStar_Pprint.op_Hat_Hat FStar_Pprint.hardline uu____3608
           in
        let uu____3614 =
          let uu____3615 =
            let uu____3616 =
              let uu____3617 =
                let uu____3618 = str doc1  in
                let uu____3619 =
                  let uu____3620 =
                    let uu____3621 =
                      FStar_Pprint.op_Hat_Hat FStar_Pprint.rparen
                        FStar_Pprint.hardline
                       in
                    FStar_Pprint.op_Hat_Hat FStar_Pprint.star uu____3621  in
                  FStar_Pprint.op_Hat_Hat kwd_args_doc uu____3620  in
                FStar_Pprint.op_Hat_Hat uu____3618 uu____3619  in
              FStar_Pprint.op_Hat_Hat FStar_Pprint.star uu____3617  in
            FStar_Pprint.op_Hat_Hat FStar_Pprint.star uu____3616  in
          FStar_Pprint.op_Hat_Hat FStar_Pprint.lparen uu____3615  in
        FStar_Pprint.op_Hat_Hat FStar_Pprint.hardline uu____3614

and (p_justSig : FStar_Parser_AST.decl -> FStar_Pprint.document) =
  fun d  ->
    match d.FStar_Parser_AST.d with
    | FStar_Parser_AST.Val (lid,t) ->
        let uu____3625 =
          let uu____3626 = str "val"  in
          let uu____3627 =
            let uu____3628 =
              let uu____3629 = p_lident lid  in
              let uu____3630 =
                FStar_Pprint.op_Hat_Hat FStar_Pprint.space FStar_Pprint.colon
                 in
              FStar_Pprint.op_Hat_Hat uu____3629 uu____3630  in
            FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____3628  in
          FStar_Pprint.op_Hat_Hat uu____3626 uu____3627  in
        let uu____3631 = p_typ false false t  in
        FStar_Pprint.op_Hat_Hat uu____3625 uu____3631
    | FStar_Parser_AST.TopLevelLet (uu____3632,lbs) ->
        FStar_Pprint.separate_map FStar_Pprint.hardline
          (fun lb  ->
             let uu____3657 =
               let uu____3658 = str "let"  in p_letlhs uu____3658 lb  in
             FStar_Pprint.group uu____3657) lbs
    | uu____3659 -> FStar_Pprint.empty

and (p_rawDecl : FStar_Parser_AST.decl -> FStar_Pprint.document) =
  fun d  ->
    match d.FStar_Parser_AST.d with
    | FStar_Parser_AST.Open uid ->
        let uu____3662 =
          let uu____3663 = str "open"  in
          let uu____3664 = p_quident uid  in
          FStar_Pprint.op_Hat_Slash_Hat uu____3663 uu____3664  in
        FStar_Pprint.group uu____3662
    | FStar_Parser_AST.Include uid ->
        let uu____3666 =
          let uu____3667 = str "include"  in
          let uu____3668 = p_quident uid  in
          FStar_Pprint.op_Hat_Slash_Hat uu____3667 uu____3668  in
        FStar_Pprint.group uu____3666
    | FStar_Parser_AST.ModuleAbbrev (uid1,uid2) ->
        let uu____3671 =
          let uu____3672 = str "module"  in
          let uu____3673 =
            let uu____3674 =
              let uu____3675 = p_uident uid1  in
              let uu____3676 =
                FStar_Pprint.op_Hat_Hat FStar_Pprint.space
                  FStar_Pprint.equals
                 in
              FStar_Pprint.op_Hat_Hat uu____3675 uu____3676  in
            FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____3674  in
          FStar_Pprint.op_Hat_Hat uu____3672 uu____3673  in
        let uu____3677 = p_quident uid2  in
        op_Hat_Slash_Plus_Hat uu____3671 uu____3677
    | FStar_Parser_AST.TopLevelModule uid ->
        let uu____3679 =
          let uu____3680 = str "module"  in
          let uu____3681 =
            let uu____3682 = p_quident uid  in
            FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____3682  in
          FStar_Pprint.op_Hat_Hat uu____3680 uu____3681  in
        FStar_Pprint.group uu____3679
    | FStar_Parser_AST.Tycon
        (true
         ,(FStar_Parser_AST.TyconAbbrev
           (uid,tpars,FStar_Pervasives_Native.None ,t),FStar_Pervasives_Native.None
           )::[])
        ->
        let effect_prefix_doc =
          let uu____3715 = str "effect"  in
          let uu____3716 =
            let uu____3717 = p_uident uid  in
            FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____3717  in
          FStar_Pprint.op_Hat_Hat uu____3715 uu____3716  in
        let uu____3718 =
          let uu____3719 = p_typars tpars  in
          FStar_Pprint.surround (Prims.parse_int "2") (Prims.parse_int "1")
            effect_prefix_doc uu____3719 FStar_Pprint.equals
           in
        let uu____3720 = p_typ false false t  in
        op_Hat_Slash_Plus_Hat uu____3718 uu____3720
    | FStar_Parser_AST.Tycon (false ,tcdefs) ->
        let uu____3738 =
          let uu____3739 = str "type"  in
          let uu____3740 = FStar_List.hd tcdefs  in
          p_fsdocTypeDeclPairs uu____3739 uu____3740  in
        let uu____3753 =
          let uu____3754 = FStar_List.tl tcdefs  in
          FStar_All.pipe_left
            (FStar_Pprint.concat_map
               (fun x  ->
                  let uu____3792 =
                    let uu____3793 = str "and"  in
                    p_fsdocTypeDeclPairs uu____3793 x  in
                  FStar_Pprint.op_Hat_Hat break1 uu____3792)) uu____3754
           in
        FStar_Pprint.op_Hat_Hat uu____3738 uu____3753
    | FStar_Parser_AST.TopLevelLet (q,lbs) ->
        let let_doc =
          let uu____3809 = str "let"  in
          let uu____3810 = p_letqualifier q  in
          FStar_Pprint.op_Hat_Hat uu____3809 uu____3810  in
        let uu____3811 = str "and"  in
        separate_map_with_comments_kw let_doc uu____3811 p_letbinding lbs
          (fun uu____3819  ->
             match uu____3819 with
             | (p,t) ->
                 FStar_Range.union_ranges p.FStar_Parser_AST.prange
                   t.FStar_Parser_AST.range)
    | FStar_Parser_AST.Val (lid,t) ->
        let uu____3828 = str "val"  in
        let uu____3829 =
          let uu____3830 =
            let uu____3831 = p_lident lid  in
            let uu____3832 =
              let uu____3833 =
                let uu____3834 =
                  let uu____3835 = p_typ false false t  in
                  FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____3835  in
                FStar_Pprint.op_Hat_Hat FStar_Pprint.colon uu____3834  in
              FStar_Pprint.group uu____3833  in
            FStar_Pprint.op_Hat_Hat uu____3831 uu____3832  in
          FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____3830  in
        FStar_Pprint.op_Hat_Hat uu____3828 uu____3829
    | FStar_Parser_AST.Assume (id1,t) ->
        let decl_keyword =
          let uu____3839 =
            let uu____3840 =
              FStar_Util.char_at id1.FStar_Ident.idText (Prims.parse_int "0")
               in
            FStar_All.pipe_right uu____3840 FStar_Util.is_upper  in
          if uu____3839
          then FStar_Pprint.empty
          else
            (let uu____3842 = str "val"  in
             FStar_Pprint.op_Hat_Hat uu____3842 FStar_Pprint.space)
           in
        let uu____3843 =
          let uu____3844 = p_ident id1  in
          let uu____3845 =
            let uu____3846 =
              let uu____3847 =
                let uu____3848 = p_typ false false t  in
                FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____3848  in
              FStar_Pprint.op_Hat_Hat FStar_Pprint.colon uu____3847  in
            FStar_Pprint.group uu____3846  in
          FStar_Pprint.op_Hat_Hat uu____3844 uu____3845  in
        FStar_Pprint.op_Hat_Hat decl_keyword uu____3843
    | FStar_Parser_AST.Exception (uid,t_opt) ->
        let uu____3855 = str "exception"  in
        let uu____3856 =
          let uu____3857 =
            let uu____3858 = p_uident uid  in
            let uu____3859 =
              FStar_Pprint.optional
                (fun t  ->
                   let uu____3863 =
                     let uu____3864 = str "of"  in
                     let uu____3865 = p_typ false false t  in
                     op_Hat_Slash_Plus_Hat uu____3864 uu____3865  in
                   FStar_Pprint.op_Hat_Hat break1 uu____3863) t_opt
               in
            FStar_Pprint.op_Hat_Hat uu____3858 uu____3859  in
          FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____3857  in
        FStar_Pprint.op_Hat_Hat uu____3855 uu____3856
    | FStar_Parser_AST.NewEffect ne ->
        let uu____3867 = str "new_effect"  in
        let uu____3868 =
          let uu____3869 = p_newEffect ne  in
          FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____3869  in
        FStar_Pprint.op_Hat_Hat uu____3867 uu____3868
    | FStar_Parser_AST.SubEffect se ->
        let uu____3871 = str "sub_effect"  in
        let uu____3872 =
          let uu____3873 = p_subEffect se  in
          FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____3873  in
        FStar_Pprint.op_Hat_Hat uu____3871 uu____3872
    | FStar_Parser_AST.Pragma p -> p_pragma p
    | FStar_Parser_AST.Fsdoc doc1 ->
        let uu____3876 = p_fsdoc doc1  in
        FStar_Pprint.op_Hat_Hat uu____3876 FStar_Pprint.hardline
    | FStar_Parser_AST.Main uu____3877 ->
        failwith "*Main declaration* : Is that really still in use ??"
    | FStar_Parser_AST.Tycon (true ,uu____3878) ->
        failwith
          "Effect abbreviation is expected to be defined by an abbreviation"
    | FStar_Parser_AST.Splice t ->
        let uu____3896 = str "%splice"  in
        let uu____3897 =
          let uu____3898 = p_term false false t  in
          FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____3898  in
        FStar_Pprint.op_Hat_Hat uu____3896 uu____3897

and (p_pragma : FStar_Parser_AST.pragma -> FStar_Pprint.document) =
  fun uu___53_3899  ->
    match uu___53_3899 with
    | FStar_Parser_AST.SetOptions s ->
        let uu____3901 = str "#set-options"  in
        let uu____3902 =
          let uu____3903 =
            let uu____3904 = str s  in FStar_Pprint.dquotes uu____3904  in
          FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____3903  in
        FStar_Pprint.op_Hat_Hat uu____3901 uu____3902
    | FStar_Parser_AST.ResetOptions s_opt ->
        let uu____3908 = str "#reset-options"  in
        let uu____3909 =
          FStar_Pprint.optional
            (fun s  ->
               let uu____3913 =
                 let uu____3914 = str s  in FStar_Pprint.dquotes uu____3914
                  in
               FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____3913) s_opt
           in
        FStar_Pprint.op_Hat_Hat uu____3908 uu____3909
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
    fun uu____3939  ->
      match uu____3939 with
      | (typedecl,fsdoc_opt) ->
          let uu____3952 = p_typeDecl (kw, fsdoc_opt) typedecl  in
          (match uu____3952 with
           | (decl,body) ->
               let uu____3967 = body ()  in
               FStar_Pprint.op_Hat_Hat decl uu____3967)

and (p_typeDecl :
  (FStar_Pprint.document,FStar_Parser_AST.fsdoc
                           FStar_Pervasives_Native.option)
    FStar_Pervasives_Native.tuple2 ->
    FStar_Parser_AST.tycon ->
      (FStar_Pprint.document,Prims.unit -> FStar_Pprint.document)
        FStar_Pervasives_Native.tuple2)
  =
  fun pre  ->
    fun uu___54_3969  ->
      match uu___54_3969 with
      | FStar_Parser_AST.TyconAbstract (lid,bs,typ_opt) ->
          let empty' uu____3996 = FStar_Pprint.empty  in
          let uu____3997 = p_typeDeclPrefix pre false lid bs typ_opt  in
          (uu____3997, empty')
      | FStar_Parser_AST.TyconAbbrev (lid,bs,typ_opt,t) ->
          let f uu____4015 =
            let uu____4016 = p_typ false false t  in jump2 uu____4016  in
          let uu____4017 = p_typeDeclPrefix pre true lid bs typ_opt  in
          (uu____4017, f)
      | FStar_Parser_AST.TyconRecord (lid,bs,typ_opt,record_field_decls) ->
          let p_recordFieldAndComments ps uu____4066 =
            match uu____4066 with
            | (lid1,t,doc_opt) ->
                let uu____4082 =
                  FStar_Range.extend_to_end_of_line t.FStar_Parser_AST.range
                   in
                with_comment (p_recordFieldDecl ps) (lid1, t, doc_opt)
                  uu____4082
             in
          let p_fields uu____4096 =
            let uu____4097 =
              let uu____4098 =
                let uu____4099 =
                  FStar_Pprint.op_Hat_Hat FStar_Pprint.semi break1  in
                separate_map_last uu____4099 p_recordFieldAndComments
                  record_field_decls
                 in
              braces_with_nesting uu____4098  in
            FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____4097  in
          let uu____4108 = p_typeDeclPrefix pre true lid bs typ_opt  in
          (uu____4108, p_fields)
      | FStar_Parser_AST.TyconVariant (lid,bs,typ_opt,ct_decls) ->
          let p_constructorBranchAndComments uu____4166 =
            match uu____4166 with
            | (uid,t_opt,doc_opt,use_of) ->
                let range =
                  let uu____4192 =
                    let uu____4193 =
                      FStar_Util.map_opt t_opt
                        (fun t  -> t.FStar_Parser_AST.range)
                       in
                    FStar_Util.dflt uid.FStar_Ident.idRange uu____4193  in
                  FStar_Range.extend_to_end_of_line uu____4192  in
                with_comment p_constructorBranch
                  (uid, t_opt, doc_opt, use_of) range
             in
          let datacon_doc uu____4217 =
            FStar_Pprint.separate_map FStar_Pprint.hardline
              p_constructorBranchAndComments ct_decls
             in
          let uu____4230 = p_typeDeclPrefix pre true lid bs typ_opt  in
          (uu____4230,
            ((fun uu____4235  ->
                let uu____4236 = datacon_doc ()  in jump2 uu____4236)))

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
  fun uu____4237  ->
    fun eq1  ->
      fun lid  ->
        fun bs  ->
          fun typ_opt  ->
            match uu____4237 with
            | (kw,fsdoc_opt) ->
                let maybe_with_fsdoc cont =
                  let lid_doc = p_ident lid  in
                  let kw_lid =
                    let uu____4269 = FStar_Pprint.op_Hat_Slash_Hat kw lid_doc
                       in
                    FStar_Pprint.group uu____4269  in
                  match fsdoc_opt with
                  | FStar_Pervasives_Native.None  -> cont kw_lid
                  | FStar_Pervasives_Native.Some fsdoc ->
                      let uu____4271 =
                        let uu____4274 =
                          let uu____4277 = p_fsdoc fsdoc  in
                          let uu____4278 =
                            let uu____4281 = cont lid_doc  in [uu____4281]
                             in
                          uu____4277 :: uu____4278  in
                        kw :: uu____4274  in
                      FStar_Pprint.separate FStar_Pprint.hardline uu____4271
                   in
                let typ =
                  let maybe_eq =
                    if eq1 then FStar_Pprint.equals else FStar_Pprint.empty
                     in
                  match typ_opt with
                  | FStar_Pervasives_Native.None  -> maybe_eq
                  | FStar_Pervasives_Native.Some t ->
                      let uu____4286 =
                        let uu____4287 =
                          let uu____4288 = p_typ false false t  in
                          FStar_Pprint.op_Hat_Slash_Hat uu____4288 maybe_eq
                           in
                        FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____4287
                         in
                      FStar_Pprint.op_Hat_Hat FStar_Pprint.colon uu____4286
                   in
                if bs = []
                then maybe_with_fsdoc (fun n1  -> prefix2 n1 typ)
                else
                  (let binders = p_binders_list true bs  in
                   maybe_with_fsdoc
                     (fun n1  ->
                        let uu____4303 =
                          let uu____4304 = FStar_Pprint.flow break1 binders
                             in
                          prefix2 n1 uu____4304  in
                        prefix2 uu____4303 typ))

and (p_recordFieldDecl :
  Prims.bool ->
    (FStar_Ident.ident,FStar_Parser_AST.term,FStar_Parser_AST.fsdoc
                                               FStar_Pervasives_Native.option)
      FStar_Pervasives_Native.tuple3 -> FStar_Pprint.document)
  =
  fun ps  ->
    fun uu____4306  ->
      match uu____4306 with
      | (lid,t,doc_opt) ->
          let uu____4322 =
            let uu____4323 = FStar_Pprint.optional p_fsdoc doc_opt  in
            let uu____4324 =
              let uu____4325 = p_lident lid  in
              let uu____4326 =
                let uu____4327 = p_typ ps false t  in
                FStar_Pprint.op_Hat_Hat FStar_Pprint.colon uu____4327  in
              FStar_Pprint.op_Hat_Hat uu____4325 uu____4326  in
            FStar_Pprint.op_Hat_Hat uu____4323 uu____4324  in
          FStar_Pprint.group uu____4322

and (p_constructorBranch :
  (FStar_Ident.ident,FStar_Parser_AST.term FStar_Pervasives_Native.option,
    FStar_Parser_AST.fsdoc FStar_Pervasives_Native.option,Prims.bool)
    FStar_Pervasives_Native.tuple4 -> FStar_Pprint.document)
  =
  fun uu____4328  ->
    match uu____4328 with
    | (uid,t_opt,doc_opt,use_of) ->
        let sep = if use_of then str "of" else FStar_Pprint.colon  in
        let uid_doc =
          let uu____4356 =
            let uu____4357 =
              let uu____4358 = p_uident uid  in
              FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____4358  in
            FStar_Pprint.op_Hat_Hat FStar_Pprint.bar uu____4357  in
          FStar_Pprint.group uu____4356  in
        let uu____4359 = FStar_Pprint.optional p_fsdoc doc_opt  in
        let uu____4360 =
          default_or_map uid_doc
            (fun t  ->
               let uu____4364 =
                 let uu____4365 =
                   let uu____4366 =
                     let uu____4367 =
                       let uu____4368 = p_typ false false t  in
                       FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____4368
                        in
                     FStar_Pprint.op_Hat_Hat sep uu____4367  in
                   FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____4366  in
                 FStar_Pprint.op_Hat_Hat uid_doc uu____4365  in
               FStar_Pprint.group uu____4364) t_opt
           in
        FStar_Pprint.op_Hat_Hat uu____4359 uu____4360

and (p_letlhs :
  FStar_Pprint.document ->
    (FStar_Parser_AST.pattern,FStar_Parser_AST.term)
      FStar_Pervasives_Native.tuple2 -> FStar_Pprint.document)
  =
  fun kw  ->
    fun uu____4370  ->
      match uu____4370 with
      | (pat,uu____4376) ->
          let uu____4377 =
            match pat.FStar_Parser_AST.pat with
            | FStar_Parser_AST.PatAscribed
                (pat1,(t,FStar_Pervasives_Native.None )) ->
                let uu____4396 =
                  let uu____4397 =
                    let uu____4398 =
                      let uu____4399 = p_tmArrow p_tmNoEq t  in
                      FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____4399
                       in
                    FStar_Pprint.op_Hat_Hat FStar_Pprint.colon uu____4398  in
                  FStar_Pprint.group uu____4397  in
                (pat1, uu____4396)
            | FStar_Parser_AST.PatAscribed
                (pat1,(t,FStar_Pervasives_Native.Some tac)) ->
                let uu____4411 =
                  let uu____4412 =
                    let uu____4413 =
                      let uu____4414 =
                        let uu____4415 = p_tmArrow p_tmNoEq t  in
                        FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____4415
                         in
                      FStar_Pprint.op_Hat_Hat FStar_Pprint.colon uu____4414
                       in
                    FStar_Pprint.group uu____4413  in
                  let uu____4416 =
                    let uu____4417 =
                      let uu____4418 = str "by"  in
                      let uu____4419 =
                        let uu____4420 = p_atomicTerm tac  in
                        FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____4420
                         in
                      FStar_Pprint.op_Hat_Hat uu____4418 uu____4419  in
                    FStar_Pprint.group uu____4417  in
                  FStar_Pprint.op_Hat_Hat uu____4412 uu____4416  in
                (pat1, uu____4411)
            | uu____4421 -> (pat, FStar_Pprint.empty)  in
          (match uu____4377 with
           | (pat1,ascr_doc) ->
               (match pat1.FStar_Parser_AST.pat with
                | FStar_Parser_AST.PatApp
                    ({
                       FStar_Parser_AST.pat = FStar_Parser_AST.PatVar
                         (x,uu____4425);
                       FStar_Parser_AST.prange = uu____4426;_},pats)
                    ->
                    let uu____4436 =
                      let uu____4437 =
                        let uu____4438 =
                          let uu____4439 = p_lident x  in
                          FStar_Pprint.op_Hat_Slash_Hat kw uu____4439  in
                        FStar_Pprint.group uu____4438  in
                      let uu____4440 =
                        FStar_Pprint.flow_map break1 p_atomicPattern pats  in
                      prefix2 uu____4437 uu____4440  in
                    prefix2_nonempty uu____4436 ascr_doc
                | uu____4441 ->
                    let uu____4442 =
                      let uu____4443 =
                        let uu____4444 =
                          let uu____4445 = p_tuplePattern pat1  in
                          FStar_Pprint.op_Hat_Slash_Hat kw uu____4445  in
                        FStar_Pprint.group uu____4444  in
                      FStar_Pprint.op_Hat_Hat uu____4443 ascr_doc  in
                    FStar_Pprint.group uu____4442))

and (p_letbinding :
  FStar_Pprint.document ->
    (FStar_Parser_AST.pattern,FStar_Parser_AST.term)
      FStar_Pervasives_Native.tuple2 -> FStar_Pprint.document)
  =
  fun kw  ->
    fun uu____4447  ->
      match uu____4447 with
      | (pat,e) ->
          let doc_pat = p_letlhs kw (pat, e)  in
          let doc_expr = p_term false false e  in
          let uu____4456 =
            let uu____4457 =
              FStar_Pprint.op_Hat_Slash_Hat FStar_Pprint.equals doc_expr  in
            FStar_Pprint.op_Hat_Slash_Hat doc_pat uu____4457  in
          let uu____4458 =
            let uu____4459 =
              let uu____4460 =
                let uu____4461 =
                  let uu____4462 = jump2 doc_expr  in
                  FStar_Pprint.op_Hat_Hat FStar_Pprint.equals uu____4462  in
                FStar_Pprint.group uu____4461  in
              FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____4460  in
            FStar_Pprint.op_Hat_Hat doc_pat uu____4459  in
          FStar_Pprint.ifflat uu____4456 uu____4458

and (p_newEffect : FStar_Parser_AST.effect_decl -> FStar_Pprint.document) =
  fun uu___55_4463  ->
    match uu___55_4463 with
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
        let uu____4488 = p_uident uid  in
        let uu____4489 = p_binders true bs  in
        let uu____4490 =
          let uu____4491 = p_simpleTerm false false t  in
          prefix2 FStar_Pprint.equals uu____4491  in
        surround_maybe_empty (Prims.parse_int "2") (Prims.parse_int "1")
          uu____4488 uu____4489 uu____4490

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
          let uu____4501 =
            let uu____4502 =
              let uu____4503 =
                let uu____4504 = p_uident uid  in
                let uu____4505 = p_binders true bs  in
                let uu____4506 =
                  let uu____4507 = p_typ false false t  in
                  prefix2 FStar_Pprint.colon uu____4507  in
                surround_maybe_empty (Prims.parse_int "2")
                  (Prims.parse_int "1") uu____4504 uu____4505 uu____4506
                 in
              FStar_Pprint.group uu____4503  in
            let uu____4508 =
              let uu____4509 = str "with"  in
              let uu____4510 =
                let uu____4511 =
                  let uu____4512 =
                    let uu____4513 =
                      let uu____4514 =
                        let uu____4515 =
                          FStar_Pprint.op_Hat_Hat FStar_Pprint.semi
                            FStar_Pprint.space
                           in
                        FStar_Pprint.op_Hat_Hat FStar_Pprint.hardline
                          uu____4515
                         in
                      separate_map_last uu____4514 p_effectDecl eff_decls  in
                    FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____4513  in
                  FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____4512  in
                FStar_Pprint.op_Hat_Hat FStar_Pprint.hardline uu____4511  in
              FStar_Pprint.op_Hat_Hat uu____4509 uu____4510  in
            FStar_Pprint.op_Hat_Slash_Hat uu____4502 uu____4508  in
          braces_with_nesting uu____4501

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
          let uu____4546 =
            let uu____4547 = p_lident lid  in
            let uu____4548 =
              FStar_Pprint.op_Hat_Hat FStar_Pprint.space FStar_Pprint.equals
               in
            FStar_Pprint.op_Hat_Hat uu____4547 uu____4548  in
          let uu____4549 = p_simpleTerm ps false e  in
          prefix2 uu____4546 uu____4549
      | uu____4550 ->
          let uu____4551 =
            let uu____4552 = FStar_Parser_AST.decl_to_string d  in
            FStar_Util.format1
              "Not a declaration of an effect member... or at least I hope so : %s"
              uu____4552
             in
          failwith uu____4551

and (p_subEffect : FStar_Parser_AST.lift -> FStar_Pprint.document) =
  fun lift  ->
    let lift_op_doc =
      let lifts =
        match lift.FStar_Parser_AST.lift_op with
        | FStar_Parser_AST.NonReifiableLift t -> [("lift_wp", t)]
        | FStar_Parser_AST.ReifiableLift (t1,t2) ->
            [("lift_wp", t1); ("lift", t2)]
        | FStar_Parser_AST.LiftForFree t -> [("lift", t)]  in
      let p_lift ps uu____4610 =
        match uu____4610 with
        | (kwd,t) ->
            let uu____4617 =
              let uu____4618 = str kwd  in
              let uu____4619 =
                FStar_Pprint.op_Hat_Hat FStar_Pprint.space
                  FStar_Pprint.equals
                 in
              FStar_Pprint.op_Hat_Hat uu____4618 uu____4619  in
            let uu____4620 = p_simpleTerm ps false t  in
            prefix2 uu____4617 uu____4620
         in
      separate_break_map_last FStar_Pprint.semi p_lift lifts  in
    let uu____4625 =
      let uu____4626 =
        let uu____4627 = p_quident lift.FStar_Parser_AST.msource  in
        let uu____4628 =
          let uu____4629 = str "~>"  in
          FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____4629  in
        FStar_Pprint.op_Hat_Hat uu____4627 uu____4628  in
      let uu____4630 = p_quident lift.FStar_Parser_AST.mdest  in
      prefix2 uu____4626 uu____4630  in
    let uu____4631 =
      let uu____4632 = braces_with_nesting lift_op_doc  in
      FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____4632  in
    FStar_Pprint.op_Hat_Hat uu____4625 uu____4631

and (p_qualifier : FStar_Parser_AST.qualifier -> FStar_Pprint.document) =
  fun uu___56_4633  ->
    match uu___56_4633 with
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
    | uu____4635 ->
        let uu____4636 =
          let uu____4637 = FStar_List.map p_qualifier qs  in
          FStar_Pprint.flow break1 uu____4637  in
        FStar_Pprint.op_Hat_Hat uu____4636 FStar_Pprint.hardline

and (p_letqualifier :
  FStar_Parser_AST.let_qualifier -> FStar_Pprint.document) =
  fun uu___57_4640  ->
    match uu___57_4640 with
    | FStar_Parser_AST.Rec  ->
        let uu____4641 = str "rec"  in
        FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____4641
    | FStar_Parser_AST.Mutable  ->
        let uu____4642 = str "mutable"  in
        FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____4642
    | FStar_Parser_AST.NoLetQualifier  -> FStar_Pprint.empty

and (p_aqual : FStar_Parser_AST.arg_qualifier -> FStar_Pprint.document) =
  fun uu___58_4643  ->
    match uu___58_4643 with
    | FStar_Parser_AST.Implicit  -> str "#"
    | FStar_Parser_AST.Equality  -> str "$"

and (p_disjunctivePattern :
  FStar_Parser_AST.pattern -> FStar_Pprint.document) =
  fun p  ->
    match p.FStar_Parser_AST.pat with
    | FStar_Parser_AST.PatOr pats ->
        let uu____4648 =
          let uu____4649 =
            let uu____4650 =
              FStar_Pprint.op_Hat_Hat FStar_Pprint.bar FStar_Pprint.space  in
            FStar_Pprint.op_Hat_Hat break1 uu____4650  in
          FStar_Pprint.separate_map uu____4649 p_tuplePattern pats  in
        FStar_Pprint.group uu____4648
    | uu____4651 -> p_tuplePattern p

and (p_tuplePattern : FStar_Parser_AST.pattern -> FStar_Pprint.document) =
  fun p  ->
    match p.FStar_Parser_AST.pat with
    | FStar_Parser_AST.PatTuple (pats,false ) ->
        let uu____4658 =
          let uu____4659 = FStar_Pprint.op_Hat_Hat FStar_Pprint.comma break1
             in
          FStar_Pprint.separate_map uu____4659 p_constructorPattern pats  in
        FStar_Pprint.group uu____4658
    | uu____4660 -> p_constructorPattern p

and (p_constructorPattern :
  FStar_Parser_AST.pattern -> FStar_Pprint.document) =
  fun p  ->
    match p.FStar_Parser_AST.pat with
    | FStar_Parser_AST.PatApp
        ({ FStar_Parser_AST.pat = FStar_Parser_AST.PatName maybe_cons_lid;
           FStar_Parser_AST.prange = uu____4663;_},hd1::tl1::[])
        when
        FStar_Ident.lid_equals maybe_cons_lid FStar_Parser_Const.cons_lid ->
        let uu____4668 =
          FStar_Pprint.op_Hat_Hat FStar_Pprint.colon FStar_Pprint.colon  in
        let uu____4669 = p_constructorPattern hd1  in
        let uu____4670 = p_constructorPattern tl1  in
        infix0 uu____4668 uu____4669 uu____4670
    | FStar_Parser_AST.PatApp
        ({ FStar_Parser_AST.pat = FStar_Parser_AST.PatName uid;
           FStar_Parser_AST.prange = uu____4672;_},pats)
        ->
        let uu____4678 = p_quident uid  in
        let uu____4679 =
          FStar_Pprint.separate_map break1 p_atomicPattern pats  in
        prefix2 uu____4678 uu____4679
    | uu____4680 -> p_atomicPattern p

and (p_atomicPattern : FStar_Parser_AST.pattern -> FStar_Pprint.document) =
  fun p  ->
    match p.FStar_Parser_AST.pat with
    | FStar_Parser_AST.PatAscribed (pat,(t,FStar_Pervasives_Native.None )) ->
        (match ((pat.FStar_Parser_AST.pat), (t.FStar_Parser_AST.tm)) with
         | (FStar_Parser_AST.PatVar (lid,aqual),FStar_Parser_AST.Refine
            ({ FStar_Parser_AST.b = FStar_Parser_AST.Annotated (lid',t1);
               FStar_Parser_AST.brange = uu____4696;
               FStar_Parser_AST.blevel = uu____4697;
               FStar_Parser_AST.aqual = uu____4698;_},phi))
             when lid.FStar_Ident.idText = lid'.FStar_Ident.idText ->
             let uu____4704 =
               let uu____4705 = p_ident lid  in
               p_refinement aqual uu____4705 t1 phi  in
             soft_parens_with_nesting uu____4704
         | (FStar_Parser_AST.PatWild ,FStar_Parser_AST.Refine
            ({ FStar_Parser_AST.b = FStar_Parser_AST.NoName t1;
               FStar_Parser_AST.brange = uu____4707;
               FStar_Parser_AST.blevel = uu____4708;
               FStar_Parser_AST.aqual = uu____4709;_},phi))
             ->
             let uu____4711 =
               p_refinement FStar_Pervasives_Native.None
                 FStar_Pprint.underscore t1 phi
                in
             soft_parens_with_nesting uu____4711
         | uu____4712 ->
             let uu____4717 =
               let uu____4718 = p_tuplePattern pat  in
               let uu____4719 =
                 let uu____4720 = p_tmEqNoRefinement t  in
                 FStar_Pprint.op_Hat_Slash_Hat FStar_Pprint.colon uu____4720
                  in
               FStar_Pprint.op_Hat_Hat uu____4718 uu____4719  in
             soft_parens_with_nesting uu____4717)
    | FStar_Parser_AST.PatList pats ->
        let uu____4724 =
          separate_break_map FStar_Pprint.semi p_tuplePattern pats  in
        FStar_Pprint.surround (Prims.parse_int "2") (Prims.parse_int "0")
          FStar_Pprint.lbracket uu____4724 FStar_Pprint.rbracket
    | FStar_Parser_AST.PatRecord pats ->
        let p_recordFieldPat uu____4739 =
          match uu____4739 with
          | (lid,pat) ->
              let uu____4746 = p_qlident lid  in
              let uu____4747 = p_tuplePattern pat  in
              infix2 FStar_Pprint.equals uu____4746 uu____4747
           in
        let uu____4748 =
          separate_break_map FStar_Pprint.semi p_recordFieldPat pats  in
        soft_braces_with_nesting uu____4748
    | FStar_Parser_AST.PatTuple (pats,true ) ->
        let uu____4758 =
          FStar_Pprint.op_Hat_Hat FStar_Pprint.lparen FStar_Pprint.bar  in
        let uu____4759 =
          separate_break_map FStar_Pprint.comma p_constructorPattern pats  in
        let uu____4760 =
          FStar_Pprint.op_Hat_Hat FStar_Pprint.bar FStar_Pprint.rparen  in
        FStar_Pprint.surround (Prims.parse_int "2") (Prims.parse_int "1")
          uu____4758 uu____4759 uu____4760
    | FStar_Parser_AST.PatTvar (tv,arg_qualifier_opt) -> p_tvar tv
    | FStar_Parser_AST.PatOp op ->
        let uu____4771 =
          let uu____4772 =
            let uu____4773 = str (FStar_Ident.text_of_id op)  in
            let uu____4774 =
              FStar_Pprint.op_Hat_Hat FStar_Pprint.space FStar_Pprint.rparen
               in
            FStar_Pprint.op_Hat_Hat uu____4773 uu____4774  in
          FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____4772  in
        FStar_Pprint.op_Hat_Hat FStar_Pprint.lparen uu____4771
    | FStar_Parser_AST.PatWild  -> FStar_Pprint.underscore
    | FStar_Parser_AST.PatConst c -> p_constant c
    | FStar_Parser_AST.PatVar (lid,aqual) ->
        let uu____4782 = FStar_Pprint.optional p_aqual aqual  in
        let uu____4783 = p_lident lid  in
        FStar_Pprint.op_Hat_Hat uu____4782 uu____4783
    | FStar_Parser_AST.PatName uid -> p_quident uid
    | FStar_Parser_AST.PatOr uu____4785 -> failwith "Inner or pattern !"
    | FStar_Parser_AST.PatApp
        ({ FStar_Parser_AST.pat = FStar_Parser_AST.PatName uu____4788;
           FStar_Parser_AST.prange = uu____4789;_},uu____4790)
        ->
        let uu____4795 = p_tuplePattern p  in
        soft_parens_with_nesting uu____4795
    | FStar_Parser_AST.PatTuple (uu____4796,false ) ->
        let uu____4801 = p_tuplePattern p  in
        soft_parens_with_nesting uu____4801
    | uu____4802 ->
        let uu____4803 =
          let uu____4804 = FStar_Parser_AST.pat_to_string p  in
          FStar_Util.format1 "Invalid pattern %s" uu____4804  in
        failwith uu____4803

and (p_binder :
  Prims.bool -> FStar_Parser_AST.binder -> FStar_Pprint.document) =
  fun is_atomic  ->
    fun b  ->
      match b.FStar_Parser_AST.b with
      | FStar_Parser_AST.Variable lid ->
          let uu____4808 =
            FStar_Pprint.optional p_aqual b.FStar_Parser_AST.aqual  in
          let uu____4809 = p_lident lid  in
          FStar_Pprint.op_Hat_Hat uu____4808 uu____4809
      | FStar_Parser_AST.TVariable lid -> p_lident lid
      | FStar_Parser_AST.Annotated (lid,t) ->
          let doc1 =
            match t.FStar_Parser_AST.tm with
            | FStar_Parser_AST.Refine
                ({ FStar_Parser_AST.b = FStar_Parser_AST.Annotated (lid',t1);
                   FStar_Parser_AST.brange = uu____4816;
                   FStar_Parser_AST.blevel = uu____4817;
                   FStar_Parser_AST.aqual = uu____4818;_},phi)
                when lid.FStar_Ident.idText = lid'.FStar_Ident.idText ->
                let uu____4820 = p_lident lid  in
                p_refinement b.FStar_Parser_AST.aqual uu____4820 t1 phi
            | uu____4821 ->
                let uu____4822 =
                  FStar_Pprint.optional p_aqual b.FStar_Parser_AST.aqual  in
                let uu____4823 =
                  let uu____4824 = p_lident lid  in
                  let uu____4825 =
                    let uu____4826 = p_tmFormula t  in
                    FStar_Pprint.op_Hat_Slash_Hat FStar_Pprint.colon
                      uu____4826
                     in
                  FStar_Pprint.op_Hat_Hat uu____4824 uu____4825  in
                FStar_Pprint.op_Hat_Hat uu____4822 uu____4823
             in
          if is_atomic
          then
            let uu____4827 =
              let uu____4828 =
                FStar_Pprint.op_Hat_Hat doc1 FStar_Pprint.rparen  in
              FStar_Pprint.op_Hat_Hat FStar_Pprint.lparen uu____4828  in
            FStar_Pprint.group uu____4827
          else FStar_Pprint.group doc1
      | FStar_Parser_AST.TAnnotated uu____4830 ->
          failwith "Is this still used ?"
      | FStar_Parser_AST.NoName t ->
          (match t.FStar_Parser_AST.tm with
           | FStar_Parser_AST.Refine
               ({ FStar_Parser_AST.b = FStar_Parser_AST.NoName t1;
                  FStar_Parser_AST.brange = uu____4837;
                  FStar_Parser_AST.blevel = uu____4838;
                  FStar_Parser_AST.aqual = uu____4839;_},phi)
               ->
               if is_atomic
               then
                 let uu____4841 =
                   let uu____4842 =
                     let uu____4843 =
                       p_refinement b.FStar_Parser_AST.aqual
                         FStar_Pprint.underscore t1 phi
                        in
                     FStar_Pprint.op_Hat_Hat uu____4843 FStar_Pprint.rparen
                      in
                   FStar_Pprint.op_Hat_Hat FStar_Pprint.lparen uu____4842  in
                 FStar_Pprint.group uu____4841
               else
                 (let uu____4845 =
                    p_refinement b.FStar_Parser_AST.aqual
                      FStar_Pprint.underscore t1 phi
                     in
                  FStar_Pprint.group uu____4845)
           | uu____4846 -> if is_atomic then p_atomicTerm t else p_appTerm t)

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
            | FStar_Parser_AST.Construct uu____4855 -> false
            | FStar_Parser_AST.App uu____4866 -> false
            | FStar_Parser_AST.Op uu____4873 -> false
            | uu____4880 -> true  in
          let phi1 = p_noSeqTerm false false phi  in
          let jump_break =
            if is_t_atomic
            then (Prims.parse_int "0")
            else (Prims.parse_int "1")  in
          let uu____4884 =
            let uu____4885 = FStar_Pprint.optional p_aqual aqual_opt  in
            let uu____4886 =
              FStar_Pprint.op_Hat_Hat binder FStar_Pprint.colon  in
            FStar_Pprint.op_Hat_Hat uu____4885 uu____4886  in
          let uu____4887 =
            let uu____4888 = p_appTerm t  in
            let uu____4889 =
              let uu____4890 =
                let uu____4891 =
                  let uu____4892 = soft_braces_with_nesting_tight phi1  in
                  let uu____4893 = soft_braces_with_nesting phi1  in
                  FStar_Pprint.ifflat uu____4892 uu____4893  in
                FStar_Pprint.group uu____4891  in
              FStar_Pprint.jump (Prims.parse_int "2") jump_break uu____4890
               in
            FStar_Pprint.op_Hat_Hat uu____4888 uu____4889  in
          FStar_Pprint.op_Hat_Slash_Hat uu____4884 uu____4887

and (p_binders_list :
  Prims.bool ->
    FStar_Parser_AST.binder Prims.list -> FStar_Pprint.document Prims.list)
  = fun is_atomic  -> fun bs  -> FStar_List.map (p_binder is_atomic) bs

and (p_binders :
  Prims.bool -> FStar_Parser_AST.binder Prims.list -> FStar_Pprint.document)
  =
  fun is_atomic  ->
    fun bs  ->
      let uu____4904 = p_binders_list is_atomic bs  in
      separate_or_flow break1 uu____4904

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
            let uu____4927 =
              let uu____4928 =
                let uu____4929 = p_noSeqTerm true false e1  in
                FStar_Pprint.op_Hat_Hat uu____4929 FStar_Pprint.semi  in
              FStar_Pprint.group uu____4928  in
            let uu____4930 = p_term ps pb e2  in
            FStar_Pprint.op_Hat_Slash_Hat uu____4927 uu____4930
        | FStar_Parser_AST.Bind (x,e1,e2) ->
            let uu____4934 =
              let uu____4935 =
                let uu____4936 =
                  let uu____4937 = p_lident x  in
                  let uu____4938 =
                    FStar_Pprint.op_Hat_Hat FStar_Pprint.space
                      FStar_Pprint.long_left_arrow
                     in
                  FStar_Pprint.op_Hat_Hat uu____4937 uu____4938  in
                let uu____4939 =
                  let uu____4940 = p_noSeqTerm true false e1  in
                  let uu____4941 =
                    FStar_Pprint.op_Hat_Hat FStar_Pprint.space
                      FStar_Pprint.semi
                     in
                  FStar_Pprint.op_Hat_Hat uu____4940 uu____4941  in
                op_Hat_Slash_Plus_Hat uu____4936 uu____4939  in
              FStar_Pprint.group uu____4935  in
            let uu____4942 = p_term ps pb e2  in
            FStar_Pprint.op_Hat_Slash_Hat uu____4934 uu____4942
        | uu____4943 ->
            let uu____4944 = p_noSeqTerm ps pb e  in
            FStar_Pprint.group uu____4944

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
            let uu____4955 =
              let uu____4956 = p_tmIff e1  in
              let uu____4957 =
                let uu____4958 =
                  let uu____4959 = p_typ ps pb t  in
                  FStar_Pprint.op_Hat_Slash_Hat FStar_Pprint.colon uu____4959
                   in
                FStar_Pprint.op_Hat_Hat FStar_Pprint.langle uu____4958  in
              FStar_Pprint.op_Hat_Slash_Hat uu____4956 uu____4957  in
            FStar_Pprint.group uu____4955
        | FStar_Parser_AST.Ascribed (e1,t,FStar_Pervasives_Native.Some tac)
            ->
            let uu____4965 =
              let uu____4966 = p_tmIff e1  in
              let uu____4967 =
                let uu____4968 =
                  let uu____4969 =
                    let uu____4970 = p_typ false false t  in
                    let uu____4971 =
                      let uu____4972 = str "by"  in
                      let uu____4973 = p_typ ps pb tac  in
                      FStar_Pprint.op_Hat_Slash_Hat uu____4972 uu____4973  in
                    FStar_Pprint.op_Hat_Slash_Hat uu____4970 uu____4971  in
                  FStar_Pprint.op_Hat_Slash_Hat FStar_Pprint.colon uu____4969
                   in
                FStar_Pprint.op_Hat_Hat FStar_Pprint.langle uu____4968  in
              FStar_Pprint.op_Hat_Slash_Hat uu____4966 uu____4967  in
            FStar_Pprint.group uu____4965
        | FStar_Parser_AST.Op
            ({ FStar_Ident.idText = ".()<-";
               FStar_Ident.idRange = uu____4974;_},e1::e2::e3::[])
            ->
            let uu____4980 =
              let uu____4981 =
                let uu____4982 =
                  let uu____4983 = p_atomicTermNotQUident e1  in
                  let uu____4984 =
                    let uu____4985 =
                      let uu____4986 =
                        let uu____4987 = p_term false false e2  in
                        soft_parens_with_nesting uu____4987  in
                      let uu____4988 =
                        FStar_Pprint.op_Hat_Hat FStar_Pprint.space
                          FStar_Pprint.larrow
                         in
                      FStar_Pprint.op_Hat_Hat uu____4986 uu____4988  in
                    FStar_Pprint.op_Hat_Hat FStar_Pprint.dot uu____4985  in
                  FStar_Pprint.op_Hat_Hat uu____4983 uu____4984  in
                FStar_Pprint.group uu____4982  in
              let uu____4989 =
                let uu____4990 = p_noSeqTerm ps pb e3  in jump2 uu____4990
                 in
              FStar_Pprint.op_Hat_Hat uu____4981 uu____4989  in
            FStar_Pprint.group uu____4980
        | FStar_Parser_AST.Op
            ({ FStar_Ident.idText = ".[]<-";
               FStar_Ident.idRange = uu____4991;_},e1::e2::e3::[])
            ->
            let uu____4997 =
              let uu____4998 =
                let uu____4999 =
                  let uu____5000 = p_atomicTermNotQUident e1  in
                  let uu____5001 =
                    let uu____5002 =
                      let uu____5003 =
                        let uu____5004 = p_term false false e2  in
                        soft_brackets_with_nesting uu____5004  in
                      let uu____5005 =
                        FStar_Pprint.op_Hat_Hat FStar_Pprint.space
                          FStar_Pprint.larrow
                         in
                      FStar_Pprint.op_Hat_Hat uu____5003 uu____5005  in
                    FStar_Pprint.op_Hat_Hat FStar_Pprint.dot uu____5002  in
                  FStar_Pprint.op_Hat_Hat uu____5000 uu____5001  in
                FStar_Pprint.group uu____4999  in
              let uu____5006 =
                let uu____5007 = p_noSeqTerm ps pb e3  in jump2 uu____5007
                 in
              FStar_Pprint.op_Hat_Hat uu____4998 uu____5006  in
            FStar_Pprint.group uu____4997
        | FStar_Parser_AST.Requires (e1,wtf) ->
            let uu____5017 =
              let uu____5018 = str "requires"  in
              let uu____5019 = p_typ ps pb e1  in
              FStar_Pprint.op_Hat_Slash_Hat uu____5018 uu____5019  in
            FStar_Pprint.group uu____5017
        | FStar_Parser_AST.Ensures (e1,wtf) ->
            let uu____5029 =
              let uu____5030 = str "ensures"  in
              let uu____5031 = p_typ ps pb e1  in
              FStar_Pprint.op_Hat_Slash_Hat uu____5030 uu____5031  in
            FStar_Pprint.group uu____5029
        | FStar_Parser_AST.Attributes es ->
            let uu____5035 =
              let uu____5036 = str "attributes"  in
              let uu____5037 =
                FStar_Pprint.separate_map break1 p_atomicTerm es  in
              FStar_Pprint.op_Hat_Slash_Hat uu____5036 uu____5037  in
            FStar_Pprint.group uu____5035
        | FStar_Parser_AST.If (e1,e2,e3) ->
            if is_unit e3
            then
              let uu____5041 =
                let uu____5042 =
                  let uu____5043 = str "if"  in
                  let uu____5044 = p_noSeqTerm false false e1  in
                  op_Hat_Slash_Plus_Hat uu____5043 uu____5044  in
                let uu____5045 =
                  let uu____5046 = str "then"  in
                  let uu____5047 = p_noSeqTerm ps pb e2  in
                  op_Hat_Slash_Plus_Hat uu____5046 uu____5047  in
                FStar_Pprint.op_Hat_Slash_Hat uu____5042 uu____5045  in
              FStar_Pprint.group uu____5041
            else
              (let e2_doc =
                 match e2.FStar_Parser_AST.tm with
                 | FStar_Parser_AST.If (uu____5050,uu____5051,e31) when
                     is_unit e31 ->
                     let uu____5053 = p_noSeqTerm false false e2  in
                     soft_parens_with_nesting uu____5053
                 | uu____5054 -> p_noSeqTerm false false e2  in
               let uu____5055 =
                 let uu____5056 =
                   let uu____5057 = str "if"  in
                   let uu____5058 = p_noSeqTerm false false e1  in
                   op_Hat_Slash_Plus_Hat uu____5057 uu____5058  in
                 let uu____5059 =
                   let uu____5060 =
                     let uu____5061 = str "then"  in
                     op_Hat_Slash_Plus_Hat uu____5061 e2_doc  in
                   let uu____5062 =
                     let uu____5063 = str "else"  in
                     let uu____5064 = p_noSeqTerm ps pb e3  in
                     op_Hat_Slash_Plus_Hat uu____5063 uu____5064  in
                   FStar_Pprint.op_Hat_Slash_Hat uu____5060 uu____5062  in
                 FStar_Pprint.op_Hat_Slash_Hat uu____5056 uu____5059  in
               FStar_Pprint.group uu____5055)
        | FStar_Parser_AST.TryWith (e1,branches) ->
            let uu____5087 =
              let uu____5088 =
                let uu____5089 =
                  let uu____5090 = str "try"  in
                  let uu____5091 = p_noSeqTerm false false e1  in
                  prefix2 uu____5090 uu____5091  in
                let uu____5092 =
                  let uu____5093 = str "with"  in
                  let uu____5094 =
                    separate_map_last FStar_Pprint.hardline p_patternBranch
                      branches
                     in
                  FStar_Pprint.op_Hat_Slash_Hat uu____5093 uu____5094  in
                FStar_Pprint.op_Hat_Slash_Hat uu____5089 uu____5092  in
              FStar_Pprint.group uu____5088  in
            let uu____5103 = paren_if (ps || pb)  in uu____5103 uu____5087
        | FStar_Parser_AST.Match (e1,branches) ->
            let uu____5128 =
              let uu____5129 =
                let uu____5130 =
                  let uu____5131 = str "match"  in
                  let uu____5132 = p_noSeqTerm false false e1  in
                  let uu____5133 = str "with"  in
                  FStar_Pprint.surround (Prims.parse_int "2")
                    (Prims.parse_int "1") uu____5131 uu____5132 uu____5133
                   in
                let uu____5134 =
                  separate_map_last FStar_Pprint.hardline p_patternBranch
                    branches
                   in
                FStar_Pprint.op_Hat_Slash_Hat uu____5130 uu____5134  in
              FStar_Pprint.group uu____5129  in
            let uu____5143 = paren_if (ps || pb)  in uu____5143 uu____5128
        | FStar_Parser_AST.LetOpen (uid,e1) ->
            let uu____5148 =
              let uu____5149 =
                let uu____5150 =
                  let uu____5151 = str "let open"  in
                  let uu____5152 = p_quident uid  in
                  let uu____5153 = str "in"  in
                  FStar_Pprint.surround (Prims.parse_int "2")
                    (Prims.parse_int "1") uu____5151 uu____5152 uu____5153
                   in
                let uu____5154 = p_term false pb e1  in
                FStar_Pprint.op_Hat_Slash_Hat uu____5150 uu____5154  in
              FStar_Pprint.group uu____5149  in
            let uu____5155 = paren_if ps  in uu____5155 uu____5148
        | FStar_Parser_AST.Let (q,lbs,e1) ->
            let p_lb q1 uu____5211 is_last =
              match uu____5211 with
              | (a,(pat,e2)) ->
                  let attrs = p_attrs_opt a  in
                  let doc_let_or_and =
                    match q1 with
                    | FStar_Pervasives_Native.Some (FStar_Parser_AST.Rec ) ->
                        let uu____5244 =
                          let uu____5245 = str "let"  in
                          let uu____5246 = str "rec"  in
                          FStar_Pprint.op_Hat_Slash_Hat uu____5245 uu____5246
                           in
                        FStar_Pprint.group uu____5244
                    | FStar_Pervasives_Native.Some
                        (FStar_Parser_AST.NoLetQualifier ) -> str "let"
                    | uu____5247 -> str "and"  in
                  let doc_pat = p_letlhs doc_let_or_and (pat, e2)  in
                  let doc_expr = p_term false false e2  in
                  let uu____5252 =
                    if is_last
                    then
                      let uu____5253 =
                        FStar_Pprint.flow break1
                          [doc_pat; FStar_Pprint.equals]
                         in
                      let uu____5254 = str "in"  in
                      FStar_Pprint.surround (Prims.parse_int "2")
                        (Prims.parse_int "1") uu____5253 doc_expr uu____5254
                    else
                      (let uu____5256 =
                         FStar_Pprint.flow break1
                           [doc_pat; FStar_Pprint.equals; doc_expr]
                          in
                       FStar_Pprint.hang (Prims.parse_int "2") uu____5256)
                     in
                  FStar_Pprint.op_Hat_Hat attrs uu____5252
               in
            let l = FStar_List.length lbs  in
            let lbs_docs =
              FStar_List.mapi
                (fun i  ->
                   fun lb  ->
                     if i = (Prims.parse_int "0")
                     then
                       let uu____5302 =
                         p_lb (FStar_Pervasives_Native.Some q) lb
                           (i = (l - (Prims.parse_int "1")))
                          in
                       FStar_Pprint.group uu____5302
                     else
                       (let uu____5310 =
                          p_lb FStar_Pervasives_Native.None lb
                            (i = (l - (Prims.parse_int "1")))
                           in
                        FStar_Pprint.group uu____5310)) lbs
               in
            let lbs_doc =
              let uu____5318 = FStar_Pprint.separate break1 lbs_docs  in
              FStar_Pprint.group uu____5318  in
            let uu____5319 =
              let uu____5320 =
                let uu____5321 =
                  let uu____5322 = p_term false pb e1  in
                  FStar_Pprint.op_Hat_Hat FStar_Pprint.hardline uu____5322
                   in
                FStar_Pprint.op_Hat_Hat lbs_doc uu____5321  in
              FStar_Pprint.group uu____5320  in
            let uu____5323 = paren_if ps  in uu____5323 uu____5319
        | FStar_Parser_AST.Abs
            ({ FStar_Parser_AST.pat = FStar_Parser_AST.PatVar (x,typ_opt);
               FStar_Parser_AST.prange = uu____5328;_}::[],{
                                                             FStar_Parser_AST.tm
                                                               =
                                                               FStar_Parser_AST.Match
                                                               (maybe_x,branches);
                                                             FStar_Parser_AST.range
                                                               = uu____5331;
                                                             FStar_Parser_AST.level
                                                               = uu____5332;_})
            when matches_var maybe_x x ->
            let uu____5359 =
              let uu____5360 =
                let uu____5361 = str "function"  in
                let uu____5362 =
                  separate_map_last FStar_Pprint.hardline p_patternBranch
                    branches
                   in
                FStar_Pprint.op_Hat_Slash_Hat uu____5361 uu____5362  in
              FStar_Pprint.group uu____5360  in
            let uu____5371 = paren_if (ps || pb)  in uu____5371 uu____5359
        | FStar_Parser_AST.Quote (e1,FStar_Parser_AST.Dynamic ) ->
            let uu____5375 =
              let uu____5376 = str "quote"  in
              let uu____5377 = p_noSeqTerm ps pb e1  in
              FStar_Pprint.op_Hat_Slash_Hat uu____5376 uu____5377  in
            FStar_Pprint.group uu____5375
        | FStar_Parser_AST.Quote (e1,FStar_Parser_AST.Static ) ->
            let uu____5379 =
              let uu____5380 = str "`"  in
              let uu____5381 = p_noSeqTerm ps pb e1  in
              FStar_Pprint.op_Hat_Hat uu____5380 uu____5381  in
            FStar_Pprint.group uu____5379
        | FStar_Parser_AST.VQuote e1 ->
            let uu____5383 =
              let uu____5384 = str "%`"  in
              let uu____5385 = p_noSeqTerm ps pb e1  in
              FStar_Pprint.op_Hat_Hat uu____5384 uu____5385  in
            FStar_Pprint.group uu____5383
        | uu____5386 -> p_typ ps pb e

and (p_attrs_opt :
  FStar_Parser_AST.term Prims.list FStar_Pervasives_Native.option ->
    FStar_Pprint.document)
  =
  fun uu___59_5387  ->
    match uu___59_5387 with
    | FStar_Pervasives_Native.None  -> FStar_Pprint.empty
    | FStar_Pervasives_Native.Some terms ->
        let uu____5399 =
          let uu____5400 = str "[@"  in
          let uu____5401 =
            let uu____5402 =
              FStar_Pprint.separate_map break1 p_atomicTerm terms  in
            let uu____5403 = str "]"  in
            FStar_Pprint.op_Hat_Slash_Hat uu____5402 uu____5403  in
          FStar_Pprint.op_Hat_Slash_Hat uu____5400 uu____5401  in
        FStar_Pprint.group uu____5399

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
                 let uu____5429 =
                   let uu____5430 =
                     let uu____5431 = p_quantifier e  in
                     FStar_Pprint.op_Hat_Hat uu____5431 FStar_Pprint.space
                      in
                   FStar_Pprint.soft_surround (Prims.parse_int "2")
                     (Prims.parse_int "0") uu____5430 binders_doc
                     FStar_Pprint.dot
                    in
                 prefix2 uu____5429 term_doc
             | pats ->
                 let uu____5437 =
                   let uu____5438 =
                     let uu____5439 =
                       let uu____5440 =
                         let uu____5441 = p_quantifier e  in
                         FStar_Pprint.op_Hat_Hat uu____5441
                           FStar_Pprint.space
                          in
                       FStar_Pprint.soft_surround (Prims.parse_int "2")
                         (Prims.parse_int "0") uu____5440 binders_doc
                         FStar_Pprint.dot
                        in
                     let uu____5442 = p_trigger trigger  in
                     prefix2 uu____5439 uu____5442  in
                   FStar_Pprint.group uu____5438  in
                 prefix2 uu____5437 term_doc)
        | FStar_Parser_AST.QExists (bs,trigger,e1) ->
            let binders_doc = p_binders true bs  in
            let term_doc = p_noSeqTerm ps pb e1  in
            (match trigger with
             | [] ->
                 let uu____5462 =
                   let uu____5463 =
                     let uu____5464 = p_quantifier e  in
                     FStar_Pprint.op_Hat_Hat uu____5464 FStar_Pprint.space
                      in
                   FStar_Pprint.soft_surround (Prims.parse_int "2")
                     (Prims.parse_int "0") uu____5463 binders_doc
                     FStar_Pprint.dot
                    in
                 prefix2 uu____5462 term_doc
             | pats ->
                 let uu____5470 =
                   let uu____5471 =
                     let uu____5472 =
                       let uu____5473 =
                         let uu____5474 = p_quantifier e  in
                         FStar_Pprint.op_Hat_Hat uu____5474
                           FStar_Pprint.space
                          in
                       FStar_Pprint.soft_surround (Prims.parse_int "2")
                         (Prims.parse_int "0") uu____5473 binders_doc
                         FStar_Pprint.dot
                        in
                     let uu____5475 = p_trigger trigger  in
                     prefix2 uu____5472 uu____5475  in
                   FStar_Pprint.group uu____5471  in
                 prefix2 uu____5470 term_doc)
        | uu____5476 -> p_simpleTerm ps pb e

and (p_quantifier : FStar_Parser_AST.term -> FStar_Pprint.document) =
  fun e  ->
    match e.FStar_Parser_AST.tm with
    | FStar_Parser_AST.QForall uu____5478 -> str "forall"
    | FStar_Parser_AST.QExists uu____5491 -> str "exists"
    | uu____5504 ->
        failwith "Imposible : p_quantifier called on a non-quantifier term"

and (p_trigger :
  FStar_Parser_AST.term Prims.list Prims.list -> FStar_Pprint.document) =
  fun uu___60_5505  ->
    match uu___60_5505 with
    | [] -> FStar_Pprint.empty
    | pats ->
        let uu____5517 =
          let uu____5518 =
            let uu____5519 =
              let uu____5520 = str "pattern"  in
              let uu____5521 =
                let uu____5522 =
                  let uu____5523 = p_disjunctivePats pats  in
                  FStar_Pprint.jump (Prims.parse_int "2")
                    (Prims.parse_int "0") uu____5523
                   in
                FStar_Pprint.op_Hat_Hat uu____5522 FStar_Pprint.rbrace  in
              FStar_Pprint.op_Hat_Slash_Hat uu____5520 uu____5521  in
            FStar_Pprint.op_Hat_Hat FStar_Pprint.colon uu____5519  in
          FStar_Pprint.op_Hat_Hat FStar_Pprint.lbrace uu____5518  in
        FStar_Pprint.group uu____5517

and (p_disjunctivePats :
  FStar_Parser_AST.term Prims.list Prims.list -> FStar_Pprint.document) =
  fun pats  ->
    let uu____5529 = str "\\/"  in
    FStar_Pprint.separate_map uu____5529 p_conjunctivePats pats

and (p_conjunctivePats :
  FStar_Parser_AST.term Prims.list -> FStar_Pprint.document) =
  fun pats  ->
    let uu____5535 =
      let uu____5536 = FStar_Pprint.op_Hat_Hat FStar_Pprint.semi break1  in
      FStar_Pprint.separate_map uu____5536 p_appTerm pats  in
    FStar_Pprint.group uu____5535

and (p_simpleTerm :
  Prims.bool -> Prims.bool -> FStar_Parser_AST.term -> FStar_Pprint.document)
  =
  fun ps  ->
    fun pb  ->
      fun e  ->
        match e.FStar_Parser_AST.tm with
        | FStar_Parser_AST.Abs (pats,e1) ->
            let uu____5546 =
              let uu____5547 =
                let uu____5548 = str "fun"  in
                let uu____5549 =
                  let uu____5550 =
                    FStar_Pprint.separate_map break1 p_atomicPattern pats  in
                  FStar_Pprint.op_Hat_Slash_Hat uu____5550
                    FStar_Pprint.rarrow
                   in
                op_Hat_Slash_Plus_Hat uu____5548 uu____5549  in
              let uu____5551 = p_term false pb e1  in
              op_Hat_Slash_Plus_Hat uu____5547 uu____5551  in
            let uu____5552 = paren_if ps  in uu____5552 uu____5546
        | uu____5555 -> p_tmIff e

and (p_maybeFocusArrow : Prims.bool -> FStar_Pprint.document) =
  fun b  -> if b then str "~>" else FStar_Pprint.rarrow

and (p_patternBranch :
  Prims.bool ->
    (FStar_Parser_AST.pattern,FStar_Parser_AST.term
                                FStar_Pervasives_Native.option,FStar_Parser_AST.term)
      FStar_Pervasives_Native.tuple3 -> FStar_Pprint.document)
  =
  fun pb  ->
    fun uu____5559  ->
      match uu____5559 with
      | (pat,when_opt,e) ->
          let one_pattern_branch p =
            let branch =
              match when_opt with
              | FStar_Pervasives_Native.None  ->
                  let uu____5580 =
                    let uu____5581 =
                      let uu____5582 =
                        let uu____5583 = p_tuplePattern p  in
                        let uu____5584 =
                          FStar_Pprint.op_Hat_Hat FStar_Pprint.space
                            FStar_Pprint.rarrow
                           in
                        FStar_Pprint.op_Hat_Hat uu____5583 uu____5584  in
                      FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____5582
                       in
                    FStar_Pprint.op_Hat_Hat FStar_Pprint.bar uu____5581  in
                  FStar_Pprint.group uu____5580
              | FStar_Pervasives_Native.Some f ->
                  let uu____5586 =
                    let uu____5587 =
                      let uu____5588 =
                        let uu____5589 =
                          let uu____5590 =
                            let uu____5591 = p_tuplePattern p  in
                            let uu____5592 = str "when"  in
                            FStar_Pprint.op_Hat_Slash_Hat uu____5591
                              uu____5592
                             in
                          FStar_Pprint.group uu____5590  in
                        let uu____5593 =
                          let uu____5594 =
                            let uu____5597 = p_tmFormula f  in
                            [uu____5597; FStar_Pprint.rarrow]  in
                          FStar_Pprint.flow break1 uu____5594  in
                        FStar_Pprint.op_Hat_Slash_Hat uu____5589 uu____5593
                         in
                      FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____5588
                       in
                    FStar_Pprint.op_Hat_Hat FStar_Pprint.bar uu____5587  in
                  FStar_Pprint.hang (Prims.parse_int "2") uu____5586
               in
            let uu____5598 =
              let uu____5599 = p_term false pb e  in
              op_Hat_Slash_Plus_Hat branch uu____5599  in
            FStar_Pprint.group uu____5598  in
          (match pat.FStar_Parser_AST.pat with
           | FStar_Parser_AST.PatOr pats ->
               (match FStar_List.rev pats with
                | hd1::tl1 ->
                    let last_pat_branch = one_pattern_branch hd1  in
                    let uu____5608 =
                      let uu____5609 =
                        let uu____5610 =
                          let uu____5611 =
                            let uu____5612 =
                              let uu____5613 =
                                FStar_Pprint.op_Hat_Hat FStar_Pprint.bar
                                  FStar_Pprint.space
                                 in
                              FStar_Pprint.op_Hat_Hat break1 uu____5613  in
                            FStar_Pprint.separate_map uu____5612
                              p_tuplePattern (FStar_List.rev tl1)
                             in
                          FStar_Pprint.op_Hat_Slash_Hat uu____5611
                            last_pat_branch
                           in
                        FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____5610
                         in
                      FStar_Pprint.op_Hat_Hat FStar_Pprint.bar uu____5609  in
                    FStar_Pprint.group uu____5608
                | [] ->
                    failwith "Impossible: disjunctive pattern can't be empty")
           | uu____5614 -> one_pattern_branch pat)

and (p_tmIff : FStar_Parser_AST.term -> FStar_Pprint.document) =
  fun e  ->
    match e.FStar_Parser_AST.tm with
    | FStar_Parser_AST.Op
        ({ FStar_Ident.idText = "<==>"; FStar_Ident.idRange = uu____5616;_},e1::e2::[])
        ->
        let uu____5621 = str "<==>"  in
        let uu____5622 = p_tmImplies e1  in
        let uu____5623 = p_tmIff e2  in
        infix0 uu____5621 uu____5622 uu____5623
    | uu____5624 -> p_tmImplies e

and (p_tmImplies : FStar_Parser_AST.term -> FStar_Pprint.document) =
  fun e  ->
    match e.FStar_Parser_AST.tm with
    | FStar_Parser_AST.Op
        ({ FStar_Ident.idText = "==>"; FStar_Ident.idRange = uu____5626;_},e1::e2::[])
        ->
        let uu____5631 = str "==>"  in
        let uu____5632 = p_tmArrow p_tmFormula e1  in
        let uu____5633 = p_tmImplies e2  in
        infix0 uu____5631 uu____5632 uu____5633
    | uu____5634 -> p_tmArrow p_tmFormula e

and (p_tmArrow :
  (FStar_Parser_AST.term -> FStar_Pprint.document) ->
    FStar_Parser_AST.term -> FStar_Pprint.document)
  =
  fun p_Tm  ->
    fun e  ->
      let terms = p_tmArrow' p_Tm e  in
      let uu____5642 =
        FStar_List.splitAt
          ((FStar_List.length terms) - (Prims.parse_int "1")) terms
         in
      match uu____5642 with
      | (terms',last1) ->
          let last_op =
            if (FStar_List.length terms) > (Prims.parse_int "1")
            then
              FStar_Pprint.op_Hat_Hat FStar_Pprint.space FStar_Pprint.rarrow
            else FStar_Pprint.empty  in
          (match FStar_List.length terms with
           | _0_31 when _0_31 = (Prims.parse_int "1") -> FStar_List.hd terms
           | uu____5663 ->
               let uu____5664 =
                 let uu____5665 =
                   let uu____5666 =
                     let uu____5667 =
                       FStar_Pprint.op_Hat_Hat FStar_Pprint.rarrow break1  in
                     FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____5667
                      in
                   FStar_Pprint.separate uu____5666 terms  in
                 let uu____5668 =
                   let uu____5669 =
                     let uu____5670 =
                       let uu____5671 =
                         let uu____5672 =
                           let uu____5673 =
                             let uu____5674 =
                               FStar_Pprint.op_Hat_Hat FStar_Pprint.rarrow
                                 break1
                                in
                             FStar_Pprint.op_Hat_Hat FStar_Pprint.space
                               uu____5674
                              in
                           FStar_Pprint.separate uu____5673 terms'  in
                         FStar_Pprint.op_Hat_Hat uu____5672 last_op  in
                       let uu____5675 =
                         let uu____5676 =
                           let uu____5677 =
                             let uu____5678 =
                               let uu____5679 =
                                 FStar_Pprint.op_Hat_Hat FStar_Pprint.rarrow
                                   break1
                                  in
                               FStar_Pprint.op_Hat_Hat FStar_Pprint.space
                                 uu____5679
                                in
                             FStar_Pprint.separate uu____5678 terms'  in
                           FStar_Pprint.op_Hat_Hat uu____5677 last_op  in
                         jump2 uu____5676  in
                       FStar_Pprint.ifflat uu____5671 uu____5675  in
                     FStar_Pprint.group uu____5670  in
                   let uu____5680 = FStar_List.hd last1  in
                   prefix2 uu____5669 uu____5680  in
                 FStar_Pprint.ifflat uu____5665 uu____5668  in
               FStar_Pprint.group uu____5664)

and (p_tmArrow' :
  (FStar_Parser_AST.term -> FStar_Pprint.document) ->
    FStar_Parser_AST.term -> FStar_Pprint.document Prims.list)
  =
  fun p_Tm  ->
    fun e  ->
      match e.FStar_Parser_AST.tm with
      | FStar_Parser_AST.Product (bs,tgt) ->
          let uu____5693 = FStar_List.map (fun b  -> p_binder false b) bs  in
          let uu____5698 = p_tmArrow' p_Tm tgt  in
          FStar_List.append uu____5693 uu____5698
      | uu____5701 -> let uu____5702 = p_Tm e  in [uu____5702]

and (p_tmFormula : FStar_Parser_AST.term -> FStar_Pprint.document) =
  fun e  ->
    let conj =
      let uu____5705 =
        let uu____5706 = str "/\\"  in
        FStar_Pprint.op_Hat_Hat uu____5706 break1  in
      FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____5705  in
    let disj =
      let uu____5708 =
        let uu____5709 = str "\\/"  in
        FStar_Pprint.op_Hat_Hat uu____5709 break1  in
      FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____5708  in
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
        ({ FStar_Ident.idText = "\\/"; FStar_Ident.idRange = uu____5728;_},e1::e2::[])
        ->
        let uu____5733 = p_tmDisjunction e1  in
        let uu____5738 = let uu____5743 = p_tmConjunction e2  in [uu____5743]
           in
        FStar_List.append uu____5733 uu____5738
    | uu____5752 -> let uu____5753 = p_tmConjunction e  in [uu____5753]

and (p_tmConjunction :
  FStar_Parser_AST.term -> FStar_Pprint.document Prims.list) =
  fun e  ->
    match e.FStar_Parser_AST.tm with
    | FStar_Parser_AST.Op
        ({ FStar_Ident.idText = "/\\"; FStar_Ident.idRange = uu____5763;_},e1::e2::[])
        ->
        let uu____5768 = p_tmConjunction e1  in
        let uu____5771 = let uu____5774 = p_tmTuple e2  in [uu____5774]  in
        FStar_List.append uu____5768 uu____5771
    | uu____5775 -> let uu____5776 = p_tmTuple e  in [uu____5776]

and (p_tmTuple : FStar_Parser_AST.term -> FStar_Pprint.document) =
  fun e  -> with_comment p_tmTuple' e e.FStar_Parser_AST.range

and (p_tmTuple' : FStar_Parser_AST.term -> FStar_Pprint.document) =
  fun e  ->
    match e.FStar_Parser_AST.tm with
    | FStar_Parser_AST.Construct (lid,args) when is_tuple_constructor lid ->
        let uu____5793 = FStar_Pprint.op_Hat_Hat FStar_Pprint.comma break1
           in
        FStar_Pprint.separate_map uu____5793
          (fun uu____5801  ->
             match uu____5801 with | (e1,uu____5807) -> p_tmEq e1) args
    | uu____5808 -> p_tmEq e

and (paren_if_gt :
  Prims.int -> Prims.int -> FStar_Pprint.document -> FStar_Pprint.document) =
  fun curr  ->
    fun mine  ->
      fun doc1  ->
        if mine <= curr
        then doc1
        else
          (let uu____5813 =
             let uu____5814 =
               FStar_Pprint.op_Hat_Hat doc1 FStar_Pprint.rparen  in
             FStar_Pprint.op_Hat_Hat FStar_Pprint.lparen uu____5814  in
           FStar_Pprint.group uu____5813)

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
            let uu____5877 = levels op1  in
            (match uu____5877 with
             | (left1,mine,right1) ->
                 let uu____5887 =
                   let uu____5888 = FStar_All.pipe_left str op1  in
                   let uu____5889 = p_tmEqWith' p_X left1 e1  in
                   let uu____5890 = p_tmEqWith' p_X right1 e2  in
                   infix0 uu____5888 uu____5889 uu____5890  in
                 paren_if_gt curr mine uu____5887)
        | FStar_Parser_AST.Op
            ({ FStar_Ident.idText = ":="; FStar_Ident.idRange = uu____5891;_},e1::e2::[])
            ->
            let uu____5896 =
              let uu____5897 = p_tmEqWith p_X e1  in
              let uu____5898 =
                let uu____5899 =
                  let uu____5900 =
                    let uu____5901 = p_tmEqWith p_X e2  in
                    op_Hat_Slash_Plus_Hat FStar_Pprint.equals uu____5901  in
                  FStar_Pprint.op_Hat_Hat FStar_Pprint.colon uu____5900  in
                FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____5899  in
              FStar_Pprint.op_Hat_Hat uu____5897 uu____5898  in
            FStar_Pprint.group uu____5896
        | FStar_Parser_AST.Op
            ({ FStar_Ident.idText = "-"; FStar_Ident.idRange = uu____5902;_},e1::[])
            ->
            let uu____5906 = levels "-"  in
            (match uu____5906 with
             | (left1,mine,right1) ->
                 let uu____5916 = p_tmEqWith' p_X mine e1  in
                 FStar_Pprint.op_Hat_Slash_Hat FStar_Pprint.minus uu____5916)
        | uu____5917 -> p_tmNoEqWith p_X e

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
              (lid,(e1,uu____5989)::(e2,uu____5991)::[]) when
              (FStar_Ident.lid_equals lid FStar_Parser_Const.cons_lid) &&
                (let uu____6011 = is_list e  in Prims.op_Negation uu____6011)
              ->
              let op = "::"  in
              let uu____6013 = levels op  in
              (match uu____6013 with
               | (left1,mine,right1) ->
                   let uu____6023 =
                     let uu____6024 = str op  in
                     let uu____6025 = p_tmNoEqWith' false p_X left1 e1  in
                     let uu____6026 = p_tmNoEqWith' false p_X right1 e2  in
                     infix0 uu____6024 uu____6025 uu____6026  in
                   paren_if_gt curr mine uu____6023)
          | FStar_Parser_AST.Sum (binders,res) ->
              let op = "&"  in
              let uu____6034 = levels op  in
              (match uu____6034 with
               | (left1,mine,right1) ->
                   let p_dsumfst b =
                     let uu____6048 = p_binder false b  in
                     let uu____6049 =
                       let uu____6050 =
                         let uu____6051 = str op  in
                         FStar_Pprint.op_Hat_Hat uu____6051 break1  in
                       FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____6050
                        in
                     FStar_Pprint.op_Hat_Hat uu____6048 uu____6049  in
                   let uu____6052 =
                     let uu____6053 =
                       FStar_Pprint.concat_map p_dsumfst binders  in
                     let uu____6054 = p_tmNoEqWith' false p_X right1 res  in
                     FStar_Pprint.op_Hat_Hat uu____6053 uu____6054  in
                   paren_if_gt curr mine uu____6052)
          | FStar_Parser_AST.Op
              ({ FStar_Ident.idText = "*";
                 FStar_Ident.idRange = uu____6055;_},e1::e2::[])
              ->
              let op = "*"  in
              let uu____6061 = levels op  in
              (match uu____6061 with
               | (left1,mine,right1) ->
                   if inside_tuple
                   then
                     let uu____6071 = str op  in
                     let uu____6072 = p_tmNoEqWith' true p_X left1 e1  in
                     let uu____6073 = p_tmNoEqWith' true p_X right1 e2  in
                     infix0 uu____6071 uu____6072 uu____6073
                   else
                     (let uu____6074 =
                        let uu____6075 = str op  in
                        let uu____6076 = p_tmNoEqWith' true p_X left1 e1  in
                        let uu____6077 = p_tmNoEqWith' true p_X right1 e2  in
                        infix0 uu____6075 uu____6076 uu____6077  in
                      paren_if_gt curr mine uu____6074))
          | FStar_Parser_AST.Op (op,e1::e2::[]) when is_operatorInfix34 op ->
              let op1 = FStar_Ident.text_of_id op  in
              let uu____6084 = levels op1  in
              (match uu____6084 with
               | (left1,mine,right1) ->
                   let uu____6094 =
                     let uu____6095 = str op1  in
                     let uu____6096 = p_tmNoEqWith' false p_X left1 e1  in
                     let uu____6097 = p_tmNoEqWith' false p_X right1 e2  in
                     infix0 uu____6095 uu____6096 uu____6097  in
                   paren_if_gt curr mine uu____6094)
          | FStar_Parser_AST.Record (with_opt,record_fields) ->
              let uu____6116 =
                let uu____6117 =
                  default_or_map FStar_Pprint.empty p_with_clause with_opt
                   in
                let uu____6118 =
                  let uu____6119 =
                    FStar_Pprint.op_Hat_Hat FStar_Pprint.semi break1  in
                  separate_map_last uu____6119 p_simpleDef record_fields  in
                FStar_Pprint.op_Hat_Hat uu____6117 uu____6118  in
              braces_with_nesting uu____6116
          | FStar_Parser_AST.Op
              ({ FStar_Ident.idText = "~";
                 FStar_Ident.idRange = uu____6124;_},e1::[])
              ->
              let uu____6128 =
                let uu____6129 = str "~"  in
                let uu____6130 = p_atomicTerm e1  in
                FStar_Pprint.op_Hat_Hat uu____6129 uu____6130  in
              FStar_Pprint.group uu____6128
          | FStar_Parser_AST.Paren p when inside_tuple ->
              (match p.FStar_Parser_AST.tm with
               | FStar_Parser_AST.Op
                   ({ FStar_Ident.idText = "*";
                      FStar_Ident.idRange = uu____6132;_},e1::e2::[])
                   ->
                   let op = "*"  in
                   let uu____6138 = levels op  in
                   (match uu____6138 with
                    | (left1,mine,right1) ->
                        let uu____6148 =
                          let uu____6149 = str op  in
                          let uu____6150 = p_tmNoEqWith' true p_X left1 e1
                             in
                          let uu____6151 = p_tmNoEqWith' true p_X right1 e2
                             in
                          infix0 uu____6149 uu____6150 uu____6151  in
                        paren_if_gt curr mine uu____6148)
               | uu____6152 -> p_X e)
          | uu____6153 -> p_X e

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
        let uu____6160 =
          let uu____6161 = p_lident lid  in
          let uu____6162 =
            let uu____6163 = p_appTerm e1  in
            FStar_Pprint.op_Hat_Slash_Hat FStar_Pprint.colon uu____6163  in
          FStar_Pprint.op_Hat_Slash_Hat uu____6161 uu____6162  in
        FStar_Pprint.group uu____6160
    | FStar_Parser_AST.Refine (b,phi) -> p_refinedBinder b phi
    | uu____6166 -> p_appTerm e

and (p_with_clause : FStar_Parser_AST.term -> FStar_Pprint.document) =
  fun e  ->
    let uu____6168 = p_appTerm e  in
    let uu____6169 =
      let uu____6170 =
        let uu____6171 = str "with"  in
        FStar_Pprint.op_Hat_Hat uu____6171 break1  in
      FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____6170  in
    FStar_Pprint.op_Hat_Hat uu____6168 uu____6169

and (p_refinedBinder :
  FStar_Parser_AST.binder -> FStar_Parser_AST.term -> FStar_Pprint.document)
  =
  fun b  ->
    fun phi  ->
      match b.FStar_Parser_AST.b with
      | FStar_Parser_AST.Annotated (lid,t) ->
          let uu____6176 = p_lident lid  in
          p_refinement b.FStar_Parser_AST.aqual uu____6176 t phi
      | FStar_Parser_AST.TAnnotated uu____6177 ->
          failwith "Is this still used ?"
      | FStar_Parser_AST.Variable uu____6182 ->
          let uu____6183 =
            let uu____6184 = FStar_Parser_AST.binder_to_string b  in
            FStar_Util.format1
              "Imposible : a refined binder ought to be annotated %s"
              uu____6184
             in
          failwith uu____6183
      | FStar_Parser_AST.TVariable uu____6185 ->
          let uu____6186 =
            let uu____6187 = FStar_Parser_AST.binder_to_string b  in
            FStar_Util.format1
              "Imposible : a refined binder ought to be annotated %s"
              uu____6187
             in
          failwith uu____6186
      | FStar_Parser_AST.NoName uu____6188 ->
          let uu____6189 =
            let uu____6190 = FStar_Parser_AST.binder_to_string b  in
            FStar_Util.format1
              "Imposible : a refined binder ought to be annotated %s"
              uu____6190
             in
          failwith uu____6189

and (p_simpleDef :
  Prims.bool ->
    (FStar_Ident.lid,FStar_Parser_AST.term) FStar_Pervasives_Native.tuple2 ->
      FStar_Pprint.document)
  =
  fun ps  ->
    fun uu____6192  ->
      match uu____6192 with
      | (lid,e) ->
          let uu____6199 =
            let uu____6200 = p_qlident lid  in
            let uu____6201 =
              let uu____6202 = p_noSeqTerm ps false e  in
              FStar_Pprint.op_Hat_Slash_Hat FStar_Pprint.equals uu____6202
               in
            FStar_Pprint.op_Hat_Slash_Hat uu____6200 uu____6201  in
          FStar_Pprint.group uu____6199

and (p_appTerm : FStar_Parser_AST.term -> FStar_Pprint.document) =
  fun e  ->
    match e.FStar_Parser_AST.tm with
    | FStar_Parser_AST.App uu____6204 when is_general_application e ->
        let uu____6211 = head_and_args e  in
        (match uu____6211 with
         | (head1,args) ->
             let uu____6236 =
               let uu____6247 = FStar_ST.op_Bang should_print_fs_typ_app  in
               if uu____6247
               then
                 let uu____6277 =
                   FStar_Util.take
                     (fun uu____6301  ->
                        match uu____6301 with
                        | (uu____6306,aq) -> aq = FStar_Parser_AST.FsTypApp)
                     args
                    in
                 match uu____6277 with
                 | (fs_typ_args,args1) ->
                     let uu____6344 =
                       let uu____6345 = p_indexingTerm head1  in
                       let uu____6346 =
                         let uu____6347 =
                           FStar_Pprint.op_Hat_Hat FStar_Pprint.comma break1
                            in
                         soft_surround_map_or_flow (Prims.parse_int "2")
                           (Prims.parse_int "0") FStar_Pprint.empty
                           FStar_Pprint.langle uu____6347 FStar_Pprint.rangle
                           p_fsTypArg fs_typ_args
                          in
                       FStar_Pprint.op_Hat_Hat uu____6345 uu____6346  in
                     (uu____6344, args1)
               else
                 (let uu____6359 = p_indexingTerm head1  in
                  (uu____6359, args))
                in
             (match uu____6236 with
              | (head_doc,args1) ->
                  let uu____6380 =
                    let uu____6381 =
                      FStar_Pprint.op_Hat_Hat head_doc FStar_Pprint.space  in
                    soft_surround_map_or_flow (Prims.parse_int "2")
                      (Prims.parse_int "0") head_doc uu____6381 break1
                      FStar_Pprint.empty p_argTerm args1
                     in
                  FStar_Pprint.group uu____6380))
    | FStar_Parser_AST.Construct (lid,args) when
        (is_general_construction e) &&
          (let uu____6401 = is_dtuple_constructor lid  in
           Prims.op_Negation uu____6401)
        ->
        (match args with
         | [] -> p_quident lid
         | arg::[] ->
             let uu____6419 =
               let uu____6420 = p_quident lid  in
               let uu____6421 = p_argTerm arg  in
               FStar_Pprint.op_Hat_Slash_Hat uu____6420 uu____6421  in
             FStar_Pprint.group uu____6419
         | hd1::tl1 ->
             let uu____6438 =
               let uu____6439 =
                 let uu____6440 =
                   let uu____6441 = p_quident lid  in
                   let uu____6442 = p_argTerm hd1  in
                   prefix2 uu____6441 uu____6442  in
                 FStar_Pprint.group uu____6440  in
               let uu____6443 =
                 let uu____6444 =
                   FStar_Pprint.separate_map break1 p_argTerm tl1  in
                 jump2 uu____6444  in
               FStar_Pprint.op_Hat_Hat uu____6439 uu____6443  in
             FStar_Pprint.group uu____6438)
    | uu____6449 -> p_indexingTerm e

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
         (let uu____6458 = p_indexingTerm e  in
          FStar_Pprint.surround (Prims.parse_int "2") (Prims.parse_int "1")
            FStar_Pprint.langle uu____6458 FStar_Pprint.rangle))
    | (e,FStar_Parser_AST.Hash ) ->
        let uu____6460 = str "#"  in
        let uu____6461 = p_indexingTerm e  in
        FStar_Pprint.op_Hat_Hat uu____6460 uu____6461
    | (e,FStar_Parser_AST.Nothing ) -> p_indexingTerm e

and (p_fsTypArg :
  (FStar_Parser_AST.term,FStar_Parser_AST.imp) FStar_Pervasives_Native.tuple2
    -> FStar_Pprint.document)
  =
  fun uu____6463  ->
    match uu____6463 with | (e,uu____6469) -> p_indexingTerm e

and (p_indexingTerm_aux :
  (FStar_Parser_AST.term -> FStar_Pprint.document) ->
    FStar_Parser_AST.term -> FStar_Pprint.document)
  =
  fun exit1  ->
    fun e  ->
      match e.FStar_Parser_AST.tm with
      | FStar_Parser_AST.Op
          ({ FStar_Ident.idText = ".()"; FStar_Ident.idRange = uu____6474;_},e1::e2::[])
          ->
          let uu____6479 =
            let uu____6480 = p_indexingTerm_aux p_atomicTermNotQUident e1  in
            let uu____6481 =
              let uu____6482 =
                let uu____6483 = p_term false false e2  in
                soft_parens_with_nesting uu____6483  in
              FStar_Pprint.op_Hat_Hat FStar_Pprint.dot uu____6482  in
            FStar_Pprint.op_Hat_Hat uu____6480 uu____6481  in
          FStar_Pprint.group uu____6479
      | FStar_Parser_AST.Op
          ({ FStar_Ident.idText = ".[]"; FStar_Ident.idRange = uu____6484;_},e1::e2::[])
          ->
          let uu____6489 =
            let uu____6490 = p_indexingTerm_aux p_atomicTermNotQUident e1  in
            let uu____6491 =
              let uu____6492 =
                let uu____6493 = p_term false false e2  in
                soft_brackets_with_nesting uu____6493  in
              FStar_Pprint.op_Hat_Hat FStar_Pprint.dot uu____6492  in
            FStar_Pprint.op_Hat_Hat uu____6490 uu____6491  in
          FStar_Pprint.group uu____6489
      | uu____6494 -> exit1 e

and (p_indexingTerm : FStar_Parser_AST.term -> FStar_Pprint.document) =
  fun e  -> p_indexingTerm_aux p_atomicTerm e

and (p_atomicTerm : FStar_Parser_AST.term -> FStar_Pprint.document) =
  fun e  ->
    match e.FStar_Parser_AST.tm with
    | FStar_Parser_AST.LetOpen (lid,e1) ->
        let uu____6499 = p_quident lid  in
        let uu____6500 =
          let uu____6501 =
            let uu____6502 = p_term false false e1  in
            soft_parens_with_nesting uu____6502  in
          FStar_Pprint.op_Hat_Hat FStar_Pprint.dot uu____6501  in
        FStar_Pprint.op_Hat_Hat uu____6499 uu____6500
    | FStar_Parser_AST.Name lid -> p_quident lid
    | FStar_Parser_AST.Op (op,e1::[]) when is_general_prefix_op op ->
        let uu____6508 = str (FStar_Ident.text_of_id op)  in
        let uu____6509 = p_atomicTerm e1  in
        FStar_Pprint.op_Hat_Hat uu____6508 uu____6509
    | uu____6510 -> p_atomicTermNotQUident e

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
         | uu____6517 -> p_constant c)
    | FStar_Parser_AST.Name lid when
        FStar_Ident.lid_equals lid FStar_Parser_Const.true_lid -> str "True"
    | FStar_Parser_AST.Name lid when
        FStar_Ident.lid_equals lid FStar_Parser_Const.false_lid ->
        str "False"
    | FStar_Parser_AST.Op (op,e1::[]) when is_general_prefix_op op ->
        let uu____6524 = str (FStar_Ident.text_of_id op)  in
        let uu____6525 = p_atomicTermNotQUident e1  in
        FStar_Pprint.op_Hat_Hat uu____6524 uu____6525
    | FStar_Parser_AST.Op (op,[]) ->
        let uu____6529 =
          let uu____6530 =
            let uu____6531 = str (FStar_Ident.text_of_id op)  in
            let uu____6532 =
              FStar_Pprint.op_Hat_Hat FStar_Pprint.space FStar_Pprint.rparen
               in
            FStar_Pprint.op_Hat_Hat uu____6531 uu____6532  in
          FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____6530  in
        FStar_Pprint.op_Hat_Hat FStar_Pprint.lparen uu____6529
    | FStar_Parser_AST.Construct (lid,args) when is_dtuple_constructor lid ->
        let uu____6547 =
          FStar_Pprint.op_Hat_Hat FStar_Pprint.lparen FStar_Pprint.bar  in
        let uu____6548 =
          let uu____6549 = FStar_Pprint.op_Hat_Hat FStar_Pprint.comma break1
             in
          let uu____6550 = FStar_List.map FStar_Pervasives_Native.fst args
             in
          FStar_Pprint.separate_map uu____6549 p_tmEq uu____6550  in
        let uu____6557 =
          FStar_Pprint.op_Hat_Hat FStar_Pprint.bar FStar_Pprint.rparen  in
        FStar_Pprint.surround (Prims.parse_int "2") (Prims.parse_int "1")
          uu____6547 uu____6548 uu____6557
    | FStar_Parser_AST.Project (e1,lid) ->
        let uu____6560 =
          let uu____6561 = p_atomicTermNotQUident e1  in
          let uu____6562 =
            let uu____6563 = p_qlident lid  in
            FStar_Pprint.op_Hat_Hat FStar_Pprint.dot uu____6563  in
          FStar_Pprint.prefix (Prims.parse_int "2") (Prims.parse_int "0")
            uu____6561 uu____6562
           in
        FStar_Pprint.group uu____6560
    | uu____6564 -> p_projectionLHS e

and (p_projectionLHS : FStar_Parser_AST.term -> FStar_Pprint.document) =
  fun e  ->
    match e.FStar_Parser_AST.tm with
    | FStar_Parser_AST.Var lid -> p_qlident lid
    | FStar_Parser_AST.Projector (constr_lid,field_lid) ->
        let uu____6569 = p_quident constr_lid  in
        let uu____6570 =
          let uu____6571 =
            let uu____6572 = p_lident field_lid  in
            FStar_Pprint.op_Hat_Hat FStar_Pprint.dot uu____6572  in
          FStar_Pprint.op_Hat_Hat FStar_Pprint.qmark uu____6571  in
        FStar_Pprint.op_Hat_Hat uu____6569 uu____6570
    | FStar_Parser_AST.Discrim constr_lid ->
        let uu____6574 = p_quident constr_lid  in
        FStar_Pprint.op_Hat_Hat uu____6574 FStar_Pprint.qmark
    | FStar_Parser_AST.Paren e1 ->
        let uu____6576 = p_term false false e1  in
        soft_parens_with_nesting uu____6576
    | uu____6577 when is_array e ->
        let es = extract_from_list e  in
        let uu____6581 =
          FStar_Pprint.op_Hat_Hat FStar_Pprint.lbracket FStar_Pprint.bar  in
        let uu____6582 =
          let uu____6583 = FStar_Pprint.op_Hat_Hat FStar_Pprint.semi break1
             in
          separate_map_or_flow_last uu____6583
            (fun ps  -> p_noSeqTerm ps false) es
           in
        let uu____6586 =
          FStar_Pprint.op_Hat_Hat FStar_Pprint.bar FStar_Pprint.rbracket  in
        FStar_Pprint.surround (Prims.parse_int "2") (Prims.parse_int "0")
          uu____6581 uu____6582 uu____6586
    | uu____6587 when is_list e ->
        let uu____6588 =
          let uu____6589 = FStar_Pprint.op_Hat_Hat FStar_Pprint.semi break1
             in
          let uu____6590 = extract_from_list e  in
          separate_map_or_flow_last uu____6589
            (fun ps  -> p_noSeqTerm ps false) uu____6590
           in
        FStar_Pprint.surround (Prims.parse_int "2") (Prims.parse_int "0")
          FStar_Pprint.lbracket uu____6588 FStar_Pprint.rbracket
    | uu____6595 when is_lex_list e ->
        let uu____6596 =
          FStar_Pprint.op_Hat_Hat FStar_Pprint.percent FStar_Pprint.lbracket
           in
        let uu____6597 =
          let uu____6598 = FStar_Pprint.op_Hat_Hat FStar_Pprint.semi break1
             in
          let uu____6599 = extract_from_list e  in
          separate_map_or_flow_last uu____6598
            (fun ps  -> p_noSeqTerm ps false) uu____6599
           in
        FStar_Pprint.surround (Prims.parse_int "2") (Prims.parse_int "1")
          uu____6596 uu____6597 FStar_Pprint.rbracket
    | uu____6604 when is_ref_set e ->
        let es = extract_from_ref_set e  in
        let uu____6608 =
          FStar_Pprint.op_Hat_Hat FStar_Pprint.bang FStar_Pprint.lbrace  in
        let uu____6609 =
          let uu____6610 = FStar_Pprint.op_Hat_Hat FStar_Pprint.comma break1
             in
          separate_map_or_flow uu____6610 p_appTerm es  in
        FStar_Pprint.surround (Prims.parse_int "2") (Prims.parse_int "0")
          uu____6608 uu____6609 FStar_Pprint.rbrace
    | FStar_Parser_AST.Labeled (e1,s,b) ->
        let uu____6614 = str (Prims.strcat "(*" (Prims.strcat s "*)"))  in
        let uu____6615 = p_term false false e1  in
        FStar_Pprint.op_Hat_Slash_Hat uu____6614 uu____6615
    | FStar_Parser_AST.Op (op,args) when
        let uu____6622 = handleable_op op args  in
        Prims.op_Negation uu____6622 ->
        let uu____6623 =
          let uu____6624 =
            let uu____6625 =
              let uu____6626 =
                let uu____6627 =
                  FStar_Util.string_of_int (FStar_List.length args)  in
                Prims.strcat uu____6627
                  " arguments couldn't be handled by the pretty printer"
                 in
              Prims.strcat " with " uu____6626  in
            Prims.strcat (FStar_Ident.text_of_id op) uu____6625  in
          Prims.strcat "Operation " uu____6624  in
        failwith uu____6623
    | FStar_Parser_AST.Uvar uu____6628 ->
        failwith "Unexpected universe variable out of universe context"
    | FStar_Parser_AST.Wild  ->
        let uu____6629 = p_term false false e  in
        soft_parens_with_nesting uu____6629
    | FStar_Parser_AST.Const uu____6630 ->
        let uu____6631 = p_term false false e  in
        soft_parens_with_nesting uu____6631
    | FStar_Parser_AST.Op uu____6632 ->
        let uu____6639 = p_term false false e  in
        soft_parens_with_nesting uu____6639
    | FStar_Parser_AST.Tvar uu____6640 ->
        let uu____6641 = p_term false false e  in
        soft_parens_with_nesting uu____6641
    | FStar_Parser_AST.Var uu____6642 ->
        let uu____6643 = p_term false false e  in
        soft_parens_with_nesting uu____6643
    | FStar_Parser_AST.Name uu____6644 ->
        let uu____6645 = p_term false false e  in
        soft_parens_with_nesting uu____6645
    | FStar_Parser_AST.Construct uu____6646 ->
        let uu____6657 = p_term false false e  in
        soft_parens_with_nesting uu____6657
    | FStar_Parser_AST.Abs uu____6658 ->
        let uu____6665 = p_term false false e  in
        soft_parens_with_nesting uu____6665
    | FStar_Parser_AST.App uu____6666 ->
        let uu____6673 = p_term false false e  in
        soft_parens_with_nesting uu____6673
    | FStar_Parser_AST.Let uu____6674 ->
        let uu____6695 = p_term false false e  in
        soft_parens_with_nesting uu____6695
    | FStar_Parser_AST.LetOpen uu____6696 ->
        let uu____6701 = p_term false false e  in
        soft_parens_with_nesting uu____6701
    | FStar_Parser_AST.Seq uu____6702 ->
        let uu____6707 = p_term false false e  in
        soft_parens_with_nesting uu____6707
    | FStar_Parser_AST.Bind uu____6708 ->
        let uu____6715 = p_term false false e  in
        soft_parens_with_nesting uu____6715
    | FStar_Parser_AST.If uu____6716 ->
        let uu____6723 = p_term false false e  in
        soft_parens_with_nesting uu____6723
    | FStar_Parser_AST.Match uu____6724 ->
        let uu____6739 = p_term false false e  in
        soft_parens_with_nesting uu____6739
    | FStar_Parser_AST.TryWith uu____6740 ->
        let uu____6755 = p_term false false e  in
        soft_parens_with_nesting uu____6755
    | FStar_Parser_AST.Ascribed uu____6756 ->
        let uu____6765 = p_term false false e  in
        soft_parens_with_nesting uu____6765
    | FStar_Parser_AST.Record uu____6766 ->
        let uu____6779 = p_term false false e  in
        soft_parens_with_nesting uu____6779
    | FStar_Parser_AST.Project uu____6780 ->
        let uu____6785 = p_term false false e  in
        soft_parens_with_nesting uu____6785
    | FStar_Parser_AST.Product uu____6786 ->
        let uu____6793 = p_term false false e  in
        soft_parens_with_nesting uu____6793
    | FStar_Parser_AST.Sum uu____6794 ->
        let uu____6801 = p_term false false e  in
        soft_parens_with_nesting uu____6801
    | FStar_Parser_AST.QForall uu____6802 ->
        let uu____6815 = p_term false false e  in
        soft_parens_with_nesting uu____6815
    | FStar_Parser_AST.QExists uu____6816 ->
        let uu____6829 = p_term false false e  in
        soft_parens_with_nesting uu____6829
    | FStar_Parser_AST.Refine uu____6830 ->
        let uu____6835 = p_term false false e  in
        soft_parens_with_nesting uu____6835
    | FStar_Parser_AST.NamedTyp uu____6836 ->
        let uu____6841 = p_term false false e  in
        soft_parens_with_nesting uu____6841
    | FStar_Parser_AST.Requires uu____6842 ->
        let uu____6849 = p_term false false e  in
        soft_parens_with_nesting uu____6849
    | FStar_Parser_AST.Ensures uu____6850 ->
        let uu____6857 = p_term false false e  in
        soft_parens_with_nesting uu____6857
    | FStar_Parser_AST.Attributes uu____6858 ->
        let uu____6861 = p_term false false e  in
        soft_parens_with_nesting uu____6861
    | FStar_Parser_AST.Quote uu____6862 ->
        let uu____6867 = p_term false false e  in
        soft_parens_with_nesting uu____6867
    | FStar_Parser_AST.VQuote uu____6868 ->
        let uu____6869 = p_term false false e  in
        soft_parens_with_nesting uu____6869

and (p_constant : FStar_Const.sconst -> FStar_Pprint.document) =
  fun uu___63_6870  ->
    match uu___63_6870 with
    | FStar_Const.Const_effect  -> str "Effect"
    | FStar_Const.Const_unit  -> str "()"
    | FStar_Const.Const_bool b -> FStar_Pprint.doc_of_bool b
    | FStar_Const.Const_float x -> str (FStar_Util.string_of_float x)
    | FStar_Const.Const_char x -> FStar_Pprint.doc_of_char x
    | FStar_Const.Const_string (s,uu____6875) ->
        let uu____6876 = str s  in FStar_Pprint.dquotes uu____6876
    | FStar_Const.Const_bytearray (bytes,uu____6878) ->
        let uu____6883 =
          let uu____6884 = str (FStar_Util.string_of_bytes bytes)  in
          FStar_Pprint.dquotes uu____6884  in
        let uu____6885 = str "B"  in
        FStar_Pprint.op_Hat_Hat uu____6883 uu____6885
    | FStar_Const.Const_int (repr,sign_width_opt) ->
        let signedness uu___61_6903 =
          match uu___61_6903 with
          | FStar_Const.Unsigned  -> str "u"
          | FStar_Const.Signed  -> FStar_Pprint.empty  in
        let width uu___62_6907 =
          match uu___62_6907 with
          | FStar_Const.Int8  -> str "y"
          | FStar_Const.Int16  -> str "s"
          | FStar_Const.Int32  -> str "l"
          | FStar_Const.Int64  -> str "L"  in
        let ending =
          default_or_map FStar_Pprint.empty
            (fun uu____6918  ->
               match uu____6918 with
               | (s,w) ->
                   let uu____6925 = signedness s  in
                   let uu____6926 = width w  in
                   FStar_Pprint.op_Hat_Hat uu____6925 uu____6926)
            sign_width_opt
           in
        let uu____6927 = str repr  in
        FStar_Pprint.op_Hat_Hat uu____6927 ending
    | FStar_Const.Const_range_of  -> str "range_of"
    | FStar_Const.Const_set_range_of  -> str "set_range_of"
    | FStar_Const.Const_range r ->
        let uu____6929 = FStar_Range.string_of_range r  in str uu____6929
    | FStar_Const.Const_reify  -> str "reify"
    | FStar_Const.Const_reflect lid ->
        let uu____6931 = p_quident lid  in
        let uu____6932 =
          let uu____6933 =
            let uu____6934 = str "reflect"  in
            FStar_Pprint.op_Hat_Hat FStar_Pprint.dot uu____6934  in
          FStar_Pprint.op_Hat_Hat FStar_Pprint.qmark uu____6933  in
        FStar_Pprint.op_Hat_Hat uu____6931 uu____6932

and (p_universe : FStar_Parser_AST.term -> FStar_Pprint.document) =
  fun u  ->
    let uu____6936 = str "u#"  in
    let uu____6937 = p_atomicUniverse u  in
    FStar_Pprint.op_Hat_Hat uu____6936 uu____6937

and (p_universeFrom : FStar_Parser_AST.term -> FStar_Pprint.document) =
  fun u  ->
    match u.FStar_Parser_AST.tm with
    | FStar_Parser_AST.Op
        ({ FStar_Ident.idText = "+"; FStar_Ident.idRange = uu____6939;_},u1::u2::[])
        ->
        let uu____6944 =
          let uu____6945 = p_universeFrom u1  in
          let uu____6946 =
            let uu____6947 = p_universeFrom u2  in
            FStar_Pprint.op_Hat_Slash_Hat FStar_Pprint.plus uu____6947  in
          FStar_Pprint.op_Hat_Slash_Hat uu____6945 uu____6946  in
        FStar_Pprint.group uu____6944
    | FStar_Parser_AST.App uu____6948 ->
        let uu____6955 = head_and_args u  in
        (match uu____6955 with
         | (head1,args) ->
             (match head1.FStar_Parser_AST.tm with
              | FStar_Parser_AST.Var maybe_max_lid when
                  FStar_Ident.lid_equals maybe_max_lid
                    FStar_Parser_Const.max_lid
                  ->
                  let uu____6981 =
                    let uu____6982 = p_qlident FStar_Parser_Const.max_lid  in
                    let uu____6983 =
                      FStar_Pprint.separate_map FStar_Pprint.space
                        (fun uu____6991  ->
                           match uu____6991 with
                           | (u1,uu____6997) -> p_atomicUniverse u1) args
                       in
                    op_Hat_Slash_Plus_Hat uu____6982 uu____6983  in
                  FStar_Pprint.group uu____6981
              | uu____6998 ->
                  let uu____6999 =
                    let uu____7000 = FStar_Parser_AST.term_to_string u  in
                    FStar_Util.format1 "Invalid term in universe context %s"
                      uu____7000
                     in
                  failwith uu____6999))
    | uu____7001 -> p_atomicUniverse u

and (p_atomicUniverse : FStar_Parser_AST.term -> FStar_Pprint.document) =
  fun u  ->
    match u.FStar_Parser_AST.tm with
    | FStar_Parser_AST.Wild  -> FStar_Pprint.underscore
    | FStar_Parser_AST.Const (FStar_Const.Const_int (r,sw)) ->
        p_constant (FStar_Const.Const_int (r, sw))
    | FStar_Parser_AST.Uvar id1 -> str (FStar_Ident.text_of_id id1)
    | FStar_Parser_AST.Paren u1 ->
        let uu____7025 = p_universeFrom u1  in
        soft_parens_with_nesting uu____7025
    | FStar_Parser_AST.Op
        ({ FStar_Ident.idText = "+"; FStar_Ident.idRange = uu____7026;_},uu____7027::uu____7028::[])
        ->
        let uu____7031 = p_universeFrom u  in
        soft_parens_with_nesting uu____7031
    | FStar_Parser_AST.App uu____7032 ->
        let uu____7039 = p_universeFrom u  in
        soft_parens_with_nesting uu____7039
    | uu____7040 ->
        let uu____7041 =
          let uu____7042 = FStar_Parser_AST.term_to_string u  in
          FStar_Util.format1 "Invalid term in universe context %s" uu____7042
           in
        failwith uu____7041

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
       | FStar_Parser_AST.Module (uu____7082,decls) ->
           let uu____7088 =
             FStar_All.pipe_right decls (FStar_List.map decl_to_document)  in
           FStar_All.pipe_right uu____7088
             (FStar_Pprint.separate FStar_Pprint.hardline)
       | FStar_Parser_AST.Interface (uu____7097,decls,uu____7099) ->
           let uu____7104 =
             FStar_All.pipe_right decls (FStar_List.map decl_to_document)  in
           FStar_All.pipe_right uu____7104
             (FStar_Pprint.separate FStar_Pprint.hardline)
        in
     FStar_ST.op_Colon_Equals should_print_fs_typ_app false; res)
  
let (comments_to_document :
  (Prims.string,FStar_Range.range) FStar_Pervasives_Native.tuple2 Prims.list
    -> FStar_Pprint.document)
  =
  fun comments  ->
    FStar_Pprint.separate_map FStar_Pprint.hardline
      (fun uu____7155  ->
         match uu____7155 with | (comment,range) -> str comment) comments
  
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
        | FStar_Parser_AST.Module (uu____7195,decls) -> decls
        | FStar_Parser_AST.Interface (uu____7201,decls,uu____7203) -> decls
         in
      FStar_ST.op_Colon_Equals should_print_fs_typ_app false;
      (match decls with
       | [] -> (FStar_Pprint.empty, comments)
       | d::ds ->
           let uu____7248 =
             match ds with
             | {
                 FStar_Parser_AST.d = FStar_Parser_AST.Pragma
                   (FStar_Parser_AST.LightOff );
                 FStar_Parser_AST.drange = uu____7261;
                 FStar_Parser_AST.doc = uu____7262;
                 FStar_Parser_AST.quals = uu____7263;
                 FStar_Parser_AST.attrs = uu____7264;_}::uu____7265 ->
                 let d0 = FStar_List.hd ds  in
                 let uu____7271 =
                   let uu____7274 =
                     let uu____7277 = FStar_List.tl ds  in d :: uu____7277
                      in
                   d0 :: uu____7274  in
                 (uu____7271, (d0.FStar_Parser_AST.drange))
             | uu____7282 -> ((d :: ds), (d.FStar_Parser_AST.drange))  in
           (match uu____7248 with
            | (decls1,first_range) ->
                let extract_decl_range d1 = d1.FStar_Parser_AST.drange  in
                (FStar_ST.op_Colon_Equals comment_stack comments;
                 (let initial_comment =
                    let uu____7340 = FStar_Range.start_of_range first_range
                       in
                    place_comments_until_pos (Prims.parse_int "0")
                      (Prims.parse_int "1") uu____7340 FStar_Pprint.empty
                     in
                  let doc1 =
                    separate_map_with_comments FStar_Pprint.empty
                      FStar_Pprint.empty decl_to_document decls1
                      extract_decl_range
                     in
                  let comments1 = FStar_ST.op_Bang comment_stack  in
                  FStar_ST.op_Colon_Equals comment_stack [];
                  FStar_ST.op_Colon_Equals should_print_fs_typ_app false;
                  (let uu____7436 =
                     FStar_Pprint.op_Hat_Hat initial_comment doc1  in
                   (uu____7436, comments1))))))
  