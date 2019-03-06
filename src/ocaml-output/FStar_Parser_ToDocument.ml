open Prims
let (min : Prims.int -> Prims.int -> Prims.int) =
  fun x  -> fun y  -> if x > y then y else x 
let (max : Prims.int -> Prims.int -> Prims.int) =
  fun x  -> fun y  -> if x > y then x else y 
let map_rev : 'a 'b . ('a -> 'b) -> 'a Prims.list -> 'b Prims.list =
  fun f  ->
    fun l  ->
      let rec aux l1 acc =
        match l1 with
        | [] -> acc
        | x::xs ->
            let uu____39574 = let uu____39577 = f x  in uu____39577 :: acc
               in
            aux xs uu____39574
         in
      aux l []
  
let rec map_if_all :
  'a 'b .
    ('a -> 'b FStar_Pervasives_Native.option) ->
      'a Prims.list -> 'b Prims.list FStar_Pervasives_Native.option
  =
  fun f  ->
    fun l  ->
      let rec aux l1 acc =
        match l1 with
        | [] -> acc
        | x::xs ->
            let uu____39644 = f x  in
            (match uu____39644 with
             | FStar_Pervasives_Native.Some r -> aux xs (r :: acc)
             | FStar_Pervasives_Native.None  -> [])
         in
      let r = aux l []  in
      if (FStar_List.length l) = (FStar_List.length r)
      then FStar_Pervasives_Native.Some r
      else FStar_Pervasives_Native.None
  
let rec all : 'a . ('a -> Prims.bool) -> 'a Prims.list -> Prims.bool =
  fun f  ->
    fun l  ->
      match l with
      | [] -> true
      | x::xs ->
          let uu____39700 = f x  in if uu____39700 then all f xs else false
  
let (all_explicit :
  (FStar_Parser_AST.term * FStar_Parser_AST.imp) Prims.list -> Prims.bool) =
  fun args  ->
    FStar_Util.for_all
      (fun uu___324_39733  ->
         match uu___324_39733 with
         | (uu____39739,FStar_Parser_AST.Nothing ) -> true
         | uu____39741 -> false) args
  
let (should_print_fs_typ_app : Prims.bool FStar_ST.ref) =
  FStar_Util.mk_ref false 
let (unfold_tuples : Prims.bool FStar_ST.ref) = FStar_Util.mk_ref true 
let with_fs_typ_app :
  'Auu____39770 'Auu____39771 .
    Prims.bool ->
      ('Auu____39770 -> 'Auu____39771) -> 'Auu____39770 -> 'Auu____39771
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
  'Auu____39881 'Auu____39882 .
    'Auu____39881 ->
      ('Auu____39882 -> 'Auu____39881) ->
        'Auu____39882 FStar_Pervasives_Native.option -> 'Auu____39881
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
  'Auu____39995 .
    FStar_Pprint.document ->
      ('Auu____39995 -> FStar_Pprint.document) ->
        'Auu____39995 Prims.list -> FStar_Pprint.document
  =
  fun sep  ->
    fun f  ->
      fun l  ->
        let uu____40020 =
          let uu____40021 =
            let uu____40022 = FStar_Pprint.op_Hat_Hat sep break1  in
            FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____40022  in
          FStar_Pprint.separate_map uu____40021 f l  in
        FStar_Pprint.group uu____40020
  
let precede_break_separate_map :
  'Auu____40034 .
    FStar_Pprint.document ->
      FStar_Pprint.document ->
        ('Auu____40034 -> FStar_Pprint.document) ->
          'Auu____40034 Prims.list -> FStar_Pprint.document
  =
  fun prec  ->
    fun sep  ->
      fun f  ->
        fun l  ->
          let uu____40064 =
            let uu____40065 = FStar_Pprint.op_Hat_Hat prec FStar_Pprint.space
               in
            let uu____40066 =
              let uu____40067 = FStar_List.hd l  in
              FStar_All.pipe_right uu____40067 f  in
            FStar_Pprint.precede uu____40065 uu____40066  in
          let uu____40068 =
            let uu____40069 = FStar_List.tl l  in
            FStar_Pprint.concat_map
              (fun x  ->
                 let uu____40075 =
                   let uu____40076 =
                     let uu____40077 = f x  in
                     FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____40077
                      in
                   FStar_Pprint.op_Hat_Hat sep uu____40076  in
                 FStar_Pprint.op_Hat_Hat break1 uu____40075) uu____40069
             in
          FStar_Pprint.op_Hat_Hat uu____40064 uu____40068
  
let concat_break_map :
  'Auu____40085 .
    ('Auu____40085 -> FStar_Pprint.document) ->
      'Auu____40085 Prims.list -> FStar_Pprint.document
  =
  fun f  ->
    fun l  ->
      let uu____40105 =
        FStar_Pprint.concat_map
          (fun x  ->
             let uu____40109 = f x  in
             FStar_Pprint.op_Hat_Hat uu____40109 break1) l
         in
      FStar_Pprint.group uu____40105
  
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
    let uu____40172 = str "begin"  in
    let uu____40174 = str "end"  in
    FStar_Pprint.soft_surround (Prims.parse_int "2") (Prims.parse_int "1")
      uu____40172 contents uu____40174
  
let separate_map_last :
  'Auu____40187 .
    FStar_Pprint.document ->
      (Prims.bool -> 'Auu____40187 -> FStar_Pprint.document) ->
        'Auu____40187 Prims.list -> FStar_Pprint.document
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
  'Auu____40239 .
    FStar_Pprint.document ->
      (Prims.bool -> 'Auu____40239 -> FStar_Pprint.document) ->
        'Auu____40239 Prims.list -> FStar_Pprint.document
  =
  fun sep  ->
    fun f  ->
      fun l  ->
        let uu____40271 =
          let uu____40272 =
            let uu____40273 = FStar_Pprint.op_Hat_Hat sep break1  in
            FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____40273  in
          separate_map_last uu____40272 f l  in
        FStar_Pprint.group uu____40271
  
let separate_map_or_flow :
  'Auu____40283 .
    FStar_Pprint.document ->
      ('Auu____40283 -> FStar_Pprint.document) ->
        'Auu____40283 Prims.list -> FStar_Pprint.document
  =
  fun sep  ->
    fun f  ->
      fun l  ->
        if (FStar_List.length l) < (Prims.parse_int "10")
        then FStar_Pprint.separate_map sep f l
        else FStar_Pprint.flow_map sep f l
  
let flow_map_last :
  'Auu____40321 .
    FStar_Pprint.document ->
      (Prims.bool -> 'Auu____40321 -> FStar_Pprint.document) ->
        'Auu____40321 Prims.list -> FStar_Pprint.document
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
  'Auu____40373 .
    FStar_Pprint.document ->
      (Prims.bool -> 'Auu____40373 -> FStar_Pprint.document) ->
        'Auu____40373 Prims.list -> FStar_Pprint.document
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
              let uu____40455 = FStar_Pprint.op_Hat_Slash_Hat doc1 doc3  in
              FStar_Pprint.group uu____40455
            else FStar_Pprint.surround n1 b doc1 doc2 doc3
  
let soft_surround_separate_map :
  'Auu____40477 .
    Prims.int ->
      Prims.int ->
        FStar_Pprint.document ->
          FStar_Pprint.document ->
            FStar_Pprint.document ->
              FStar_Pprint.document ->
                ('Auu____40477 -> FStar_Pprint.document) ->
                  'Auu____40477 Prims.list -> FStar_Pprint.document
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
                    (let uu____40536 = FStar_Pprint.separate_map sep f xs  in
                     FStar_Pprint.soft_surround n1 b opening uu____40536
                       closing)
  
let soft_surround_map_or_flow :
  'Auu____40556 .
    Prims.int ->
      Prims.int ->
        FStar_Pprint.document ->
          FStar_Pprint.document ->
            FStar_Pprint.document ->
              FStar_Pprint.document ->
                ('Auu____40556 -> FStar_Pprint.document) ->
                  'Auu____40556 Prims.list -> FStar_Pprint.document
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
                    (let uu____40615 = separate_map_or_flow sep f xs  in
                     FStar_Pprint.soft_surround n1 b opening uu____40615
                       closing)
  
let (doc_of_fsdoc :
  (Prims.string * (Prims.string * Prims.string) Prims.list) ->
    FStar_Pprint.document)
  =
  fun uu____40634  ->
    match uu____40634 with
    | (comment,keywords) ->
        let uu____40668 =
          let uu____40669 =
            let uu____40672 = str comment  in
            let uu____40673 =
              let uu____40676 =
                let uu____40679 =
                  FStar_Pprint.separate_map FStar_Pprint.comma
                    (fun uu____40690  ->
                       match uu____40690 with
                       | (k,v1) ->
                           let uu____40703 =
                             let uu____40706 = str k  in
                             let uu____40707 =
                               let uu____40710 =
                                 let uu____40713 = str v1  in [uu____40713]
                                  in
                               FStar_Pprint.rarrow :: uu____40710  in
                             uu____40706 :: uu____40707  in
                           FStar_Pprint.concat uu____40703) keywords
                   in
                [uu____40679]  in
              FStar_Pprint.space :: uu____40676  in
            uu____40672 :: uu____40673  in
          FStar_Pprint.concat uu____40669  in
        FStar_Pprint.group uu____40668
  
let (is_unit : FStar_Parser_AST.term -> Prims.bool) =
  fun e  ->
    match e.FStar_Parser_AST.tm with
    | FStar_Parser_AST.Const (FStar_Const.Const_unit ) -> true
    | uu____40723 -> false
  
let (matches_var : FStar_Parser_AST.term -> FStar_Ident.ident -> Prims.bool)
  =
  fun t  ->
    fun x  ->
      match t.FStar_Parser_AST.tm with
      | FStar_Parser_AST.Var y ->
          let uu____40739 = FStar_Ident.text_of_lid y  in
          x.FStar_Ident.idText = uu____40739
      | uu____40742 -> false
  
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
        | FStar_Parser_AST.Construct (lid,uu____40793::(e2,uu____40795)::[])
            -> (FStar_Ident.lid_equals lid cons_lid1) && (aux e2)
        | uu____40818 -> false  in
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
    | FStar_Parser_AST.Construct (uu____40842,[]) -> []
    | FStar_Parser_AST.Construct
        (uu____40853,(e1,FStar_Parser_AST.Nothing )::(e2,FStar_Parser_AST.Nothing
                                                      )::[])
        -> let uu____40874 = extract_from_list e2  in e1 :: uu____40874
    | uu____40877 ->
        let uu____40878 =
          let uu____40880 = FStar_Parser_AST.term_to_string e  in
          FStar_Util.format1 "Not a list %s" uu____40880  in
        failwith uu____40878
  
let (is_array : FStar_Parser_AST.term -> Prims.bool) =
  fun e  ->
    match e.FStar_Parser_AST.tm with
    | FStar_Parser_AST.App
        ({ FStar_Parser_AST.tm = FStar_Parser_AST.Var lid;
           FStar_Parser_AST.range = uu____40894;
           FStar_Parser_AST.level = uu____40895;_},l,FStar_Parser_AST.Nothing
         )
        ->
        (FStar_Ident.lid_equals lid FStar_Parser_Const.array_mk_array_lid) &&
          (is_list l)
    | uu____40897 -> false
  
let rec (is_ref_set : FStar_Parser_AST.term -> Prims.bool) =
  fun e  ->
    match e.FStar_Parser_AST.tm with
    | FStar_Parser_AST.Var maybe_empty_lid ->
        FStar_Ident.lid_equals maybe_empty_lid FStar_Parser_Const.set_empty
    | FStar_Parser_AST.App
        ({ FStar_Parser_AST.tm = FStar_Parser_AST.Var maybe_singleton_lid;
           FStar_Parser_AST.range = uu____40909;
           FStar_Parser_AST.level = uu____40910;_},{
                                                     FStar_Parser_AST.tm =
                                                       FStar_Parser_AST.App
                                                       ({
                                                          FStar_Parser_AST.tm
                                                            =
                                                            FStar_Parser_AST.Var
                                                            maybe_addr_of_lid;
                                                          FStar_Parser_AST.range
                                                            = uu____40912;
                                                          FStar_Parser_AST.level
                                                            = uu____40913;_},e1,FStar_Parser_AST.Nothing
                                                        );
                                                     FStar_Parser_AST.range =
                                                       uu____40915;
                                                     FStar_Parser_AST.level =
                                                       uu____40916;_},FStar_Parser_AST.Nothing
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
                FStar_Parser_AST.range = uu____40918;
                FStar_Parser_AST.level = uu____40919;_},e1,FStar_Parser_AST.Nothing
              );
           FStar_Parser_AST.range = uu____40921;
           FStar_Parser_AST.level = uu____40922;_},e2,FStar_Parser_AST.Nothing
         )
        ->
        ((FStar_Ident.lid_equals maybe_union_lid FStar_Parser_Const.set_union)
           && (is_ref_set e1))
          && (is_ref_set e2)
    | uu____40924 -> false
  
let rec (extract_from_ref_set :
  FStar_Parser_AST.term -> FStar_Parser_AST.term Prims.list) =
  fun e  ->
    match e.FStar_Parser_AST.tm with
    | FStar_Parser_AST.Var uu____40936 -> []
    | FStar_Parser_AST.App
        ({ FStar_Parser_AST.tm = FStar_Parser_AST.Var uu____40937;
           FStar_Parser_AST.range = uu____40938;
           FStar_Parser_AST.level = uu____40939;_},{
                                                     FStar_Parser_AST.tm =
                                                       FStar_Parser_AST.App
                                                       ({
                                                          FStar_Parser_AST.tm
                                                            =
                                                            FStar_Parser_AST.Var
                                                            uu____40940;
                                                          FStar_Parser_AST.range
                                                            = uu____40941;
                                                          FStar_Parser_AST.level
                                                            = uu____40942;_},e1,FStar_Parser_AST.Nothing
                                                        );
                                                     FStar_Parser_AST.range =
                                                       uu____40944;
                                                     FStar_Parser_AST.level =
                                                       uu____40945;_},FStar_Parser_AST.Nothing
         )
        -> [e1]
    | FStar_Parser_AST.App
        ({
           FStar_Parser_AST.tm = FStar_Parser_AST.App
             ({ FStar_Parser_AST.tm = FStar_Parser_AST.Var uu____40946;
                FStar_Parser_AST.range = uu____40947;
                FStar_Parser_AST.level = uu____40948;_},e1,FStar_Parser_AST.Nothing
              );
           FStar_Parser_AST.range = uu____40950;
           FStar_Parser_AST.level = uu____40951;_},e2,FStar_Parser_AST.Nothing
         )
        ->
        let uu____40953 = extract_from_ref_set e1  in
        let uu____40956 = extract_from_ref_set e2  in
        FStar_List.append uu____40953 uu____40956
    | uu____40959 ->
        let uu____40960 =
          let uu____40962 = FStar_Parser_AST.term_to_string e  in
          FStar_Util.format1 "Not a ref set %s" uu____40962  in
        failwith uu____40960
  
let (is_general_application : FStar_Parser_AST.term -> Prims.bool) =
  fun e  ->
    let uu____40974 = (is_array e) || (is_ref_set e)  in
    Prims.op_Negation uu____40974
  
let (is_general_construction : FStar_Parser_AST.term -> Prims.bool) =
  fun e  ->
    let uu____40983 = (is_list e) || (is_lex_list e)  in
    Prims.op_Negation uu____40983
  
let (is_general_prefix_op : FStar_Ident.ident -> Prims.bool) =
  fun op  ->
    let op_starting_char =
      let uu____40994 = FStar_Ident.text_of_id op  in
      FStar_Util.char_at uu____40994 (Prims.parse_int "0")  in
    ((op_starting_char = 33) || (op_starting_char = 63)) ||
      ((op_starting_char = 126) &&
         (let uu____41004 = FStar_Ident.text_of_id op  in uu____41004 <> "~"))
  
let (head_and_args :
  FStar_Parser_AST.term ->
    (FStar_Parser_AST.term * (FStar_Parser_AST.term * FStar_Parser_AST.imp)
      Prims.list))
  =
  fun e  ->
    let rec aux e1 acc =
      match e1.FStar_Parser_AST.tm with
      | FStar_Parser_AST.App (head1,arg,imp) -> aux head1 ((arg, imp) :: acc)
      | uu____41074 -> (e1, acc)  in
    aux e []
  
type associativity =
  | Left 
  | Right 
  | NonAssoc 
let (uu___is_Left : associativity -> Prims.bool) =
  fun projectee  ->
    match projectee with | Left  -> true | uu____41094 -> false
  
let (uu___is_Right : associativity -> Prims.bool) =
  fun projectee  ->
    match projectee with | Right  -> true | uu____41105 -> false
  
let (uu___is_NonAssoc : associativity -> Prims.bool) =
  fun projectee  ->
    match projectee with | NonAssoc  -> true | uu____41116 -> false
  
type token = (FStar_Char.char,Prims.string) FStar_Util.either
type associativity_level = (associativity * token Prims.list)
let (token_to_string :
  (FStar_BaseTypes.char,Prims.string) FStar_Util.either -> Prims.string) =
  fun uu___325_41142  ->
    match uu___325_41142 with
    | FStar_Util.Inl c -> Prims.op_Hat (FStar_Util.string_of_char c) ".*"
    | FStar_Util.Inr s -> s
  
let (matches_token :
  Prims.string ->
    (FStar_Char.char,Prims.string) FStar_Util.either -> Prims.bool)
  =
  fun s  ->
    fun uu___326_41177  ->
      match uu___326_41177 with
      | FStar_Util.Inl c ->
          let uu____41190 = FStar_String.get s (Prims.parse_int "0")  in
          uu____41190 = c
      | FStar_Util.Inr s' -> s = s'
  
let matches_level :
  'Auu____41206 .
    Prims.string ->
      ('Auu____41206 * (FStar_Char.char,Prims.string) FStar_Util.either
        Prims.list) -> Prims.bool
  =
  fun s  ->
    fun uu____41230  ->
      match uu____41230 with
      | (assoc_levels,tokens) ->
          let uu____41262 = FStar_List.tryFind (matches_token s) tokens  in
          uu____41262 <> FStar_Pervasives_Native.None
  
let (opinfix4 : associativity_level) = (Right, [FStar_Util.Inr "**"]) 
let (opinfix3 : associativity_level) =
  (Left, [FStar_Util.Inl 42; FStar_Util.Inl 47; FStar_Util.Inl 37]) 
let (opinfix2 : associativity_level) =
  (Left, [FStar_Util.Inl 43; FStar_Util.Inl 45]) 
let (minus_lvl : associativity_level) = (Left, [FStar_Util.Inr "-"]) 
let (opinfix1 : associativity_level) =
  (Right, [FStar_Util.Inl 64; FStar_Util.Inl 94]) 
let (pipe_right : associativity_level) = (Left, [FStar_Util.Inr "|>"]) 
let (opinfix0d : associativity_level) = (Left, [FStar_Util.Inl 36]) 
let (opinfix0c : associativity_level) =
  (Left, [FStar_Util.Inl 61; FStar_Util.Inl 60; FStar_Util.Inl 62]) 
let (equal : associativity_level) = (Left, [FStar_Util.Inr "="]) 
let (opinfix0b : associativity_level) = (Left, [FStar_Util.Inl 38]) 
let (opinfix0a : associativity_level) = (Left, [FStar_Util.Inl 124]) 
let (colon_equals : associativity_level) = (NonAssoc, [FStar_Util.Inr ":="]) 
let (amp : associativity_level) = (Right, [FStar_Util.Inr "&"]) 
let (colon_colon : associativity_level) = (Right, [FStar_Util.Inr "::"]) 
let (level_associativity_spec : associativity_level Prims.list) =
  [opinfix4;
  opinfix3;
  opinfix2;
  opinfix1;
  pipe_right;
  opinfix0d;
  opinfix0c;
  opinfix0b;
  opinfix0a;
  colon_equals;
  amp;
  colon_colon] 
let (level_table :
  ((Prims.int * Prims.int * Prims.int) * token Prims.list) Prims.list) =
  let levels_from_associativity l uu___327_41434 =
    match uu___327_41434 with
    | Left  -> (l, l, (l - (Prims.parse_int "1")))
    | Right  -> ((l - (Prims.parse_int "1")), l, l)
    | NonAssoc  ->
        ((l - (Prims.parse_int "1")), l, (l - (Prims.parse_int "1")))
     in
  FStar_List.mapi
    (fun i  ->
       fun uu____41484  ->
         match uu____41484 with
         | (assoc1,tokens) -> ((levels_from_associativity i assoc1), tokens))
    level_associativity_spec
  
let (assign_levels :
  associativity_level Prims.list ->
    Prims.string -> (Prims.int * Prims.int * Prims.int))
  =
  fun token_associativity_spec  ->
    fun s  ->
      let uu____41559 = FStar_List.tryFind (matches_level s) level_table  in
      match uu____41559 with
      | FStar_Pervasives_Native.Some (assoc_levels,uu____41611) ->
          assoc_levels
      | uu____41649 -> failwith (Prims.op_Hat "Unrecognized operator " s)
  
let max_level :
  'Auu____41682 . ('Auu____41682 * token Prims.list) Prims.list -> Prims.int
  =
  fun l  ->
    let find_level_and_max n1 level =
      let uu____41731 =
        FStar_List.tryFind
          (fun uu____41767  ->
             match uu____41767 with
             | (uu____41784,tokens) ->
                 tokens = (FStar_Pervasives_Native.snd level)) level_table
         in
      match uu____41731 with
      | FStar_Pervasives_Native.Some
          ((uu____41813,l1,uu____41815),uu____41816) -> max n1 l1
      | FStar_Pervasives_Native.None  ->
          let uu____41866 =
            let uu____41868 =
              let uu____41870 =
                FStar_List.map token_to_string
                  (FStar_Pervasives_Native.snd level)
                 in
              FStar_String.concat "," uu____41870  in
            FStar_Util.format1 "Undefined associativity level %s" uu____41868
             in
          failwith uu____41866
       in
    FStar_List.fold_left find_level_and_max (Prims.parse_int "0") l
  
let (levels : Prims.string -> (Prims.int * Prims.int * Prims.int)) =
  fun op  ->
    let uu____41905 = assign_levels level_associativity_spec op  in
    match uu____41905 with
    | (left1,mine,right1) ->
        if op = "*"
        then ((left1 - (Prims.parse_int "1")), mine, right1)
        else (left1, mine, right1)
  
let (operatorInfix0ad12 : associativity_level Prims.list) =
  [opinfix0a; opinfix0b; opinfix0c; opinfix0d; opinfix1; opinfix2] 
let (is_operatorInfix0ad12 : FStar_Ident.ident -> Prims.bool) =
  fun op  ->
    let uu____41964 =
      let uu____41967 =
        let uu____41973 = FStar_Ident.text_of_id op  in
        FStar_All.pipe_left matches_level uu____41973  in
      FStar_List.tryFind uu____41967 operatorInfix0ad12  in
    uu____41964 <> FStar_Pervasives_Native.None
  
let (is_operatorInfix34 : FStar_Ident.ident -> Prims.bool) =
  let opinfix34 = [opinfix3; opinfix4]  in
  fun op  ->
    let uu____42040 =
      let uu____42055 =
        let uu____42073 = FStar_Ident.text_of_id op  in
        FStar_All.pipe_left matches_level uu____42073  in
      FStar_List.tryFind uu____42055 opinfix34  in
    uu____42040 <> FStar_Pervasives_Native.None
  
let (handleable_args_length : FStar_Ident.ident -> Prims.int) =
  fun op  ->
    let op_s = FStar_Ident.text_of_id op  in
    let uu____42139 =
      (is_general_prefix_op op) || (FStar_List.mem op_s ["-"; "~"])  in
    if uu____42139
    then (Prims.parse_int "1")
    else
      (let uu____42152 =
         ((is_operatorInfix0ad12 op) || (is_operatorInfix34 op)) ||
           (FStar_List.mem op_s
              ["<==>"; "==>"; "\\/"; "/\\"; "="; "|>"; ":="; ".()"; ".[]"])
          in
       if uu____42152
       then (Prims.parse_int "2")
       else
         if FStar_List.mem op_s [".()<-"; ".[]<-"]
         then (Prims.parse_int "3")
         else (Prims.parse_int "0"))
  
let handleable_op :
  'Auu____42198 . FStar_Ident.ident -> 'Auu____42198 Prims.list -> Prims.bool
  =
  fun op  ->
    fun args  ->
      match FStar_List.length args with
      | _42214 when _42214 = (Prims.parse_int "0") -> true
      | _42216 when _42216 = (Prims.parse_int "1") ->
          (is_general_prefix_op op) ||
            (let uu____42218 = FStar_Ident.text_of_id op  in
             FStar_List.mem uu____42218 ["-"; "~"])
      | _42226 when _42226 = (Prims.parse_int "2") ->
          ((is_operatorInfix0ad12 op) || (is_operatorInfix34 op)) ||
            (let uu____42228 = FStar_Ident.text_of_id op  in
             FStar_List.mem uu____42228
               ["<==>"; "==>"; "\\/"; "/\\"; "="; "|>"; ":="; ".()"; ".[]"])
      | _42250 when _42250 = (Prims.parse_int "3") ->
          let uu____42251 = FStar_Ident.text_of_id op  in
          FStar_List.mem uu____42251 [".()<-"; ".[]<-"]
      | uu____42259 -> false
  
type annotation_style =
  | Binders of (Prims.int * Prims.int * Prims.bool) 
  | Arrows of (Prims.int * Prims.int) 
let (uu___is_Binders : annotation_style -> Prims.bool) =
  fun projectee  ->
    match projectee with | Binders _0 -> true | uu____42305 -> false
  
let (__proj__Binders__item___0 :
  annotation_style -> (Prims.int * Prims.int * Prims.bool)) =
  fun projectee  -> match projectee with | Binders _0 -> _0 
let (uu___is_Arrows : annotation_style -> Prims.bool) =
  fun projectee  ->
    match projectee with | Arrows _0 -> true | uu____42358 -> false
  
let (__proj__Arrows__item___0 : annotation_style -> (Prims.int * Prims.int))
  = fun projectee  -> match projectee with | Arrows _0 -> _0 
let (all_binders_annot : FStar_Parser_AST.term -> Prims.bool) =
  fun e  ->
    let is_binder_annot b =
      match b.FStar_Parser_AST.b with
      | FStar_Parser_AST.Annotated uu____42401 -> true
      | uu____42407 -> false  in
    let rec all_binders e1 l =
      match e1.FStar_Parser_AST.tm with
      | FStar_Parser_AST.Product (bs,tgt) ->
          let uu____42440 = FStar_List.for_all is_binder_annot bs  in
          if uu____42440
          then all_binders tgt (l + (FStar_List.length bs))
          else (false, (Prims.parse_int "0"))
      | uu____42455 -> (true, (l + (Prims.parse_int "1")))  in
    let uu____42460 = all_binders e (Prims.parse_int "0")  in
    match uu____42460 with
    | (b,l) -> if b && (l > (Prims.parse_int "1")) then true else false
  
type catf =
  FStar_Pprint.document -> FStar_Pprint.document -> FStar_Pprint.document
let (cat_with_colon :
  FStar_Pprint.document -> FStar_Pprint.document -> FStar_Pprint.document) =
  fun x  ->
    fun y  ->
      let uu____42499 = FStar_Pprint.op_Hat_Slash_Hat FStar_Pprint.colon y
         in
      FStar_Pprint.op_Hat_Hat x uu____42499
  
let (comment_stack :
  (Prims.string * FStar_Range.range) Prims.list FStar_ST.ref) =
  FStar_Util.mk_ref [] 
type decl_meta =
  {
  r: FStar_Range.range ;
  has_qs: Prims.bool ;
  has_attrs: Prims.bool ;
  has_fsdoc: Prims.bool ;
  is_fsdoc: Prims.bool }
let (__proj__Mkdecl_meta__item__r : decl_meta -> FStar_Range.range) =
  fun projectee  ->
    match projectee with
    | { r; has_qs; has_attrs; has_fsdoc; is_fsdoc;_} -> r
  
let (__proj__Mkdecl_meta__item__has_qs : decl_meta -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | { r; has_qs; has_attrs; has_fsdoc; is_fsdoc;_} -> has_qs
  
let (__proj__Mkdecl_meta__item__has_attrs : decl_meta -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | { r; has_qs; has_attrs; has_fsdoc; is_fsdoc;_} -> has_attrs
  
let (__proj__Mkdecl_meta__item__has_fsdoc : decl_meta -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | { r; has_qs; has_attrs; has_fsdoc; is_fsdoc;_} -> has_fsdoc
  
let (__proj__Mkdecl_meta__item__is_fsdoc : decl_meta -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | { r; has_qs; has_attrs; has_fsdoc; is_fsdoc;_} -> is_fsdoc
  
let (dummy_meta : decl_meta) =
  {
    r = FStar_Range.dummyRange;
    has_qs = false;
    has_attrs = false;
    has_fsdoc = false;
    is_fsdoc = false
  } 
let with_comment :
  'Auu____42648 .
    ('Auu____42648 -> FStar_Pprint.document) ->
      'Auu____42648 -> FStar_Range.range -> FStar_Pprint.document
  =
  fun printer  ->
    fun tm  ->
      fun tmrange  ->
        let rec comments_before_pos acc print_pos lookahead_pos =
          let uu____42690 = FStar_ST.op_Bang comment_stack  in
          match uu____42690 with
          | [] -> (acc, false)
          | (c,crange)::cs ->
              let comment =
                let uu____42761 = str c  in
                FStar_Pprint.op_Hat_Hat uu____42761 FStar_Pprint.hardline  in
              let uu____42762 = FStar_Range.range_before_pos crange print_pos
                 in
              if uu____42762
              then
                (FStar_ST.op_Colon_Equals comment_stack cs;
                 (let uu____42804 = FStar_Pprint.op_Hat_Hat acc comment  in
                  comments_before_pos uu____42804 print_pos lookahead_pos))
              else
                (let uu____42807 =
                   FStar_Range.range_before_pos crange lookahead_pos  in
                 (acc, uu____42807))
           in
        let uu____42810 =
          let uu____42816 =
            let uu____42817 = FStar_Range.start_of_range tmrange  in
            FStar_Range.end_of_line uu____42817  in
          let uu____42818 = FStar_Range.end_of_range tmrange  in
          comments_before_pos FStar_Pprint.empty uu____42816 uu____42818  in
        match uu____42810 with
        | (comments,has_lookahead) ->
            let printed_e = printer tm  in
            let comments1 =
              if has_lookahead
              then
                let pos = FStar_Range.end_of_range tmrange  in
                let uu____42827 = comments_before_pos comments pos pos  in
                FStar_Pervasives_Native.fst uu____42827
              else comments  in
            if comments1 = FStar_Pprint.empty
            then printed_e
            else
              (let uu____42839 = FStar_Pprint.op_Hat_Hat comments1 printed_e
                  in
               FStar_Pprint.group uu____42839)
  
let with_comment_sep :
  'Auu____42851 'Auu____42852 .
    ('Auu____42851 -> 'Auu____42852) ->
      'Auu____42851 ->
        FStar_Range.range -> (FStar_Pprint.document * 'Auu____42852)
  =
  fun printer  ->
    fun tm  ->
      fun tmrange  ->
        let rec comments_before_pos acc print_pos lookahead_pos =
          let uu____42898 = FStar_ST.op_Bang comment_stack  in
          match uu____42898 with
          | [] -> (acc, false)
          | (c,crange)::cs ->
              let comment = str c  in
              let uu____42969 = FStar_Range.range_before_pos crange print_pos
                 in
              if uu____42969
              then
                (FStar_ST.op_Colon_Equals comment_stack cs;
                 (let uu____43011 =
                    if acc = FStar_Pprint.empty
                    then comment
                    else
                      (let uu____43015 =
                         FStar_Pprint.op_Hat_Hat FStar_Pprint.hardline
                           comment
                          in
                       FStar_Pprint.op_Hat_Hat acc uu____43015)
                     in
                  comments_before_pos uu____43011 print_pos lookahead_pos))
              else
                (let uu____43018 =
                   FStar_Range.range_before_pos crange lookahead_pos  in
                 (acc, uu____43018))
           in
        let uu____43021 =
          let uu____43027 =
            let uu____43028 = FStar_Range.start_of_range tmrange  in
            FStar_Range.end_of_line uu____43028  in
          let uu____43029 = FStar_Range.end_of_range tmrange  in
          comments_before_pos FStar_Pprint.empty uu____43027 uu____43029  in
        match uu____43021 with
        | (comments,has_lookahead) ->
            let printed_e = printer tm  in
            let comments1 =
              if has_lookahead
              then
                let pos = FStar_Range.end_of_range tmrange  in
                let uu____43042 = comments_before_pos comments pos pos  in
                FStar_Pervasives_Native.fst uu____43042
              else comments  in
            (comments1, printed_e)
  
let rec (place_comments_until_pos :
  Prims.int ->
    Prims.int ->
      FStar_Range.pos ->
        decl_meta ->
          FStar_Pprint.document ->
            Prims.bool -> Prims.bool -> FStar_Pprint.document)
  =
  fun k  ->
    fun lbegin  ->
      fun pos  ->
        fun meta_decl  ->
          fun doc1  ->
            fun r  ->
              fun init1  ->
                let uu____43095 = FStar_ST.op_Bang comment_stack  in
                match uu____43095 with
                | (comment,crange)::cs when
                    FStar_Range.range_before_pos crange pos ->
                    (FStar_ST.op_Colon_Equals comment_stack cs;
                     (let lnum =
                        let uu____43189 =
                          let uu____43191 =
                            let uu____43193 =
                              FStar_Range.start_of_range crange  in
                            FStar_Range.line_of_pos uu____43193  in
                          uu____43191 - lbegin  in
                        max k uu____43189  in
                      let lnum1 = min (Prims.parse_int "2") lnum  in
                      let doc2 =
                        let uu____43198 =
                          let uu____43199 =
                            FStar_Pprint.repeat lnum1 FStar_Pprint.hardline
                             in
                          let uu____43200 = str comment  in
                          FStar_Pprint.op_Hat_Hat uu____43199 uu____43200  in
                        FStar_Pprint.op_Hat_Hat doc1 uu____43198  in
                      let uu____43201 =
                        let uu____43203 = FStar_Range.end_of_range crange  in
                        FStar_Range.line_of_pos uu____43203  in
                      place_comments_until_pos (Prims.parse_int "1")
                        uu____43201 pos meta_decl doc2 true init1))
                | uu____43206 ->
                    if doc1 = FStar_Pprint.empty
                    then FStar_Pprint.empty
                    else
                      (let lnum =
                         let uu____43219 = FStar_Range.line_of_pos pos  in
                         uu____43219 - lbegin  in
                       let lnum1 = min (Prims.parse_int "3") lnum  in
                       let lnum2 =
                         if meta_decl.has_qs || meta_decl.has_attrs
                         then lnum1 - (Prims.parse_int "1")
                         else lnum1  in
                       let lnum3 = max k lnum2  in
                       let lnum4 =
                         if meta_decl.has_qs && meta_decl.has_attrs
                         then (Prims.parse_int "2")
                         else lnum3  in
                       let lnum5 =
                         if (Prims.op_Negation r) && meta_decl.has_fsdoc
                         then min (Prims.parse_int "2") lnum4
                         else lnum4  in
                       let lnum6 =
                         if r && (meta_decl.is_fsdoc || meta_decl.has_fsdoc)
                         then (Prims.parse_int "1")
                         else lnum5  in
                       let lnum7 =
                         if init1 then (Prims.parse_int "2") else lnum6  in
                       let uu____43261 =
                         FStar_Pprint.repeat lnum7 FStar_Pprint.hardline  in
                       FStar_Pprint.op_Hat_Hat doc1 uu____43261)
  
let separate_map_with_comments :
  'Auu____43275 .
    FStar_Pprint.document ->
      FStar_Pprint.document ->
        ('Auu____43275 -> FStar_Pprint.document) ->
          'Auu____43275 Prims.list ->
            ('Auu____43275 -> decl_meta) -> FStar_Pprint.document
  =
  fun prefix1  ->
    fun sep  ->
      fun f  ->
        fun xs  ->
          fun extract_meta  ->
            let fold_fun uu____43334 x =
              match uu____43334 with
              | (last_line,doc1) ->
                  let meta_decl = extract_meta x  in
                  let r = meta_decl.r  in
                  let doc2 =
                    let uu____43353 = FStar_Range.start_of_range r  in
                    place_comments_until_pos (Prims.parse_int "1") last_line
                      uu____43353 meta_decl doc1 false false
                     in
                  let uu____43357 =
                    let uu____43359 = FStar_Range.end_of_range r  in
                    FStar_Range.line_of_pos uu____43359  in
                  let uu____43360 =
                    let uu____43361 =
                      let uu____43362 = f x  in
                      FStar_Pprint.op_Hat_Hat sep uu____43362  in
                    FStar_Pprint.op_Hat_Hat doc2 uu____43361  in
                  (uu____43357, uu____43360)
               in
            let uu____43364 =
              let uu____43371 = FStar_List.hd xs  in
              let uu____43372 = FStar_List.tl xs  in
              (uu____43371, uu____43372)  in
            match uu____43364 with
            | (x,xs1) ->
                let init1 =
                  let meta_decl = extract_meta x  in
                  let uu____43390 =
                    let uu____43392 = FStar_Range.end_of_range meta_decl.r
                       in
                    FStar_Range.line_of_pos uu____43392  in
                  let uu____43393 =
                    let uu____43394 = f x  in
                    FStar_Pprint.op_Hat_Hat prefix1 uu____43394  in
                  (uu____43390, uu____43393)  in
                let uu____43396 = FStar_List.fold_left fold_fun init1 xs1  in
                FStar_Pervasives_Native.snd uu____43396
  
let separate_map_with_comments_kw :
  'Auu____43423 'Auu____43424 .
    'Auu____43423 ->
      'Auu____43423 ->
        ('Auu____43423 -> 'Auu____43424 -> FStar_Pprint.document) ->
          'Auu____43424 Prims.list ->
            ('Auu____43424 -> decl_meta) -> FStar_Pprint.document
  =
  fun prefix1  ->
    fun sep  ->
      fun f  ->
        fun xs  ->
          fun extract_meta  ->
            let fold_fun uu____43488 x =
              match uu____43488 with
              | (last_line,doc1) ->
                  let meta_decl = extract_meta x  in
                  let r = meta_decl.r  in
                  let doc2 =
                    let uu____43507 = FStar_Range.start_of_range r  in
                    place_comments_until_pos (Prims.parse_int "1") last_line
                      uu____43507 meta_decl doc1 false false
                     in
                  let uu____43511 =
                    let uu____43513 = FStar_Range.end_of_range r  in
                    FStar_Range.line_of_pos uu____43513  in
                  let uu____43514 =
                    let uu____43515 = f sep x  in
                    FStar_Pprint.op_Hat_Hat doc2 uu____43515  in
                  (uu____43511, uu____43514)
               in
            let uu____43517 =
              let uu____43524 = FStar_List.hd xs  in
              let uu____43525 = FStar_List.tl xs  in
              (uu____43524, uu____43525)  in
            match uu____43517 with
            | (x,xs1) ->
                let init1 =
                  let meta_decl = extract_meta x  in
                  let uu____43543 =
                    let uu____43545 = FStar_Range.end_of_range meta_decl.r
                       in
                    FStar_Range.line_of_pos uu____43545  in
                  let uu____43546 = f prefix1 x  in
                  (uu____43543, uu____43546)  in
                let uu____43548 = FStar_List.fold_left fold_fun init1 xs1  in
                FStar_Pervasives_Native.snd uu____43548
  
let rec (p_decl : FStar_Parser_AST.decl -> FStar_Pprint.document) =
  fun d  ->
    let qualifiers =
      match ((d.FStar_Parser_AST.quals), (d.FStar_Parser_AST.d)) with
      | ((FStar_Parser_AST.Assumption )::[],FStar_Parser_AST.Assume
         (id1,uu____44534)) ->
          let uu____44537 =
            let uu____44539 =
              FStar_Util.char_at id1.FStar_Ident.idText (Prims.parse_int "0")
               in
            FStar_All.pipe_right uu____44539 FStar_Util.is_upper  in
          if uu____44537
          then
            let uu____44545 = p_qualifier FStar_Parser_AST.Assumption  in
            FStar_Pprint.op_Hat_Hat uu____44545 FStar_Pprint.space
          else p_qualifiers d.FStar_Parser_AST.quals
      | uu____44548 -> p_qualifiers d.FStar_Parser_AST.quals  in
    let uu____44555 =
      FStar_Pprint.optional (fun d1  -> p_fsdoc d1) d.FStar_Parser_AST.doc
       in
    let uu____44558 =
      let uu____44559 = p_attributes d.FStar_Parser_AST.attrs  in
      let uu____44560 =
        let uu____44561 = p_rawDecl d  in
        FStar_Pprint.op_Hat_Hat qualifiers uu____44561  in
      FStar_Pprint.op_Hat_Hat uu____44559 uu____44560  in
    FStar_Pprint.op_Hat_Hat uu____44555 uu____44558

and (p_attributes : FStar_Parser_AST.attributes_ -> FStar_Pprint.document) =
  fun attrs  ->
    match attrs with
    | [] -> FStar_Pprint.empty
    | uu____44563 ->
        let uu____44564 =
          let uu____44565 = str "@ "  in
          let uu____44567 =
            let uu____44568 =
              let uu____44569 =
                let uu____44570 =
                  let uu____44571 = FStar_List.map p_atomicTerm attrs  in
                  FStar_Pprint.flow break1 uu____44571  in
                FStar_Pprint.op_Hat_Hat uu____44570 FStar_Pprint.rbracket  in
              FStar_Pprint.align uu____44569  in
            FStar_Pprint.op_Hat_Hat uu____44568 FStar_Pprint.hardline  in
          FStar_Pprint.op_Hat_Hat uu____44565 uu____44567  in
        FStar_Pprint.op_Hat_Hat FStar_Pprint.lbracket uu____44564

and (p_fsdoc : FStar_Parser_AST.fsdoc -> FStar_Pprint.document) =
  fun uu____44574  ->
    match uu____44574 with
    | (doc1,kwd_args) ->
        let kwd_args_doc =
          match kwd_args with
          | [] -> FStar_Pprint.empty
          | kwd_args1 ->
              let process_kwd_arg uu____44622 =
                match uu____44622 with
                | (kwd,arg) ->
                    let uu____44635 = str "@"  in
                    let uu____44637 =
                      let uu____44638 = str kwd  in
                      let uu____44639 =
                        let uu____44640 = str arg  in
                        FStar_Pprint.op_Hat_Hat FStar_Pprint.space
                          uu____44640
                         in
                      FStar_Pprint.op_Hat_Hat uu____44638 uu____44639  in
                    FStar_Pprint.op_Hat_Hat uu____44635 uu____44637
                 in
              let uu____44641 =
                FStar_Pprint.separate_map FStar_Pprint.hardline
                  process_kwd_arg kwd_args1
                 in
              FStar_Pprint.op_Hat_Hat uu____44641 FStar_Pprint.hardline
           in
        let uu____44648 =
          let uu____44649 =
            let uu____44650 =
              let uu____44651 = str doc1  in
              let uu____44652 =
                let uu____44653 =
                  let uu____44654 =
                    FStar_Pprint.op_Hat_Hat FStar_Pprint.rparen
                      FStar_Pprint.hardline
                     in
                  FStar_Pprint.op_Hat_Hat FStar_Pprint.star uu____44654  in
                FStar_Pprint.op_Hat_Hat kwd_args_doc uu____44653  in
              FStar_Pprint.op_Hat_Hat uu____44651 uu____44652  in
            FStar_Pprint.op_Hat_Hat FStar_Pprint.star uu____44650  in
          FStar_Pprint.op_Hat_Hat FStar_Pprint.star uu____44649  in
        FStar_Pprint.op_Hat_Hat FStar_Pprint.lparen uu____44648

and (p_justSig : FStar_Parser_AST.decl -> FStar_Pprint.document) =
  fun d  ->
    match d.FStar_Parser_AST.d with
    | FStar_Parser_AST.Val (lid,t) ->
        let uu____44658 =
          let uu____44659 = str "val"  in
          let uu____44661 =
            let uu____44662 =
              let uu____44663 = p_lident lid  in
              let uu____44664 =
                FStar_Pprint.op_Hat_Hat FStar_Pprint.space FStar_Pprint.colon
                 in
              FStar_Pprint.op_Hat_Hat uu____44663 uu____44664  in
            FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____44662  in
          FStar_Pprint.op_Hat_Hat uu____44659 uu____44661  in
        let uu____44665 = p_typ false false t  in
        FStar_Pprint.op_Hat_Hat uu____44658 uu____44665
    | FStar_Parser_AST.TopLevelLet (uu____44668,lbs) ->
        FStar_Pprint.separate_map FStar_Pprint.hardline
          (fun lb  ->
             let uu____44693 =
               let uu____44694 = str "let"  in p_letlhs uu____44694 lb false
                in
             FStar_Pprint.group uu____44693) lbs
    | uu____44697 -> FStar_Pprint.empty

and (p_list :
  (FStar_Ident.ident -> FStar_Pprint.document) ->
    FStar_Pprint.document ->
      FStar_Ident.ident Prims.list -> FStar_Pprint.document)
  =
  fun f  ->
    fun sep  ->
      fun l  ->
        let rec p_list' uu___328_44712 =
          match uu___328_44712 with
          | [] -> FStar_Pprint.empty
          | x::[] -> f x
          | x::xs ->
              let uu____44720 = f x  in
              let uu____44721 =
                let uu____44722 = p_list' xs  in
                FStar_Pprint.op_Hat_Hat sep uu____44722  in
              FStar_Pprint.op_Hat_Hat uu____44720 uu____44721
           in
        let uu____44723 = str "["  in
        let uu____44725 =
          let uu____44726 = p_list' l  in
          let uu____44727 = str "]"  in
          FStar_Pprint.op_Hat_Hat uu____44726 uu____44727  in
        FStar_Pprint.op_Hat_Hat uu____44723 uu____44725

and (p_rawDecl : FStar_Parser_AST.decl -> FStar_Pprint.document) =
  fun d  ->
    match d.FStar_Parser_AST.d with
    | FStar_Parser_AST.Open uid ->
        let uu____44731 =
          let uu____44732 = str "open"  in
          let uu____44734 = p_quident uid  in
          FStar_Pprint.op_Hat_Slash_Hat uu____44732 uu____44734  in
        FStar_Pprint.group uu____44731
    | FStar_Parser_AST.Include uid ->
        let uu____44736 =
          let uu____44737 = str "include"  in
          let uu____44739 = p_quident uid  in
          FStar_Pprint.op_Hat_Slash_Hat uu____44737 uu____44739  in
        FStar_Pprint.group uu____44736
    | FStar_Parser_AST.Friend uid ->
        let uu____44741 =
          let uu____44742 = str "friend"  in
          let uu____44744 = p_quident uid  in
          FStar_Pprint.op_Hat_Slash_Hat uu____44742 uu____44744  in
        FStar_Pprint.group uu____44741
    | FStar_Parser_AST.ModuleAbbrev (uid1,uid2) ->
        let uu____44747 =
          let uu____44748 = str "module"  in
          let uu____44750 =
            let uu____44751 =
              let uu____44752 = p_uident uid1  in
              let uu____44753 =
                FStar_Pprint.op_Hat_Hat FStar_Pprint.space
                  FStar_Pprint.equals
                 in
              FStar_Pprint.op_Hat_Hat uu____44752 uu____44753  in
            FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____44751  in
          FStar_Pprint.op_Hat_Hat uu____44748 uu____44750  in
        let uu____44754 = p_quident uid2  in
        op_Hat_Slash_Plus_Hat uu____44747 uu____44754
    | FStar_Parser_AST.TopLevelModule uid ->
        let uu____44756 =
          let uu____44757 = str "module"  in
          let uu____44759 =
            let uu____44760 = p_quident uid  in
            FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____44760  in
          FStar_Pprint.op_Hat_Hat uu____44757 uu____44759  in
        FStar_Pprint.group uu____44756
    | FStar_Parser_AST.Tycon
        (true
         ,uu____44761,(FStar_Parser_AST.TyconAbbrev
                       (uid,tpars,FStar_Pervasives_Native.None ,t),FStar_Pervasives_Native.None
                       )::[])
        ->
        let effect_prefix_doc =
          let uu____44798 = str "effect"  in
          let uu____44800 =
            let uu____44801 = p_uident uid  in
            FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____44801  in
          FStar_Pprint.op_Hat_Hat uu____44798 uu____44800  in
        let uu____44802 =
          let uu____44803 = p_typars tpars  in
          FStar_Pprint.surround (Prims.parse_int "2") (Prims.parse_int "1")
            effect_prefix_doc uu____44803 FStar_Pprint.equals
           in
        let uu____44806 = p_typ false false t  in
        op_Hat_Slash_Plus_Hat uu____44802 uu____44806
    | FStar_Parser_AST.Tycon (false ,tc,tcdefs) ->
        let s = if tc then str "class" else str "type"  in
        let uu____44837 =
          let uu____44838 = FStar_List.hd tcdefs  in
          p_fsdocTypeDeclPairs s uu____44838  in
        let uu____44851 =
          let uu____44852 = FStar_List.tl tcdefs  in
          FStar_All.pipe_left
            (FStar_Pprint.concat_map
               (fun x  ->
                  let uu____44890 =
                    let uu____44891 = str "and"  in
                    p_fsdocTypeDeclPairs uu____44891 x  in
                  FStar_Pprint.op_Hat_Hat break1 uu____44890)) uu____44852
           in
        FStar_Pprint.op_Hat_Hat uu____44837 uu____44851
    | FStar_Parser_AST.TopLevelLet (q,lbs) ->
        let let_doc =
          let uu____44908 = str "let"  in
          let uu____44910 = p_letqualifier q  in
          FStar_Pprint.op_Hat_Hat uu____44908 uu____44910  in
        let uu____44911 = str "and"  in
        separate_map_with_comments_kw let_doc uu____44911 p_letbinding lbs
          (fun uu____44921  ->
             match uu____44921 with
             | (p,t) ->
                 let uu____44928 =
                   FStar_Range.union_ranges p.FStar_Parser_AST.prange
                     t.FStar_Parser_AST.range
                    in
                 {
                   r = uu____44928;
                   has_qs = false;
                   has_attrs = false;
                   has_fsdoc = (FStar_Util.is_some d.FStar_Parser_AST.doc);
                   is_fsdoc = false
                 })
    | FStar_Parser_AST.Val (lid,t) ->
        let uu____44934 =
          let uu____44935 = str "val"  in
          let uu____44937 =
            let uu____44938 =
              let uu____44939 = p_lident lid  in
              let uu____44940 = sig_as_binders_if_possible t false  in
              FStar_Pprint.op_Hat_Hat uu____44939 uu____44940  in
            FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____44938  in
          FStar_Pprint.op_Hat_Hat uu____44935 uu____44937  in
        FStar_All.pipe_left FStar_Pprint.group uu____44934
    | FStar_Parser_AST.Assume (id1,t) ->
        let decl_keyword =
          let uu____44945 =
            let uu____44947 =
              FStar_Util.char_at id1.FStar_Ident.idText (Prims.parse_int "0")
               in
            FStar_All.pipe_right uu____44947 FStar_Util.is_upper  in
          if uu____44945
          then FStar_Pprint.empty
          else
            (let uu____44955 = str "val"  in
             FStar_Pprint.op_Hat_Hat uu____44955 FStar_Pprint.space)
           in
        let uu____44957 =
          let uu____44958 = p_ident id1  in
          let uu____44959 =
            let uu____44960 =
              let uu____44961 =
                let uu____44962 = p_typ false false t  in
                FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____44962  in
              FStar_Pprint.op_Hat_Hat FStar_Pprint.colon uu____44961  in
            FStar_Pprint.group uu____44960  in
          FStar_Pprint.op_Hat_Hat uu____44958 uu____44959  in
        FStar_Pprint.op_Hat_Hat decl_keyword uu____44957
    | FStar_Parser_AST.Exception (uid,t_opt) ->
        let uu____44971 = str "exception"  in
        let uu____44973 =
          let uu____44974 =
            let uu____44975 = p_uident uid  in
            let uu____44976 =
              FStar_Pprint.optional
                (fun t  ->
                   let uu____44980 =
                     let uu____44981 = str "of"  in
                     let uu____44983 = p_typ false false t  in
                     op_Hat_Slash_Plus_Hat uu____44981 uu____44983  in
                   FStar_Pprint.op_Hat_Hat break1 uu____44980) t_opt
               in
            FStar_Pprint.op_Hat_Hat uu____44975 uu____44976  in
          FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____44974  in
        FStar_Pprint.op_Hat_Hat uu____44971 uu____44973
    | FStar_Parser_AST.NewEffect ne ->
        let uu____44987 = str "new_effect"  in
        let uu____44989 =
          let uu____44990 = p_newEffect ne  in
          FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____44990  in
        FStar_Pprint.op_Hat_Hat uu____44987 uu____44989
    | FStar_Parser_AST.SubEffect se ->
        let uu____44992 = str "sub_effect"  in
        let uu____44994 =
          let uu____44995 = p_subEffect se  in
          FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____44995  in
        FStar_Pprint.op_Hat_Hat uu____44992 uu____44994
    | FStar_Parser_AST.Pragma p -> p_pragma p
    | FStar_Parser_AST.Fsdoc doc1 -> p_fsdoc doc1
    | FStar_Parser_AST.Main uu____44998 ->
        failwith "*Main declaration* : Is that really still in use ??"
    | FStar_Parser_AST.Tycon (true ,uu____45000,uu____45001) ->
        failwith
          "Effect abbreviation is expected to be defined by an abbreviation"
    | FStar_Parser_AST.Splice (ids,t) ->
        let uu____45029 = str "%splice"  in
        let uu____45031 =
          let uu____45032 =
            let uu____45033 = str ";"  in p_list p_uident uu____45033 ids  in
          let uu____45035 =
            let uu____45036 = p_term false false t  in
            FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____45036  in
          FStar_Pprint.op_Hat_Hat uu____45032 uu____45035  in
        FStar_Pprint.op_Hat_Hat uu____45029 uu____45031

and (p_pragma : FStar_Parser_AST.pragma -> FStar_Pprint.document) =
  fun uu___329_45039  ->
    match uu___329_45039 with
    | FStar_Parser_AST.SetOptions s ->
        let uu____45042 = str "#set-options"  in
        let uu____45044 =
          let uu____45045 =
            let uu____45046 = str s  in FStar_Pprint.dquotes uu____45046  in
          FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____45045  in
        FStar_Pprint.op_Hat_Hat uu____45042 uu____45044
    | FStar_Parser_AST.ResetOptions s_opt ->
        let uu____45051 = str "#reset-options"  in
        let uu____45053 =
          FStar_Pprint.optional
            (fun s  ->
               let uu____45059 =
                 let uu____45060 = str s  in FStar_Pprint.dquotes uu____45060
                  in
               FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____45059) s_opt
           in
        FStar_Pprint.op_Hat_Hat uu____45051 uu____45053
    | FStar_Parser_AST.PushOptions s_opt ->
        let uu____45065 = str "#push-options"  in
        let uu____45067 =
          FStar_Pprint.optional
            (fun s  ->
               let uu____45073 =
                 let uu____45074 = str s  in FStar_Pprint.dquotes uu____45074
                  in
               FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____45073) s_opt
           in
        FStar_Pprint.op_Hat_Hat uu____45065 uu____45067
    | FStar_Parser_AST.PopOptions  -> str "#pop-options"
    | FStar_Parser_AST.LightOff  ->
        (FStar_ST.op_Colon_Equals should_print_fs_typ_app true;
         str "#light \"off\"")

and (p_typars : FStar_Parser_AST.binder Prims.list -> FStar_Pprint.document)
  = fun bs  -> p_binders true bs

and (p_fsdocTypeDeclPairs :
  FStar_Pprint.document ->
    (FStar_Parser_AST.tycon * FStar_Parser_AST.fsdoc
      FStar_Pervasives_Native.option) -> FStar_Pprint.document)
  =
  fun kw  ->
    fun uu____45105  ->
      match uu____45105 with
      | (typedecl,fsdoc_opt) ->
          let uu____45118 = p_typeDecl (kw, fsdoc_opt) typedecl  in
          (match uu____45118 with
           | (comm,decl,body,pre) ->
               if comm = FStar_Pprint.empty
               then
                 let uu____45143 = pre body  in
                 FStar_Pprint.op_Hat_Hat decl uu____45143
               else
                 (let uu____45146 =
                    let uu____45147 =
                      let uu____45148 =
                        let uu____45149 = pre body  in
                        FStar_Pprint.op_Hat_Slash_Hat uu____45149 comm  in
                      FStar_Pprint.op_Hat_Hat decl uu____45148  in
                    let uu____45150 =
                      let uu____45151 =
                        let uu____45152 =
                          let uu____45153 =
                            let uu____45154 =
                              FStar_Pprint.op_Hat_Hat FStar_Pprint.hardline
                                body
                               in
                            FStar_Pprint.op_Hat_Hat comm uu____45154  in
                          FStar_Pprint.op_Hat_Hat FStar_Pprint.hardline
                            uu____45153
                           in
                        FStar_Pprint.nest (Prims.parse_int "2") uu____45152
                         in
                      FStar_Pprint.op_Hat_Hat decl uu____45151  in
                    FStar_Pprint.ifflat uu____45147 uu____45150  in
                  FStar_All.pipe_left FStar_Pprint.group uu____45146))

and (p_typeDecl :
  (FStar_Pprint.document * FStar_Parser_AST.fsdoc
    FStar_Pervasives_Native.option) ->
    FStar_Parser_AST.tycon ->
      (FStar_Pprint.document * FStar_Pprint.document * FStar_Pprint.document
        * (FStar_Pprint.document -> FStar_Pprint.document)))
  =
  fun pre  ->
    fun uu___330_45157  ->
      match uu___330_45157 with
      | FStar_Parser_AST.TyconAbstract (lid,bs,typ_opt) ->
          let uu____45186 = p_typeDeclPrefix pre false lid bs typ_opt  in
          (FStar_Pprint.empty, uu____45186, FStar_Pprint.empty,
            FStar_Pervasives.id)
      | FStar_Parser_AST.TyconAbbrev (lid,bs,typ_opt,t) ->
          let uu____45203 = p_typ_sep false false t  in
          (match uu____45203 with
           | (comm,doc1) ->
               let uu____45223 = p_typeDeclPrefix pre true lid bs typ_opt  in
               (comm, uu____45223, doc1, jump2))
      | FStar_Parser_AST.TyconRecord (lid,bs,typ_opt,record_field_decls) ->
          let p_recordFieldAndComments ps uu____45279 =
            match uu____45279 with
            | (lid1,t,doc_opt) ->
                let uu____45296 =
                  let uu____45301 =
                    FStar_Range.extend_to_end_of_line
                      t.FStar_Parser_AST.range
                     in
                  with_comment_sep (p_recordFieldDecl ps) (lid1, t, doc_opt)
                    uu____45301
                   in
                (match uu____45296 with
                 | (comm,field) ->
                     let sep =
                       if ps then FStar_Pprint.semi else FStar_Pprint.empty
                        in
                     inline_comment_or_above comm field sep)
             in
          let p_fields =
            let uu____45319 =
              separate_map_last FStar_Pprint.hardline
                p_recordFieldAndComments record_field_decls
               in
            braces_with_nesting uu____45319  in
          let uu____45328 = p_typeDeclPrefix pre true lid bs typ_opt  in
          (FStar_Pprint.empty, uu____45328, p_fields,
            ((fun d  -> FStar_Pprint.op_Hat_Hat FStar_Pprint.space d)))
      | FStar_Parser_AST.TyconVariant (lid,bs,typ_opt,ct_decls) ->
          let p_constructorBranchAndComments uu____45395 =
            match uu____45395 with
            | (uid,t_opt,doc_opt,use_of) ->
                let range =
                  let uu____45424 =
                    let uu____45425 =
                      FStar_Util.map_opt t_opt
                        (fun t  -> t.FStar_Parser_AST.range)
                       in
                    FStar_Util.dflt uid.FStar_Ident.idRange uu____45425  in
                  FStar_Range.extend_to_end_of_line uu____45424  in
                let uu____45430 =
                  with_comment_sep p_constructorBranch
                    (uid, t_opt, doc_opt, use_of) range
                   in
                (match uu____45430 with
                 | (comm,ctor) ->
                     inline_comment_or_above comm ctor FStar_Pprint.empty)
             in
          let datacon_doc =
            FStar_Pprint.separate_map FStar_Pprint.hardline
              p_constructorBranchAndComments ct_decls
             in
          let uu____45469 = p_typeDeclPrefix pre true lid bs typ_opt  in
          (FStar_Pprint.empty, uu____45469, datacon_doc, jump2)

and (p_typeDeclPrefix :
  (FStar_Pprint.document * FStar_Parser_AST.fsdoc
    FStar_Pervasives_Native.option) ->
    Prims.bool ->
      FStar_Ident.ident ->
        FStar_Parser_AST.binder Prims.list ->
          FStar_Parser_AST.knd FStar_Pervasives_Native.option ->
            FStar_Pprint.document)
  =
  fun uu____45474  ->
    fun eq1  ->
      fun lid  ->
        fun bs  ->
          fun typ_opt  ->
            match uu____45474 with
            | (kw,fsdoc_opt) ->
                let maybe_with_fsdoc cont =
                  let lid_doc = p_ident lid  in
                  let kw_lid =
                    let uu____45509 =
                      FStar_Pprint.op_Hat_Slash_Hat kw lid_doc  in
                    FStar_Pprint.group uu____45509  in
                  match fsdoc_opt with
                  | FStar_Pervasives_Native.None  -> cont kw_lid
                  | FStar_Pervasives_Native.Some fsdoc ->
                      let uu____45511 =
                        let uu____45514 =
                          let uu____45517 = p_fsdoc fsdoc  in
                          let uu____45518 =
                            let uu____45521 = cont lid_doc  in [uu____45521]
                             in
                          uu____45517 :: uu____45518  in
                        kw :: uu____45514  in
                      FStar_Pprint.separate FStar_Pprint.hardline uu____45511
                   in
                let typ =
                  let maybe_eq =
                    if eq1 then FStar_Pprint.equals else FStar_Pprint.empty
                     in
                  match typ_opt with
                  | FStar_Pervasives_Native.None  -> maybe_eq
                  | FStar_Pervasives_Native.Some t ->
                      let uu____45528 =
                        let uu____45529 =
                          let uu____45530 = p_typ false false t  in
                          FStar_Pprint.op_Hat_Slash_Hat uu____45530 maybe_eq
                           in
                        FStar_Pprint.op_Hat_Hat FStar_Pprint.space
                          uu____45529
                         in
                      FStar_Pprint.op_Hat_Hat FStar_Pprint.colon uu____45528
                   in
                if bs = []
                then maybe_with_fsdoc (fun n1  -> prefix2 n1 typ)
                else
                  (let binders = p_binders_list true bs  in
                   maybe_with_fsdoc
                     (fun n1  ->
                        let uu____45550 =
                          let uu____45551 = FStar_Pprint.flow break1 binders
                             in
                          prefix2 n1 uu____45551  in
                        prefix2 uu____45550 typ))

and (p_recordFieldDecl :
  Prims.bool ->
    (FStar_Ident.ident * FStar_Parser_AST.term * FStar_Parser_AST.fsdoc
      FStar_Pervasives_Native.option) -> FStar_Pprint.document)
  =
  fun ps  ->
    fun uu____45553  ->
      match uu____45553 with
      | (lid,t,doc_opt) ->
          let uu____45570 =
            let uu____45571 = FStar_Pprint.optional p_fsdoc doc_opt  in
            let uu____45572 =
              let uu____45573 = p_lident lid  in
              let uu____45574 =
                let uu____45575 = p_typ ps false t  in
                FStar_Pprint.op_Hat_Hat FStar_Pprint.colon uu____45575  in
              FStar_Pprint.op_Hat_Hat uu____45573 uu____45574  in
            FStar_Pprint.op_Hat_Hat uu____45571 uu____45572  in
          FStar_Pprint.group uu____45570

and (p_constructorBranch :
  (FStar_Ident.ident * FStar_Parser_AST.term FStar_Pervasives_Native.option *
    FStar_Parser_AST.fsdoc FStar_Pervasives_Native.option * Prims.bool) ->
    FStar_Pprint.document)
  =
  fun uu____45577  ->
    match uu____45577 with
    | (uid,t_opt,doc_opt,use_of) ->
        let sep = if use_of then str "of" else FStar_Pprint.colon  in
        let uid_doc =
          let uu____45611 =
            let uu____45612 =
              let uu____45613 = p_uident uid  in
              FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____45613  in
            FStar_Pprint.op_Hat_Hat FStar_Pprint.bar uu____45612  in
          FStar_Pprint.group uu____45611  in
        let uu____45614 = FStar_Pprint.optional p_fsdoc doc_opt  in
        let uu____45615 =
          default_or_map uid_doc
            (fun t  ->
               let uu____45619 =
                 let uu____45620 =
                   let uu____45621 =
                     let uu____45622 =
                       let uu____45623 = p_typ false false t  in
                       FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____45623
                        in
                     FStar_Pprint.op_Hat_Hat sep uu____45622  in
                   FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____45621  in
                 FStar_Pprint.op_Hat_Hat uid_doc uu____45620  in
               FStar_Pprint.group uu____45619) t_opt
           in
        FStar_Pprint.op_Hat_Hat uu____45614 uu____45615

and (p_letlhs :
  FStar_Pprint.document ->
    (FStar_Parser_AST.pattern * FStar_Parser_AST.term) ->
      Prims.bool -> FStar_Pprint.document)
  =
  fun kw  ->
    fun uu____45627  ->
      fun inner_let  ->
        match uu____45627 with
        | (pat,uu____45635) ->
            let uu____45636 =
              match pat.FStar_Parser_AST.pat with
              | FStar_Parser_AST.PatAscribed
                  (pat1,(t,FStar_Pervasives_Native.None )) ->
                  (pat1,
                    (FStar_Pervasives_Native.Some (t, FStar_Pprint.empty)))
              | FStar_Parser_AST.PatAscribed
                  (pat1,(t,FStar_Pervasives_Native.Some tac)) ->
                  let uu____45688 =
                    let uu____45695 =
                      let uu____45700 =
                        let uu____45701 =
                          let uu____45702 =
                            let uu____45703 = str "by"  in
                            let uu____45705 =
                              let uu____45706 = p_atomicTerm tac  in
                              FStar_Pprint.op_Hat_Hat FStar_Pprint.space
                                uu____45706
                               in
                            FStar_Pprint.op_Hat_Hat uu____45703 uu____45705
                             in
                          FStar_Pprint.op_Hat_Hat FStar_Pprint.space
                            uu____45702
                           in
                        FStar_Pprint.group uu____45701  in
                      (t, uu____45700)  in
                    FStar_Pervasives_Native.Some uu____45695  in
                  (pat1, uu____45688)
              | uu____45717 -> (pat, FStar_Pervasives_Native.None)  in
            (match uu____45636 with
             | (pat1,ascr) ->
                 (match pat1.FStar_Parser_AST.pat with
                  | FStar_Parser_AST.PatApp
                      ({
                         FStar_Parser_AST.pat = FStar_Parser_AST.PatVar
                           (lid,uu____45743);
                         FStar_Parser_AST.prange = uu____45744;_},pats)
                      ->
                      let ascr_doc =
                        match ascr with
                        | FStar_Pervasives_Native.Some (t,tac) ->
                            let uu____45761 =
                              sig_as_binders_if_possible t true  in
                            FStar_Pprint.op_Hat_Hat uu____45761 tac
                        | FStar_Pervasives_Native.None  -> FStar_Pprint.empty
                         in
                      let uu____45767 =
                        if inner_let
                        then
                          let uu____45781 = pats_as_binders_if_possible pats
                             in
                          match uu____45781 with
                          | (bs,style) ->
                              ((FStar_List.append bs [ascr_doc]), style)
                        else
                          (let uu____45804 = pats_as_binders_if_possible pats
                              in
                           match uu____45804 with
                           | (bs,style) ->
                               ((FStar_List.append bs [ascr_doc]), style))
                         in
                      (match uu____45767 with
                       | (terms,style) ->
                           let uu____45831 =
                             let uu____45832 =
                               let uu____45833 =
                                 let uu____45834 = p_lident lid  in
                                 let uu____45835 =
                                   format_sig style terms true true  in
                                 FStar_Pprint.op_Hat_Hat uu____45834
                                   uu____45835
                                  in
                               FStar_Pprint.op_Hat_Hat FStar_Pprint.space
                                 uu____45833
                                in
                             FStar_Pprint.op_Hat_Hat kw uu____45832  in
                           FStar_All.pipe_left FStar_Pprint.group uu____45831)
                  | uu____45838 ->
                      let ascr_doc =
                        match ascr with
                        | FStar_Pervasives_Native.Some (t,tac) ->
                            let uu____45846 =
                              let uu____45847 =
                                let uu____45848 =
                                  p_typ_top
                                    (Arrows
                                       ((Prims.parse_int "2"),
                                         (Prims.parse_int "2"))) false false
                                    t
                                   in
                                FStar_Pprint.op_Hat_Hat FStar_Pprint.colon
                                  uu____45848
                                 in
                              FStar_Pprint.group uu____45847  in
                            FStar_Pprint.op_Hat_Hat uu____45846 tac
                        | FStar_Pervasives_Native.None  -> FStar_Pprint.empty
                         in
                      let uu____45859 =
                        let uu____45860 =
                          let uu____45861 =
                            let uu____45862 = p_tuplePattern pat1  in
                            FStar_Pprint.op_Hat_Slash_Hat kw uu____45862  in
                          FStar_Pprint.group uu____45861  in
                        FStar_Pprint.op_Hat_Hat uu____45860 ascr_doc  in
                      FStar_Pprint.group uu____45859))

and (p_letbinding :
  FStar_Pprint.document ->
    (FStar_Parser_AST.pattern * FStar_Parser_AST.term) ->
      FStar_Pprint.document)
  =
  fun kw  ->
    fun uu____45864  ->
      match uu____45864 with
      | (pat,e) ->
          let doc_pat = p_letlhs kw (pat, e) false  in
          let uu____45873 = p_term_sep false false e  in
          (match uu____45873 with
           | (comm,doc_expr) ->
               let doc_expr1 =
                 inline_comment_or_above comm doc_expr FStar_Pprint.empty  in
               let uu____45883 =
                 let uu____45884 =
                   FStar_Pprint.op_Hat_Slash_Hat FStar_Pprint.equals
                     doc_expr1
                    in
                 FStar_Pprint.op_Hat_Slash_Hat doc_pat uu____45884  in
               let uu____45885 =
                 let uu____45886 =
                   let uu____45887 =
                     let uu____45888 =
                       let uu____45889 = jump2 doc_expr1  in
                       FStar_Pprint.op_Hat_Hat FStar_Pprint.equals
                         uu____45889
                        in
                     FStar_Pprint.group uu____45888  in
                   FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____45887  in
                 FStar_Pprint.op_Hat_Hat doc_pat uu____45886  in
               FStar_Pprint.ifflat uu____45883 uu____45885)

and (p_newEffect : FStar_Parser_AST.effect_decl -> FStar_Pprint.document) =
  fun uu___331_45890  ->
    match uu___331_45890 with
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
        let uu____45915 = p_uident uid  in
        let uu____45916 = p_binders true bs  in
        let uu____45918 =
          let uu____45919 = p_simpleTerm false false t  in
          prefix2 FStar_Pprint.equals uu____45919  in
        surround_maybe_empty (Prims.parse_int "2") (Prims.parse_int "1")
          uu____45915 uu____45916 uu____45918

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
          let uu____45934 =
            let uu____45935 =
              let uu____45936 =
                let uu____45937 = p_uident uid  in
                let uu____45938 = p_binders true bs  in
                let uu____45940 =
                  let uu____45941 = p_typ false false t  in
                  prefix2 FStar_Pprint.colon uu____45941  in
                surround_maybe_empty (Prims.parse_int "2")
                  (Prims.parse_int "1") uu____45937 uu____45938 uu____45940
                 in
              FStar_Pprint.group uu____45936  in
            let uu____45946 =
              let uu____45947 = str "with"  in
              let uu____45949 =
                let uu____45950 =
                  let uu____45951 =
                    let uu____45952 =
                      let uu____45953 =
                        let uu____45954 =
                          FStar_Pprint.op_Hat_Hat FStar_Pprint.semi
                            FStar_Pprint.space
                           in
                        FStar_Pprint.op_Hat_Hat FStar_Pprint.hardline
                          uu____45954
                         in
                      separate_map_last uu____45953 p_effectDecl eff_decls
                       in
                    FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____45952
                     in
                  FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____45951  in
                FStar_Pprint.op_Hat_Hat FStar_Pprint.hardline uu____45950  in
              FStar_Pprint.op_Hat_Hat uu____45947 uu____45949  in
            FStar_Pprint.op_Hat_Slash_Hat uu____45935 uu____45946  in
          braces_with_nesting uu____45934

and (p_effectDecl :
  Prims.bool -> FStar_Parser_AST.decl -> FStar_Pprint.document) =
  fun ps  ->
    fun d  ->
      match d.FStar_Parser_AST.d with
      | FStar_Parser_AST.Tycon
          (false
           ,uu____45958,(FStar_Parser_AST.TyconAbbrev
                         (lid,[],FStar_Pervasives_Native.None ,e),FStar_Pervasives_Native.None
                         )::[])
          ->
          let uu____45991 =
            let uu____45992 = p_lident lid  in
            let uu____45993 =
              FStar_Pprint.op_Hat_Hat FStar_Pprint.space FStar_Pprint.equals
               in
            FStar_Pprint.op_Hat_Hat uu____45992 uu____45993  in
          let uu____45994 = p_simpleTerm ps false e  in
          prefix2 uu____45991 uu____45994
      | uu____45996 ->
          let uu____45997 =
            let uu____45999 = FStar_Parser_AST.decl_to_string d  in
            FStar_Util.format1
              "Not a declaration of an effect member... or at least I hope so : %s"
              uu____45999
             in
          failwith uu____45997

and (p_subEffect : FStar_Parser_AST.lift -> FStar_Pprint.document) =
  fun lift  ->
    let lift_op_doc =
      let lifts =
        match lift.FStar_Parser_AST.lift_op with
        | FStar_Parser_AST.NonReifiableLift t -> [("lift_wp", t)]
        | FStar_Parser_AST.ReifiableLift (t1,t2) ->
            [("lift_wp", t1); ("lift", t2)]
        | FStar_Parser_AST.LiftForFree t -> [("lift", t)]  in
      let p_lift ps uu____46082 =
        match uu____46082 with
        | (kwd,t) ->
            let uu____46093 =
              let uu____46094 = str kwd  in
              let uu____46095 =
                FStar_Pprint.op_Hat_Hat FStar_Pprint.space
                  FStar_Pprint.equals
                 in
              FStar_Pprint.op_Hat_Hat uu____46094 uu____46095  in
            let uu____46096 = p_simpleTerm ps false t  in
            prefix2 uu____46093 uu____46096
         in
      separate_break_map_last FStar_Pprint.semi p_lift lifts  in
    let uu____46103 =
      let uu____46104 =
        let uu____46105 = p_quident lift.FStar_Parser_AST.msource  in
        let uu____46106 =
          let uu____46107 = str "~>"  in
          FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____46107  in
        FStar_Pprint.op_Hat_Hat uu____46105 uu____46106  in
      let uu____46109 = p_quident lift.FStar_Parser_AST.mdest  in
      prefix2 uu____46104 uu____46109  in
    let uu____46110 =
      let uu____46111 = braces_with_nesting lift_op_doc  in
      FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____46111  in
    FStar_Pprint.op_Hat_Hat uu____46103 uu____46110

and (p_qualifier : FStar_Parser_AST.qualifier -> FStar_Pprint.document) =
  fun uu___332_46112  ->
    match uu___332_46112 with
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
    | q::[] ->
        let uu____46132 = p_qualifier q  in
        FStar_Pprint.op_Hat_Hat uu____46132 FStar_Pprint.hardline
    | uu____46133 ->
        let uu____46134 =
          let uu____46135 = FStar_List.map p_qualifier qs  in
          FStar_Pprint.flow break1 uu____46135  in
        FStar_Pprint.op_Hat_Hat uu____46134 FStar_Pprint.hardline

and (p_letqualifier :
  FStar_Parser_AST.let_qualifier -> FStar_Pprint.document) =
  fun uu___333_46138  ->
    match uu___333_46138 with
    | FStar_Parser_AST.Rec  ->
        let uu____46139 = str "rec"  in
        FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____46139
    | FStar_Parser_AST.NoLetQualifier  -> FStar_Pprint.empty

and (p_aqual : FStar_Parser_AST.arg_qualifier -> FStar_Pprint.document) =
  fun uu___334_46141  ->
    match uu___334_46141 with
    | FStar_Parser_AST.Implicit  -> str "#"
    | FStar_Parser_AST.Equality  -> str "$"
    | FStar_Parser_AST.Meta t ->
        let t1 =
          match t.FStar_Parser_AST.tm with
          | FStar_Parser_AST.Abs (uu____46146,e) -> e
          | uu____46152 ->
              FStar_Parser_AST.mk_term
                (FStar_Parser_AST.App
                   (t,
                     (FStar_Parser_AST.unit_const t.FStar_Parser_AST.range),
                     FStar_Parser_AST.Nothing)) t.FStar_Parser_AST.range
                FStar_Parser_AST.Expr
           in
        let uu____46153 = str "#["  in
        let uu____46155 =
          let uu____46156 = p_term false false t1  in
          let uu____46159 =
            let uu____46160 = str "]"  in
            FStar_Pprint.op_Hat_Hat uu____46160 break1  in
          FStar_Pprint.op_Hat_Hat uu____46156 uu____46159  in
        FStar_Pprint.op_Hat_Hat uu____46153 uu____46155

and (p_disjunctivePattern :
  FStar_Parser_AST.pattern -> FStar_Pprint.document) =
  fun p  ->
    match p.FStar_Parser_AST.pat with
    | FStar_Parser_AST.PatOr pats ->
        let uu____46166 =
          let uu____46167 =
            let uu____46168 =
              FStar_Pprint.op_Hat_Hat FStar_Pprint.bar FStar_Pprint.space  in
            FStar_Pprint.op_Hat_Hat break1 uu____46168  in
          FStar_Pprint.separate_map uu____46167 p_tuplePattern pats  in
        FStar_Pprint.group uu____46166
    | uu____46169 -> p_tuplePattern p

and (p_tuplePattern : FStar_Parser_AST.pattern -> FStar_Pprint.document) =
  fun p  ->
    match p.FStar_Parser_AST.pat with
    | FStar_Parser_AST.PatTuple (pats,false ) ->
        let uu____46178 =
          let uu____46179 = FStar_Pprint.op_Hat_Hat FStar_Pprint.comma break1
             in
          FStar_Pprint.separate_map uu____46179 p_constructorPattern pats  in
        FStar_Pprint.group uu____46178
    | uu____46180 -> p_constructorPattern p

and (p_constructorPattern :
  FStar_Parser_AST.pattern -> FStar_Pprint.document) =
  fun p  ->
    match p.FStar_Parser_AST.pat with
    | FStar_Parser_AST.PatApp
        ({ FStar_Parser_AST.pat = FStar_Parser_AST.PatName maybe_cons_lid;
           FStar_Parser_AST.prange = uu____46183;_},hd1::tl1::[])
        when
        FStar_Ident.lid_equals maybe_cons_lid FStar_Parser_Const.cons_lid ->
        let uu____46188 =
          FStar_Pprint.op_Hat_Hat FStar_Pprint.colon FStar_Pprint.colon  in
        let uu____46189 = p_constructorPattern hd1  in
        let uu____46190 = p_constructorPattern tl1  in
        infix0 uu____46188 uu____46189 uu____46190
    | FStar_Parser_AST.PatApp
        ({ FStar_Parser_AST.pat = FStar_Parser_AST.PatName uid;
           FStar_Parser_AST.prange = uu____46192;_},pats)
        ->
        let uu____46198 = p_quident uid  in
        let uu____46199 =
          FStar_Pprint.separate_map break1 p_atomicPattern pats  in
        prefix2 uu____46198 uu____46199
    | uu____46200 -> p_atomicPattern p

and (p_atomicPattern : FStar_Parser_AST.pattern -> FStar_Pprint.document) =
  fun p  ->
    match p.FStar_Parser_AST.pat with
    | FStar_Parser_AST.PatAscribed (pat,(t,FStar_Pervasives_Native.None )) ->
        (match ((pat.FStar_Parser_AST.pat), (t.FStar_Parser_AST.tm)) with
         | (FStar_Parser_AST.PatVar (lid,aqual),FStar_Parser_AST.Refine
            ({ FStar_Parser_AST.b = FStar_Parser_AST.Annotated (lid',t1);
               FStar_Parser_AST.brange = uu____46216;
               FStar_Parser_AST.blevel = uu____46217;
               FStar_Parser_AST.aqual = uu____46218;_},phi))
             when lid.FStar_Ident.idText = lid'.FStar_Ident.idText ->
             let uu____46227 =
               let uu____46228 = p_ident lid  in
               p_refinement aqual uu____46228 t1 phi  in
             soft_parens_with_nesting uu____46227
         | (FStar_Parser_AST.PatWild aqual,FStar_Parser_AST.Refine
            ({ FStar_Parser_AST.b = FStar_Parser_AST.NoName t1;
               FStar_Parser_AST.brange = uu____46231;
               FStar_Parser_AST.blevel = uu____46232;
               FStar_Parser_AST.aqual = uu____46233;_},phi))
             ->
             let uu____46239 =
               p_refinement aqual FStar_Pprint.underscore t1 phi  in
             soft_parens_with_nesting uu____46239
         | uu____46240 ->
             let uu____46245 =
               let uu____46246 = p_tuplePattern pat  in
               let uu____46247 =
                 let uu____46248 = p_tmEqNoRefinement t  in
                 FStar_Pprint.op_Hat_Slash_Hat FStar_Pprint.colon uu____46248
                  in
               FStar_Pprint.op_Hat_Hat uu____46246 uu____46247  in
             soft_parens_with_nesting uu____46245)
    | FStar_Parser_AST.PatList pats ->
        let uu____46252 =
          separate_break_map FStar_Pprint.semi p_tuplePattern pats  in
        FStar_Pprint.surround (Prims.parse_int "2") (Prims.parse_int "0")
          FStar_Pprint.lbracket uu____46252 FStar_Pprint.rbracket
    | FStar_Parser_AST.PatRecord pats ->
        let p_recordFieldPat uu____46271 =
          match uu____46271 with
          | (lid,pat) ->
              let uu____46278 = p_qlident lid  in
              let uu____46279 = p_tuplePattern pat  in
              infix2 FStar_Pprint.equals uu____46278 uu____46279
           in
        let uu____46280 =
          separate_break_map FStar_Pprint.semi p_recordFieldPat pats  in
        soft_braces_with_nesting uu____46280
    | FStar_Parser_AST.PatTuple (pats,true ) ->
        let uu____46292 =
          FStar_Pprint.op_Hat_Hat FStar_Pprint.lparen FStar_Pprint.bar  in
        let uu____46293 =
          separate_break_map FStar_Pprint.comma p_constructorPattern pats  in
        let uu____46294 =
          FStar_Pprint.op_Hat_Hat FStar_Pprint.bar FStar_Pprint.rparen  in
        FStar_Pprint.surround (Prims.parse_int "2") (Prims.parse_int "1")
          uu____46292 uu____46293 uu____46294
    | FStar_Parser_AST.PatTvar (tv,arg_qualifier_opt) -> p_tvar tv
    | FStar_Parser_AST.PatOp op ->
        let uu____46305 =
          let uu____46306 =
            let uu____46307 =
              let uu____46308 = FStar_Ident.text_of_id op  in str uu____46308
               in
            let uu____46310 =
              FStar_Pprint.op_Hat_Hat FStar_Pprint.space FStar_Pprint.rparen
               in
            FStar_Pprint.op_Hat_Hat uu____46307 uu____46310  in
          FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____46306  in
        FStar_Pprint.op_Hat_Hat FStar_Pprint.lparen uu____46305
    | FStar_Parser_AST.PatWild aqual ->
        let uu____46314 = FStar_Pprint.optional p_aqual aqual  in
        FStar_Pprint.op_Hat_Hat uu____46314 FStar_Pprint.underscore
    | FStar_Parser_AST.PatConst c -> p_constant c
    | FStar_Parser_AST.PatVar (lid,aqual) ->
        let uu____46322 = FStar_Pprint.optional p_aqual aqual  in
        let uu____46323 = p_lident lid  in
        FStar_Pprint.op_Hat_Hat uu____46322 uu____46323
    | FStar_Parser_AST.PatName uid -> p_quident uid
    | FStar_Parser_AST.PatOr uu____46325 -> failwith "Inner or pattern !"
    | FStar_Parser_AST.PatApp
        ({ FStar_Parser_AST.pat = FStar_Parser_AST.PatName uu____46329;
           FStar_Parser_AST.prange = uu____46330;_},uu____46331)
        ->
        let uu____46336 = p_tuplePattern p  in
        soft_parens_with_nesting uu____46336
    | FStar_Parser_AST.PatTuple (uu____46337,false ) ->
        let uu____46344 = p_tuplePattern p  in
        soft_parens_with_nesting uu____46344
    | uu____46345 ->
        let uu____46346 =
          let uu____46348 = FStar_Parser_AST.pat_to_string p  in
          FStar_Util.format1 "Invalid pattern %s" uu____46348  in
        failwith uu____46346

and (is_typ_tuple : FStar_Parser_AST.term -> Prims.bool) =
  fun e  ->
    match e.FStar_Parser_AST.tm with
    | FStar_Parser_AST.Op
        ({ FStar_Ident.idText = "*"; FStar_Ident.idRange = uu____46353;_},uu____46354)
        -> true
    | uu____46361 -> false

and (is_meta_qualifier :
  FStar_Parser_AST.arg_qualifier FStar_Pervasives_Native.option -> Prims.bool)
  =
  fun aq  ->
    match aq with
    | FStar_Pervasives_Native.Some (FStar_Parser_AST.Meta uu____46367) ->
        true
    | uu____46369 -> false

and (p_binder :
  Prims.bool -> FStar_Parser_AST.binder -> FStar_Pprint.document) =
  fun is_atomic  ->
    fun b  ->
      let uu____46376 = p_binder' is_atomic b  in
      match uu____46376 with
      | (b',t',catf) ->
          (match t' with
           | FStar_Pervasives_Native.Some typ -> catf b' typ
           | FStar_Pervasives_Native.None  -> b')

and (p_binder' :
  Prims.bool ->
    FStar_Parser_AST.binder ->
      (FStar_Pprint.document * FStar_Pprint.document
        FStar_Pervasives_Native.option * catf))
  =
  fun is_atomic  ->
    fun b  ->
      match b.FStar_Parser_AST.b with
      | FStar_Parser_AST.Variable lid ->
          let uu____46413 =
            let uu____46414 =
              FStar_Pprint.optional p_aqual b.FStar_Parser_AST.aqual  in
            let uu____46415 = p_lident lid  in
            FStar_Pprint.op_Hat_Hat uu____46414 uu____46415  in
          (uu____46413, FStar_Pervasives_Native.None, cat_with_colon)
      | FStar_Parser_AST.TVariable lid ->
          let uu____46421 = p_lident lid  in
          (uu____46421, FStar_Pervasives_Native.None, cat_with_colon)
      | FStar_Parser_AST.Annotated (lid,t) ->
          let uu____46428 =
            match t.FStar_Parser_AST.tm with
            | FStar_Parser_AST.Refine
                ({ FStar_Parser_AST.b = FStar_Parser_AST.Annotated (lid',t1);
                   FStar_Parser_AST.brange = uu____46439;
                   FStar_Parser_AST.blevel = uu____46440;
                   FStar_Parser_AST.aqual = uu____46441;_},phi)
                when lid.FStar_Ident.idText = lid'.FStar_Ident.idText ->
                let uu____46446 = p_lident lid  in
                p_refinement' b.FStar_Parser_AST.aqual uu____46446 t1 phi
            | uu____46447 ->
                let t' =
                  let uu____46449 = is_typ_tuple t  in
                  if uu____46449
                  then
                    let uu____46452 = p_tmFormula t  in
                    soft_parens_with_nesting uu____46452
                  else p_tmFormula t  in
                let uu____46455 =
                  let uu____46456 =
                    FStar_Pprint.optional p_aqual b.FStar_Parser_AST.aqual
                     in
                  let uu____46457 = p_lident lid  in
                  FStar_Pprint.op_Hat_Hat uu____46456 uu____46457  in
                (uu____46455, t')
             in
          (match uu____46428 with
           | (b',t') ->
               let catf =
                 let uu____46475 =
                   is_atomic || (is_meta_qualifier b.FStar_Parser_AST.aqual)
                    in
                 if uu____46475
                 then
                   fun x  ->
                     fun y  ->
                       let uu____46482 =
                         let uu____46483 =
                           let uu____46484 = cat_with_colon x y  in
                           FStar_Pprint.op_Hat_Hat uu____46484
                             FStar_Pprint.rparen
                            in
                         FStar_Pprint.op_Hat_Hat FStar_Pprint.lparen
                           uu____46483
                          in
                       FStar_Pprint.group uu____46482
                 else
                   (fun x  ->
                      fun y  ->
                        let uu____46489 = cat_with_colon x y  in
                        FStar_Pprint.group uu____46489)
                  in
               (b', (FStar_Pervasives_Native.Some t'), catf))
      | FStar_Parser_AST.TAnnotated uu____46494 ->
          failwith "Is this still used ?"
      | FStar_Parser_AST.NoName t ->
          (match t.FStar_Parser_AST.tm with
           | FStar_Parser_AST.Refine
               ({ FStar_Parser_AST.b = FStar_Parser_AST.NoName t1;
                  FStar_Parser_AST.brange = uu____46522;
                  FStar_Parser_AST.blevel = uu____46523;
                  FStar_Parser_AST.aqual = uu____46524;_},phi)
               ->
               let uu____46528 =
                 p_refinement' b.FStar_Parser_AST.aqual
                   FStar_Pprint.underscore t1 phi
                  in
               (match uu____46528 with
                | (b',t') ->
                    (b', (FStar_Pervasives_Native.Some t'), cat_with_colon))
           | uu____46549 ->
               if is_atomic
               then
                 let uu____46561 = p_atomicTerm t  in
                 (uu____46561, FStar_Pervasives_Native.None, cat_with_colon)
               else
                 (let uu____46568 = p_appTerm t  in
                  (uu____46568, FStar_Pervasives_Native.None, cat_with_colon)))

and (p_refinement :
  FStar_Parser_AST.arg_qualifier FStar_Pervasives_Native.option ->
    FStar_Pprint.document ->
      FStar_Parser_AST.term -> FStar_Parser_AST.term -> FStar_Pprint.document)
  =
  fun aqual_opt  ->
    fun binder  ->
      fun t  ->
        fun phi  ->
          let uu____46579 = p_refinement' aqual_opt binder t phi  in
          match uu____46579 with | (b,typ) -> cat_with_colon b typ

and (p_refinement' :
  FStar_Parser_AST.arg_qualifier FStar_Pervasives_Native.option ->
    FStar_Pprint.document ->
      FStar_Parser_AST.term ->
        FStar_Parser_AST.term ->
          (FStar_Pprint.document * FStar_Pprint.document))
  =
  fun aqual_opt  ->
    fun binder  ->
      fun t  ->
        fun phi  ->
          let is_t_atomic =
            match t.FStar_Parser_AST.tm with
            | FStar_Parser_AST.Construct uu____46595 -> false
            | FStar_Parser_AST.App uu____46607 -> false
            | FStar_Parser_AST.Op uu____46615 -> false
            | uu____46623 -> true  in
          let uu____46625 = p_noSeqTerm false false phi  in
          match uu____46625 with
          | (comm,phi1) ->
              let phi2 =
                if comm = FStar_Pprint.empty
                then phi1
                else
                  (let uu____46642 =
                     FStar_Pprint.op_Hat_Hat FStar_Pprint.hardline phi1  in
                   FStar_Pprint.op_Hat_Hat comm uu____46642)
                 in
              let jump_break =
                if is_t_atomic
                then (Prims.parse_int "0")
                else (Prims.parse_int "1")  in
              let uu____46651 =
                let uu____46652 = FStar_Pprint.optional p_aqual aqual_opt  in
                FStar_Pprint.op_Hat_Hat uu____46652 binder  in
              let uu____46653 =
                let uu____46654 = p_appTerm t  in
                let uu____46655 =
                  let uu____46656 =
                    let uu____46657 =
                      let uu____46658 = soft_braces_with_nesting_tight phi2
                         in
                      let uu____46659 = soft_braces_with_nesting phi2  in
                      FStar_Pprint.ifflat uu____46658 uu____46659  in
                    FStar_Pprint.group uu____46657  in
                  FStar_Pprint.jump (Prims.parse_int "2") jump_break
                    uu____46656
                   in
                FStar_Pprint.op_Hat_Hat uu____46654 uu____46655  in
              (uu____46651, uu____46653)

and (p_binders_list :
  Prims.bool ->
    FStar_Parser_AST.binder Prims.list -> FStar_Pprint.document Prims.list)
  = fun is_atomic  -> fun bs  -> FStar_List.map (p_binder is_atomic) bs

and (p_binders :
  Prims.bool -> FStar_Parser_AST.binder Prims.list -> FStar_Pprint.document)
  =
  fun is_atomic  ->
    fun bs  ->
      let uu____46673 = p_binders_list is_atomic bs  in
      separate_or_flow break1 uu____46673

and (text_of_id_or_underscore : FStar_Ident.ident -> FStar_Pprint.document) =
  fun lid  ->
    let uu____46677 =
      (FStar_Util.starts_with lid.FStar_Ident.idText
         FStar_Ident.reserved_prefix)
        &&
        (let uu____46680 = FStar_Options.print_real_names ()  in
         Prims.op_Negation uu____46680)
       in
    if uu____46677
    then FStar_Pprint.underscore
    else (let uu____46685 = FStar_Ident.text_of_id lid  in str uu____46685)

and (text_of_lid_or_underscore : FStar_Ident.lident -> FStar_Pprint.document)
  =
  fun lid  ->
    let uu____46688 =
      (FStar_Util.starts_with (lid.FStar_Ident.ident).FStar_Ident.idText
         FStar_Ident.reserved_prefix)
        &&
        (let uu____46691 = FStar_Options.print_real_names ()  in
         Prims.op_Negation uu____46691)
       in
    if uu____46688
    then FStar_Pprint.underscore
    else (let uu____46696 = FStar_Ident.text_of_lid lid  in str uu____46696)

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

and (inline_comment_or_above :
  FStar_Pprint.document ->
    FStar_Pprint.document -> FStar_Pprint.document -> FStar_Pprint.document)
  =
  fun comm  ->
    fun doc1  ->
      fun sep  ->
        if comm = FStar_Pprint.empty
        then
          let uu____46717 = FStar_Pprint.op_Hat_Hat doc1 sep  in
          FStar_Pprint.group uu____46717
        else
          (let uu____46720 =
             let uu____46721 =
               let uu____46722 =
                 let uu____46723 =
                   let uu____46724 = FStar_Pprint.op_Hat_Hat break1 comm  in
                   FStar_Pprint.op_Hat_Hat sep uu____46724  in
                 FStar_Pprint.op_Hat_Hat doc1 uu____46723  in
               FStar_Pprint.group uu____46722  in
             let uu____46725 =
               let uu____46726 =
                 let uu____46727 = FStar_Pprint.op_Hat_Hat doc1 sep  in
                 FStar_Pprint.op_Hat_Hat FStar_Pprint.hardline uu____46727
                  in
               FStar_Pprint.op_Hat_Hat comm uu____46726  in
             FStar_Pprint.ifflat uu____46721 uu____46725  in
           FStar_All.pipe_left FStar_Pprint.group uu____46720)

and (p_term :
  Prims.bool -> Prims.bool -> FStar_Parser_AST.term -> FStar_Pprint.document)
  =
  fun ps  ->
    fun pb  ->
      fun e  ->
        match e.FStar_Parser_AST.tm with
        | FStar_Parser_AST.Seq (e1,e2) ->
            let uu____46735 = p_noSeqTerm true false e1  in
            (match uu____46735 with
             | (comm,t1) ->
                 let uu____46744 =
                   inline_comment_or_above comm t1 FStar_Pprint.semi  in
                 let uu____46745 =
                   let uu____46746 = p_term ps pb e2  in
                   FStar_Pprint.op_Hat_Hat FStar_Pprint.hardline uu____46746
                    in
                 FStar_Pprint.op_Hat_Hat uu____46744 uu____46745)
        | FStar_Parser_AST.Bind (x,e1,e2) ->
            let uu____46750 =
              let uu____46751 =
                let uu____46752 =
                  let uu____46753 = p_lident x  in
                  let uu____46754 =
                    FStar_Pprint.op_Hat_Hat FStar_Pprint.space
                      FStar_Pprint.long_left_arrow
                     in
                  FStar_Pprint.op_Hat_Hat uu____46753 uu____46754  in
                let uu____46755 =
                  let uu____46756 = p_noSeqTermAndComment true false e1  in
                  let uu____46759 =
                    FStar_Pprint.op_Hat_Hat FStar_Pprint.space
                      FStar_Pprint.semi
                     in
                  FStar_Pprint.op_Hat_Hat uu____46756 uu____46759  in
                op_Hat_Slash_Plus_Hat uu____46752 uu____46755  in
              FStar_Pprint.group uu____46751  in
            let uu____46760 = p_term ps pb e2  in
            FStar_Pprint.op_Hat_Slash_Hat uu____46750 uu____46760
        | uu____46761 ->
            let uu____46762 = p_noSeqTermAndComment ps pb e  in
            FStar_Pprint.group uu____46762

and (p_term_sep :
  Prims.bool ->
    Prims.bool ->
      FStar_Parser_AST.term ->
        (FStar_Pprint.document * FStar_Pprint.document))
  =
  fun ps  ->
    fun pb  ->
      fun e  ->
        match e.FStar_Parser_AST.tm with
        | FStar_Parser_AST.Seq (e1,e2) ->
            let uu____46774 = p_noSeqTerm true false e1  in
            (match uu____46774 with
             | (comm,t1) ->
                 let uu____46787 =
                   let uu____46788 =
                     let uu____46789 =
                       FStar_Pprint.op_Hat_Hat t1 FStar_Pprint.semi  in
                     FStar_Pprint.group uu____46789  in
                   let uu____46790 =
                     let uu____46791 = p_term ps pb e2  in
                     FStar_Pprint.op_Hat_Hat FStar_Pprint.hardline
                       uu____46791
                      in
                   FStar_Pprint.op_Hat_Hat uu____46788 uu____46790  in
                 (comm, uu____46787))
        | FStar_Parser_AST.Bind (x,e1,e2) ->
            let uu____46795 =
              let uu____46796 =
                let uu____46797 =
                  let uu____46798 =
                    let uu____46799 = p_lident x  in
                    let uu____46800 =
                      FStar_Pprint.op_Hat_Hat FStar_Pprint.space
                        FStar_Pprint.long_left_arrow
                       in
                    FStar_Pprint.op_Hat_Hat uu____46799 uu____46800  in
                  let uu____46801 =
                    let uu____46802 = p_noSeqTermAndComment true false e1  in
                    let uu____46805 =
                      FStar_Pprint.op_Hat_Hat FStar_Pprint.space
                        FStar_Pprint.semi
                       in
                    FStar_Pprint.op_Hat_Hat uu____46802 uu____46805  in
                  op_Hat_Slash_Plus_Hat uu____46798 uu____46801  in
                FStar_Pprint.group uu____46797  in
              let uu____46806 = p_term ps pb e2  in
              FStar_Pprint.op_Hat_Slash_Hat uu____46796 uu____46806  in
            (FStar_Pprint.empty, uu____46795)
        | uu____46807 -> p_noSeqTerm ps pb e

and (p_noSeqTerm :
  Prims.bool ->
    Prims.bool ->
      FStar_Parser_AST.term ->
        (FStar_Pprint.document * FStar_Pprint.document))
  =
  fun ps  ->
    fun pb  ->
      fun e  ->
        with_comment_sep (p_noSeqTerm' ps pb) e e.FStar_Parser_AST.range

and (p_noSeqTermAndComment :
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
            let uu____46827 =
              let uu____46828 = p_tmIff e1  in
              let uu____46829 =
                let uu____46830 =
                  let uu____46831 = p_typ ps pb t  in
                  FStar_Pprint.op_Hat_Slash_Hat FStar_Pprint.colon
                    uu____46831
                   in
                FStar_Pprint.op_Hat_Hat FStar_Pprint.langle uu____46830  in
              FStar_Pprint.op_Hat_Slash_Hat uu____46828 uu____46829  in
            FStar_Pprint.group uu____46827
        | FStar_Parser_AST.Ascribed (e1,t,FStar_Pervasives_Native.Some tac)
            ->
            let uu____46837 =
              let uu____46838 = p_tmIff e1  in
              let uu____46839 =
                let uu____46840 =
                  let uu____46841 =
                    let uu____46842 = p_typ false false t  in
                    let uu____46845 =
                      let uu____46846 = str "by"  in
                      let uu____46848 = p_typ ps pb tac  in
                      FStar_Pprint.op_Hat_Slash_Hat uu____46846 uu____46848
                       in
                    FStar_Pprint.op_Hat_Slash_Hat uu____46842 uu____46845  in
                  FStar_Pprint.op_Hat_Slash_Hat FStar_Pprint.colon
                    uu____46841
                   in
                FStar_Pprint.op_Hat_Hat FStar_Pprint.langle uu____46840  in
              FStar_Pprint.op_Hat_Slash_Hat uu____46838 uu____46839  in
            FStar_Pprint.group uu____46837
        | FStar_Parser_AST.Op
            ({ FStar_Ident.idText = ".()<-";
               FStar_Ident.idRange = uu____46849;_},e1::e2::e3::[])
            ->
            let uu____46856 =
              let uu____46857 =
                let uu____46858 =
                  let uu____46859 = p_atomicTermNotQUident e1  in
                  let uu____46860 =
                    let uu____46861 =
                      let uu____46862 =
                        let uu____46863 = p_term false false e2  in
                        soft_parens_with_nesting uu____46863  in
                      let uu____46866 =
                        FStar_Pprint.op_Hat_Hat FStar_Pprint.space
                          FStar_Pprint.larrow
                         in
                      FStar_Pprint.op_Hat_Hat uu____46862 uu____46866  in
                    FStar_Pprint.op_Hat_Hat FStar_Pprint.dot uu____46861  in
                  FStar_Pprint.op_Hat_Hat uu____46859 uu____46860  in
                FStar_Pprint.group uu____46858  in
              let uu____46867 =
                let uu____46868 = p_noSeqTermAndComment ps pb e3  in
                jump2 uu____46868  in
              FStar_Pprint.op_Hat_Hat uu____46857 uu____46867  in
            FStar_Pprint.group uu____46856
        | FStar_Parser_AST.Op
            ({ FStar_Ident.idText = ".[]<-";
               FStar_Ident.idRange = uu____46869;_},e1::e2::e3::[])
            ->
            let uu____46876 =
              let uu____46877 =
                let uu____46878 =
                  let uu____46879 = p_atomicTermNotQUident e1  in
                  let uu____46880 =
                    let uu____46881 =
                      let uu____46882 =
                        let uu____46883 = p_term false false e2  in
                        soft_brackets_with_nesting uu____46883  in
                      let uu____46886 =
                        FStar_Pprint.op_Hat_Hat FStar_Pprint.space
                          FStar_Pprint.larrow
                         in
                      FStar_Pprint.op_Hat_Hat uu____46882 uu____46886  in
                    FStar_Pprint.op_Hat_Hat FStar_Pprint.dot uu____46881  in
                  FStar_Pprint.op_Hat_Hat uu____46879 uu____46880  in
                FStar_Pprint.group uu____46878  in
              let uu____46887 =
                let uu____46888 = p_noSeqTermAndComment ps pb e3  in
                jump2 uu____46888  in
              FStar_Pprint.op_Hat_Hat uu____46877 uu____46887  in
            FStar_Pprint.group uu____46876
        | FStar_Parser_AST.Requires (e1,wtf) ->
            let uu____46898 =
              let uu____46899 = str "requires"  in
              let uu____46901 = p_typ ps pb e1  in
              FStar_Pprint.op_Hat_Slash_Hat uu____46899 uu____46901  in
            FStar_Pprint.group uu____46898
        | FStar_Parser_AST.Ensures (e1,wtf) ->
            let uu____46911 =
              let uu____46912 = str "ensures"  in
              let uu____46914 = p_typ ps pb e1  in
              FStar_Pprint.op_Hat_Slash_Hat uu____46912 uu____46914  in
            FStar_Pprint.group uu____46911
        | FStar_Parser_AST.Attributes es ->
            let uu____46918 =
              let uu____46919 = str "attributes"  in
              let uu____46921 =
                FStar_Pprint.separate_map break1 p_atomicTerm es  in
              FStar_Pprint.op_Hat_Slash_Hat uu____46919 uu____46921  in
            FStar_Pprint.group uu____46918
        | FStar_Parser_AST.If (e1,e2,e3) ->
            if is_unit e3
            then
              let uu____46926 =
                let uu____46927 =
                  let uu____46928 = str "if"  in
                  let uu____46930 = p_noSeqTermAndComment false false e1  in
                  op_Hat_Slash_Plus_Hat uu____46928 uu____46930  in
                let uu____46933 =
                  let uu____46934 = str "then"  in
                  let uu____46936 = p_noSeqTermAndComment ps pb e2  in
                  op_Hat_Slash_Plus_Hat uu____46934 uu____46936  in
                FStar_Pprint.op_Hat_Slash_Hat uu____46927 uu____46933  in
              FStar_Pprint.group uu____46926
            else
              (let e2_doc =
                 match e2.FStar_Parser_AST.tm with
                 | FStar_Parser_AST.If (uu____46940,uu____46941,e31) when
                     is_unit e31 ->
                     let uu____46943 = p_noSeqTermAndComment false false e2
                        in
                     soft_parens_with_nesting uu____46943
                 | uu____46946 -> p_noSeqTermAndComment false false e2  in
               let uu____46949 =
                 let uu____46950 =
                   let uu____46951 = str "if"  in
                   let uu____46953 = p_noSeqTermAndComment false false e1  in
                   op_Hat_Slash_Plus_Hat uu____46951 uu____46953  in
                 let uu____46956 =
                   let uu____46957 =
                     let uu____46958 = str "then"  in
                     op_Hat_Slash_Plus_Hat uu____46958 e2_doc  in
                   let uu____46960 =
                     let uu____46961 = str "else"  in
                     let uu____46963 = p_noSeqTermAndComment ps pb e3  in
                     op_Hat_Slash_Plus_Hat uu____46961 uu____46963  in
                   FStar_Pprint.op_Hat_Slash_Hat uu____46957 uu____46960  in
                 FStar_Pprint.op_Hat_Slash_Hat uu____46950 uu____46956  in
               FStar_Pprint.group uu____46949)
        | FStar_Parser_AST.TryWith (e1,branches) ->
            let uu____46986 =
              let uu____46987 =
                let uu____46988 =
                  let uu____46989 = str "try"  in
                  let uu____46991 = p_noSeqTermAndComment false false e1  in
                  prefix2 uu____46989 uu____46991  in
                let uu____46994 =
                  let uu____46995 = str "with"  in
                  let uu____46997 =
                    separate_map_last FStar_Pprint.hardline p_patternBranch
                      branches
                     in
                  FStar_Pprint.op_Hat_Slash_Hat uu____46995 uu____46997  in
                FStar_Pprint.op_Hat_Slash_Hat uu____46988 uu____46994  in
              FStar_Pprint.group uu____46987  in
            let uu____47006 = paren_if (ps || pb)  in uu____47006 uu____46986
        | FStar_Parser_AST.Match (e1,branches) ->
            let uu____47033 =
              let uu____47034 =
                let uu____47035 =
                  let uu____47036 = str "match"  in
                  let uu____47038 = p_noSeqTermAndComment false false e1  in
                  let uu____47041 = str "with"  in
                  FStar_Pprint.surround (Prims.parse_int "2")
                    (Prims.parse_int "1") uu____47036 uu____47038 uu____47041
                   in
                let uu____47045 =
                  separate_map_last FStar_Pprint.hardline p_patternBranch
                    branches
                   in
                FStar_Pprint.op_Hat_Slash_Hat uu____47035 uu____47045  in
              FStar_Pprint.group uu____47034  in
            let uu____47054 = paren_if (ps || pb)  in uu____47054 uu____47033
        | FStar_Parser_AST.LetOpen (uid,e1) ->
            let uu____47061 =
              let uu____47062 =
                let uu____47063 =
                  let uu____47064 = str "let open"  in
                  let uu____47066 = p_quident uid  in
                  let uu____47067 = str "in"  in
                  FStar_Pprint.surround (Prims.parse_int "2")
                    (Prims.parse_int "1") uu____47064 uu____47066 uu____47067
                   in
                let uu____47071 = p_term false pb e1  in
                FStar_Pprint.op_Hat_Slash_Hat uu____47063 uu____47071  in
              FStar_Pprint.group uu____47062  in
            let uu____47073 = paren_if ps  in uu____47073 uu____47061
        | FStar_Parser_AST.Let (q,lbs,e1) ->
            let p_lb q1 uu____47138 is_last =
              match uu____47138 with
              | (a,(pat,e2)) ->
                  let attrs = p_attrs_opt a  in
                  let doc_let_or_and =
                    match q1 with
                    | FStar_Pervasives_Native.Some (FStar_Parser_AST.Rec ) ->
                        let uu____47172 =
                          let uu____47173 = str "let"  in
                          let uu____47175 = str "rec"  in
                          FStar_Pprint.op_Hat_Slash_Hat uu____47173
                            uu____47175
                           in
                        FStar_Pprint.group uu____47172
                    | FStar_Pervasives_Native.Some
                        (FStar_Parser_AST.NoLetQualifier ) -> str "let"
                    | uu____47178 -> str "and"  in
                  let doc_pat = p_letlhs doc_let_or_and (pat, e2) true  in
                  let uu____47184 = p_term_sep false false e2  in
                  (match uu____47184 with
                   | (comm,doc_expr) ->
                       let doc_expr1 =
                         inline_comment_or_above comm doc_expr
                           FStar_Pprint.empty
                          in
                       let uu____47194 =
                         if is_last
                         then
                           let uu____47196 =
                             FStar_Pprint.flow break1
                               [doc_pat; FStar_Pprint.equals]
                              in
                           let uu____47197 = str "in"  in
                           FStar_Pprint.surround (Prims.parse_int "2")
                             (Prims.parse_int "1") uu____47196 doc_expr1
                             uu____47197
                         else
                           (let uu____47203 =
                              FStar_Pprint.flow break1
                                [doc_pat; FStar_Pprint.equals; doc_expr1]
                               in
                            FStar_Pprint.hang (Prims.parse_int "2")
                              uu____47203)
                          in
                       FStar_Pprint.op_Hat_Hat attrs uu____47194)
               in
            let l = FStar_List.length lbs  in
            let lbs_docs =
              FStar_List.mapi
                (fun i  ->
                   fun lb  ->
                     if i = (Prims.parse_int "0")
                     then
                       let uu____47254 =
                         p_lb (FStar_Pervasives_Native.Some q) lb
                           (i = (l - (Prims.parse_int "1")))
                          in
                       FStar_Pprint.group uu____47254
                     else
                       (let uu____47259 =
                          p_lb FStar_Pervasives_Native.None lb
                            (i = (l - (Prims.parse_int "1")))
                           in
                        FStar_Pprint.group uu____47259)) lbs
               in
            let lbs_doc =
              let uu____47263 = FStar_Pprint.separate break1 lbs_docs  in
              FStar_Pprint.group uu____47263  in
            let uu____47264 =
              let uu____47265 =
                let uu____47266 =
                  let uu____47267 = p_term false pb e1  in
                  FStar_Pprint.op_Hat_Hat FStar_Pprint.hardline uu____47267
                   in
                FStar_Pprint.op_Hat_Hat lbs_doc uu____47266  in
              FStar_Pprint.group uu____47265  in
            let uu____47269 = paren_if ps  in uu____47269 uu____47264
        | FStar_Parser_AST.Abs
            ({ FStar_Parser_AST.pat = FStar_Parser_AST.PatVar (x,typ_opt);
               FStar_Parser_AST.prange = uu____47276;_}::[],{
                                                              FStar_Parser_AST.tm
                                                                =
                                                                FStar_Parser_AST.Match
                                                                (maybe_x,branches);
                                                              FStar_Parser_AST.range
                                                                = uu____47279;
                                                              FStar_Parser_AST.level
                                                                = uu____47280;_})
            when matches_var maybe_x x ->
            let uu____47307 =
              let uu____47308 =
                let uu____47309 = str "function"  in
                let uu____47311 =
                  separate_map_last FStar_Pprint.hardline p_patternBranch
                    branches
                   in
                FStar_Pprint.op_Hat_Slash_Hat uu____47309 uu____47311  in
              FStar_Pprint.group uu____47308  in
            let uu____47320 = paren_if (ps || pb)  in uu____47320 uu____47307
        | FStar_Parser_AST.Quote (e1,FStar_Parser_AST.Dynamic ) ->
            let uu____47326 =
              let uu____47327 = str "quote"  in
              let uu____47329 = p_noSeqTermAndComment ps pb e1  in
              FStar_Pprint.op_Hat_Slash_Hat uu____47327 uu____47329  in
            FStar_Pprint.group uu____47326
        | FStar_Parser_AST.Quote (e1,FStar_Parser_AST.Static ) ->
            let uu____47331 =
              let uu____47332 = str "`"  in
              let uu____47334 = p_noSeqTermAndComment ps pb e1  in
              FStar_Pprint.op_Hat_Hat uu____47332 uu____47334  in
            FStar_Pprint.group uu____47331
        | FStar_Parser_AST.VQuote e1 ->
            let uu____47336 =
              let uu____47337 = str "`%"  in
              let uu____47339 = p_noSeqTermAndComment ps pb e1  in
              FStar_Pprint.op_Hat_Hat uu____47337 uu____47339  in
            FStar_Pprint.group uu____47336
        | FStar_Parser_AST.Antiquote
            {
              FStar_Parser_AST.tm = FStar_Parser_AST.Quote
                (e1,FStar_Parser_AST.Dynamic );
              FStar_Parser_AST.range = uu____47341;
              FStar_Parser_AST.level = uu____47342;_}
            ->
            let uu____47343 =
              let uu____47344 = str "`@"  in
              let uu____47346 = p_noSeqTermAndComment ps pb e1  in
              FStar_Pprint.op_Hat_Hat uu____47344 uu____47346  in
            FStar_Pprint.group uu____47343
        | FStar_Parser_AST.Antiquote e1 ->
            let uu____47348 =
              let uu____47349 = str "`#"  in
              let uu____47351 = p_noSeqTermAndComment ps pb e1  in
              FStar_Pprint.op_Hat_Hat uu____47349 uu____47351  in
            FStar_Pprint.group uu____47348
        | FStar_Parser_AST.CalcProof (rel,init1,steps) ->
            let head1 =
              let uu____47360 = str "calc"  in
              let uu____47362 =
                let uu____47363 =
                  let uu____47364 = p_noSeqTermAndComment false false rel  in
                  let uu____47367 =
                    FStar_Pprint.op_Hat_Hat FStar_Pprint.space
                      FStar_Pprint.lbrace
                     in
                  FStar_Pprint.op_Hat_Hat uu____47364 uu____47367  in
                FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____47363  in
              FStar_Pprint.op_Hat_Hat uu____47360 uu____47362  in
            let bot = FStar_Pprint.rbrace  in
            let uu____47369 =
              FStar_Pprint.op_Hat_Hat FStar_Pprint.hardline bot  in
            let uu____47370 =
              let uu____47371 =
                let uu____47372 =
                  let uu____47373 = p_noSeqTermAndComment false false init1
                     in
                  let uu____47376 =
                    let uu____47377 = str ";"  in
                    let uu____47379 =
                      let uu____47380 =
                        separate_map_last FStar_Pprint.hardline p_calcStep
                          steps
                         in
                      FStar_Pprint.op_Hat_Hat FStar_Pprint.hardline
                        uu____47380
                       in
                    FStar_Pprint.op_Hat_Hat uu____47377 uu____47379  in
                  FStar_Pprint.op_Hat_Hat uu____47373 uu____47376  in
                FStar_Pprint.op_Hat_Hat FStar_Pprint.hardline uu____47372  in
              FStar_All.pipe_left (FStar_Pprint.nest (Prims.parse_int "2"))
                uu____47371
               in
            FStar_Pprint.enclose head1 uu____47369 uu____47370
        | uu____47382 -> p_typ ps pb e

and (p_calcStep :
  Prims.bool -> FStar_Parser_AST.calc_step -> FStar_Pprint.document) =
  fun uu____47383  ->
    fun uu____47384  ->
      match uu____47384 with
      | FStar_Parser_AST.CalcStep (rel,just,next) ->
          let uu____47389 =
            let uu____47390 = p_noSeqTermAndComment false false rel  in
            let uu____47393 =
              let uu____47394 =
                let uu____47395 =
                  let uu____47396 =
                    let uu____47397 = p_noSeqTermAndComment false false just
                       in
                    let uu____47400 =
                      let uu____47401 =
                        let uu____47402 =
                          let uu____47403 =
                            let uu____47404 =
                              p_noSeqTermAndComment false false next  in
                            let uu____47407 = str ";"  in
                            FStar_Pprint.op_Hat_Hat uu____47404 uu____47407
                             in
                          FStar_Pprint.op_Hat_Hat FStar_Pprint.hardline
                            uu____47403
                           in
                        FStar_Pprint.op_Hat_Hat FStar_Pprint.rbrace
                          uu____47402
                         in
                      FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____47401
                       in
                    FStar_Pprint.op_Hat_Hat uu____47397 uu____47400  in
                  FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____47396  in
                FStar_Pprint.op_Hat_Hat FStar_Pprint.lbrace uu____47395  in
              FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____47394  in
            FStar_Pprint.op_Hat_Hat uu____47390 uu____47393  in
          FStar_Pprint.group uu____47389

and (p_attrs_opt :
  FStar_Parser_AST.term Prims.list FStar_Pervasives_Native.option ->
    FStar_Pprint.document)
  =
  fun uu___335_47409  ->
    match uu___335_47409 with
    | FStar_Pervasives_Native.None  -> FStar_Pprint.empty
    | FStar_Pervasives_Native.Some terms ->
        let uu____47421 =
          let uu____47422 = str "[@"  in
          let uu____47424 =
            let uu____47425 =
              FStar_Pprint.separate_map break1 p_atomicTerm terms  in
            let uu____47426 = str "]"  in
            FStar_Pprint.op_Hat_Slash_Hat uu____47425 uu____47426  in
          FStar_Pprint.op_Hat_Slash_Hat uu____47422 uu____47424  in
        FStar_Pprint.group uu____47421

and (p_typ :
  Prims.bool -> Prims.bool -> FStar_Parser_AST.term -> FStar_Pprint.document)
  =
  fun ps  ->
    fun pb  ->
      fun e  -> with_comment (p_typ' ps pb) e e.FStar_Parser_AST.range

and (p_typ_sep :
  Prims.bool ->
    Prims.bool ->
      FStar_Parser_AST.term ->
        (FStar_Pprint.document * FStar_Pprint.document))
  =
  fun ps  ->
    fun pb  ->
      fun e  -> with_comment_sep (p_typ' ps pb) e e.FStar_Parser_AST.range

and (p_typ' :
  Prims.bool -> Prims.bool -> FStar_Parser_AST.term -> FStar_Pprint.document)
  =
  fun ps  ->
    fun pb  ->
      fun e  ->
        match e.FStar_Parser_AST.tm with
        | FStar_Parser_AST.QForall (bs,trigger,e1) ->
            let binders_doc = p_binders true bs  in
            let term_doc = p_noSeqTermAndComment ps pb e1  in
            (match trigger with
             | [] ->
                 let uu____47463 =
                   let uu____47464 =
                     let uu____47465 = p_quantifier e  in
                     FStar_Pprint.op_Hat_Hat uu____47465 FStar_Pprint.space
                      in
                   FStar_Pprint.soft_surround (Prims.parse_int "2")
                     (Prims.parse_int "0") uu____47464 binders_doc
                     FStar_Pprint.dot
                    in
                 prefix2 uu____47463 term_doc
             | pats ->
                 let uu____47473 =
                   let uu____47474 =
                     let uu____47475 =
                       let uu____47476 =
                         let uu____47477 = p_quantifier e  in
                         FStar_Pprint.op_Hat_Hat uu____47477
                           FStar_Pprint.space
                          in
                       FStar_Pprint.soft_surround (Prims.parse_int "2")
                         (Prims.parse_int "0") uu____47476 binders_doc
                         FStar_Pprint.dot
                        in
                     let uu____47480 = p_trigger trigger  in
                     prefix2 uu____47475 uu____47480  in
                   FStar_Pprint.group uu____47474  in
                 prefix2 uu____47473 term_doc)
        | FStar_Parser_AST.QExists (bs,trigger,e1) ->
            let binders_doc = p_binders true bs  in
            let term_doc = p_noSeqTermAndComment ps pb e1  in
            (match trigger with
             | [] ->
                 let uu____47501 =
                   let uu____47502 =
                     let uu____47503 = p_quantifier e  in
                     FStar_Pprint.op_Hat_Hat uu____47503 FStar_Pprint.space
                      in
                   FStar_Pprint.soft_surround (Prims.parse_int "2")
                     (Prims.parse_int "0") uu____47502 binders_doc
                     FStar_Pprint.dot
                    in
                 prefix2 uu____47501 term_doc
             | pats ->
                 let uu____47511 =
                   let uu____47512 =
                     let uu____47513 =
                       let uu____47514 =
                         let uu____47515 = p_quantifier e  in
                         FStar_Pprint.op_Hat_Hat uu____47515
                           FStar_Pprint.space
                          in
                       FStar_Pprint.soft_surround (Prims.parse_int "2")
                         (Prims.parse_int "0") uu____47514 binders_doc
                         FStar_Pprint.dot
                        in
                     let uu____47518 = p_trigger trigger  in
                     prefix2 uu____47513 uu____47518  in
                   FStar_Pprint.group uu____47512  in
                 prefix2 uu____47511 term_doc)
        | uu____47519 -> p_simpleTerm ps pb e

and (p_typ_top :
  annotation_style ->
    Prims.bool ->
      Prims.bool -> FStar_Parser_AST.term -> FStar_Pprint.document)
  =
  fun style  ->
    fun ps  ->
      fun pb  ->
        fun e  ->
          with_comment (p_typ_top' style ps pb) e e.FStar_Parser_AST.range

and (p_typ_top' :
  annotation_style ->
    Prims.bool ->
      Prims.bool -> FStar_Parser_AST.term -> FStar_Pprint.document)
  =
  fun style  ->
    fun ps  -> fun pb  -> fun e  -> p_tmArrow style true p_tmFormula e

and (sig_as_binders_if_possible :
  FStar_Parser_AST.term -> Prims.bool -> FStar_Pprint.document) =
  fun t  ->
    fun extra_space  ->
      let s = if extra_space then FStar_Pprint.space else FStar_Pprint.empty
         in
      let uu____47540 = all_binders_annot t  in
      if uu____47540
      then
        let uu____47543 =
          p_typ_top
            (Binders ((Prims.parse_int "4"), (Prims.parse_int "0"), true))
            false false t
           in
        FStar_Pprint.op_Hat_Hat s uu____47543
      else
        (let uu____47554 =
           let uu____47555 =
             let uu____47556 =
               p_typ_top
                 (Arrows ((Prims.parse_int "2"), (Prims.parse_int "2")))
                 false false t
                in
             FStar_Pprint.op_Hat_Hat s uu____47556  in
           FStar_Pprint.op_Hat_Hat FStar_Pprint.colon uu____47555  in
         FStar_Pprint.group uu____47554)

and (collapse_pats :
  (FStar_Pprint.document * FStar_Pprint.document) Prims.list ->
    FStar_Pprint.document Prims.list)
  =
  fun pats  ->
    let fold_fun bs x =
      let uu____47615 = x  in
      match uu____47615 with
      | (b1,t1) ->
          (match bs with
           | [] -> [([b1], t1)]
           | hd1::tl1 ->
               let uu____47680 = hd1  in
               (match uu____47680 with
                | (b2s,t2) ->
                    if t1 = t2
                    then ((FStar_List.append b2s [b1]), t1) :: tl1
                    else ([b1], t1) :: hd1 :: tl1))
       in
    let p_collapsed_binder cb =
      let uu____47752 = cb  in
      match uu____47752 with
      | (bs,typ) ->
          (match bs with
           | [] -> failwith "Impossible"
           | b::[] -> cat_with_colon b typ
           | hd1::tl1 ->
               let uu____47771 =
                 FStar_List.fold_left
                   (fun x  ->
                      fun y  ->
                        let uu____47777 =
                          FStar_Pprint.op_Hat_Hat FStar_Pprint.space y  in
                        FStar_Pprint.op_Hat_Hat x uu____47777) hd1 tl1
                  in
               cat_with_colon uu____47771 typ)
       in
    let binders = FStar_List.fold_left fold_fun [] (FStar_List.rev pats)  in
    map_rev p_collapsed_binder binders

and (pats_as_binders_if_possible :
  FStar_Parser_AST.pattern Prims.list ->
    (FStar_Pprint.document Prims.list * annotation_style))
  =
  fun pats  ->
    let all_binders p =
      match p.FStar_Parser_AST.pat with
      | FStar_Parser_AST.PatAscribed (pat,(t,FStar_Pervasives_Native.None ))
          ->
          (match ((pat.FStar_Parser_AST.pat), (t.FStar_Parser_AST.tm)) with
           | (FStar_Parser_AST.PatVar (lid,aqual),FStar_Parser_AST.Refine
              ({ FStar_Parser_AST.b = FStar_Parser_AST.Annotated (lid',t1);
                 FStar_Parser_AST.brange = uu____47856;
                 FStar_Parser_AST.blevel = uu____47857;
                 FStar_Parser_AST.aqual = uu____47858;_},phi))
               when lid.FStar_Ident.idText = lid'.FStar_Ident.idText ->
               let uu____47867 =
                 let uu____47872 = p_ident lid  in
                 p_refinement' aqual uu____47872 t1 phi  in
               FStar_Pervasives_Native.Some uu____47867
           | (FStar_Parser_AST.PatVar (lid,aqual),uu____47879) ->
               let uu____47884 =
                 let uu____47889 =
                   let uu____47890 = FStar_Pprint.optional p_aqual aqual  in
                   let uu____47891 = p_ident lid  in
                   FStar_Pprint.op_Hat_Hat uu____47890 uu____47891  in
                 let uu____47892 = p_tmEqNoRefinement t  in
                 (uu____47889, uu____47892)  in
               FStar_Pervasives_Native.Some uu____47884
           | uu____47897 -> FStar_Pervasives_Native.None)
      | uu____47906 -> FStar_Pervasives_Native.None  in
    let all_unbound p =
      match p.FStar_Parser_AST.pat with
      | FStar_Parser_AST.PatAscribed uu____47919 -> false
      | uu____47931 -> true  in
    let uu____47933 = map_if_all all_binders pats  in
    match uu____47933 with
    | FStar_Pervasives_Native.Some bs ->
        let uu____47965 = collapse_pats bs  in
        (uu____47965,
          (Binders ((Prims.parse_int "4"), (Prims.parse_int "0"), true)))
    | FStar_Pervasives_Native.None  ->
        let uu____47982 = FStar_List.map p_atomicPattern pats  in
        (uu____47982,
          (Binders ((Prims.parse_int "4"), (Prims.parse_int "0"), false)))

and (p_quantifier : FStar_Parser_AST.term -> FStar_Pprint.document) =
  fun e  ->
    match e.FStar_Parser_AST.tm with
    | FStar_Parser_AST.QForall uu____47994 -> str "forall"
    | FStar_Parser_AST.QExists uu____48008 -> str "exists"
    | uu____48022 ->
        failwith "Imposible : p_quantifier called on a non-quantifier term"

and (p_trigger :
  FStar_Parser_AST.term Prims.list Prims.list -> FStar_Pprint.document) =
  fun uu___336_48024  ->
    match uu___336_48024 with
    | [] -> FStar_Pprint.empty
    | pats ->
        let uu____48036 =
          let uu____48037 =
            let uu____48038 =
              let uu____48039 = str "pattern"  in
              let uu____48041 =
                let uu____48042 =
                  let uu____48043 = p_disjunctivePats pats  in
                  FStar_Pprint.jump (Prims.parse_int "2")
                    (Prims.parse_int "0") uu____48043
                   in
                FStar_Pprint.op_Hat_Hat uu____48042 FStar_Pprint.rbrace  in
              FStar_Pprint.op_Hat_Slash_Hat uu____48039 uu____48041  in
            FStar_Pprint.op_Hat_Hat FStar_Pprint.colon uu____48038  in
          FStar_Pprint.op_Hat_Hat FStar_Pprint.lbrace uu____48037  in
        FStar_Pprint.group uu____48036

and (p_disjunctivePats :
  FStar_Parser_AST.term Prims.list Prims.list -> FStar_Pprint.document) =
  fun pats  ->
    let uu____48051 = str "\\/"  in
    FStar_Pprint.separate_map uu____48051 p_conjunctivePats pats

and (p_conjunctivePats :
  FStar_Parser_AST.term Prims.list -> FStar_Pprint.document) =
  fun pats  ->
    let uu____48058 =
      let uu____48059 = FStar_Pprint.op_Hat_Hat FStar_Pprint.semi break1  in
      FStar_Pprint.separate_map uu____48059 p_appTerm pats  in
    FStar_Pprint.group uu____48058

and (p_simpleTerm :
  Prims.bool -> Prims.bool -> FStar_Parser_AST.term -> FStar_Pprint.document)
  =
  fun ps  ->
    fun pb  ->
      fun e  ->
        match e.FStar_Parser_AST.tm with
        | FStar_Parser_AST.Abs (pats,e1) ->
            let uu____48071 = p_term_sep false pb e1  in
            (match uu____48071 with
             | (comm,doc1) ->
                 let prefix1 =
                   let uu____48080 = str "fun"  in
                   let uu____48082 =
                     let uu____48083 =
                       FStar_Pprint.separate_map break1 p_atomicPattern pats
                        in
                     FStar_Pprint.op_Hat_Slash_Hat uu____48083
                       FStar_Pprint.rarrow
                      in
                   op_Hat_Slash_Plus_Hat uu____48080 uu____48082  in
                 let uu____48084 =
                   if comm <> FStar_Pprint.empty
                   then
                     let uu____48086 =
                       let uu____48087 =
                         let uu____48088 =
                           FStar_Pprint.op_Hat_Hat FStar_Pprint.hardline doc1
                            in
                         FStar_Pprint.op_Hat_Hat comm uu____48088  in
                       FStar_Pprint.op_Hat_Hat FStar_Pprint.hardline
                         uu____48087
                        in
                     FStar_Pprint.op_Hat_Hat prefix1 uu____48086
                   else
                     (let uu____48091 = op_Hat_Slash_Plus_Hat prefix1 doc1
                         in
                      FStar_Pprint.group uu____48091)
                    in
                 let uu____48092 = paren_if ps  in uu____48092 uu____48084)
        | uu____48097 -> p_tmIff e

and (p_maybeFocusArrow : Prims.bool -> FStar_Pprint.document) =
  fun b  -> if b then str "~>" else FStar_Pprint.rarrow

and (p_patternBranch :
  Prims.bool ->
    (FStar_Parser_AST.pattern * FStar_Parser_AST.term
      FStar_Pervasives_Native.option * FStar_Parser_AST.term) ->
      FStar_Pprint.document)
  =
  fun pb  ->
    fun uu____48105  ->
      match uu____48105 with
      | (pat,when_opt,e) ->
          let one_pattern_branch p =
            let branch =
              match when_opt with
              | FStar_Pervasives_Native.None  ->
                  let uu____48129 =
                    let uu____48130 =
                      let uu____48131 =
                        let uu____48132 = p_tuplePattern p  in
                        let uu____48133 =
                          FStar_Pprint.op_Hat_Hat FStar_Pprint.space
                            FStar_Pprint.rarrow
                           in
                        FStar_Pprint.op_Hat_Hat uu____48132 uu____48133  in
                      FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____48131
                       in
                    FStar_Pprint.op_Hat_Hat FStar_Pprint.bar uu____48130  in
                  FStar_Pprint.group uu____48129
              | FStar_Pervasives_Native.Some f ->
                  let uu____48135 =
                    let uu____48136 =
                      let uu____48137 =
                        let uu____48138 =
                          let uu____48139 =
                            let uu____48140 = p_tuplePattern p  in
                            let uu____48141 = str "when"  in
                            FStar_Pprint.op_Hat_Slash_Hat uu____48140
                              uu____48141
                             in
                          FStar_Pprint.group uu____48139  in
                        let uu____48143 =
                          let uu____48144 =
                            let uu____48147 = p_tmFormula f  in
                            [uu____48147; FStar_Pprint.rarrow]  in
                          FStar_Pprint.flow break1 uu____48144  in
                        FStar_Pprint.op_Hat_Slash_Hat uu____48138 uu____48143
                         in
                      FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____48137
                       in
                    FStar_Pprint.op_Hat_Hat FStar_Pprint.bar uu____48136  in
                  FStar_Pprint.hang (Prims.parse_int "2") uu____48135
               in
            let uu____48149 = p_term_sep false pb e  in
            match uu____48149 with
            | (comm,doc1) ->
                if pb
                then
                  (if comm = FStar_Pprint.empty
                   then
                     let uu____48159 = op_Hat_Slash_Plus_Hat branch doc1  in
                     FStar_Pprint.group uu____48159
                   else
                     (let uu____48162 =
                        let uu____48163 =
                          let uu____48164 =
                            let uu____48165 =
                              let uu____48166 =
                                FStar_Pprint.op_Hat_Hat break1 comm  in
                              FStar_Pprint.op_Hat_Hat doc1 uu____48166  in
                            op_Hat_Slash_Plus_Hat branch uu____48165  in
                          FStar_Pprint.group uu____48164  in
                        let uu____48167 =
                          let uu____48168 =
                            let uu____48169 =
                              inline_comment_or_above comm doc1
                                FStar_Pprint.empty
                               in
                            jump2 uu____48169  in
                          FStar_Pprint.op_Hat_Hat branch uu____48168  in
                        FStar_Pprint.ifflat uu____48163 uu____48167  in
                      FStar_Pprint.group uu____48162))
                else
                  if comm <> FStar_Pprint.empty
                  then
                    (let uu____48173 =
                       let uu____48174 =
                         FStar_Pprint.op_Hat_Hat FStar_Pprint.hardline doc1
                          in
                       FStar_Pprint.op_Hat_Hat comm uu____48174  in
                     op_Hat_Slash_Plus_Hat branch uu____48173)
                  else op_Hat_Slash_Plus_Hat branch doc1
             in
          (match pat.FStar_Parser_AST.pat with
           | FStar_Parser_AST.PatOr pats ->
               (match FStar_List.rev pats with
                | hd1::tl1 ->
                    let last_pat_branch = one_pattern_branch hd1  in
                    let uu____48185 =
                      let uu____48186 =
                        let uu____48187 =
                          let uu____48188 =
                            let uu____48189 =
                              let uu____48190 =
                                FStar_Pprint.op_Hat_Hat FStar_Pprint.bar
                                  FStar_Pprint.space
                                 in
                              FStar_Pprint.op_Hat_Hat break1 uu____48190  in
                            FStar_Pprint.separate_map uu____48189
                              p_tuplePattern (FStar_List.rev tl1)
                             in
                          FStar_Pprint.op_Hat_Slash_Hat uu____48188
                            last_pat_branch
                           in
                        FStar_Pprint.op_Hat_Hat FStar_Pprint.space
                          uu____48187
                         in
                      FStar_Pprint.op_Hat_Hat FStar_Pprint.bar uu____48186
                       in
                    FStar_Pprint.group uu____48185
                | [] ->
                    failwith "Impossible: disjunctive pattern can't be empty")
           | uu____48192 -> one_pattern_branch pat)

and (p_tmIff : FStar_Parser_AST.term -> FStar_Pprint.document) =
  fun e  ->
    match e.FStar_Parser_AST.tm with
    | FStar_Parser_AST.Op
        ({ FStar_Ident.idText = "<==>"; FStar_Ident.idRange = uu____48194;_},e1::e2::[])
        ->
        let uu____48200 = str "<==>"  in
        let uu____48202 = p_tmImplies e1  in
        let uu____48203 = p_tmIff e2  in
        infix0 uu____48200 uu____48202 uu____48203
    | uu____48204 -> p_tmImplies e

and (p_tmImplies : FStar_Parser_AST.term -> FStar_Pprint.document) =
  fun e  ->
    match e.FStar_Parser_AST.tm with
    | FStar_Parser_AST.Op
        ({ FStar_Ident.idText = "==>"; FStar_Ident.idRange = uu____48206;_},e1::e2::[])
        ->
        let uu____48212 = str "==>"  in
        let uu____48214 =
          p_tmArrow (Arrows ((Prims.parse_int "2"), (Prims.parse_int "2")))
            false p_tmFormula e1
           in
        let uu____48220 = p_tmImplies e2  in
        infix0 uu____48212 uu____48214 uu____48220
    | uu____48221 ->
        p_tmArrow (Arrows ((Prims.parse_int "2"), (Prims.parse_int "2")))
          false p_tmFormula e

and (format_sig :
  annotation_style ->
    FStar_Pprint.document Prims.list ->
      Prims.bool -> Prims.bool -> FStar_Pprint.document)
  =
  fun style  ->
    fun terms  ->
      fun no_last_op  ->
        fun flat_space  ->
          let uu____48235 =
            FStar_List.splitAt
              ((FStar_List.length terms) - (Prims.parse_int "1")) terms
             in
          match uu____48235 with
          | (terms',last1) ->
              let uu____48255 =
                match style with
                | Arrows (n1,ln) ->
                    let uu____48290 =
                      let uu____48291 =
                        FStar_Pprint.op_Hat_Hat FStar_Pprint.rarrow break1
                         in
                      FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____48291
                       in
                    let uu____48292 =
                      FStar_Pprint.op_Hat_Hat FStar_Pprint.rarrow
                        FStar_Pprint.space
                       in
                    (n1, ln, terms', uu____48290, uu____48292)
                | Binders (n1,ln,parens1) ->
                    let uu____48306 =
                      if parens1
                      then FStar_List.map soft_parens_with_nesting terms'
                      else terms'  in
                    let uu____48314 =
                      FStar_Pprint.op_Hat_Hat FStar_Pprint.colon
                        FStar_Pprint.space
                       in
                    (n1, ln, uu____48306, break1, uu____48314)
                 in
              (match uu____48255 with
               | (n1,last_n,terms'1,sep,last_op) ->
                   let last2 = FStar_List.hd last1  in
                   let last_op1 =
                     if
                       ((FStar_List.length terms) > (Prims.parse_int "1")) &&
                         (Prims.op_Negation no_last_op)
                     then last_op
                     else FStar_Pprint.empty  in
                   let one_line_space =
                     if
                       (Prims.op_Negation (last2 = FStar_Pprint.empty)) ||
                         (Prims.op_Negation no_last_op)
                     then FStar_Pprint.space
                     else FStar_Pprint.empty  in
                   let single_line_arg_indent =
                     FStar_Pprint.repeat n1 FStar_Pprint.space  in
                   let fs =
                     if flat_space
                     then FStar_Pprint.space
                     else FStar_Pprint.empty  in
                   (match FStar_List.length terms with
                    | _48347 when _48347 = (Prims.parse_int "1") ->
                        FStar_List.hd terms
                    | uu____48348 ->
                        let uu____48349 =
                          let uu____48350 =
                            let uu____48351 =
                              let uu____48352 =
                                FStar_Pprint.separate sep terms'1  in
                              let uu____48353 =
                                let uu____48354 =
                                  FStar_Pprint.op_Hat_Hat last_op1 last2  in
                                FStar_Pprint.op_Hat_Hat one_line_space
                                  uu____48354
                                 in
                              FStar_Pprint.op_Hat_Hat uu____48352 uu____48353
                               in
                            FStar_Pprint.op_Hat_Hat fs uu____48351  in
                          let uu____48355 =
                            let uu____48356 =
                              let uu____48357 =
                                let uu____48358 =
                                  let uu____48359 =
                                    FStar_Pprint.separate sep terms'1  in
                                  FStar_Pprint.op_Hat_Hat fs uu____48359  in
                                let uu____48360 =
                                  let uu____48361 =
                                    let uu____48362 =
                                      let uu____48363 =
                                        FStar_Pprint.op_Hat_Hat sep
                                          single_line_arg_indent
                                         in
                                      let uu____48364 =
                                        FStar_List.map
                                          (fun x  ->
                                             let uu____48370 =
                                               FStar_Pprint.hang
                                                 (Prims.parse_int "2") x
                                                in
                                             FStar_Pprint.align uu____48370)
                                          terms'1
                                         in
                                      FStar_Pprint.separate uu____48363
                                        uu____48364
                                       in
                                    FStar_Pprint.op_Hat_Hat
                                      single_line_arg_indent uu____48362
                                     in
                                  jump2 uu____48361  in
                                FStar_Pprint.ifflat uu____48358 uu____48360
                                 in
                              FStar_Pprint.group uu____48357  in
                            let uu____48372 =
                              let uu____48373 =
                                let uu____48374 =
                                  FStar_Pprint.op_Hat_Hat last_op1 last2  in
                                FStar_Pprint.hang last_n uu____48374  in
                              FStar_Pprint.align uu____48373  in
                            FStar_Pprint.prefix n1 (Prims.parse_int "1")
                              uu____48356 uu____48372
                             in
                          FStar_Pprint.ifflat uu____48350 uu____48355  in
                        FStar_Pprint.group uu____48349))

and (p_tmArrow :
  annotation_style ->
    Prims.bool ->
      (FStar_Parser_AST.term -> FStar_Pprint.document) ->
        FStar_Parser_AST.term -> FStar_Pprint.document)
  =
  fun style  ->
    fun flat_space  ->
      fun p_Tm  ->
        fun e  ->
          let terms =
            match style with
            | Arrows uu____48388 -> p_tmArrow' p_Tm e
            | Binders uu____48395 -> collapse_binders p_Tm e  in
          format_sig style terms false flat_space

and (p_tmArrow' :
  (FStar_Parser_AST.term -> FStar_Pprint.document) ->
    FStar_Parser_AST.term -> FStar_Pprint.document Prims.list)
  =
  fun p_Tm  ->
    fun e  ->
      match e.FStar_Parser_AST.tm with
      | FStar_Parser_AST.Product (bs,tgt) ->
          let uu____48418 = FStar_List.map (fun b  -> p_binder false b) bs
             in
          let uu____48424 = p_tmArrow' p_Tm tgt  in
          FStar_List.append uu____48418 uu____48424
      | uu____48427 -> let uu____48428 = p_Tm e  in [uu____48428]

and (collapse_binders :
  (FStar_Parser_AST.term -> FStar_Pprint.document) ->
    FStar_Parser_AST.term -> FStar_Pprint.document Prims.list)
  =
  fun p_Tm  ->
    fun e  ->
      let rec accumulate_binders p_Tm1 e1 =
        match e1.FStar_Parser_AST.tm with
        | FStar_Parser_AST.Product (bs,tgt) ->
            let uu____48481 = FStar_List.map (fun b  -> p_binder' false b) bs
               in
            let uu____48507 = accumulate_binders p_Tm1 tgt  in
            FStar_List.append uu____48481 uu____48507
        | uu____48530 ->
            let uu____48531 =
              let uu____48542 = p_Tm1 e1  in
              (uu____48542, FStar_Pervasives_Native.None, cat_with_colon)  in
            [uu____48531]
         in
      let fold_fun bs x =
        let uu____48640 = x  in
        match uu____48640 with
        | (b1,t1,f1) ->
            (match bs with
             | [] -> [([b1], t1, f1)]
             | hd1::tl1 ->
                 let uu____48772 = hd1  in
                 (match uu____48772 with
                  | (b2s,t2,uu____48801) ->
                      (match (t1, t2) with
                       | (FStar_Pervasives_Native.Some
                          typ1,FStar_Pervasives_Native.Some typ2) ->
                           if typ1 = typ2
                           then ((FStar_List.append b2s [b1]), t1, f1) :: tl1
                           else ([b1], t1, f1) :: hd1 :: tl1
                       | uu____48903 -> ([b1], t1, f1) :: bs)))
         in
      let p_collapsed_binder cb =
        let uu____48960 = cb  in
        match uu____48960 with
        | (bs,t,f) ->
            (match t with
             | FStar_Pervasives_Native.None  ->
                 (match bs with
                  | b::[] -> b
                  | uu____48989 -> failwith "Impossible")
             | FStar_Pervasives_Native.Some typ ->
                 (match bs with
                  | [] -> failwith "Impossible"
                  | b::[] -> f b typ
                  | hd1::tl1 ->
                      let uu____49000 =
                        FStar_List.fold_left
                          (fun x  ->
                             fun y  ->
                               let uu____49006 =
                                 FStar_Pprint.op_Hat_Hat FStar_Pprint.space y
                                  in
                               FStar_Pprint.op_Hat_Hat x uu____49006) hd1 tl1
                         in
                      f uu____49000 typ))
         in
      let binders =
        let uu____49022 = accumulate_binders p_Tm e  in
        FStar_List.fold_left fold_fun [] uu____49022  in
      map_rev p_collapsed_binder binders

and (p_tmFormula : FStar_Parser_AST.term -> FStar_Pprint.document) =
  fun e  ->
    let conj =
      let uu____49085 =
        let uu____49086 = str "/\\"  in
        FStar_Pprint.op_Hat_Hat uu____49086 break1  in
      FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____49085  in
    let disj =
      let uu____49089 =
        let uu____49090 = str "\\/"  in
        FStar_Pprint.op_Hat_Hat uu____49090 break1  in
      FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____49089  in
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
        ({ FStar_Ident.idText = "\\/"; FStar_Ident.idRange = uu____49110;_},e1::e2::[])
        ->
        let uu____49116 = p_tmDisjunction e1  in
        let uu____49121 =
          let uu____49126 = p_tmConjunction e2  in [uu____49126]  in
        FStar_List.append uu____49116 uu____49121
    | uu____49135 -> let uu____49136 = p_tmConjunction e  in [uu____49136]

and (p_tmConjunction :
  FStar_Parser_AST.term -> FStar_Pprint.document Prims.list) =
  fun e  ->
    match e.FStar_Parser_AST.tm with
    | FStar_Parser_AST.Op
        ({ FStar_Ident.idText = "/\\"; FStar_Ident.idRange = uu____49146;_},e1::e2::[])
        ->
        let uu____49152 = p_tmConjunction e1  in
        let uu____49155 = let uu____49158 = p_tmTuple e2  in [uu____49158]
           in
        FStar_List.append uu____49152 uu____49155
    | uu____49159 -> let uu____49160 = p_tmTuple e  in [uu____49160]

and (p_tmTuple : FStar_Parser_AST.term -> FStar_Pprint.document) =
  fun e  -> with_comment p_tmTuple' e e.FStar_Parser_AST.range

and (p_tmTuple' : FStar_Parser_AST.term -> FStar_Pprint.document) =
  fun e  ->
    match e.FStar_Parser_AST.tm with
    | FStar_Parser_AST.Construct (lid,args) when
        (is_tuple_constructor lid) && (all_explicit args) ->
        let uu____49177 = FStar_Pprint.op_Hat_Hat FStar_Pprint.comma break1
           in
        FStar_Pprint.separate_map uu____49177
          (fun uu____49185  ->
             match uu____49185 with | (e1,uu____49191) -> p_tmEq e1) args
    | uu____49192 -> p_tmEq e

and (paren_if_gt :
  Prims.int -> Prims.int -> FStar_Pprint.document -> FStar_Pprint.document) =
  fun curr  ->
    fun mine  ->
      fun doc1  ->
        if mine <= curr
        then doc1
        else
          (let uu____49201 =
             let uu____49202 =
               FStar_Pprint.op_Hat_Hat doc1 FStar_Pprint.rparen  in
             FStar_Pprint.op_Hat_Hat FStar_Pprint.lparen uu____49202  in
           FStar_Pprint.group uu____49201)

and (p_tmEqWith :
  (FStar_Parser_AST.term -> FStar_Pprint.document) ->
    FStar_Parser_AST.term -> FStar_Pprint.document)
  =
  fun p_X  ->
    fun e  ->
      let n1 =
        max_level
          (FStar_List.append [colon_equals; pipe_right] operatorInfix0ad12)
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
               (let uu____49221 = FStar_Ident.text_of_id op  in
                uu____49221 = "="))
              ||
              (let uu____49226 = FStar_Ident.text_of_id op  in
               uu____49226 = "|>")
            ->
            let op1 = FStar_Ident.text_of_id op  in
            let uu____49232 = levels op1  in
            (match uu____49232 with
             | (left1,mine,right1) ->
                 let uu____49251 =
                   let uu____49252 = FStar_All.pipe_left str op1  in
                   let uu____49254 = p_tmEqWith' p_X left1 e1  in
                   let uu____49255 = p_tmEqWith' p_X right1 e2  in
                   infix0 uu____49252 uu____49254 uu____49255  in
                 paren_if_gt curr mine uu____49251)
        | FStar_Parser_AST.Op
            ({ FStar_Ident.idText = ":=";
               FStar_Ident.idRange = uu____49256;_},e1::e2::[])
            ->
            let uu____49262 =
              let uu____49263 = p_tmEqWith p_X e1  in
              let uu____49264 =
                let uu____49265 =
                  let uu____49266 =
                    let uu____49267 = p_tmEqWith p_X e2  in
                    op_Hat_Slash_Plus_Hat FStar_Pprint.equals uu____49267  in
                  FStar_Pprint.op_Hat_Hat FStar_Pprint.colon uu____49266  in
                FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____49265  in
              FStar_Pprint.op_Hat_Hat uu____49263 uu____49264  in
            FStar_Pprint.group uu____49262
        | FStar_Parser_AST.Op
            ({ FStar_Ident.idText = "-"; FStar_Ident.idRange = uu____49268;_},e1::[])
            ->
            let uu____49273 = levels "-"  in
            (match uu____49273 with
             | (left1,mine,right1) ->
                 let uu____49293 = p_tmEqWith' p_X mine e1  in
                 FStar_Pprint.op_Hat_Slash_Hat FStar_Pprint.minus uu____49293)
        | uu____49294 -> p_tmNoEqWith p_X e

and (p_tmNoEqWith :
  (FStar_Parser_AST.term -> FStar_Pprint.document) ->
    FStar_Parser_AST.term -> FStar_Pprint.document)
  =
  fun p_X  ->
    fun e  ->
      let n1 = max_level [colon_colon; amp; opinfix3; opinfix4]  in
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
              (lid,(e1,uu____49342)::(e2,uu____49344)::[]) when
              (FStar_Ident.lid_equals lid FStar_Parser_Const.cons_lid) &&
                (let uu____49364 = is_list e  in
                 Prims.op_Negation uu____49364)
              ->
              let op = "::"  in
              let uu____49369 = levels op  in
              (match uu____49369 with
               | (left1,mine,right1) ->
                   let uu____49388 =
                     let uu____49389 = str op  in
                     let uu____49390 = p_tmNoEqWith' false p_X left1 e1  in
                     let uu____49392 = p_tmNoEqWith' false p_X right1 e2  in
                     infix0 uu____49389 uu____49390 uu____49392  in
                   paren_if_gt curr mine uu____49388)
          | FStar_Parser_AST.Sum (binders,res) ->
              let op = "&"  in
              let uu____49411 = levels op  in
              (match uu____49411 with
               | (left1,mine,right1) ->
                   let p_dsumfst bt =
                     match bt with
                     | FStar_Util.Inl b ->
                         let uu____49445 = p_binder false b  in
                         let uu____49447 =
                           let uu____49448 =
                             let uu____49449 = str op  in
                             FStar_Pprint.op_Hat_Hat uu____49449 break1  in
                           FStar_Pprint.op_Hat_Hat FStar_Pprint.space
                             uu____49448
                            in
                         FStar_Pprint.op_Hat_Hat uu____49445 uu____49447
                     | FStar_Util.Inr t ->
                         let uu____49451 = p_tmNoEqWith' false p_X left1 t
                            in
                         let uu____49453 =
                           let uu____49454 =
                             let uu____49455 = str op  in
                             FStar_Pprint.op_Hat_Hat uu____49455 break1  in
                           FStar_Pprint.op_Hat_Hat FStar_Pprint.space
                             uu____49454
                            in
                         FStar_Pprint.op_Hat_Hat uu____49451 uu____49453
                      in
                   let uu____49456 =
                     let uu____49457 =
                       FStar_Pprint.concat_map p_dsumfst binders  in
                     let uu____49462 = p_tmNoEqWith' false p_X right1 res  in
                     FStar_Pprint.op_Hat_Hat uu____49457 uu____49462  in
                   paren_if_gt curr mine uu____49456)
          | FStar_Parser_AST.Op
              ({ FStar_Ident.idText = "*";
                 FStar_Ident.idRange = uu____49464;_},e1::e2::[])
              when FStar_ST.op_Bang unfold_tuples ->
              let op = "*"  in
              let uu____49494 = levels op  in
              (match uu____49494 with
               | (left1,mine,right1) ->
                   if inside_tuple
                   then
                     let uu____49514 = str op  in
                     let uu____49515 = p_tmNoEqWith' true p_X left1 e1  in
                     let uu____49517 = p_tmNoEqWith' true p_X right1 e2  in
                     infix0 uu____49514 uu____49515 uu____49517
                   else
                     (let uu____49521 =
                        let uu____49522 = str op  in
                        let uu____49523 = p_tmNoEqWith' true p_X left1 e1  in
                        let uu____49525 = p_tmNoEqWith' true p_X right1 e2
                           in
                        infix0 uu____49522 uu____49523 uu____49525  in
                      paren_if_gt curr mine uu____49521))
          | FStar_Parser_AST.Op (op,e1::e2::[]) when is_operatorInfix34 op ->
              let op1 = FStar_Ident.text_of_id op  in
              let uu____49534 = levels op1  in
              (match uu____49534 with
               | (left1,mine,right1) ->
                   let uu____49553 =
                     let uu____49554 = str op1  in
                     let uu____49555 = p_tmNoEqWith' false p_X left1 e1  in
                     let uu____49557 = p_tmNoEqWith' false p_X right1 e2  in
                     infix0 uu____49554 uu____49555 uu____49557  in
                   paren_if_gt curr mine uu____49553)
          | FStar_Parser_AST.Record (with_opt,record_fields) ->
              let uu____49577 =
                let uu____49578 =
                  default_or_map FStar_Pprint.empty p_with_clause with_opt
                   in
                let uu____49579 =
                  let uu____49580 =
                    FStar_Pprint.op_Hat_Hat FStar_Pprint.semi break1  in
                  separate_map_last uu____49580 p_simpleDef record_fields  in
                FStar_Pprint.op_Hat_Hat uu____49578 uu____49579  in
              braces_with_nesting uu____49577
          | FStar_Parser_AST.Op
              ({ FStar_Ident.idText = "~";
                 FStar_Ident.idRange = uu____49585;_},e1::[])
              ->
              let uu____49590 =
                let uu____49591 = str "~"  in
                let uu____49593 = p_atomicTerm e1  in
                FStar_Pprint.op_Hat_Hat uu____49591 uu____49593  in
              FStar_Pprint.group uu____49590
          | FStar_Parser_AST.Paren p when inside_tuple ->
              (match p.FStar_Parser_AST.tm with
               | FStar_Parser_AST.Op
                   ({ FStar_Ident.idText = "*";
                      FStar_Ident.idRange = uu____49595;_},e1::e2::[])
                   ->
                   let op = "*"  in
                   let uu____49604 = levels op  in
                   (match uu____49604 with
                    | (left1,mine,right1) ->
                        let uu____49623 =
                          let uu____49624 = str op  in
                          let uu____49625 = p_tmNoEqWith' true p_X left1 e1
                             in
                          let uu____49627 = p_tmNoEqWith' true p_X right1 e2
                             in
                          infix0 uu____49624 uu____49625 uu____49627  in
                        paren_if_gt curr mine uu____49623)
               | uu____49629 -> p_X e)
          | uu____49630 -> p_X e

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
        let uu____49637 =
          let uu____49638 = p_lident lid  in
          let uu____49639 =
            let uu____49640 = p_appTerm e1  in
            FStar_Pprint.op_Hat_Slash_Hat FStar_Pprint.colon uu____49640  in
          FStar_Pprint.op_Hat_Slash_Hat uu____49638 uu____49639  in
        FStar_Pprint.group uu____49637
    | FStar_Parser_AST.Refine (b,phi) -> p_refinedBinder b phi
    | uu____49643 -> p_appTerm e

and (p_with_clause : FStar_Parser_AST.term -> FStar_Pprint.document) =
  fun e  ->
    let uu____49645 = p_appTerm e  in
    let uu____49646 =
      let uu____49647 =
        let uu____49648 = str "with"  in
        FStar_Pprint.op_Hat_Hat uu____49648 break1  in
      FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____49647  in
    FStar_Pprint.op_Hat_Hat uu____49645 uu____49646

and (p_refinedBinder :
  FStar_Parser_AST.binder -> FStar_Parser_AST.term -> FStar_Pprint.document)
  =
  fun b  ->
    fun phi  ->
      match b.FStar_Parser_AST.b with
      | FStar_Parser_AST.Annotated (lid,t) ->
          let uu____49654 = p_lident lid  in
          p_refinement b.FStar_Parser_AST.aqual uu____49654 t phi
      | FStar_Parser_AST.TAnnotated uu____49655 ->
          failwith "Is this still used ?"
      | FStar_Parser_AST.Variable uu____49661 ->
          let uu____49662 =
            let uu____49664 = FStar_Parser_AST.binder_to_string b  in
            FStar_Util.format1
              "Imposible : a refined binder ought to be annotated %s"
              uu____49664
             in
          failwith uu____49662
      | FStar_Parser_AST.TVariable uu____49667 ->
          let uu____49668 =
            let uu____49670 = FStar_Parser_AST.binder_to_string b  in
            FStar_Util.format1
              "Imposible : a refined binder ought to be annotated %s"
              uu____49670
             in
          failwith uu____49668
      | FStar_Parser_AST.NoName uu____49673 ->
          let uu____49674 =
            let uu____49676 = FStar_Parser_AST.binder_to_string b  in
            FStar_Util.format1
              "Imposible : a refined binder ought to be annotated %s"
              uu____49676
             in
          failwith uu____49674

and (p_simpleDef :
  Prims.bool ->
    (FStar_Ident.lid * FStar_Parser_AST.term) -> FStar_Pprint.document)
  =
  fun ps  ->
    fun uu____49680  ->
      match uu____49680 with
      | (lid,e) ->
          let uu____49688 =
            let uu____49689 = p_qlident lid  in
            let uu____49690 =
              let uu____49691 = p_noSeqTermAndComment ps false e  in
              FStar_Pprint.op_Hat_Slash_Hat FStar_Pprint.equals uu____49691
               in
            FStar_Pprint.op_Hat_Slash_Hat uu____49689 uu____49690  in
          FStar_Pprint.group uu____49688

and (p_appTerm : FStar_Parser_AST.term -> FStar_Pprint.document) =
  fun e  ->
    match e.FStar_Parser_AST.tm with
    | FStar_Parser_AST.App uu____49694 when is_general_application e ->
        let uu____49701 = head_and_args e  in
        (match uu____49701 with
         | (head1,args) ->
             (match args with
              | e1::e2::[] when
                  (FStar_Pervasives_Native.snd e1) = FStar_Parser_AST.Infix
                  ->
                  let uu____49748 = p_argTerm e1  in
                  let uu____49749 =
                    let uu____49750 =
                      let uu____49751 =
                        let uu____49752 = str "`"  in
                        let uu____49754 =
                          let uu____49755 = p_indexingTerm head1  in
                          let uu____49756 = str "`"  in
                          FStar_Pprint.op_Hat_Hat uu____49755 uu____49756  in
                        FStar_Pprint.op_Hat_Hat uu____49752 uu____49754  in
                      FStar_Pprint.group uu____49751  in
                    let uu____49758 = p_argTerm e2  in
                    FStar_Pprint.op_Hat_Slash_Hat uu____49750 uu____49758  in
                  FStar_Pprint.op_Hat_Slash_Hat uu____49748 uu____49749
              | uu____49759 ->
                  let uu____49766 =
                    let uu____49777 =
                      FStar_ST.op_Bang should_print_fs_typ_app  in
                    if uu____49777
                    then
                      let uu____49811 =
                        FStar_Util.take
                          (fun uu____49835  ->
                             match uu____49835 with
                             | (uu____49841,aq) ->
                                 aq = FStar_Parser_AST.FsTypApp) args
                         in
                      match uu____49811 with
                      | (fs_typ_args,args1) ->
                          let uu____49879 =
                            let uu____49880 = p_indexingTerm head1  in
                            let uu____49881 =
                              let uu____49882 =
                                FStar_Pprint.op_Hat_Hat FStar_Pprint.comma
                                  break1
                                 in
                              soft_surround_map_or_flow (Prims.parse_int "2")
                                (Prims.parse_int "0") FStar_Pprint.empty
                                FStar_Pprint.langle uu____49882
                                FStar_Pprint.rangle p_fsTypArg fs_typ_args
                               in
                            FStar_Pprint.op_Hat_Hat uu____49880 uu____49881
                             in
                          (uu____49879, args1)
                    else
                      (let uu____49897 = p_indexingTerm head1  in
                       (uu____49897, args))
                     in
                  (match uu____49766 with
                   | (head_doc,args1) ->
                       let uu____49918 =
                         let uu____49919 =
                           FStar_Pprint.op_Hat_Hat head_doc
                             FStar_Pprint.space
                            in
                         soft_surround_map_or_flow (Prims.parse_int "2")
                           (Prims.parse_int "0") head_doc uu____49919 break1
                           FStar_Pprint.empty p_argTerm args1
                          in
                       FStar_Pprint.group uu____49918)))
    | FStar_Parser_AST.Construct (lid,args) when
        (is_general_construction e) &&
          (let uu____49941 = is_dtuple_constructor lid  in
           Prims.op_Negation uu____49941)
        ->
        (match args with
         | [] -> p_quident lid
         | arg::[] ->
             let uu____49960 =
               let uu____49961 = p_quident lid  in
               let uu____49962 = p_argTerm arg  in
               FStar_Pprint.op_Hat_Slash_Hat uu____49961 uu____49962  in
             FStar_Pprint.group uu____49960
         | hd1::tl1 ->
             let uu____49979 =
               let uu____49980 =
                 let uu____49981 =
                   let uu____49982 = p_quident lid  in
                   let uu____49983 = p_argTerm hd1  in
                   prefix2 uu____49982 uu____49983  in
                 FStar_Pprint.group uu____49981  in
               let uu____49984 =
                 let uu____49985 =
                   FStar_Pprint.separate_map break1 p_argTerm tl1  in
                 jump2 uu____49985  in
               FStar_Pprint.op_Hat_Hat uu____49980 uu____49984  in
             FStar_Pprint.group uu____49979)
    | uu____49990 -> p_indexingTerm e

and (p_argTerm :
  (FStar_Parser_AST.term * FStar_Parser_AST.imp) -> FStar_Pprint.document) =
  fun arg_imp  ->
    match arg_imp with
    | (u,FStar_Parser_AST.UnivApp ) -> p_universe u
    | (e,FStar_Parser_AST.FsTypApp ) ->
        (FStar_Errors.log_issue e.FStar_Parser_AST.range
           (FStar_Errors.Warning_UnexpectedFsTypApp,
             "Unexpected FsTypApp, output might not be formatted correctly.");
         (let uu____50001 = p_indexingTerm e  in
          FStar_Pprint.surround (Prims.parse_int "2") (Prims.parse_int "1")
            FStar_Pprint.langle uu____50001 FStar_Pprint.rangle))
    | (e,FStar_Parser_AST.Hash ) ->
        let uu____50005 = str "#"  in
        let uu____50007 = p_indexingTerm e  in
        FStar_Pprint.op_Hat_Hat uu____50005 uu____50007
    | (e,FStar_Parser_AST.HashBrace t) ->
        let uu____50010 = str "#["  in
        let uu____50012 =
          let uu____50013 = p_indexingTerm t  in
          let uu____50014 =
            let uu____50015 = str "]"  in
            let uu____50017 = p_indexingTerm e  in
            FStar_Pprint.op_Hat_Hat uu____50015 uu____50017  in
          FStar_Pprint.op_Hat_Hat uu____50013 uu____50014  in
        FStar_Pprint.op_Hat_Hat uu____50010 uu____50012
    | (e,FStar_Parser_AST.Infix ) -> p_indexingTerm e
    | (e,FStar_Parser_AST.Nothing ) -> p_indexingTerm e

and (p_fsTypArg :
  (FStar_Parser_AST.term * FStar_Parser_AST.imp) -> FStar_Pprint.document) =
  fun uu____50020  ->
    match uu____50020 with | (e,uu____50026) -> p_indexingTerm e

and (p_indexingTerm_aux :
  (FStar_Parser_AST.term -> FStar_Pprint.document) ->
    FStar_Parser_AST.term -> FStar_Pprint.document)
  =
  fun exit1  ->
    fun e  ->
      match e.FStar_Parser_AST.tm with
      | FStar_Parser_AST.Op
          ({ FStar_Ident.idText = ".()"; FStar_Ident.idRange = uu____50031;_},e1::e2::[])
          ->
          let uu____50037 =
            let uu____50038 = p_indexingTerm_aux p_atomicTermNotQUident e1
               in
            let uu____50039 =
              let uu____50040 =
                let uu____50041 = p_term false false e2  in
                soft_parens_with_nesting uu____50041  in
              FStar_Pprint.op_Hat_Hat FStar_Pprint.dot uu____50040  in
            FStar_Pprint.op_Hat_Hat uu____50038 uu____50039  in
          FStar_Pprint.group uu____50037
      | FStar_Parser_AST.Op
          ({ FStar_Ident.idText = ".[]"; FStar_Ident.idRange = uu____50044;_},e1::e2::[])
          ->
          let uu____50050 =
            let uu____50051 = p_indexingTerm_aux p_atomicTermNotQUident e1
               in
            let uu____50052 =
              let uu____50053 =
                let uu____50054 = p_term false false e2  in
                soft_brackets_with_nesting uu____50054  in
              FStar_Pprint.op_Hat_Hat FStar_Pprint.dot uu____50053  in
            FStar_Pprint.op_Hat_Hat uu____50051 uu____50052  in
          FStar_Pprint.group uu____50050
      | uu____50057 -> exit1 e

and (p_indexingTerm : FStar_Parser_AST.term -> FStar_Pprint.document) =
  fun e  -> p_indexingTerm_aux p_atomicTerm e

and (p_atomicTerm : FStar_Parser_AST.term -> FStar_Pprint.document) =
  fun e  ->
    match e.FStar_Parser_AST.tm with
    | FStar_Parser_AST.LetOpen (lid,e1) ->
        let uu____50062 = p_quident lid  in
        let uu____50063 =
          let uu____50064 =
            let uu____50065 = p_term false false e1  in
            soft_parens_with_nesting uu____50065  in
          FStar_Pprint.op_Hat_Hat FStar_Pprint.dot uu____50064  in
        FStar_Pprint.op_Hat_Hat uu____50062 uu____50063
    | FStar_Parser_AST.Name lid -> p_quident lid
    | FStar_Parser_AST.Op (op,e1::[]) when is_general_prefix_op op ->
        let uu____50073 =
          let uu____50074 = FStar_Ident.text_of_id op  in str uu____50074  in
        let uu____50076 = p_atomicTerm e1  in
        FStar_Pprint.op_Hat_Hat uu____50073 uu____50076
    | uu____50077 -> p_atomicTermNotQUident e

and (p_atomicTermNotQUident : FStar_Parser_AST.term -> FStar_Pprint.document)
  =
  fun e  ->
    match e.FStar_Parser_AST.tm with
    | FStar_Parser_AST.Wild  -> FStar_Pprint.underscore
    | FStar_Parser_AST.Var lid when
        FStar_Ident.lid_equals lid FStar_Parser_Const.assert_lid ->
        str "assert"
    | FStar_Parser_AST.Var lid when
        FStar_Ident.lid_equals lid FStar_Parser_Const.assume_lid ->
        str "assume"
    | FStar_Parser_AST.Tvar tv -> p_tvar tv
    | FStar_Parser_AST.Const c ->
        (match c with
         | FStar_Const.Const_char x when x = 10 -> str "0x0Az"
         | uu____50090 -> p_constant c)
    | FStar_Parser_AST.Name lid when
        FStar_Ident.lid_equals lid FStar_Parser_Const.true_lid -> str "True"
    | FStar_Parser_AST.Name lid when
        FStar_Ident.lid_equals lid FStar_Parser_Const.false_lid ->
        str "False"
    | FStar_Parser_AST.Op (op,e1::[]) when is_general_prefix_op op ->
        let uu____50099 =
          let uu____50100 = FStar_Ident.text_of_id op  in str uu____50100  in
        let uu____50102 = p_atomicTermNotQUident e1  in
        FStar_Pprint.op_Hat_Hat uu____50099 uu____50102
    | FStar_Parser_AST.Op (op,[]) ->
        let uu____50106 =
          let uu____50107 =
            let uu____50108 =
              let uu____50109 = FStar_Ident.text_of_id op  in str uu____50109
               in
            let uu____50111 =
              FStar_Pprint.op_Hat_Hat FStar_Pprint.space FStar_Pprint.rparen
               in
            FStar_Pprint.op_Hat_Hat uu____50108 uu____50111  in
          FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____50107  in
        FStar_Pprint.op_Hat_Hat FStar_Pprint.lparen uu____50106
    | FStar_Parser_AST.Construct (lid,args) when is_dtuple_constructor lid ->
        let uu____50126 = all_explicit args  in
        if uu____50126
        then
          let uu____50129 =
            FStar_Pprint.op_Hat_Hat FStar_Pprint.lparen FStar_Pprint.bar  in
          let uu____50130 =
            let uu____50131 =
              FStar_Pprint.op_Hat_Hat FStar_Pprint.comma break1  in
            let uu____50132 = FStar_List.map FStar_Pervasives_Native.fst args
               in
            FStar_Pprint.separate_map uu____50131 p_tmEq uu____50132  in
          let uu____50139 =
            FStar_Pprint.op_Hat_Hat FStar_Pprint.bar FStar_Pprint.rparen  in
          FStar_Pprint.surround (Prims.parse_int "2") (Prims.parse_int "1")
            uu____50129 uu____50130 uu____50139
        else
          (match args with
           | [] -> p_quident lid
           | arg::[] ->
               let uu____50161 =
                 let uu____50162 = p_quident lid  in
                 let uu____50163 = p_argTerm arg  in
                 FStar_Pprint.op_Hat_Slash_Hat uu____50162 uu____50163  in
               FStar_Pprint.group uu____50161
           | hd1::tl1 ->
               let uu____50180 =
                 let uu____50181 =
                   let uu____50182 =
                     let uu____50183 = p_quident lid  in
                     let uu____50184 = p_argTerm hd1  in
                     prefix2 uu____50183 uu____50184  in
                   FStar_Pprint.group uu____50182  in
                 let uu____50185 =
                   let uu____50186 =
                     FStar_Pprint.separate_map break1 p_argTerm tl1  in
                   jump2 uu____50186  in
                 FStar_Pprint.op_Hat_Hat uu____50181 uu____50185  in
               FStar_Pprint.group uu____50180)
    | FStar_Parser_AST.Project (e1,lid) ->
        let uu____50193 =
          let uu____50194 = p_atomicTermNotQUident e1  in
          let uu____50195 =
            let uu____50196 = p_qlident lid  in
            FStar_Pprint.op_Hat_Hat FStar_Pprint.dot uu____50196  in
          FStar_Pprint.prefix (Prims.parse_int "2") (Prims.parse_int "0")
            uu____50194 uu____50195
           in
        FStar_Pprint.group uu____50193
    | uu____50199 -> p_projectionLHS e

and (p_projectionLHS : FStar_Parser_AST.term -> FStar_Pprint.document) =
  fun e  ->
    match e.FStar_Parser_AST.tm with
    | FStar_Parser_AST.Var lid -> p_qlident lid
    | FStar_Parser_AST.Projector (constr_lid,field_lid) ->
        let uu____50204 = p_quident constr_lid  in
        let uu____50205 =
          let uu____50206 =
            let uu____50207 = p_lident field_lid  in
            FStar_Pprint.op_Hat_Hat FStar_Pprint.dot uu____50207  in
          FStar_Pprint.op_Hat_Hat FStar_Pprint.qmark uu____50206  in
        FStar_Pprint.op_Hat_Hat uu____50204 uu____50205
    | FStar_Parser_AST.Discrim constr_lid ->
        let uu____50209 = p_quident constr_lid  in
        FStar_Pprint.op_Hat_Hat uu____50209 FStar_Pprint.qmark
    | FStar_Parser_AST.Paren e1 ->
        let uu____50211 = p_term_sep false false e1  in
        (match uu____50211 with
         | (comm,t) ->
             let doc1 = soft_parens_with_nesting t  in
             if comm = FStar_Pprint.empty
             then doc1
             else
               (let uu____50224 =
                  FStar_Pprint.op_Hat_Hat FStar_Pprint.hardline doc1  in
                FStar_Pprint.op_Hat_Hat comm uu____50224))
    | uu____50225 when is_array e ->
        let es = extract_from_list e  in
        let uu____50229 =
          FStar_Pprint.op_Hat_Hat FStar_Pprint.lbracket FStar_Pprint.bar  in
        let uu____50230 =
          let uu____50231 = FStar_Pprint.op_Hat_Hat FStar_Pprint.semi break1
             in
          separate_map_or_flow_last uu____50231
            (fun ps  -> p_noSeqTermAndComment ps false) es
           in
        let uu____50236 =
          FStar_Pprint.op_Hat_Hat FStar_Pprint.bar FStar_Pprint.rbracket  in
        FStar_Pprint.surround (Prims.parse_int "2") (Prims.parse_int "0")
          uu____50229 uu____50230 uu____50236
    | uu____50239 when is_list e ->
        let uu____50240 =
          let uu____50241 = FStar_Pprint.op_Hat_Hat FStar_Pprint.semi break1
             in
          let uu____50242 = extract_from_list e  in
          separate_map_or_flow_last uu____50241
            (fun ps  -> p_noSeqTermAndComment ps false) uu____50242
           in
        FStar_Pprint.surround (Prims.parse_int "2") (Prims.parse_int "0")
          FStar_Pprint.lbracket uu____50240 FStar_Pprint.rbracket
    | uu____50251 when is_lex_list e ->
        let uu____50252 =
          FStar_Pprint.op_Hat_Hat FStar_Pprint.percent FStar_Pprint.lbracket
           in
        let uu____50253 =
          let uu____50254 = FStar_Pprint.op_Hat_Hat FStar_Pprint.semi break1
             in
          let uu____50255 = extract_from_list e  in
          separate_map_or_flow_last uu____50254
            (fun ps  -> p_noSeqTermAndComment ps false) uu____50255
           in
        FStar_Pprint.surround (Prims.parse_int "2") (Prims.parse_int "1")
          uu____50252 uu____50253 FStar_Pprint.rbracket
    | uu____50264 when is_ref_set e ->
        let es = extract_from_ref_set e  in
        let uu____50268 =
          FStar_Pprint.op_Hat_Hat FStar_Pprint.bang FStar_Pprint.lbrace  in
        let uu____50269 =
          let uu____50270 = FStar_Pprint.op_Hat_Hat FStar_Pprint.comma break1
             in
          separate_map_or_flow uu____50270 p_appTerm es  in
        FStar_Pprint.surround (Prims.parse_int "2") (Prims.parse_int "0")
          uu____50268 uu____50269 FStar_Pprint.rbrace
    | FStar_Parser_AST.Labeled (e1,s,b) ->
        let uu____50280 = str (Prims.op_Hat "(*" (Prims.op_Hat s "*)"))  in
        let uu____50283 = p_term false false e1  in
        FStar_Pprint.op_Hat_Slash_Hat uu____50280 uu____50283
    | FStar_Parser_AST.Op (op,args) when
        let uu____50292 = handleable_op op args  in
        Prims.op_Negation uu____50292 ->
        let uu____50294 =
          let uu____50296 =
            let uu____50298 = FStar_Ident.text_of_id op  in
            let uu____50300 =
              let uu____50302 =
                let uu____50304 =
                  FStar_Util.string_of_int (FStar_List.length args)  in
                Prims.op_Hat uu____50304
                  " arguments couldn't be handled by the pretty printer"
                 in
              Prims.op_Hat " with " uu____50302  in
            Prims.op_Hat uu____50298 uu____50300  in
          Prims.op_Hat "Operation " uu____50296  in
        failwith uu____50294
    | FStar_Parser_AST.Uvar id1 ->
        failwith "Unexpected universe variable out of universe context"
    | FStar_Parser_AST.Wild  ->
        let uu____50311 = p_term false false e  in
        soft_parens_with_nesting uu____50311
    | FStar_Parser_AST.Const uu____50314 ->
        let uu____50315 = p_term false false e  in
        soft_parens_with_nesting uu____50315
    | FStar_Parser_AST.Op uu____50318 ->
        let uu____50325 = p_term false false e  in
        soft_parens_with_nesting uu____50325
    | FStar_Parser_AST.Tvar uu____50328 ->
        let uu____50329 = p_term false false e  in
        soft_parens_with_nesting uu____50329
    | FStar_Parser_AST.Var uu____50332 ->
        let uu____50333 = p_term false false e  in
        soft_parens_with_nesting uu____50333
    | FStar_Parser_AST.Name uu____50336 ->
        let uu____50337 = p_term false false e  in
        soft_parens_with_nesting uu____50337
    | FStar_Parser_AST.Construct uu____50340 ->
        let uu____50351 = p_term false false e  in
        soft_parens_with_nesting uu____50351
    | FStar_Parser_AST.Abs uu____50354 ->
        let uu____50361 = p_term false false e  in
        soft_parens_with_nesting uu____50361
    | FStar_Parser_AST.App uu____50364 ->
        let uu____50371 = p_term false false e  in
        soft_parens_with_nesting uu____50371
    | FStar_Parser_AST.Let uu____50374 ->
        let uu____50395 = p_term false false e  in
        soft_parens_with_nesting uu____50395
    | FStar_Parser_AST.LetOpen uu____50398 ->
        let uu____50403 = p_term false false e  in
        soft_parens_with_nesting uu____50403
    | FStar_Parser_AST.Seq uu____50406 ->
        let uu____50411 = p_term false false e  in
        soft_parens_with_nesting uu____50411
    | FStar_Parser_AST.Bind uu____50414 ->
        let uu____50421 = p_term false false e  in
        soft_parens_with_nesting uu____50421
    | FStar_Parser_AST.If uu____50424 ->
        let uu____50431 = p_term false false e  in
        soft_parens_with_nesting uu____50431
    | FStar_Parser_AST.Match uu____50434 ->
        let uu____50449 = p_term false false e  in
        soft_parens_with_nesting uu____50449
    | FStar_Parser_AST.TryWith uu____50452 ->
        let uu____50467 = p_term false false e  in
        soft_parens_with_nesting uu____50467
    | FStar_Parser_AST.Ascribed uu____50470 ->
        let uu____50479 = p_term false false e  in
        soft_parens_with_nesting uu____50479
    | FStar_Parser_AST.Record uu____50482 ->
        let uu____50495 = p_term false false e  in
        soft_parens_with_nesting uu____50495
    | FStar_Parser_AST.Project uu____50498 ->
        let uu____50503 = p_term false false e  in
        soft_parens_with_nesting uu____50503
    | FStar_Parser_AST.Product uu____50506 ->
        let uu____50513 = p_term false false e  in
        soft_parens_with_nesting uu____50513
    | FStar_Parser_AST.Sum uu____50516 ->
        let uu____50527 = p_term false false e  in
        soft_parens_with_nesting uu____50527
    | FStar_Parser_AST.QForall uu____50530 ->
        let uu____50543 = p_term false false e  in
        soft_parens_with_nesting uu____50543
    | FStar_Parser_AST.QExists uu____50546 ->
        let uu____50559 = p_term false false e  in
        soft_parens_with_nesting uu____50559
    | FStar_Parser_AST.Refine uu____50562 ->
        let uu____50567 = p_term false false e  in
        soft_parens_with_nesting uu____50567
    | FStar_Parser_AST.NamedTyp uu____50570 ->
        let uu____50575 = p_term false false e  in
        soft_parens_with_nesting uu____50575
    | FStar_Parser_AST.Requires uu____50578 ->
        let uu____50586 = p_term false false e  in
        soft_parens_with_nesting uu____50586
    | FStar_Parser_AST.Ensures uu____50589 ->
        let uu____50597 = p_term false false e  in
        soft_parens_with_nesting uu____50597
    | FStar_Parser_AST.Attributes uu____50600 ->
        let uu____50603 = p_term false false e  in
        soft_parens_with_nesting uu____50603
    | FStar_Parser_AST.Quote uu____50606 ->
        let uu____50611 = p_term false false e  in
        soft_parens_with_nesting uu____50611
    | FStar_Parser_AST.VQuote uu____50614 ->
        let uu____50615 = p_term false false e  in
        soft_parens_with_nesting uu____50615
    | FStar_Parser_AST.Antiquote uu____50618 ->
        let uu____50619 = p_term false false e  in
        soft_parens_with_nesting uu____50619
    | FStar_Parser_AST.CalcProof uu____50622 ->
        let uu____50631 = p_term false false e  in
        soft_parens_with_nesting uu____50631

and (p_constant : FStar_Const.sconst -> FStar_Pprint.document) =
  fun uu___339_50634  ->
    match uu___339_50634 with
    | FStar_Const.Const_effect  -> str "Effect"
    | FStar_Const.Const_unit  -> str "()"
    | FStar_Const.Const_bool b -> FStar_Pprint.doc_of_bool b
    | FStar_Const.Const_real r -> str (Prims.op_Hat r "R")
    | FStar_Const.Const_float x -> str (FStar_Util.string_of_float x)
    | FStar_Const.Const_char x -> FStar_Pprint.doc_of_char x
    | FStar_Const.Const_string (s,uu____50646) ->
        let uu____50649 = str (FStar_String.escaped s)  in
        FStar_Pprint.dquotes uu____50649
    | FStar_Const.Const_bytearray (bytes,uu____50651) ->
        let uu____50656 =
          let uu____50657 = str (FStar_Util.string_of_bytes bytes)  in
          FStar_Pprint.dquotes uu____50657  in
        let uu____50658 = str "B"  in
        FStar_Pprint.op_Hat_Hat uu____50656 uu____50658
    | FStar_Const.Const_int (repr,sign_width_opt) ->
        let signedness uu___337_50681 =
          match uu___337_50681 with
          | FStar_Const.Unsigned  -> str "u"
          | FStar_Const.Signed  -> FStar_Pprint.empty  in
        let width uu___338_50688 =
          match uu___338_50688 with
          | FStar_Const.Int8  -> str "y"
          | FStar_Const.Int16  -> str "s"
          | FStar_Const.Int32  -> str "l"
          | FStar_Const.Int64  -> str "L"  in
        let ending =
          default_or_map FStar_Pprint.empty
            (fun uu____50703  ->
               match uu____50703 with
               | (s,w) ->
                   let uu____50710 = signedness s  in
                   let uu____50711 = width w  in
                   FStar_Pprint.op_Hat_Hat uu____50710 uu____50711)
            sign_width_opt
           in
        let uu____50712 = str repr  in
        FStar_Pprint.op_Hat_Hat uu____50712 ending
    | FStar_Const.Const_range_of  -> str "range_of"
    | FStar_Const.Const_set_range_of  -> str "set_range_of"
    | FStar_Const.Const_range r ->
        let uu____50716 = FStar_Range.string_of_range r  in str uu____50716
    | FStar_Const.Const_reify  -> str "reify"
    | FStar_Const.Const_reflect lid ->
        let uu____50720 = p_quident lid  in
        let uu____50721 =
          let uu____50722 =
            let uu____50723 = str "reflect"  in
            FStar_Pprint.op_Hat_Hat FStar_Pprint.dot uu____50723  in
          FStar_Pprint.op_Hat_Hat FStar_Pprint.qmark uu____50722  in
        FStar_Pprint.op_Hat_Hat uu____50720 uu____50721

and (p_universe : FStar_Parser_AST.term -> FStar_Pprint.document) =
  fun u  ->
    let uu____50726 = str "u#"  in
    let uu____50728 = p_atomicUniverse u  in
    FStar_Pprint.op_Hat_Hat uu____50726 uu____50728

and (p_universeFrom : FStar_Parser_AST.term -> FStar_Pprint.document) =
  fun u  ->
    match u.FStar_Parser_AST.tm with
    | FStar_Parser_AST.Op
        ({ FStar_Ident.idText = "+"; FStar_Ident.idRange = uu____50730;_},u1::u2::[])
        ->
        let uu____50736 =
          let uu____50737 = p_universeFrom u1  in
          let uu____50738 =
            let uu____50739 = p_universeFrom u2  in
            FStar_Pprint.op_Hat_Slash_Hat FStar_Pprint.plus uu____50739  in
          FStar_Pprint.op_Hat_Slash_Hat uu____50737 uu____50738  in
        FStar_Pprint.group uu____50736
    | FStar_Parser_AST.App uu____50740 ->
        let uu____50747 = head_and_args u  in
        (match uu____50747 with
         | (head1,args) ->
             (match head1.FStar_Parser_AST.tm with
              | FStar_Parser_AST.Var maybe_max_lid when
                  FStar_Ident.lid_equals maybe_max_lid
                    FStar_Parser_Const.max_lid
                  ->
                  let uu____50773 =
                    let uu____50774 = p_qlident FStar_Parser_Const.max_lid
                       in
                    let uu____50775 =
                      FStar_Pprint.separate_map FStar_Pprint.space
                        (fun uu____50783  ->
                           match uu____50783 with
                           | (u1,uu____50789) -> p_atomicUniverse u1) args
                       in
                    op_Hat_Slash_Plus_Hat uu____50774 uu____50775  in
                  FStar_Pprint.group uu____50773
              | uu____50790 ->
                  let uu____50791 =
                    let uu____50793 = FStar_Parser_AST.term_to_string u  in
                    FStar_Util.format1 "Invalid term in universe context %s"
                      uu____50793
                     in
                  failwith uu____50791))
    | uu____50796 -> p_atomicUniverse u

and (p_atomicUniverse : FStar_Parser_AST.term -> FStar_Pprint.document) =
  fun u  ->
    match u.FStar_Parser_AST.tm with
    | FStar_Parser_AST.Wild  -> FStar_Pprint.underscore
    | FStar_Parser_AST.Const (FStar_Const.Const_int (r,sw)) ->
        p_constant (FStar_Const.Const_int (r, sw))
    | FStar_Parser_AST.Uvar id1 ->
        let uu____50822 = FStar_Ident.text_of_id id1  in str uu____50822
    | FStar_Parser_AST.Paren u1 ->
        let uu____50825 = p_universeFrom u1  in
        soft_parens_with_nesting uu____50825
    | FStar_Parser_AST.Op
        ({ FStar_Ident.idText = "+"; FStar_Ident.idRange = uu____50826;_},uu____50827::uu____50828::[])
        ->
        let uu____50832 = p_universeFrom u  in
        soft_parens_with_nesting uu____50832
    | FStar_Parser_AST.App uu____50833 ->
        let uu____50840 = p_universeFrom u  in
        soft_parens_with_nesting uu____50840
    | uu____50841 ->
        let uu____50842 =
          let uu____50844 = FStar_Parser_AST.term_to_string u  in
          FStar_Util.format1 "Invalid term in universe context %s"
            uu____50844
           in
        failwith uu____50842

let (term_to_document : FStar_Parser_AST.term -> FStar_Pprint.document) =
  fun e  ->
    FStar_ST.op_Colon_Equals unfold_tuples false; p_term false false e
  
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
       | FStar_Parser_AST.Module (uu____50933,decls) ->
           let uu____50939 =
             FStar_All.pipe_right decls (FStar_List.map decl_to_document)  in
           FStar_All.pipe_right uu____50939
             (FStar_Pprint.separate FStar_Pprint.hardline)
       | FStar_Parser_AST.Interface (uu____50948,decls,uu____50950) ->
           let uu____50957 =
             FStar_All.pipe_right decls (FStar_List.map decl_to_document)  in
           FStar_All.pipe_right uu____50957
             (FStar_Pprint.separate FStar_Pprint.hardline)
        in
     FStar_ST.op_Colon_Equals should_print_fs_typ_app false; res)
  
let (comments_to_document :
  (Prims.string * FStar_Range.range) Prims.list -> FStar_Pprint.document) =
  fun comments  ->
    FStar_Pprint.separate_map FStar_Pprint.hardline
      (fun uu____51017  ->
         match uu____51017 with | (comment,range) -> str comment) comments
  
let (extract_decl_range : FStar_Parser_AST.decl -> decl_meta) =
  fun d  ->
    let has_qs =
      match ((d.FStar_Parser_AST.quals), (d.FStar_Parser_AST.d)) with
      | ((FStar_Parser_AST.Assumption )::[],FStar_Parser_AST.Assume
         (id1,uu____51039)) -> false
      | ([],uu____51043) -> false
      | uu____51047 -> true  in
    {
      r = (d.FStar_Parser_AST.drange);
      has_qs;
      has_attrs =
        (Prims.op_Negation (FStar_List.isEmpty d.FStar_Parser_AST.attrs));
      has_fsdoc = (FStar_Util.is_some d.FStar_Parser_AST.doc);
      is_fsdoc =
        (match d.FStar_Parser_AST.d with
         | FStar_Parser_AST.Fsdoc uu____51057 -> true
         | uu____51059 -> false)
    }
  
let (modul_with_comments_to_document :
  FStar_Parser_AST.modul ->
    (Prims.string * FStar_Range.range) Prims.list ->
      (FStar_Pprint.document * (Prims.string * FStar_Range.range) Prims.list))
  =
  fun m  ->
    fun comments  ->
      let decls =
        match m with
        | FStar_Parser_AST.Module (uu____51102,decls) -> decls
        | FStar_Parser_AST.Interface (uu____51108,decls,uu____51110) -> decls
         in
      FStar_ST.op_Colon_Equals should_print_fs_typ_app false;
      (match decls with
       | [] -> (FStar_Pprint.empty, comments)
       | d::ds ->
           let uu____51162 =
             match ds with
             | {
                 FStar_Parser_AST.d = FStar_Parser_AST.Pragma
                   (FStar_Parser_AST.LightOff );
                 FStar_Parser_AST.drange = uu____51175;
                 FStar_Parser_AST.doc = uu____51176;
                 FStar_Parser_AST.quals = uu____51177;
                 FStar_Parser_AST.attrs = uu____51178;_}::uu____51179 ->
                 let d0 = FStar_List.hd ds  in
                 let uu____51185 =
                   let uu____51188 =
                     let uu____51191 = FStar_List.tl ds  in d :: uu____51191
                      in
                   d0 :: uu____51188  in
                 (uu____51185, (d0.FStar_Parser_AST.drange))
             | uu____51196 -> ((d :: ds), (d.FStar_Parser_AST.drange))  in
           (match uu____51162 with
            | (decls1,first_range) ->
                (FStar_ST.op_Colon_Equals comment_stack comments;
                 (let initial_comment =
                    let uu____51253 = FStar_Range.start_of_range first_range
                       in
                    place_comments_until_pos (Prims.parse_int "0")
                      (Prims.parse_int "1") uu____51253 dummy_meta
                      FStar_Pprint.empty false true
                     in
                  let doc1 =
                    separate_map_with_comments FStar_Pprint.empty
                      FStar_Pprint.empty p_decl decls1 extract_decl_range
                     in
                  let comments1 = FStar_ST.op_Bang comment_stack  in
                  FStar_ST.op_Colon_Equals comment_stack [];
                  FStar_ST.op_Colon_Equals should_print_fs_typ_app false;
                  (let uu____51362 =
                     FStar_Pprint.op_Hat_Hat initial_comment doc1  in
                   (uu____51362, comments1))))))
  