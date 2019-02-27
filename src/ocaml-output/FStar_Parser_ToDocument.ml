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
            let uu____43195 = let uu____43198 = f x  in uu____43198 :: acc
               in
            aux xs uu____43195
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
            let uu____43265 = f x  in
            (match uu____43265 with
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
          let uu____43321 = f x  in if uu____43321 then all f xs else false
  
let (all_explicit :
  (FStar_Parser_AST.term * FStar_Parser_AST.imp) Prims.list -> Prims.bool) =
  fun args  ->
    FStar_Util.for_all
      (fun uu___324_43354  ->
         match uu___324_43354 with
         | (uu____43360,FStar_Parser_AST.Nothing ) -> true
         | uu____43362 -> false) args
  
let (should_print_fs_typ_app : Prims.bool FStar_ST.ref) =
  FStar_Util.mk_ref false 
let (unfold_tuples : Prims.bool FStar_ST.ref) = FStar_Util.mk_ref true 
let with_fs_typ_app :
  'Auu____43413 'Auu____43414 .
    Prims.bool ->
      ('Auu____43413 -> 'Auu____43414) -> 'Auu____43413 -> 'Auu____43414
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
  'Auu____43524 'Auu____43525 .
    'Auu____43524 ->
      ('Auu____43525 -> 'Auu____43524) ->
        'Auu____43525 FStar_Pervasives_Native.option -> 'Auu____43524
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
  'Auu____43638 .
    FStar_Pprint.document ->
      ('Auu____43638 -> FStar_Pprint.document) ->
        'Auu____43638 Prims.list -> FStar_Pprint.document
  =
  fun sep  ->
    fun f  ->
      fun l  ->
        let uu____43663 =
          let uu____43664 =
            let uu____43665 = FStar_Pprint.op_Hat_Hat sep break1  in
            FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____43665  in
          FStar_Pprint.separate_map uu____43664 f l  in
        FStar_Pprint.group uu____43663
  
let precede_break_separate_map :
  'Auu____43677 .
    FStar_Pprint.document ->
      FStar_Pprint.document ->
        ('Auu____43677 -> FStar_Pprint.document) ->
          'Auu____43677 Prims.list -> FStar_Pprint.document
  =
  fun prec  ->
    fun sep  ->
      fun f  ->
        fun l  ->
          let uu____43707 =
            let uu____43708 = FStar_Pprint.op_Hat_Hat prec FStar_Pprint.space
               in
            let uu____43709 =
              let uu____43710 = FStar_List.hd l  in
              FStar_All.pipe_right uu____43710 f  in
            FStar_Pprint.precede uu____43708 uu____43709  in
          let uu____43711 =
            let uu____43712 = FStar_List.tl l  in
            FStar_Pprint.concat_map
              (fun x  ->
                 let uu____43718 =
                   let uu____43719 =
                     let uu____43720 = f x  in
                     FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____43720
                      in
                   FStar_Pprint.op_Hat_Hat sep uu____43719  in
                 FStar_Pprint.op_Hat_Hat break1 uu____43718) uu____43712
             in
          FStar_Pprint.op_Hat_Hat uu____43707 uu____43711
  
let concat_break_map :
  'Auu____43728 .
    ('Auu____43728 -> FStar_Pprint.document) ->
      'Auu____43728 Prims.list -> FStar_Pprint.document
  =
  fun f  ->
    fun l  ->
      let uu____43748 =
        FStar_Pprint.concat_map
          (fun x  ->
             let uu____43752 = f x  in
             FStar_Pprint.op_Hat_Hat uu____43752 break1) l
         in
      FStar_Pprint.group uu____43748
  
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
    let uu____43815 = str "begin"  in
    let uu____43817 = str "end"  in
    FStar_Pprint.soft_surround (Prims.parse_int "2") (Prims.parse_int "1")
      uu____43815 contents uu____43817
  
let separate_map_last :
  'Auu____43830 .
    FStar_Pprint.document ->
      (Prims.bool -> 'Auu____43830 -> FStar_Pprint.document) ->
        'Auu____43830 Prims.list -> FStar_Pprint.document
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
  'Auu____43888 .
    FStar_Pprint.document ->
      (Prims.bool -> 'Auu____43888 -> FStar_Pprint.document) ->
        'Auu____43888 Prims.list -> FStar_Pprint.document
  =
  fun sep  ->
    fun f  ->
      fun l  ->
        let uu____43920 =
          let uu____43921 =
            let uu____43922 = FStar_Pprint.op_Hat_Hat sep break1  in
            FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____43922  in
          separate_map_last uu____43921 f l  in
        FStar_Pprint.group uu____43920
  
let separate_map_or_flow :
  'Auu____43932 .
    FStar_Pprint.document ->
      ('Auu____43932 -> FStar_Pprint.document) ->
        'Auu____43932 Prims.list -> FStar_Pprint.document
  =
  fun sep  ->
    fun f  ->
      fun l  ->
        if (FStar_List.length l) < (Prims.parse_int "10")
        then FStar_Pprint.separate_map sep f l
        else FStar_Pprint.flow_map sep f l
  
let flow_map_last :
  'Auu____43970 .
    FStar_Pprint.document ->
      (Prims.bool -> 'Auu____43970 -> FStar_Pprint.document) ->
        'Auu____43970 Prims.list -> FStar_Pprint.document
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
  'Auu____44028 .
    FStar_Pprint.document ->
      (Prims.bool -> 'Auu____44028 -> FStar_Pprint.document) ->
        'Auu____44028 Prims.list -> FStar_Pprint.document
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
              let uu____44110 = FStar_Pprint.op_Hat_Slash_Hat doc1 doc3  in
              FStar_Pprint.group uu____44110
            else FStar_Pprint.surround n1 b doc1 doc2 doc3
  
let soft_surround_separate_map :
  'Auu____44132 .
    Prims.int ->
      Prims.int ->
        FStar_Pprint.document ->
          FStar_Pprint.document ->
            FStar_Pprint.document ->
              FStar_Pprint.document ->
                ('Auu____44132 -> FStar_Pprint.document) ->
                  'Auu____44132 Prims.list -> FStar_Pprint.document
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
                    (let uu____44191 = FStar_Pprint.separate_map sep f xs  in
                     FStar_Pprint.soft_surround n1 b opening uu____44191
                       closing)
  
let soft_surround_map_or_flow :
  'Auu____44211 .
    Prims.int ->
      Prims.int ->
        FStar_Pprint.document ->
          FStar_Pprint.document ->
            FStar_Pprint.document ->
              FStar_Pprint.document ->
                ('Auu____44211 -> FStar_Pprint.document) ->
                  'Auu____44211 Prims.list -> FStar_Pprint.document
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
                    (let uu____44270 = separate_map_or_flow sep f xs  in
                     FStar_Pprint.soft_surround n1 b opening uu____44270
                       closing)
  
let (doc_of_fsdoc :
  (Prims.string * (Prims.string * Prims.string) Prims.list) ->
    FStar_Pprint.document)
  =
  fun uu____44289  ->
    match uu____44289 with
    | (comment,keywords) ->
        let uu____44323 =
          let uu____44324 =
            let uu____44327 = str comment  in
            let uu____44328 =
              let uu____44331 =
                let uu____44334 =
                  FStar_Pprint.separate_map FStar_Pprint.comma
                    (fun uu____44345  ->
                       match uu____44345 with
                       | (k,v1) ->
                           let uu____44358 =
                             let uu____44361 = str k  in
                             let uu____44362 =
                               let uu____44365 =
                                 let uu____44368 = str v1  in [uu____44368]
                                  in
                               FStar_Pprint.rarrow :: uu____44365  in
                             uu____44361 :: uu____44362  in
                           FStar_Pprint.concat uu____44358) keywords
                   in
                [uu____44334]  in
              FStar_Pprint.space :: uu____44331  in
            uu____44327 :: uu____44328  in
          FStar_Pprint.concat uu____44324  in
        FStar_Pprint.group uu____44323
  
let (is_unit : FStar_Parser_AST.term -> Prims.bool) =
  fun e  ->
    match e.FStar_Parser_AST.tm with
    | FStar_Parser_AST.Const (FStar_Const.Const_unit ) -> true
    | uu____44378 -> false
  
let (matches_var : FStar_Parser_AST.term -> FStar_Ident.ident -> Prims.bool)
  =
  fun t  ->
    fun x  ->
      match t.FStar_Parser_AST.tm with
      | FStar_Parser_AST.Var y ->
          let uu____44394 = FStar_Ident.text_of_lid y  in
          x.FStar_Ident.idText = uu____44394
      | uu____44397 -> false
  
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
        | FStar_Parser_AST.Construct (lid,uu____44448::(e2,uu____44450)::[])
            -> (FStar_Ident.lid_equals lid cons_lid1) && (aux e2)
        | uu____44473 -> false  in
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
    | FStar_Parser_AST.Construct (uu____44497,[]) -> []
    | FStar_Parser_AST.Construct
        (uu____44508,(e1,FStar_Parser_AST.Nothing )::(e2,FStar_Parser_AST.Nothing
                                                      )::[])
        -> let uu____44529 = extract_from_list e2  in e1 :: uu____44529
    | uu____44532 ->
        let uu____44533 =
          let uu____44535 = FStar_Parser_AST.term_to_string e  in
          FStar_Util.format1 "Not a list %s" uu____44535  in
        failwith uu____44533
  
let (is_array : FStar_Parser_AST.term -> Prims.bool) =
  fun e  ->
    match e.FStar_Parser_AST.tm with
    | FStar_Parser_AST.App
        ({ FStar_Parser_AST.tm = FStar_Parser_AST.Var lid;
           FStar_Parser_AST.range = uu____44549;
           FStar_Parser_AST.level = uu____44550;_},l,FStar_Parser_AST.Nothing
         )
        ->
        (FStar_Ident.lid_equals lid FStar_Parser_Const.array_mk_array_lid) &&
          (is_list l)
    | uu____44552 -> false
  
let rec (is_ref_set : FStar_Parser_AST.term -> Prims.bool) =
  fun e  ->
    match e.FStar_Parser_AST.tm with
    | FStar_Parser_AST.Var maybe_empty_lid ->
        FStar_Ident.lid_equals maybe_empty_lid FStar_Parser_Const.set_empty
    | FStar_Parser_AST.App
        ({ FStar_Parser_AST.tm = FStar_Parser_AST.Var maybe_singleton_lid;
           FStar_Parser_AST.range = uu____44564;
           FStar_Parser_AST.level = uu____44565;_},{
                                                     FStar_Parser_AST.tm =
                                                       FStar_Parser_AST.App
                                                       ({
                                                          FStar_Parser_AST.tm
                                                            =
                                                            FStar_Parser_AST.Var
                                                            maybe_addr_of_lid;
                                                          FStar_Parser_AST.range
                                                            = uu____44567;
                                                          FStar_Parser_AST.level
                                                            = uu____44568;_},e1,FStar_Parser_AST.Nothing
                                                        );
                                                     FStar_Parser_AST.range =
                                                       uu____44570;
                                                     FStar_Parser_AST.level =
                                                       uu____44571;_},FStar_Parser_AST.Nothing
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
                FStar_Parser_AST.range = uu____44573;
                FStar_Parser_AST.level = uu____44574;_},e1,FStar_Parser_AST.Nothing
              );
           FStar_Parser_AST.range = uu____44576;
           FStar_Parser_AST.level = uu____44577;_},e2,FStar_Parser_AST.Nothing
         )
        ->
        ((FStar_Ident.lid_equals maybe_union_lid FStar_Parser_Const.set_union)
           && (is_ref_set e1))
          && (is_ref_set e2)
    | uu____44579 -> false
  
let rec (extract_from_ref_set :
  FStar_Parser_AST.term -> FStar_Parser_AST.term Prims.list) =
  fun e  ->
    match e.FStar_Parser_AST.tm with
    | FStar_Parser_AST.Var uu____44591 -> []
    | FStar_Parser_AST.App
        ({ FStar_Parser_AST.tm = FStar_Parser_AST.Var uu____44592;
           FStar_Parser_AST.range = uu____44593;
           FStar_Parser_AST.level = uu____44594;_},{
                                                     FStar_Parser_AST.tm =
                                                       FStar_Parser_AST.App
                                                       ({
                                                          FStar_Parser_AST.tm
                                                            =
                                                            FStar_Parser_AST.Var
                                                            uu____44595;
                                                          FStar_Parser_AST.range
                                                            = uu____44596;
                                                          FStar_Parser_AST.level
                                                            = uu____44597;_},e1,FStar_Parser_AST.Nothing
                                                        );
                                                     FStar_Parser_AST.range =
                                                       uu____44599;
                                                     FStar_Parser_AST.level =
                                                       uu____44600;_},FStar_Parser_AST.Nothing
         )
        -> [e1]
    | FStar_Parser_AST.App
        ({
           FStar_Parser_AST.tm = FStar_Parser_AST.App
             ({ FStar_Parser_AST.tm = FStar_Parser_AST.Var uu____44601;
                FStar_Parser_AST.range = uu____44602;
                FStar_Parser_AST.level = uu____44603;_},e1,FStar_Parser_AST.Nothing
              );
           FStar_Parser_AST.range = uu____44605;
           FStar_Parser_AST.level = uu____44606;_},e2,FStar_Parser_AST.Nothing
         )
        ->
        let uu____44608 = extract_from_ref_set e1  in
        let uu____44611 = extract_from_ref_set e2  in
        FStar_List.append uu____44608 uu____44611
    | uu____44614 ->
        let uu____44615 =
          let uu____44617 = FStar_Parser_AST.term_to_string e  in
          FStar_Util.format1 "Not a ref set %s" uu____44617  in
        failwith uu____44615
  
let (is_general_application : FStar_Parser_AST.term -> Prims.bool) =
  fun e  ->
    let uu____44629 = (is_array e) || (is_ref_set e)  in
    Prims.op_Negation uu____44629
  
let (is_general_construction : FStar_Parser_AST.term -> Prims.bool) =
  fun e  ->
    let uu____44638 = (is_list e) || (is_lex_list e)  in
    Prims.op_Negation uu____44638
  
let (is_general_prefix_op : FStar_Ident.ident -> Prims.bool) =
  fun op  ->
    let op_starting_char =
      let uu____44649 = FStar_Ident.text_of_id op  in
      FStar_Util.char_at uu____44649 (Prims.parse_int "0")  in
    ((op_starting_char = 33) || (op_starting_char = 63)) ||
      ((op_starting_char = 126) &&
         (let uu____44659 = FStar_Ident.text_of_id op  in uu____44659 <> "~"))
  
let (head_and_args :
  FStar_Parser_AST.term ->
    (FStar_Parser_AST.term * (FStar_Parser_AST.term * FStar_Parser_AST.imp)
      Prims.list))
  =
  fun e  ->
    let rec aux e1 acc =
      match e1.FStar_Parser_AST.tm with
      | FStar_Parser_AST.App (head1,arg,imp) -> aux head1 ((arg, imp) :: acc)
      | uu____44729 -> (e1, acc)  in
    aux e []
  
type associativity =
  | Left 
  | Right 
  | NonAssoc 
let (uu___is_Left : associativity -> Prims.bool) =
  fun projectee  ->
    match projectee with | Left  -> true | uu____44749 -> false
  
let (uu___is_Right : associativity -> Prims.bool) =
  fun projectee  ->
    match projectee with | Right  -> true | uu____44760 -> false
  
let (uu___is_NonAssoc : associativity -> Prims.bool) =
  fun projectee  ->
    match projectee with | NonAssoc  -> true | uu____44771 -> false
  
type token = (FStar_Char.char,Prims.string) FStar_Util.either
type associativity_level = (associativity * token Prims.list)
let (token_to_string :
  (FStar_BaseTypes.char,Prims.string) FStar_Util.either -> Prims.string) =
  fun uu___325_44797  ->
    match uu___325_44797 with
    | FStar_Util.Inl c -> Prims.op_Hat (FStar_Util.string_of_char c) ".*"
    | FStar_Util.Inr s -> s
  
let (matches_token :
  Prims.string ->
    (FStar_Char.char,Prims.string) FStar_Util.either -> Prims.bool)
  =
  fun s  ->
    fun uu___326_44832  ->
      match uu___326_44832 with
      | FStar_Util.Inl c ->
          let uu____44845 = FStar_String.get s (Prims.parse_int "0")  in
          uu____44845 = c
      | FStar_Util.Inr s' -> s = s'
  
let matches_level :
  'Auu____44861 .
    Prims.string ->
      ('Auu____44861 * (FStar_Char.char,Prims.string) FStar_Util.either
        Prims.list) -> Prims.bool
  =
  fun s  ->
    fun uu____44885  ->
      match uu____44885 with
      | (assoc_levels,tokens) ->
          let uu____44917 = FStar_List.tryFind (matches_token s) tokens  in
          uu____44917 <> FStar_Pervasives_Native.None
  
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
  let levels_from_associativity l uu___327_45089 =
    match uu___327_45089 with
    | Left  -> (l, l, (l - (Prims.parse_int "1")))
    | Right  -> ((l - (Prims.parse_int "1")), l, l)
    | NonAssoc  ->
        ((l - (Prims.parse_int "1")), l, (l - (Prims.parse_int "1")))
     in
  FStar_List.mapi
    (fun i  ->
       fun uu____45139  ->
         match uu____45139 with
         | (assoc1,tokens) -> ((levels_from_associativity i assoc1), tokens))
    level_associativity_spec
  
let (assign_levels :
  associativity_level Prims.list ->
    Prims.string -> (Prims.int * Prims.int * Prims.int))
  =
  fun token_associativity_spec  ->
    fun s  ->
      let uu____45214 = FStar_List.tryFind (matches_level s) level_table  in
      match uu____45214 with
      | FStar_Pervasives_Native.Some (assoc_levels,uu____45266) ->
          assoc_levels
      | uu____45304 -> failwith (Prims.op_Hat "Unrecognized operator " s)
  
let max_level :
  'Auu____45337 . ('Auu____45337 * token Prims.list) Prims.list -> Prims.int
  =
  fun l  ->
    let find_level_and_max n1 level =
      let uu____45386 =
        FStar_List.tryFind
          (fun uu____45422  ->
             match uu____45422 with
             | (uu____45439,tokens) ->
                 tokens = (FStar_Pervasives_Native.snd level)) level_table
         in
      match uu____45386 with
      | FStar_Pervasives_Native.Some
          ((uu____45468,l1,uu____45470),uu____45471) -> max n1 l1
      | FStar_Pervasives_Native.None  ->
          let uu____45521 =
            let uu____45523 =
              let uu____45525 =
                FStar_List.map token_to_string
                  (FStar_Pervasives_Native.snd level)
                 in
              FStar_String.concat "," uu____45525  in
            FStar_Util.format1 "Undefined associativity level %s" uu____45523
             in
          failwith uu____45521
       in
    FStar_List.fold_left find_level_and_max (Prims.parse_int "0") l
  
let (levels : Prims.string -> (Prims.int * Prims.int * Prims.int)) =
  fun op  ->
    let uu____45560 = assign_levels level_associativity_spec op  in
    match uu____45560 with
    | (left1,mine,right1) ->
        if op = "*"
        then ((left1 - (Prims.parse_int "1")), mine, right1)
        else (left1, mine, right1)
  
let (operatorInfix0ad12 : associativity_level Prims.list) =
  [opinfix0a; opinfix0b; opinfix0c; opinfix0d; opinfix1; opinfix2] 
let (is_operatorInfix0ad12 : FStar_Ident.ident -> Prims.bool) =
  fun op  ->
    let uu____45619 =
      let uu____45622 =
        let uu____45628 = FStar_Ident.text_of_id op  in
        FStar_All.pipe_left matches_level uu____45628  in
      FStar_List.tryFind uu____45622 operatorInfix0ad12  in
    uu____45619 <> FStar_Pervasives_Native.None
  
let (is_operatorInfix34 : FStar_Ident.ident -> Prims.bool) =
  let opinfix34 = [opinfix3; opinfix4]  in
  fun op  ->
    let uu____45695 =
      let uu____45710 =
        let uu____45728 = FStar_Ident.text_of_id op  in
        FStar_All.pipe_left matches_level uu____45728  in
      FStar_List.tryFind uu____45710 opinfix34  in
    uu____45695 <> FStar_Pervasives_Native.None
  
let (handleable_args_length : FStar_Ident.ident -> Prims.int) =
  fun op  ->
    let op_s = FStar_Ident.text_of_id op  in
    let uu____45794 =
      (is_general_prefix_op op) || (FStar_List.mem op_s ["-"; "~"])  in
    if uu____45794
    then (Prims.parse_int "1")
    else
      (let uu____45807 =
         ((is_operatorInfix0ad12 op) || (is_operatorInfix34 op)) ||
           (FStar_List.mem op_s
              ["<==>"; "==>"; "\\/"; "/\\"; "="; "|>"; ":="; ".()"; ".[]"])
          in
       if uu____45807
       then (Prims.parse_int "2")
       else
         if FStar_List.mem op_s [".()<-"; ".[]<-"]
         then (Prims.parse_int "3")
         else (Prims.parse_int "0"))
  
let handleable_op :
  'Auu____45853 . FStar_Ident.ident -> 'Auu____45853 Prims.list -> Prims.bool
  =
  fun op  ->
    fun args  ->
      match FStar_List.length args with
      | _45869 when _45869 = (Prims.parse_int "0") -> true
      | _45871 when _45871 = (Prims.parse_int "1") ->
          (is_general_prefix_op op) ||
            (let uu____45873 = FStar_Ident.text_of_id op  in
             FStar_List.mem uu____45873 ["-"; "~"])
      | _45881 when _45881 = (Prims.parse_int "2") ->
          ((is_operatorInfix0ad12 op) || (is_operatorInfix34 op)) ||
            (let uu____45883 = FStar_Ident.text_of_id op  in
             FStar_List.mem uu____45883
               ["<==>"; "==>"; "\\/"; "/\\"; "="; "|>"; ":="; ".()"; ".[]"])
      | _45905 when _45905 = (Prims.parse_int "3") ->
          let uu____45906 = FStar_Ident.text_of_id op  in
          FStar_List.mem uu____45906 [".()<-"; ".[]<-"]
      | uu____45914 -> false
  
type annotation_style =
  | Binders of (Prims.int * Prims.int * Prims.bool) 
  | Arrows of (Prims.int * Prims.int) 
let (uu___is_Binders : annotation_style -> Prims.bool) =
  fun projectee  ->
    match projectee with | Binders _0 -> true | uu____45960 -> false
  
let (__proj__Binders__item___0 :
  annotation_style -> (Prims.int * Prims.int * Prims.bool)) =
  fun projectee  -> match projectee with | Binders _0 -> _0 
let (uu___is_Arrows : annotation_style -> Prims.bool) =
  fun projectee  ->
    match projectee with | Arrows _0 -> true | uu____46013 -> false
  
let (__proj__Arrows__item___0 : annotation_style -> (Prims.int * Prims.int))
  = fun projectee  -> match projectee with | Arrows _0 -> _0 
let (all_binders_annot : FStar_Parser_AST.term -> Prims.bool) =
  fun e  ->
    let is_binder_annot b =
      match b.FStar_Parser_AST.b with
      | FStar_Parser_AST.Annotated uu____46056 -> true
      | uu____46062 -> false  in
    let rec all_binders e1 l =
      match e1.FStar_Parser_AST.tm with
      | FStar_Parser_AST.Product (bs,tgt) ->
          let uu____46095 = FStar_List.for_all is_binder_annot bs  in
          if uu____46095
          then all_binders tgt (l + (FStar_List.length bs))
          else (false, (Prims.parse_int "0"))
      | uu____46110 -> (true, (l + (Prims.parse_int "1")))  in
    let uu____46115 = all_binders e (Prims.parse_int "0")  in
    match uu____46115 with
    | (b,l) -> if b && (l > (Prims.parse_int "1")) then true else false
  
type catf =
  FStar_Pprint.document -> FStar_Pprint.document -> FStar_Pprint.document
let (cat_with_colon :
  FStar_Pprint.document -> FStar_Pprint.document -> FStar_Pprint.document) =
  fun x  ->
    fun y  ->
      let uu____46154 = FStar_Pprint.op_Hat_Slash_Hat FStar_Pprint.colon y
         in
      FStar_Pprint.op_Hat_Hat x uu____46154
  
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
  'Auu____46314 .
    ('Auu____46314 -> FStar_Pprint.document) ->
      'Auu____46314 -> FStar_Range.range -> FStar_Pprint.document
  =
  fun printer  ->
    fun tm  ->
      fun tmrange  ->
        let rec comments_before_pos acc print_pos lookahead_pos =
          let uu____46356 = FStar_ST.op_Bang comment_stack  in
          match uu____46356 with
          | [] -> (acc, false)
          | (c,crange)::cs ->
              let comment =
                let uu____46427 = str c  in
                FStar_Pprint.op_Hat_Hat uu____46427 FStar_Pprint.hardline  in
              let uu____46428 = FStar_Range.range_before_pos crange print_pos
                 in
              if uu____46428
              then
                (FStar_ST.op_Colon_Equals comment_stack cs;
                 (let uu____46470 = FStar_Pprint.op_Hat_Hat acc comment  in
                  comments_before_pos uu____46470 print_pos lookahead_pos))
              else
                (let uu____46473 =
                   FStar_Range.range_before_pos crange lookahead_pos  in
                 (acc, uu____46473))
           in
        let uu____46476 =
          let uu____46482 =
            let uu____46483 = FStar_Range.start_of_range tmrange  in
            FStar_Range.end_of_line uu____46483  in
          let uu____46484 = FStar_Range.end_of_range tmrange  in
          comments_before_pos FStar_Pprint.empty uu____46482 uu____46484  in
        match uu____46476 with
        | (comments,has_lookahead) ->
            let printed_e = printer tm  in
            let comments1 =
              if has_lookahead
              then
                let pos = FStar_Range.end_of_range tmrange  in
                let uu____46493 = comments_before_pos comments pos pos  in
                FStar_Pervasives_Native.fst uu____46493
              else comments  in
            if comments1 = FStar_Pprint.empty
            then printed_e
            else
              (let uu____46505 = FStar_Pprint.op_Hat_Hat comments1 printed_e
                  in
               FStar_Pprint.group uu____46505)
  
let with_comment_sep :
  'Auu____46517 'Auu____46518 .
    ('Auu____46517 -> 'Auu____46518) ->
      'Auu____46517 ->
        FStar_Range.range -> (FStar_Pprint.document * 'Auu____46518)
  =
  fun printer  ->
    fun tm  ->
      fun tmrange  ->
        let rec comments_before_pos acc print_pos lookahead_pos =
          let uu____46564 = FStar_ST.op_Bang comment_stack  in
          match uu____46564 with
          | [] -> (acc, false)
          | (c,crange)::cs ->
              let comment = str c  in
              let uu____46635 = FStar_Range.range_before_pos crange print_pos
                 in
              if uu____46635
              then
                (FStar_ST.op_Colon_Equals comment_stack cs;
                 (let uu____46677 =
                    if acc = FStar_Pprint.empty
                    then comment
                    else
                      (let uu____46681 =
                         FStar_Pprint.op_Hat_Hat FStar_Pprint.hardline
                           comment
                          in
                       FStar_Pprint.op_Hat_Hat acc uu____46681)
                     in
                  comments_before_pos uu____46677 print_pos lookahead_pos))
              else
                (let uu____46684 =
                   FStar_Range.range_before_pos crange lookahead_pos  in
                 (acc, uu____46684))
           in
        let uu____46687 =
          let uu____46693 =
            let uu____46694 = FStar_Range.start_of_range tmrange  in
            FStar_Range.end_of_line uu____46694  in
          let uu____46695 = FStar_Range.end_of_range tmrange  in
          comments_before_pos FStar_Pprint.empty uu____46693 uu____46695  in
        match uu____46687 with
        | (comments,has_lookahead) ->
            let printed_e = printer tm  in
            let comments1 =
              if has_lookahead
              then
                let pos = FStar_Range.end_of_range tmrange  in
                let uu____46708 = comments_before_pos comments pos pos  in
                FStar_Pervasives_Native.fst uu____46708
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
                let uu____46761 = FStar_ST.op_Bang comment_stack  in
                match uu____46761 with
                | (comment,crange)::cs when
                    FStar_Range.range_before_pos crange pos ->
                    (FStar_ST.op_Colon_Equals comment_stack cs;
                     (let lnum =
                        let uu____46855 =
                          let uu____46857 =
                            let uu____46859 =
                              FStar_Range.start_of_range crange  in
                            FStar_Range.line_of_pos uu____46859  in
                          uu____46857 - lbegin  in
                        max k uu____46855  in
                      let lnum1 = min (Prims.parse_int "2") lnum  in
                      let doc2 =
                        let uu____46864 =
                          let uu____46865 =
                            FStar_Pprint.repeat lnum1 FStar_Pprint.hardline
                             in
                          let uu____46866 = str comment  in
                          FStar_Pprint.op_Hat_Hat uu____46865 uu____46866  in
                        FStar_Pprint.op_Hat_Hat doc1 uu____46864  in
                      let uu____46867 =
                        let uu____46869 = FStar_Range.end_of_range crange  in
                        FStar_Range.line_of_pos uu____46869  in
                      place_comments_until_pos (Prims.parse_int "1")
                        uu____46867 pos meta_decl doc2 true init1))
                | uu____46872 ->
                    if doc1 = FStar_Pprint.empty
                    then FStar_Pprint.empty
                    else
                      (let lnum =
                         let uu____46885 = FStar_Range.line_of_pos pos  in
                         uu____46885 - lbegin  in
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
                       let uu____46927 =
                         FStar_Pprint.repeat lnum7 FStar_Pprint.hardline  in
                       FStar_Pprint.op_Hat_Hat doc1 uu____46927)
  
let separate_map_with_comments :
  'Auu____46941 .
    FStar_Pprint.document ->
      FStar_Pprint.document ->
        ('Auu____46941 -> FStar_Pprint.document) ->
          'Auu____46941 Prims.list ->
            ('Auu____46941 -> decl_meta) -> FStar_Pprint.document
  =
  fun prefix1  ->
    fun sep  ->
      fun f  ->
        fun xs  ->
          fun extract_meta  ->
            let fold_fun uu____47000 x =
              match uu____47000 with
              | (last_line,doc1) ->
                  let meta_decl = extract_meta x  in
                  let r = meta_decl.r  in
                  let doc2 =
                    let uu____47019 = FStar_Range.start_of_range r  in
                    place_comments_until_pos (Prims.parse_int "1") last_line
                      uu____47019 meta_decl doc1 false false
                     in
                  let uu____47023 =
                    let uu____47025 = FStar_Range.end_of_range r  in
                    FStar_Range.line_of_pos uu____47025  in
                  let uu____47026 =
                    let uu____47027 =
                      let uu____47028 = f x  in
                      FStar_Pprint.op_Hat_Hat sep uu____47028  in
                    FStar_Pprint.op_Hat_Hat doc2 uu____47027  in
                  (uu____47023, uu____47026)
               in
            let uu____47030 =
              let uu____47037 = FStar_List.hd xs  in
              let uu____47038 = FStar_List.tl xs  in
              (uu____47037, uu____47038)  in
            match uu____47030 with
            | (x,xs1) ->
                let init1 =
                  let meta_decl = extract_meta x  in
                  let uu____47056 =
                    let uu____47058 = FStar_Range.end_of_range meta_decl.r
                       in
                    FStar_Range.line_of_pos uu____47058  in
                  let uu____47059 =
                    let uu____47060 = f x  in
                    FStar_Pprint.op_Hat_Hat prefix1 uu____47060  in
                  (uu____47056, uu____47059)  in
                let uu____47062 = FStar_List.fold_left fold_fun init1 xs1  in
                FStar_Pervasives_Native.snd uu____47062
  
let separate_map_with_comments_kw :
  'Auu____47089 'Auu____47090 .
    'Auu____47089 ->
      'Auu____47089 ->
        ('Auu____47089 -> 'Auu____47090 -> FStar_Pprint.document) ->
          'Auu____47090 Prims.list ->
            ('Auu____47090 -> decl_meta) -> FStar_Pprint.document
  =
  fun prefix1  ->
    fun sep  ->
      fun f  ->
        fun xs  ->
          fun extract_meta  ->
            let fold_fun uu____47154 x =
              match uu____47154 with
              | (last_line,doc1) ->
                  let meta_decl = extract_meta x  in
                  let r = meta_decl.r  in
                  let doc2 =
                    let uu____47173 = FStar_Range.start_of_range r  in
                    place_comments_until_pos (Prims.parse_int "1") last_line
                      uu____47173 meta_decl doc1 false false
                     in
                  let uu____47177 =
                    let uu____47179 = FStar_Range.end_of_range r  in
                    FStar_Range.line_of_pos uu____47179  in
                  let uu____47180 =
                    let uu____47181 = f sep x  in
                    FStar_Pprint.op_Hat_Hat doc2 uu____47181  in
                  (uu____47177, uu____47180)
               in
            let uu____47183 =
              let uu____47190 = FStar_List.hd xs  in
              let uu____47191 = FStar_List.tl xs  in
              (uu____47190, uu____47191)  in
            match uu____47183 with
            | (x,xs1) ->
                let init1 =
                  let meta_decl = extract_meta x  in
                  let uu____47209 =
                    let uu____47211 = FStar_Range.end_of_range meta_decl.r
                       in
                    FStar_Range.line_of_pos uu____47211  in
                  let uu____47212 = f prefix1 x  in
                  (uu____47209, uu____47212)  in
                let uu____47214 = FStar_List.fold_left fold_fun init1 xs1  in
                FStar_Pervasives_Native.snd uu____47214
  
let rec (p_decl : FStar_Parser_AST.decl -> FStar_Pprint.document) =
  fun d  ->
    let qualifiers =
      match ((d.FStar_Parser_AST.quals), (d.FStar_Parser_AST.d)) with
      | ((FStar_Parser_AST.Assumption )::[],FStar_Parser_AST.Assume
         (id1,uu____48200)) ->
          let uu____48203 =
            let uu____48205 =
              FStar_Util.char_at id1.FStar_Ident.idText (Prims.parse_int "0")
               in
            FStar_All.pipe_right uu____48205 FStar_Util.is_upper  in
          if uu____48203
          then
            let uu____48211 = p_qualifier FStar_Parser_AST.Assumption  in
            FStar_Pprint.op_Hat_Hat uu____48211 FStar_Pprint.space
          else p_qualifiers d.FStar_Parser_AST.quals
      | uu____48214 -> p_qualifiers d.FStar_Parser_AST.quals  in
    let uu____48221 =
      FStar_Pprint.optional (fun d1  -> p_fsdoc d1) d.FStar_Parser_AST.doc
       in
    let uu____48224 =
      let uu____48225 = p_attributes d.FStar_Parser_AST.attrs  in
      let uu____48226 =
        let uu____48227 = p_rawDecl d  in
        FStar_Pprint.op_Hat_Hat qualifiers uu____48227  in
      FStar_Pprint.op_Hat_Hat uu____48225 uu____48226  in
    FStar_Pprint.op_Hat_Hat uu____48221 uu____48224

and (p_attributes : FStar_Parser_AST.attributes_ -> FStar_Pprint.document) =
  fun attrs  ->
    match attrs with
    | [] -> FStar_Pprint.empty
    | uu____48229 ->
        let uu____48230 =
          let uu____48231 = str "@ "  in
          let uu____48233 =
            let uu____48234 =
              let uu____48235 =
                let uu____48236 =
                  let uu____48237 = FStar_List.map p_atomicTerm attrs  in
                  FStar_Pprint.flow break1 uu____48237  in
                FStar_Pprint.op_Hat_Hat uu____48236 FStar_Pprint.rbracket  in
              FStar_Pprint.align uu____48235  in
            FStar_Pprint.op_Hat_Hat uu____48234 FStar_Pprint.hardline  in
          FStar_Pprint.op_Hat_Hat uu____48231 uu____48233  in
        FStar_Pprint.op_Hat_Hat FStar_Pprint.lbracket uu____48230

and (p_fsdoc : FStar_Parser_AST.fsdoc -> FStar_Pprint.document) =
  fun uu____48240  ->
    match uu____48240 with
    | (doc1,kwd_args) ->
        let kwd_args_doc =
          match kwd_args with
          | [] -> FStar_Pprint.empty
          | kwd_args1 ->
              let process_kwd_arg uu____48288 =
                match uu____48288 with
                | (kwd,arg) ->
                    let uu____48301 = str "@"  in
                    let uu____48303 =
                      let uu____48304 = str kwd  in
                      let uu____48305 =
                        let uu____48306 = str arg  in
                        FStar_Pprint.op_Hat_Hat FStar_Pprint.space
                          uu____48306
                         in
                      FStar_Pprint.op_Hat_Hat uu____48304 uu____48305  in
                    FStar_Pprint.op_Hat_Hat uu____48301 uu____48303
                 in
              let uu____48307 =
                FStar_Pprint.separate_map FStar_Pprint.hardline
                  process_kwd_arg kwd_args1
                 in
              FStar_Pprint.op_Hat_Hat uu____48307 FStar_Pprint.hardline
           in
        let uu____48314 =
          let uu____48315 =
            let uu____48316 =
              let uu____48317 = str doc1  in
              let uu____48318 =
                let uu____48319 =
                  let uu____48320 =
                    FStar_Pprint.op_Hat_Hat FStar_Pprint.rparen
                      FStar_Pprint.hardline
                     in
                  FStar_Pprint.op_Hat_Hat FStar_Pprint.star uu____48320  in
                FStar_Pprint.op_Hat_Hat kwd_args_doc uu____48319  in
              FStar_Pprint.op_Hat_Hat uu____48317 uu____48318  in
            FStar_Pprint.op_Hat_Hat FStar_Pprint.star uu____48316  in
          FStar_Pprint.op_Hat_Hat FStar_Pprint.star uu____48315  in
        FStar_Pprint.op_Hat_Hat FStar_Pprint.lparen uu____48314

and (p_justSig : FStar_Parser_AST.decl -> FStar_Pprint.document) =
  fun d  ->
    match d.FStar_Parser_AST.d with
    | FStar_Parser_AST.Val (lid,t) ->
        let uu____48324 =
          let uu____48325 = str "val"  in
          let uu____48327 =
            let uu____48328 =
              let uu____48329 = p_lident lid  in
              let uu____48330 =
                FStar_Pprint.op_Hat_Hat FStar_Pprint.space FStar_Pprint.colon
                 in
              FStar_Pprint.op_Hat_Hat uu____48329 uu____48330  in
            FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____48328  in
          FStar_Pprint.op_Hat_Hat uu____48325 uu____48327  in
        let uu____48331 = p_typ false false t  in
        FStar_Pprint.op_Hat_Hat uu____48324 uu____48331
    | FStar_Parser_AST.TopLevelLet (uu____48334,lbs) ->
        FStar_Pprint.separate_map FStar_Pprint.hardline
          (fun lb  ->
             let uu____48359 =
               let uu____48360 = str "let"  in p_letlhs uu____48360 lb false
                in
             FStar_Pprint.group uu____48359) lbs
    | uu____48363 -> FStar_Pprint.empty

and (p_list :
  (FStar_Ident.ident -> FStar_Pprint.document) ->
    FStar_Pprint.document ->
      FStar_Ident.ident Prims.list -> FStar_Pprint.document)
  =
  fun f  ->
    fun sep  ->
      fun l  ->
        let rec p_list' uu___328_48378 =
          match uu___328_48378 with
          | [] -> FStar_Pprint.empty
          | x::[] -> f x
          | x::xs ->
              let uu____48386 = f x  in
              let uu____48387 =
                let uu____48388 = p_list' xs  in
                FStar_Pprint.op_Hat_Hat sep uu____48388  in
              FStar_Pprint.op_Hat_Hat uu____48386 uu____48387
           in
        let uu____48389 = str "["  in
        let uu____48391 =
          let uu____48392 = p_list' l  in
          let uu____48393 = str "]"  in
          FStar_Pprint.op_Hat_Hat uu____48392 uu____48393  in
        FStar_Pprint.op_Hat_Hat uu____48389 uu____48391

and (p_rawDecl : FStar_Parser_AST.decl -> FStar_Pprint.document) =
  fun d  ->
    match d.FStar_Parser_AST.d with
    | FStar_Parser_AST.Open uid ->
        let uu____48397 =
          let uu____48398 = str "open"  in
          let uu____48400 = p_quident uid  in
          FStar_Pprint.op_Hat_Slash_Hat uu____48398 uu____48400  in
        FStar_Pprint.group uu____48397
    | FStar_Parser_AST.Include uid ->
        let uu____48402 =
          let uu____48403 = str "include"  in
          let uu____48405 = p_quident uid  in
          FStar_Pprint.op_Hat_Slash_Hat uu____48403 uu____48405  in
        FStar_Pprint.group uu____48402
    | FStar_Parser_AST.Friend uid ->
        let uu____48407 =
          let uu____48408 = str "friend"  in
          let uu____48410 = p_quident uid  in
          FStar_Pprint.op_Hat_Slash_Hat uu____48408 uu____48410  in
        FStar_Pprint.group uu____48407
    | FStar_Parser_AST.ModuleAbbrev (uid1,uid2) ->
        let uu____48413 =
          let uu____48414 = str "module"  in
          let uu____48416 =
            let uu____48417 =
              let uu____48418 = p_uident uid1  in
              let uu____48419 =
                FStar_Pprint.op_Hat_Hat FStar_Pprint.space
                  FStar_Pprint.equals
                 in
              FStar_Pprint.op_Hat_Hat uu____48418 uu____48419  in
            FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____48417  in
          FStar_Pprint.op_Hat_Hat uu____48414 uu____48416  in
        let uu____48420 = p_quident uid2  in
        op_Hat_Slash_Plus_Hat uu____48413 uu____48420
    | FStar_Parser_AST.TopLevelModule uid ->
        let uu____48422 =
          let uu____48423 = str "module"  in
          let uu____48425 =
            let uu____48426 = p_quident uid  in
            FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____48426  in
          FStar_Pprint.op_Hat_Hat uu____48423 uu____48425  in
        FStar_Pprint.group uu____48422
    | FStar_Parser_AST.Tycon
        (true
         ,uu____48427,(FStar_Parser_AST.TyconAbbrev
                       (uid,tpars,FStar_Pervasives_Native.None ,t),FStar_Pervasives_Native.None
                       )::[])
        ->
        let effect_prefix_doc =
          let uu____48464 = str "effect"  in
          let uu____48466 =
            let uu____48467 = p_uident uid  in
            FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____48467  in
          FStar_Pprint.op_Hat_Hat uu____48464 uu____48466  in
        let uu____48468 =
          let uu____48469 = p_typars tpars  in
          FStar_Pprint.surround (Prims.parse_int "2") (Prims.parse_int "1")
            effect_prefix_doc uu____48469 FStar_Pprint.equals
           in
        let uu____48472 = p_typ false false t  in
        op_Hat_Slash_Plus_Hat uu____48468 uu____48472
    | FStar_Parser_AST.Tycon (false ,tc,tcdefs) ->
        let s = if tc then str "class" else str "type"  in
        let uu____48503 =
          let uu____48504 = FStar_List.hd tcdefs  in
          p_fsdocTypeDeclPairs s uu____48504  in
        let uu____48517 =
          let uu____48518 = FStar_List.tl tcdefs  in
          FStar_All.pipe_left
            (FStar_Pprint.concat_map
               (fun x  ->
                  let uu____48556 =
                    let uu____48557 = str "and"  in
                    p_fsdocTypeDeclPairs uu____48557 x  in
                  FStar_Pprint.op_Hat_Hat break1 uu____48556)) uu____48518
           in
        FStar_Pprint.op_Hat_Hat uu____48503 uu____48517
    | FStar_Parser_AST.TopLevelLet (q,lbs) ->
        let let_doc =
          let uu____48574 = str "let"  in
          let uu____48576 = p_letqualifier q  in
          FStar_Pprint.op_Hat_Hat uu____48574 uu____48576  in
        let uu____48577 = str "and"  in
        separate_map_with_comments_kw let_doc uu____48577 p_letbinding lbs
          (fun uu____48587  ->
             match uu____48587 with
             | (p,t) ->
                 let uu____48594 =
                   FStar_Range.union_ranges p.FStar_Parser_AST.prange
                     t.FStar_Parser_AST.range
                    in
                 {
                   r = uu____48594;
                   has_qs = false;
                   has_attrs = false;
                   has_fsdoc = (FStar_Util.is_some d.FStar_Parser_AST.doc);
                   is_fsdoc = false
                 })
    | FStar_Parser_AST.Val (lid,t) ->
        let uu____48600 =
          let uu____48601 = str "val"  in
          let uu____48603 =
            let uu____48604 =
              let uu____48605 = p_lident lid  in
              let uu____48606 = sig_as_binders_if_possible t false  in
              FStar_Pprint.op_Hat_Hat uu____48605 uu____48606  in
            FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____48604  in
          FStar_Pprint.op_Hat_Hat uu____48601 uu____48603  in
        FStar_All.pipe_left FStar_Pprint.group uu____48600
    | FStar_Parser_AST.Assume (id1,t) ->
        let decl_keyword =
          let uu____48611 =
            let uu____48613 =
              FStar_Util.char_at id1.FStar_Ident.idText (Prims.parse_int "0")
               in
            FStar_All.pipe_right uu____48613 FStar_Util.is_upper  in
          if uu____48611
          then FStar_Pprint.empty
          else
            (let uu____48621 = str "val"  in
             FStar_Pprint.op_Hat_Hat uu____48621 FStar_Pprint.space)
           in
        let uu____48623 =
          let uu____48624 = p_ident id1  in
          let uu____48625 =
            let uu____48626 =
              let uu____48627 =
                let uu____48628 = p_typ false false t  in
                FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____48628  in
              FStar_Pprint.op_Hat_Hat FStar_Pprint.colon uu____48627  in
            FStar_Pprint.group uu____48626  in
          FStar_Pprint.op_Hat_Hat uu____48624 uu____48625  in
        FStar_Pprint.op_Hat_Hat decl_keyword uu____48623
    | FStar_Parser_AST.Exception (uid,t_opt) ->
        let uu____48637 = str "exception"  in
        let uu____48639 =
          let uu____48640 =
            let uu____48641 = p_uident uid  in
            let uu____48642 =
              FStar_Pprint.optional
                (fun t  ->
                   let uu____48646 =
                     let uu____48647 = str "of"  in
                     let uu____48649 = p_typ false false t  in
                     op_Hat_Slash_Plus_Hat uu____48647 uu____48649  in
                   FStar_Pprint.op_Hat_Hat break1 uu____48646) t_opt
               in
            FStar_Pprint.op_Hat_Hat uu____48641 uu____48642  in
          FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____48640  in
        FStar_Pprint.op_Hat_Hat uu____48637 uu____48639
    | FStar_Parser_AST.NewEffect ne ->
        let uu____48653 = str "new_effect"  in
        let uu____48655 =
          let uu____48656 = p_newEffect ne  in
          FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____48656  in
        FStar_Pprint.op_Hat_Hat uu____48653 uu____48655
    | FStar_Parser_AST.SubEffect se ->
        let uu____48658 = str "sub_effect"  in
        let uu____48660 =
          let uu____48661 = p_subEffect se  in
          FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____48661  in
        FStar_Pprint.op_Hat_Hat uu____48658 uu____48660
    | FStar_Parser_AST.Pragma p -> p_pragma p
    | FStar_Parser_AST.Fsdoc doc1 -> p_fsdoc doc1
    | FStar_Parser_AST.Main uu____48664 ->
        failwith "*Main declaration* : Is that really still in use ??"
    | FStar_Parser_AST.Tycon (true ,uu____48666,uu____48667) ->
        failwith
          "Effect abbreviation is expected to be defined by an abbreviation"
    | FStar_Parser_AST.Splice (ids,t) ->
        let uu____48695 = str "%splice"  in
        let uu____48697 =
          let uu____48698 =
            let uu____48699 = str ";"  in p_list p_uident uu____48699 ids  in
          let uu____48701 =
            let uu____48702 = p_term false false t  in
            FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____48702  in
          FStar_Pprint.op_Hat_Hat uu____48698 uu____48701  in
        FStar_Pprint.op_Hat_Hat uu____48695 uu____48697

and (p_pragma : FStar_Parser_AST.pragma -> FStar_Pprint.document) =
  fun uu___329_48705  ->
    match uu___329_48705 with
    | FStar_Parser_AST.SetOptions s ->
        let uu____48708 = str "#set-options"  in
        let uu____48710 =
          let uu____48711 =
            let uu____48712 = str s  in FStar_Pprint.dquotes uu____48712  in
          FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____48711  in
        FStar_Pprint.op_Hat_Hat uu____48708 uu____48710
    | FStar_Parser_AST.ResetOptions s_opt ->
        let uu____48717 = str "#reset-options"  in
        let uu____48719 =
          FStar_Pprint.optional
            (fun s  ->
               let uu____48725 =
                 let uu____48726 = str s  in FStar_Pprint.dquotes uu____48726
                  in
               FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____48725) s_opt
           in
        FStar_Pprint.op_Hat_Hat uu____48717 uu____48719
    | FStar_Parser_AST.PushOptions s_opt ->
        let uu____48731 = str "#push-options"  in
        let uu____48733 =
          FStar_Pprint.optional
            (fun s  ->
               let uu____48739 =
                 let uu____48740 = str s  in FStar_Pprint.dquotes uu____48740
                  in
               FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____48739) s_opt
           in
        FStar_Pprint.op_Hat_Hat uu____48731 uu____48733
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
    fun uu____48771  ->
      match uu____48771 with
      | (typedecl,fsdoc_opt) ->
          let uu____48784 = p_typeDecl (kw, fsdoc_opt) typedecl  in
          (match uu____48784 with
           | (comm,decl,body,pre) ->
               if comm = FStar_Pprint.empty
               then
                 let uu____48809 = pre body  in
                 FStar_Pprint.op_Hat_Hat decl uu____48809
               else
                 (let uu____48812 =
                    let uu____48813 =
                      let uu____48814 =
                        let uu____48815 = pre body  in
                        FStar_Pprint.op_Hat_Slash_Hat uu____48815 comm  in
                      FStar_Pprint.op_Hat_Hat decl uu____48814  in
                    let uu____48816 =
                      let uu____48817 =
                        let uu____48818 =
                          let uu____48819 =
                            let uu____48820 =
                              FStar_Pprint.op_Hat_Hat FStar_Pprint.hardline
                                body
                               in
                            FStar_Pprint.op_Hat_Hat comm uu____48820  in
                          FStar_Pprint.op_Hat_Hat FStar_Pprint.hardline
                            uu____48819
                           in
                        FStar_Pprint.nest (Prims.parse_int "2") uu____48818
                         in
                      FStar_Pprint.op_Hat_Hat decl uu____48817  in
                    FStar_Pprint.ifflat uu____48813 uu____48816  in
                  FStar_All.pipe_left FStar_Pprint.group uu____48812))

and (p_typeDecl :
  (FStar_Pprint.document * FStar_Parser_AST.fsdoc
    FStar_Pervasives_Native.option) ->
    FStar_Parser_AST.tycon ->
      (FStar_Pprint.document * FStar_Pprint.document * FStar_Pprint.document
        * (FStar_Pprint.document -> FStar_Pprint.document)))
  =
  fun pre  ->
    fun uu___330_48823  ->
      match uu___330_48823 with
      | FStar_Parser_AST.TyconAbstract (lid,bs,typ_opt) ->
          let uu____48852 = p_typeDeclPrefix pre false lid bs typ_opt  in
          (FStar_Pprint.empty, uu____48852, FStar_Pprint.empty,
            FStar_Pervasives.id)
      | FStar_Parser_AST.TyconAbbrev (lid,bs,typ_opt,t) ->
          let uu____48869 = p_typ_sep false false t  in
          (match uu____48869 with
           | (comm,doc1) ->
               let uu____48889 = p_typeDeclPrefix pre true lid bs typ_opt  in
               (comm, uu____48889, doc1, jump2))
      | FStar_Parser_AST.TyconRecord (lid,bs,typ_opt,record_field_decls) ->
          let p_recordFieldAndComments ps uu____48945 =
            match uu____48945 with
            | (lid1,t,doc_opt) ->
                let uu____48962 =
                  let uu____48967 =
                    FStar_Range.extend_to_end_of_line
                      t.FStar_Parser_AST.range
                     in
                  with_comment_sep (p_recordFieldDecl ps) (lid1, t, doc_opt)
                    uu____48967
                   in
                (match uu____48962 with
                 | (comm,field) ->
                     let sep =
                       if ps then FStar_Pprint.semi else FStar_Pprint.empty
                        in
                     inline_comment_or_above comm field sep)
             in
          let p_fields =
            let uu____48985 =
              separate_map_last FStar_Pprint.hardline
                p_recordFieldAndComments record_field_decls
               in
            braces_with_nesting uu____48985  in
          let uu____48994 = p_typeDeclPrefix pre true lid bs typ_opt  in
          (FStar_Pprint.empty, uu____48994, p_fields,
            ((fun d  -> FStar_Pprint.op_Hat_Hat FStar_Pprint.space d)))
      | FStar_Parser_AST.TyconVariant (lid,bs,typ_opt,ct_decls) ->
          let p_constructorBranchAndComments uu____49061 =
            match uu____49061 with
            | (uid,t_opt,doc_opt,use_of) ->
                let range =
                  let uu____49090 =
                    let uu____49091 =
                      FStar_Util.map_opt t_opt
                        (fun t  -> t.FStar_Parser_AST.range)
                       in
                    FStar_Util.dflt uid.FStar_Ident.idRange uu____49091  in
                  FStar_Range.extend_to_end_of_line uu____49090  in
                let uu____49096 =
                  with_comment_sep p_constructorBranch
                    (uid, t_opt, doc_opt, use_of) range
                   in
                (match uu____49096 with
                 | (comm,ctor) ->
                     inline_comment_or_above comm ctor FStar_Pprint.empty)
             in
          let datacon_doc =
            FStar_Pprint.separate_map FStar_Pprint.hardline
              p_constructorBranchAndComments ct_decls
             in
          let uu____49135 = p_typeDeclPrefix pre true lid bs typ_opt  in
          (FStar_Pprint.empty, uu____49135, datacon_doc, jump2)

and (p_typeDeclPrefix :
  (FStar_Pprint.document * FStar_Parser_AST.fsdoc
    FStar_Pervasives_Native.option) ->
    Prims.bool ->
      FStar_Ident.ident ->
        FStar_Parser_AST.binder Prims.list ->
          FStar_Parser_AST.knd FStar_Pervasives_Native.option ->
            FStar_Pprint.document)
  =
  fun uu____49140  ->
    fun eq1  ->
      fun lid  ->
        fun bs  ->
          fun typ_opt  ->
            match uu____49140 with
            | (kw,fsdoc_opt) ->
                let maybe_with_fsdoc cont =
                  let lid_doc = p_ident lid  in
                  let kw_lid =
                    let uu____49175 =
                      FStar_Pprint.op_Hat_Slash_Hat kw lid_doc  in
                    FStar_Pprint.group uu____49175  in
                  match fsdoc_opt with
                  | FStar_Pervasives_Native.None  -> cont kw_lid
                  | FStar_Pervasives_Native.Some fsdoc ->
                      let uu____49177 =
                        let uu____49180 =
                          let uu____49183 = p_fsdoc fsdoc  in
                          let uu____49184 =
                            let uu____49187 = cont lid_doc  in [uu____49187]
                             in
                          uu____49183 :: uu____49184  in
                        kw :: uu____49180  in
                      FStar_Pprint.separate FStar_Pprint.hardline uu____49177
                   in
                let typ =
                  let maybe_eq =
                    if eq1 then FStar_Pprint.equals else FStar_Pprint.empty
                     in
                  match typ_opt with
                  | FStar_Pervasives_Native.None  -> maybe_eq
                  | FStar_Pervasives_Native.Some t ->
                      let uu____49194 =
                        let uu____49195 =
                          let uu____49196 = p_typ false false t  in
                          FStar_Pprint.op_Hat_Slash_Hat uu____49196 maybe_eq
                           in
                        FStar_Pprint.op_Hat_Hat FStar_Pprint.space
                          uu____49195
                         in
                      FStar_Pprint.op_Hat_Hat FStar_Pprint.colon uu____49194
                   in
                if bs = []
                then maybe_with_fsdoc (fun n1  -> prefix2 n1 typ)
                else
                  (let binders = p_binders_list true bs  in
                   maybe_with_fsdoc
                     (fun n1  ->
                        let uu____49216 =
                          let uu____49217 = FStar_Pprint.flow break1 binders
                             in
                          prefix2 n1 uu____49217  in
                        prefix2 uu____49216 typ))

and (p_recordFieldDecl :
  Prims.bool ->
    (FStar_Ident.ident * FStar_Parser_AST.term * FStar_Parser_AST.fsdoc
      FStar_Pervasives_Native.option) -> FStar_Pprint.document)
  =
  fun ps  ->
    fun uu____49219  ->
      match uu____49219 with
      | (lid,t,doc_opt) ->
          let uu____49236 =
            let uu____49237 = FStar_Pprint.optional p_fsdoc doc_opt  in
            let uu____49238 =
              let uu____49239 = p_lident lid  in
              let uu____49240 =
                let uu____49241 = p_typ ps false t  in
                FStar_Pprint.op_Hat_Hat FStar_Pprint.colon uu____49241  in
              FStar_Pprint.op_Hat_Hat uu____49239 uu____49240  in
            FStar_Pprint.op_Hat_Hat uu____49237 uu____49238  in
          FStar_Pprint.group uu____49236

and (p_constructorBranch :
  (FStar_Ident.ident * FStar_Parser_AST.term FStar_Pervasives_Native.option *
    FStar_Parser_AST.fsdoc FStar_Pervasives_Native.option * Prims.bool) ->
    FStar_Pprint.document)
  =
  fun uu____49243  ->
    match uu____49243 with
    | (uid,t_opt,doc_opt,use_of) ->
        let sep = if use_of then str "of" else FStar_Pprint.colon  in
        let uid_doc =
          let uu____49277 =
            let uu____49278 =
              let uu____49279 = p_uident uid  in
              FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____49279  in
            FStar_Pprint.op_Hat_Hat FStar_Pprint.bar uu____49278  in
          FStar_Pprint.group uu____49277  in
        let uu____49280 = FStar_Pprint.optional p_fsdoc doc_opt  in
        let uu____49281 =
          default_or_map uid_doc
            (fun t  ->
               let uu____49285 =
                 let uu____49286 =
                   let uu____49287 =
                     let uu____49288 =
                       let uu____49289 = p_typ false false t  in
                       FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____49289
                        in
                     FStar_Pprint.op_Hat_Hat sep uu____49288  in
                   FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____49287  in
                 FStar_Pprint.op_Hat_Hat uid_doc uu____49286  in
               FStar_Pprint.group uu____49285) t_opt
           in
        FStar_Pprint.op_Hat_Hat uu____49280 uu____49281

and (p_letlhs :
  FStar_Pprint.document ->
    (FStar_Parser_AST.pattern * FStar_Parser_AST.term) ->
      Prims.bool -> FStar_Pprint.document)
  =
  fun kw  ->
    fun uu____49293  ->
      fun inner_let  ->
        match uu____49293 with
        | (pat,uu____49301) ->
            let uu____49302 =
              match pat.FStar_Parser_AST.pat with
              | FStar_Parser_AST.PatAscribed
                  (pat1,(t,FStar_Pervasives_Native.None )) ->
                  (pat1,
                    (FStar_Pervasives_Native.Some (t, FStar_Pprint.empty)))
              | FStar_Parser_AST.PatAscribed
                  (pat1,(t,FStar_Pervasives_Native.Some tac)) ->
                  let uu____49354 =
                    let uu____49361 =
                      let uu____49366 =
                        let uu____49367 =
                          let uu____49368 =
                            let uu____49369 = str "by"  in
                            let uu____49371 =
                              let uu____49372 = p_atomicTerm tac  in
                              FStar_Pprint.op_Hat_Hat FStar_Pprint.space
                                uu____49372
                               in
                            FStar_Pprint.op_Hat_Hat uu____49369 uu____49371
                             in
                          FStar_Pprint.op_Hat_Hat FStar_Pprint.space
                            uu____49368
                           in
                        FStar_Pprint.group uu____49367  in
                      (t, uu____49366)  in
                    FStar_Pervasives_Native.Some uu____49361  in
                  (pat1, uu____49354)
              | uu____49383 -> (pat, FStar_Pervasives_Native.None)  in
            (match uu____49302 with
             | (pat1,ascr) ->
                 (match pat1.FStar_Parser_AST.pat with
                  | FStar_Parser_AST.PatApp
                      ({
                         FStar_Parser_AST.pat = FStar_Parser_AST.PatVar
                           (lid,uu____49409);
                         FStar_Parser_AST.prange = uu____49410;_},pats)
                      ->
                      let ascr_doc =
                        match ascr with
                        | FStar_Pervasives_Native.Some (t,tac) ->
                            let uu____49427 =
                              sig_as_binders_if_possible t true  in
                            FStar_Pprint.op_Hat_Hat uu____49427 tac
                        | FStar_Pervasives_Native.None  -> FStar_Pprint.empty
                         in
                      let uu____49433 =
                        if inner_let
                        then
                          let uu____49447 = pats_as_binders_if_possible pats
                             in
                          match uu____49447 with
                          | (bs,style) ->
                              ((FStar_List.append bs [ascr_doc]), style)
                        else
                          (let uu____49470 = pats_as_binders_if_possible pats
                              in
                           match uu____49470 with
                           | (bs,style) ->
                               ((FStar_List.append bs [ascr_doc]), style))
                         in
                      (match uu____49433 with
                       | (terms,style) ->
                           let uu____49497 =
                             let uu____49498 =
                               let uu____49499 =
                                 let uu____49500 = p_lident lid  in
                                 let uu____49501 =
                                   format_sig style terms true true  in
                                 FStar_Pprint.op_Hat_Hat uu____49500
                                   uu____49501
                                  in
                               FStar_Pprint.op_Hat_Hat FStar_Pprint.space
                                 uu____49499
                                in
                             FStar_Pprint.op_Hat_Hat kw uu____49498  in
                           FStar_All.pipe_left FStar_Pprint.group uu____49497)
                  | uu____49504 ->
                      let ascr_doc =
                        match ascr with
                        | FStar_Pervasives_Native.Some (t,tac) ->
                            let uu____49512 =
                              let uu____49513 =
                                let uu____49514 =
                                  p_typ_top
                                    (Arrows
                                       ((Prims.parse_int "2"),
                                         (Prims.parse_int "2"))) false false
                                    t
                                   in
                                FStar_Pprint.op_Hat_Hat FStar_Pprint.colon
                                  uu____49514
                                 in
                              FStar_Pprint.group uu____49513  in
                            FStar_Pprint.op_Hat_Hat uu____49512 tac
                        | FStar_Pervasives_Native.None  -> FStar_Pprint.empty
                         in
                      let uu____49525 =
                        let uu____49526 =
                          let uu____49527 =
                            let uu____49528 = p_tuplePattern pat1  in
                            FStar_Pprint.op_Hat_Slash_Hat kw uu____49528  in
                          FStar_Pprint.group uu____49527  in
                        FStar_Pprint.op_Hat_Hat uu____49526 ascr_doc  in
                      FStar_Pprint.group uu____49525))

and (p_letbinding :
  FStar_Pprint.document ->
    (FStar_Parser_AST.pattern * FStar_Parser_AST.term) ->
      FStar_Pprint.document)
  =
  fun kw  ->
    fun uu____49530  ->
      match uu____49530 with
      | (pat,e) ->
          let doc_pat = p_letlhs kw (pat, e) false  in
          let uu____49539 = p_term_sep false false e  in
          (match uu____49539 with
           | (comm,doc_expr) ->
               let doc_expr1 =
                 inline_comment_or_above comm doc_expr FStar_Pprint.empty  in
               let uu____49549 =
                 let uu____49550 =
                   FStar_Pprint.op_Hat_Slash_Hat FStar_Pprint.equals
                     doc_expr1
                    in
                 FStar_Pprint.op_Hat_Slash_Hat doc_pat uu____49550  in
               let uu____49551 =
                 let uu____49552 =
                   let uu____49553 =
                     let uu____49554 =
                       let uu____49555 = jump2 doc_expr1  in
                       FStar_Pprint.op_Hat_Hat FStar_Pprint.equals
                         uu____49555
                        in
                     FStar_Pprint.group uu____49554  in
                   FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____49553  in
                 FStar_Pprint.op_Hat_Hat doc_pat uu____49552  in
               FStar_Pprint.ifflat uu____49549 uu____49551)

and (p_newEffect : FStar_Parser_AST.effect_decl -> FStar_Pprint.document) =
  fun uu___331_49556  ->
    match uu___331_49556 with
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
        let uu____49581 = p_uident uid  in
        let uu____49582 = p_binders true bs  in
        let uu____49584 =
          let uu____49585 = p_simpleTerm false false t  in
          prefix2 FStar_Pprint.equals uu____49585  in
        surround_maybe_empty (Prims.parse_int "2") (Prims.parse_int "1")
          uu____49581 uu____49582 uu____49584

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
          let uu____49600 =
            let uu____49601 =
              let uu____49602 =
                let uu____49603 = p_uident uid  in
                let uu____49604 = p_binders true bs  in
                let uu____49606 =
                  let uu____49607 = p_typ false false t  in
                  prefix2 FStar_Pprint.colon uu____49607  in
                surround_maybe_empty (Prims.parse_int "2")
                  (Prims.parse_int "1") uu____49603 uu____49604 uu____49606
                 in
              FStar_Pprint.group uu____49602  in
            let uu____49612 =
              let uu____49613 = str "with"  in
              let uu____49615 =
                let uu____49616 =
                  let uu____49617 =
                    let uu____49618 =
                      let uu____49619 =
                        let uu____49620 =
                          FStar_Pprint.op_Hat_Hat FStar_Pprint.semi
                            FStar_Pprint.space
                           in
                        FStar_Pprint.op_Hat_Hat FStar_Pprint.hardline
                          uu____49620
                         in
                      separate_map_last uu____49619 p_effectDecl eff_decls
                       in
                    FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____49618
                     in
                  FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____49617  in
                FStar_Pprint.op_Hat_Hat FStar_Pprint.hardline uu____49616  in
              FStar_Pprint.op_Hat_Hat uu____49613 uu____49615  in
            FStar_Pprint.op_Hat_Slash_Hat uu____49601 uu____49612  in
          braces_with_nesting uu____49600

and (p_effectDecl :
  Prims.bool -> FStar_Parser_AST.decl -> FStar_Pprint.document) =
  fun ps  ->
    fun d  ->
      match d.FStar_Parser_AST.d with
      | FStar_Parser_AST.Tycon
          (false
           ,uu____49624,(FStar_Parser_AST.TyconAbbrev
                         (lid,[],FStar_Pervasives_Native.None ,e),FStar_Pervasives_Native.None
                         )::[])
          ->
          let uu____49657 =
            let uu____49658 = p_lident lid  in
            let uu____49659 =
              FStar_Pprint.op_Hat_Hat FStar_Pprint.space FStar_Pprint.equals
               in
            FStar_Pprint.op_Hat_Hat uu____49658 uu____49659  in
          let uu____49660 = p_simpleTerm ps false e  in
          prefix2 uu____49657 uu____49660
      | uu____49662 ->
          let uu____49663 =
            let uu____49665 = FStar_Parser_AST.decl_to_string d  in
            FStar_Util.format1
              "Not a declaration of an effect member... or at least I hope so : %s"
              uu____49665
             in
          failwith uu____49663

and (p_subEffect : FStar_Parser_AST.lift -> FStar_Pprint.document) =
  fun lift  ->
    let lift_op_doc =
      let lifts =
        match lift.FStar_Parser_AST.lift_op with
        | FStar_Parser_AST.NonReifiableLift t -> [("lift_wp", t)]
        | FStar_Parser_AST.ReifiableLift (t1,t2) ->
            [("lift_wp", t1); ("lift", t2)]
        | FStar_Parser_AST.LiftForFree t -> [("lift", t)]  in
      let p_lift ps uu____49748 =
        match uu____49748 with
        | (kwd,t) ->
            let uu____49759 =
              let uu____49760 = str kwd  in
              let uu____49761 =
                FStar_Pprint.op_Hat_Hat FStar_Pprint.space
                  FStar_Pprint.equals
                 in
              FStar_Pprint.op_Hat_Hat uu____49760 uu____49761  in
            let uu____49762 = p_simpleTerm ps false t  in
            prefix2 uu____49759 uu____49762
         in
      separate_break_map_last FStar_Pprint.semi p_lift lifts  in
    let uu____49769 =
      let uu____49770 =
        let uu____49771 = p_quident lift.FStar_Parser_AST.msource  in
        let uu____49772 =
          let uu____49773 = str "~>"  in
          FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____49773  in
        FStar_Pprint.op_Hat_Hat uu____49771 uu____49772  in
      let uu____49775 = p_quident lift.FStar_Parser_AST.mdest  in
      prefix2 uu____49770 uu____49775  in
    let uu____49776 =
      let uu____49777 = braces_with_nesting lift_op_doc  in
      FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____49777  in
    FStar_Pprint.op_Hat_Hat uu____49769 uu____49776

and (p_qualifier : FStar_Parser_AST.qualifier -> FStar_Pprint.document) =
  fun uu___332_49778  ->
    match uu___332_49778 with
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
        let uu____49798 = p_qualifier q  in
        FStar_Pprint.op_Hat_Hat uu____49798 FStar_Pprint.hardline
    | uu____49799 ->
        let uu____49800 =
          let uu____49801 = FStar_List.map p_qualifier qs  in
          FStar_Pprint.flow break1 uu____49801  in
        FStar_Pprint.op_Hat_Hat uu____49800 FStar_Pprint.hardline

and (p_letqualifier :
  FStar_Parser_AST.let_qualifier -> FStar_Pprint.document) =
  fun uu___333_49804  ->
    match uu___333_49804 with
    | FStar_Parser_AST.Rec  ->
        let uu____49805 = str "rec"  in
        FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____49805
    | FStar_Parser_AST.NoLetQualifier  -> FStar_Pprint.empty

and (p_aqual : FStar_Parser_AST.arg_qualifier -> FStar_Pprint.document) =
  fun uu___334_49807  ->
    match uu___334_49807 with
    | FStar_Parser_AST.Implicit  -> str "#"
    | FStar_Parser_AST.Equality  -> str "$"
    | FStar_Parser_AST.Meta t ->
        let t1 =
          match t.FStar_Parser_AST.tm with
          | FStar_Parser_AST.Abs (uu____49812,e) -> e
          | uu____49818 ->
              FStar_Parser_AST.mk_term
                (FStar_Parser_AST.App
                   (t,
                     (FStar_Parser_AST.unit_const t.FStar_Parser_AST.range),
                     FStar_Parser_AST.Nothing)) t.FStar_Parser_AST.range
                FStar_Parser_AST.Expr
           in
        let uu____49819 = str "#["  in
        let uu____49821 =
          let uu____49822 = p_term false false t1  in
          let uu____49825 =
            let uu____49826 = str "]"  in
            FStar_Pprint.op_Hat_Hat uu____49826 break1  in
          FStar_Pprint.op_Hat_Hat uu____49822 uu____49825  in
        FStar_Pprint.op_Hat_Hat uu____49819 uu____49821

and (p_disjunctivePattern :
  FStar_Parser_AST.pattern -> FStar_Pprint.document) =
  fun p  ->
    match p.FStar_Parser_AST.pat with
    | FStar_Parser_AST.PatOr pats ->
        let uu____49832 =
          let uu____49833 =
            let uu____49834 =
              FStar_Pprint.op_Hat_Hat FStar_Pprint.bar FStar_Pprint.space  in
            FStar_Pprint.op_Hat_Hat break1 uu____49834  in
          FStar_Pprint.separate_map uu____49833 p_tuplePattern pats  in
        FStar_Pprint.group uu____49832
    | uu____49835 -> p_tuplePattern p

and (p_tuplePattern : FStar_Parser_AST.pattern -> FStar_Pprint.document) =
  fun p  ->
    match p.FStar_Parser_AST.pat with
    | FStar_Parser_AST.PatTuple (pats,false ) ->
        let uu____49844 =
          let uu____49845 = FStar_Pprint.op_Hat_Hat FStar_Pprint.comma break1
             in
          FStar_Pprint.separate_map uu____49845 p_constructorPattern pats  in
        FStar_Pprint.group uu____49844
    | uu____49846 -> p_constructorPattern p

and (p_constructorPattern :
  FStar_Parser_AST.pattern -> FStar_Pprint.document) =
  fun p  ->
    match p.FStar_Parser_AST.pat with
    | FStar_Parser_AST.PatApp
        ({ FStar_Parser_AST.pat = FStar_Parser_AST.PatName maybe_cons_lid;
           FStar_Parser_AST.prange = uu____49849;_},hd1::tl1::[])
        when
        FStar_Ident.lid_equals maybe_cons_lid FStar_Parser_Const.cons_lid ->
        let uu____49854 =
          FStar_Pprint.op_Hat_Hat FStar_Pprint.colon FStar_Pprint.colon  in
        let uu____49855 = p_constructorPattern hd1  in
        let uu____49856 = p_constructorPattern tl1  in
        infix0 uu____49854 uu____49855 uu____49856
    | FStar_Parser_AST.PatApp
        ({ FStar_Parser_AST.pat = FStar_Parser_AST.PatName uid;
           FStar_Parser_AST.prange = uu____49858;_},pats)
        ->
        let uu____49864 = p_quident uid  in
        let uu____49865 =
          FStar_Pprint.separate_map break1 p_atomicPattern pats  in
        prefix2 uu____49864 uu____49865
    | uu____49866 -> p_atomicPattern p

and (p_atomicPattern : FStar_Parser_AST.pattern -> FStar_Pprint.document) =
  fun p  ->
    match p.FStar_Parser_AST.pat with
    | FStar_Parser_AST.PatAscribed (pat,(t,FStar_Pervasives_Native.None )) ->
        (match ((pat.FStar_Parser_AST.pat), (t.FStar_Parser_AST.tm)) with
         | (FStar_Parser_AST.PatVar (lid,aqual),FStar_Parser_AST.Refine
            ({ FStar_Parser_AST.b = FStar_Parser_AST.Annotated (lid',t1);
               FStar_Parser_AST.brange = uu____49882;
               FStar_Parser_AST.blevel = uu____49883;
               FStar_Parser_AST.aqual = uu____49884;_},phi))
             when lid.FStar_Ident.idText = lid'.FStar_Ident.idText ->
             let uu____49893 =
               let uu____49894 = p_ident lid  in
               p_refinement aqual uu____49894 t1 phi  in
             soft_parens_with_nesting uu____49893
         | (FStar_Parser_AST.PatWild aqual,FStar_Parser_AST.Refine
            ({ FStar_Parser_AST.b = FStar_Parser_AST.NoName t1;
               FStar_Parser_AST.brange = uu____49897;
               FStar_Parser_AST.blevel = uu____49898;
               FStar_Parser_AST.aqual = uu____49899;_},phi))
             ->
             let uu____49905 =
               p_refinement aqual FStar_Pprint.underscore t1 phi  in
             soft_parens_with_nesting uu____49905
         | uu____49906 ->
             let uu____49911 =
               let uu____49912 = p_tuplePattern pat  in
               let uu____49913 =
                 let uu____49914 = p_tmEqNoRefinement t  in
                 FStar_Pprint.op_Hat_Slash_Hat FStar_Pprint.colon uu____49914
                  in
               FStar_Pprint.op_Hat_Hat uu____49912 uu____49913  in
             soft_parens_with_nesting uu____49911)
    | FStar_Parser_AST.PatList pats ->
        let uu____49918 =
          separate_break_map FStar_Pprint.semi p_tuplePattern pats  in
        FStar_Pprint.surround (Prims.parse_int "2") (Prims.parse_int "0")
          FStar_Pprint.lbracket uu____49918 FStar_Pprint.rbracket
    | FStar_Parser_AST.PatRecord pats ->
        let p_recordFieldPat uu____49937 =
          match uu____49937 with
          | (lid,pat) ->
              let uu____49944 = p_qlident lid  in
              let uu____49945 = p_tuplePattern pat  in
              infix2 FStar_Pprint.equals uu____49944 uu____49945
           in
        let uu____49946 =
          separate_break_map FStar_Pprint.semi p_recordFieldPat pats  in
        soft_braces_with_nesting uu____49946
    | FStar_Parser_AST.PatTuple (pats,true ) ->
        let uu____49958 =
          FStar_Pprint.op_Hat_Hat FStar_Pprint.lparen FStar_Pprint.bar  in
        let uu____49959 =
          separate_break_map FStar_Pprint.comma p_constructorPattern pats  in
        let uu____49960 =
          FStar_Pprint.op_Hat_Hat FStar_Pprint.bar FStar_Pprint.rparen  in
        FStar_Pprint.surround (Prims.parse_int "2") (Prims.parse_int "1")
          uu____49958 uu____49959 uu____49960
    | FStar_Parser_AST.PatTvar (tv,arg_qualifier_opt) -> p_tvar tv
    | FStar_Parser_AST.PatOp op ->
        let uu____49971 =
          let uu____49972 =
            let uu____49973 =
              let uu____49974 = FStar_Ident.text_of_id op  in str uu____49974
               in
            let uu____49976 =
              FStar_Pprint.op_Hat_Hat FStar_Pprint.space FStar_Pprint.rparen
               in
            FStar_Pprint.op_Hat_Hat uu____49973 uu____49976  in
          FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____49972  in
        FStar_Pprint.op_Hat_Hat FStar_Pprint.lparen uu____49971
    | FStar_Parser_AST.PatWild aqual ->
        let uu____49980 = FStar_Pprint.optional p_aqual aqual  in
        FStar_Pprint.op_Hat_Hat uu____49980 FStar_Pprint.underscore
    | FStar_Parser_AST.PatConst c -> p_constant c
    | FStar_Parser_AST.PatVar (lid,aqual) ->
        let uu____49988 = FStar_Pprint.optional p_aqual aqual  in
        let uu____49989 = p_lident lid  in
        FStar_Pprint.op_Hat_Hat uu____49988 uu____49989
    | FStar_Parser_AST.PatName uid -> p_quident uid
    | FStar_Parser_AST.PatOr uu____49991 -> failwith "Inner or pattern !"
    | FStar_Parser_AST.PatApp
        ({ FStar_Parser_AST.pat = FStar_Parser_AST.PatName uu____49995;
           FStar_Parser_AST.prange = uu____49996;_},uu____49997)
        ->
        let uu____50002 = p_tuplePattern p  in
        soft_parens_with_nesting uu____50002
    | FStar_Parser_AST.PatTuple (uu____50003,false ) ->
        let uu____50010 = p_tuplePattern p  in
        soft_parens_with_nesting uu____50010
    | uu____50011 ->
        let uu____50012 =
          let uu____50014 = FStar_Parser_AST.pat_to_string p  in
          FStar_Util.format1 "Invalid pattern %s" uu____50014  in
        failwith uu____50012

and (is_typ_tuple : FStar_Parser_AST.term -> Prims.bool) =
  fun e  ->
    match e.FStar_Parser_AST.tm with
    | FStar_Parser_AST.Op
        ({ FStar_Ident.idText = "*"; FStar_Ident.idRange = uu____50019;_},uu____50020)
        -> true
    | uu____50027 -> false

and (is_meta_qualifier :
  FStar_Parser_AST.arg_qualifier FStar_Pervasives_Native.option -> Prims.bool)
  =
  fun aq  ->
    match aq with
    | FStar_Pervasives_Native.Some (FStar_Parser_AST.Meta uu____50033) ->
        true
    | uu____50035 -> false

and (p_binder :
  Prims.bool -> FStar_Parser_AST.binder -> FStar_Pprint.document) =
  fun is_atomic  ->
    fun b  ->
      let uu____50042 = p_binder' is_atomic b  in
      match uu____50042 with
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
          let uu____50081 =
            let uu____50082 =
              FStar_Pprint.optional p_aqual b.FStar_Parser_AST.aqual  in
            let uu____50083 = p_lident lid  in
            FStar_Pprint.op_Hat_Hat uu____50082 uu____50083  in
          (uu____50081, FStar_Pervasives_Native.None, cat_with_colon)
      | FStar_Parser_AST.TVariable lid ->
          let uu____50089 = p_lident lid  in
          (uu____50089, FStar_Pervasives_Native.None, cat_with_colon)
      | FStar_Parser_AST.Annotated (lid,t) ->
          let uu____50096 =
            match t.FStar_Parser_AST.tm with
            | FStar_Parser_AST.Refine
                ({ FStar_Parser_AST.b = FStar_Parser_AST.Annotated (lid',t1);
                   FStar_Parser_AST.brange = uu____50107;
                   FStar_Parser_AST.blevel = uu____50108;
                   FStar_Parser_AST.aqual = uu____50109;_},phi)
                when lid.FStar_Ident.idText = lid'.FStar_Ident.idText ->
                let uu____50114 = p_lident lid  in
                p_refinement' b.FStar_Parser_AST.aqual uu____50114 t1 phi
            | uu____50115 ->
                let t' =
                  let uu____50117 = is_typ_tuple t  in
                  if uu____50117
                  then
                    let uu____50120 = p_tmFormula t  in
                    soft_parens_with_nesting uu____50120
                  else p_tmFormula t  in
                let uu____50123 =
                  let uu____50124 =
                    FStar_Pprint.optional p_aqual b.FStar_Parser_AST.aqual
                     in
                  let uu____50125 = p_lident lid  in
                  FStar_Pprint.op_Hat_Hat uu____50124 uu____50125  in
                (uu____50123, t')
             in
          (match uu____50096 with
           | (b',t') ->
               let catf =
                 let uu____50143 =
                   is_atomic || (is_meta_qualifier b.FStar_Parser_AST.aqual)
                    in
                 if uu____50143
                 then
                   fun x  ->
                     fun y  ->
                       let uu____50150 =
                         let uu____50151 =
                           let uu____50152 = cat_with_colon x y  in
                           FStar_Pprint.op_Hat_Hat uu____50152
                             FStar_Pprint.rparen
                            in
                         FStar_Pprint.op_Hat_Hat FStar_Pprint.lparen
                           uu____50151
                          in
                       FStar_Pprint.group uu____50150
                 else
                   (fun x  ->
                      fun y  ->
                        let uu____50157 = cat_with_colon x y  in
                        FStar_Pprint.group uu____50157)
                  in
               (b', (FStar_Pervasives_Native.Some t'), catf))
      | FStar_Parser_AST.TAnnotated uu____50166 ->
          failwith "Is this still used ?"
      | FStar_Parser_AST.NoName t ->
          (match t.FStar_Parser_AST.tm with
           | FStar_Parser_AST.Refine
               ({ FStar_Parser_AST.b = FStar_Parser_AST.NoName t1;
                  FStar_Parser_AST.brange = uu____50194;
                  FStar_Parser_AST.blevel = uu____50195;
                  FStar_Parser_AST.aqual = uu____50196;_},phi)
               ->
               let uu____50200 =
                 p_refinement' b.FStar_Parser_AST.aqual
                   FStar_Pprint.underscore t1 phi
                  in
               (match uu____50200 with
                | (b',t') ->
                    (b', (FStar_Pervasives_Native.Some t'), cat_with_colon))
           | uu____50221 ->
               if is_atomic
               then
                 let uu____50233 = p_atomicTerm t  in
                 (uu____50233, FStar_Pervasives_Native.None, cat_with_colon)
               else
                 (let uu____50240 = p_appTerm t  in
                  (uu____50240, FStar_Pervasives_Native.None, cat_with_colon)))

and (p_refinement :
  FStar_Parser_AST.arg_qualifier FStar_Pervasives_Native.option ->
    FStar_Pprint.document ->
      FStar_Parser_AST.term -> FStar_Parser_AST.term -> FStar_Pprint.document)
  =
  fun aqual_opt  ->
    fun binder  ->
      fun t  ->
        fun phi  ->
          let uu____50251 = p_refinement' aqual_opt binder t phi  in
          match uu____50251 with | (b,typ) -> cat_with_colon b typ

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
            | FStar_Parser_AST.Construct uu____50267 -> false
            | FStar_Parser_AST.App uu____50279 -> false
            | FStar_Parser_AST.Op uu____50287 -> false
            | uu____50295 -> true  in
          let uu____50297 = p_noSeqTerm false false phi  in
          match uu____50297 with
          | (comm,phi1) ->
              let phi2 =
                if comm = FStar_Pprint.empty
                then phi1
                else
                  (let uu____50314 =
                     FStar_Pprint.op_Hat_Hat FStar_Pprint.hardline phi1  in
                   FStar_Pprint.op_Hat_Hat comm uu____50314)
                 in
              let jump_break =
                if is_t_atomic
                then (Prims.parse_int "0")
                else (Prims.parse_int "1")  in
              let uu____50323 =
                let uu____50324 = FStar_Pprint.optional p_aqual aqual_opt  in
                FStar_Pprint.op_Hat_Hat uu____50324 binder  in
              let uu____50325 =
                let uu____50326 = p_appTerm t  in
                let uu____50327 =
                  let uu____50328 =
                    let uu____50329 =
                      let uu____50330 = soft_braces_with_nesting_tight phi2
                         in
                      let uu____50331 = soft_braces_with_nesting phi2  in
                      FStar_Pprint.ifflat uu____50330 uu____50331  in
                    FStar_Pprint.group uu____50329  in
                  FStar_Pprint.jump (Prims.parse_int "2") jump_break
                    uu____50328
                   in
                FStar_Pprint.op_Hat_Hat uu____50326 uu____50327  in
              (uu____50323, uu____50325)

and (p_binders_list :
  Prims.bool ->
    FStar_Parser_AST.binder Prims.list -> FStar_Pprint.document Prims.list)
  = fun is_atomic  -> fun bs  -> FStar_List.map (p_binder is_atomic) bs

and (p_binders :
  Prims.bool -> FStar_Parser_AST.binder Prims.list -> FStar_Pprint.document)
  =
  fun is_atomic  ->
    fun bs  ->
      let uu____50345 = p_binders_list is_atomic bs  in
      separate_or_flow break1 uu____50345

and (text_of_id_or_underscore : FStar_Ident.ident -> FStar_Pprint.document) =
  fun lid  ->
    let uu____50349 =
      (FStar_Util.starts_with lid.FStar_Ident.idText
         FStar_Ident.reserved_prefix)
        &&
        (let uu____50352 = FStar_Options.print_real_names ()  in
         Prims.op_Negation uu____50352)
       in
    if uu____50349
    then FStar_Pprint.underscore
    else (let uu____50357 = FStar_Ident.text_of_id lid  in str uu____50357)

and (text_of_lid_or_underscore : FStar_Ident.lident -> FStar_Pprint.document)
  =
  fun lid  ->
    let uu____50360 =
      (FStar_Util.starts_with (lid.FStar_Ident.ident).FStar_Ident.idText
         FStar_Ident.reserved_prefix)
        &&
        (let uu____50363 = FStar_Options.print_real_names ()  in
         Prims.op_Negation uu____50363)
       in
    if uu____50360
    then FStar_Pprint.underscore
    else (let uu____50368 = FStar_Ident.text_of_lid lid  in str uu____50368)

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
          let uu____50389 = FStar_Pprint.op_Hat_Hat doc1 sep  in
          FStar_Pprint.group uu____50389
        else
          (let uu____50392 =
             let uu____50393 =
               let uu____50394 =
                 let uu____50395 =
                   let uu____50396 = FStar_Pprint.op_Hat_Hat break1 comm  in
                   FStar_Pprint.op_Hat_Hat sep uu____50396  in
                 FStar_Pprint.op_Hat_Hat doc1 uu____50395  in
               FStar_Pprint.group uu____50394  in
             let uu____50397 =
               let uu____50398 =
                 let uu____50399 = FStar_Pprint.op_Hat_Hat doc1 sep  in
                 FStar_Pprint.op_Hat_Hat FStar_Pprint.hardline uu____50399
                  in
               FStar_Pprint.op_Hat_Hat comm uu____50398  in
             FStar_Pprint.ifflat uu____50393 uu____50397  in
           FStar_All.pipe_left FStar_Pprint.group uu____50392)

and (p_term :
  Prims.bool -> Prims.bool -> FStar_Parser_AST.term -> FStar_Pprint.document)
  =
  fun ps  ->
    fun pb  ->
      fun e  ->
        match e.FStar_Parser_AST.tm with
        | FStar_Parser_AST.Seq (e1,e2) ->
            let uu____50407 = p_noSeqTerm true false e1  in
            (match uu____50407 with
             | (comm,t1) ->
                 let uu____50416 =
                   inline_comment_or_above comm t1 FStar_Pprint.semi  in
                 let uu____50417 =
                   let uu____50418 = p_term ps pb e2  in
                   FStar_Pprint.op_Hat_Hat FStar_Pprint.hardline uu____50418
                    in
                 FStar_Pprint.op_Hat_Hat uu____50416 uu____50417)
        | FStar_Parser_AST.Bind (x,e1,e2) ->
            let uu____50422 =
              let uu____50423 =
                let uu____50424 =
                  let uu____50425 = p_lident x  in
                  let uu____50426 =
                    FStar_Pprint.op_Hat_Hat FStar_Pprint.space
                      FStar_Pprint.long_left_arrow
                     in
                  FStar_Pprint.op_Hat_Hat uu____50425 uu____50426  in
                let uu____50427 =
                  let uu____50428 = p_noSeqTermAndComment true false e1  in
                  let uu____50431 =
                    FStar_Pprint.op_Hat_Hat FStar_Pprint.space
                      FStar_Pprint.semi
                     in
                  FStar_Pprint.op_Hat_Hat uu____50428 uu____50431  in
                op_Hat_Slash_Plus_Hat uu____50424 uu____50427  in
              FStar_Pprint.group uu____50423  in
            let uu____50432 = p_term ps pb e2  in
            FStar_Pprint.op_Hat_Slash_Hat uu____50422 uu____50432
        | uu____50433 ->
            let uu____50434 = p_noSeqTermAndComment ps pb e  in
            FStar_Pprint.group uu____50434

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
            let uu____50446 = p_noSeqTerm true false e1  in
            (match uu____50446 with
             | (comm,t1) ->
                 let uu____50459 =
                   let uu____50460 =
                     let uu____50461 =
                       FStar_Pprint.op_Hat_Hat t1 FStar_Pprint.semi  in
                     FStar_Pprint.group uu____50461  in
                   let uu____50462 =
                     let uu____50463 = p_term ps pb e2  in
                     FStar_Pprint.op_Hat_Hat FStar_Pprint.hardline
                       uu____50463
                      in
                   FStar_Pprint.op_Hat_Hat uu____50460 uu____50462  in
                 (comm, uu____50459))
        | FStar_Parser_AST.Bind (x,e1,e2) ->
            let uu____50467 =
              let uu____50468 =
                let uu____50469 =
                  let uu____50470 =
                    let uu____50471 = p_lident x  in
                    let uu____50472 =
                      FStar_Pprint.op_Hat_Hat FStar_Pprint.space
                        FStar_Pprint.long_left_arrow
                       in
                    FStar_Pprint.op_Hat_Hat uu____50471 uu____50472  in
                  let uu____50473 =
                    let uu____50474 = p_noSeqTermAndComment true false e1  in
                    let uu____50477 =
                      FStar_Pprint.op_Hat_Hat FStar_Pprint.space
                        FStar_Pprint.semi
                       in
                    FStar_Pprint.op_Hat_Hat uu____50474 uu____50477  in
                  op_Hat_Slash_Plus_Hat uu____50470 uu____50473  in
                FStar_Pprint.group uu____50469  in
              let uu____50478 = p_term ps pb e2  in
              FStar_Pprint.op_Hat_Slash_Hat uu____50468 uu____50478  in
            (FStar_Pprint.empty, uu____50467)
        | uu____50479 -> p_noSeqTerm ps pb e

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
            let uu____50499 =
              let uu____50500 = p_tmIff e1  in
              let uu____50501 =
                let uu____50502 =
                  let uu____50503 = p_typ ps pb t  in
                  FStar_Pprint.op_Hat_Slash_Hat FStar_Pprint.colon
                    uu____50503
                   in
                FStar_Pprint.op_Hat_Hat FStar_Pprint.langle uu____50502  in
              FStar_Pprint.op_Hat_Slash_Hat uu____50500 uu____50501  in
            FStar_Pprint.group uu____50499
        | FStar_Parser_AST.Ascribed (e1,t,FStar_Pervasives_Native.Some tac)
            ->
            let uu____50509 =
              let uu____50510 = p_tmIff e1  in
              let uu____50511 =
                let uu____50512 =
                  let uu____50513 =
                    let uu____50514 = p_typ false false t  in
                    let uu____50517 =
                      let uu____50518 = str "by"  in
                      let uu____50520 = p_typ ps pb tac  in
                      FStar_Pprint.op_Hat_Slash_Hat uu____50518 uu____50520
                       in
                    FStar_Pprint.op_Hat_Slash_Hat uu____50514 uu____50517  in
                  FStar_Pprint.op_Hat_Slash_Hat FStar_Pprint.colon
                    uu____50513
                   in
                FStar_Pprint.op_Hat_Hat FStar_Pprint.langle uu____50512  in
              FStar_Pprint.op_Hat_Slash_Hat uu____50510 uu____50511  in
            FStar_Pprint.group uu____50509
        | FStar_Parser_AST.Op
            ({ FStar_Ident.idText = ".()<-";
               FStar_Ident.idRange = uu____50521;_},e1::e2::e3::[])
            ->
            let uu____50528 =
              let uu____50529 =
                let uu____50530 =
                  let uu____50531 = p_atomicTermNotQUident e1  in
                  let uu____50532 =
                    let uu____50533 =
                      let uu____50534 =
                        let uu____50535 = p_term false false e2  in
                        soft_parens_with_nesting uu____50535  in
                      let uu____50538 =
                        FStar_Pprint.op_Hat_Hat FStar_Pprint.space
                          FStar_Pprint.larrow
                         in
                      FStar_Pprint.op_Hat_Hat uu____50534 uu____50538  in
                    FStar_Pprint.op_Hat_Hat FStar_Pprint.dot uu____50533  in
                  FStar_Pprint.op_Hat_Hat uu____50531 uu____50532  in
                FStar_Pprint.group uu____50530  in
              let uu____50539 =
                let uu____50540 = p_noSeqTermAndComment ps pb e3  in
                jump2 uu____50540  in
              FStar_Pprint.op_Hat_Hat uu____50529 uu____50539  in
            FStar_Pprint.group uu____50528
        | FStar_Parser_AST.Op
            ({ FStar_Ident.idText = ".[]<-";
               FStar_Ident.idRange = uu____50541;_},e1::e2::e3::[])
            ->
            let uu____50548 =
              let uu____50549 =
                let uu____50550 =
                  let uu____50551 = p_atomicTermNotQUident e1  in
                  let uu____50552 =
                    let uu____50553 =
                      let uu____50554 =
                        let uu____50555 = p_term false false e2  in
                        soft_brackets_with_nesting uu____50555  in
                      let uu____50558 =
                        FStar_Pprint.op_Hat_Hat FStar_Pprint.space
                          FStar_Pprint.larrow
                         in
                      FStar_Pprint.op_Hat_Hat uu____50554 uu____50558  in
                    FStar_Pprint.op_Hat_Hat FStar_Pprint.dot uu____50553  in
                  FStar_Pprint.op_Hat_Hat uu____50551 uu____50552  in
                FStar_Pprint.group uu____50550  in
              let uu____50559 =
                let uu____50560 = p_noSeqTermAndComment ps pb e3  in
                jump2 uu____50560  in
              FStar_Pprint.op_Hat_Hat uu____50549 uu____50559  in
            FStar_Pprint.group uu____50548
        | FStar_Parser_AST.Requires (e1,wtf) ->
            let uu____50570 =
              let uu____50571 = str "requires"  in
              let uu____50573 = p_typ ps pb e1  in
              FStar_Pprint.op_Hat_Slash_Hat uu____50571 uu____50573  in
            FStar_Pprint.group uu____50570
        | FStar_Parser_AST.Ensures (e1,wtf) ->
            let uu____50583 =
              let uu____50584 = str "ensures"  in
              let uu____50586 = p_typ ps pb e1  in
              FStar_Pprint.op_Hat_Slash_Hat uu____50584 uu____50586  in
            FStar_Pprint.group uu____50583
        | FStar_Parser_AST.Attributes es ->
            let uu____50590 =
              let uu____50591 = str "attributes"  in
              let uu____50593 =
                FStar_Pprint.separate_map break1 p_atomicTerm es  in
              FStar_Pprint.op_Hat_Slash_Hat uu____50591 uu____50593  in
            FStar_Pprint.group uu____50590
        | FStar_Parser_AST.If (e1,e2,e3) ->
            if is_unit e3
            then
              let uu____50598 =
                let uu____50599 =
                  let uu____50600 = str "if"  in
                  let uu____50602 = p_noSeqTermAndComment false false e1  in
                  op_Hat_Slash_Plus_Hat uu____50600 uu____50602  in
                let uu____50605 =
                  let uu____50606 = str "then"  in
                  let uu____50608 = p_noSeqTermAndComment ps pb e2  in
                  op_Hat_Slash_Plus_Hat uu____50606 uu____50608  in
                FStar_Pprint.op_Hat_Slash_Hat uu____50599 uu____50605  in
              FStar_Pprint.group uu____50598
            else
              (let e2_doc =
                 match e2.FStar_Parser_AST.tm with
                 | FStar_Parser_AST.If (uu____50612,uu____50613,e31) when
                     is_unit e31 ->
                     let uu____50615 = p_noSeqTermAndComment false false e2
                        in
                     soft_parens_with_nesting uu____50615
                 | uu____50618 -> p_noSeqTermAndComment false false e2  in
               let uu____50621 =
                 let uu____50622 =
                   let uu____50623 = str "if"  in
                   let uu____50625 = p_noSeqTermAndComment false false e1  in
                   op_Hat_Slash_Plus_Hat uu____50623 uu____50625  in
                 let uu____50628 =
                   let uu____50629 =
                     let uu____50630 = str "then"  in
                     op_Hat_Slash_Plus_Hat uu____50630 e2_doc  in
                   let uu____50632 =
                     let uu____50633 = str "else"  in
                     let uu____50635 = p_noSeqTermAndComment ps pb e3  in
                     op_Hat_Slash_Plus_Hat uu____50633 uu____50635  in
                   FStar_Pprint.op_Hat_Slash_Hat uu____50629 uu____50632  in
                 FStar_Pprint.op_Hat_Slash_Hat uu____50622 uu____50628  in
               FStar_Pprint.group uu____50621)
        | FStar_Parser_AST.TryWith (e1,branches) ->
            let uu____50658 =
              let uu____50659 =
                let uu____50660 =
                  let uu____50661 = str "try"  in
                  let uu____50663 = p_noSeqTermAndComment false false e1  in
                  prefix2 uu____50661 uu____50663  in
                let uu____50666 =
                  let uu____50667 = str "with"  in
                  let uu____50669 =
                    separate_map_last FStar_Pprint.hardline p_patternBranch
                      branches
                     in
                  FStar_Pprint.op_Hat_Slash_Hat uu____50667 uu____50669  in
                FStar_Pprint.op_Hat_Slash_Hat uu____50660 uu____50666  in
              FStar_Pprint.group uu____50659  in
            let uu____50678 = paren_if (ps || pb)  in uu____50678 uu____50658
        | FStar_Parser_AST.Match (e1,branches) ->
            let uu____50705 =
              let uu____50706 =
                let uu____50707 =
                  let uu____50708 = str "match"  in
                  let uu____50710 = p_noSeqTermAndComment false false e1  in
                  let uu____50713 = str "with"  in
                  FStar_Pprint.surround (Prims.parse_int "2")
                    (Prims.parse_int "1") uu____50708 uu____50710 uu____50713
                   in
                let uu____50717 =
                  separate_map_last FStar_Pprint.hardline p_patternBranch
                    branches
                   in
                FStar_Pprint.op_Hat_Slash_Hat uu____50707 uu____50717  in
              FStar_Pprint.group uu____50706  in
            let uu____50726 = paren_if (ps || pb)  in uu____50726 uu____50705
        | FStar_Parser_AST.LetOpen (uid,e1) ->
            let uu____50733 =
              let uu____50734 =
                let uu____50735 =
                  let uu____50736 = str "let open"  in
                  let uu____50738 = p_quident uid  in
                  let uu____50739 = str "in"  in
                  FStar_Pprint.surround (Prims.parse_int "2")
                    (Prims.parse_int "1") uu____50736 uu____50738 uu____50739
                   in
                let uu____50743 = p_term false pb e1  in
                FStar_Pprint.op_Hat_Slash_Hat uu____50735 uu____50743  in
              FStar_Pprint.group uu____50734  in
            let uu____50745 = paren_if ps  in uu____50745 uu____50733
        | FStar_Parser_AST.Let (q,lbs,e1) ->
            let p_lb q1 uu____50810 is_last =
              match uu____50810 with
              | (a,(pat,e2)) ->
                  let attrs = p_attrs_opt a  in
                  let doc_let_or_and =
                    match q1 with
                    | FStar_Pervasives_Native.Some (FStar_Parser_AST.Rec ) ->
                        let uu____50844 =
                          let uu____50845 = str "let"  in
                          let uu____50847 = str "rec"  in
                          FStar_Pprint.op_Hat_Slash_Hat uu____50845
                            uu____50847
                           in
                        FStar_Pprint.group uu____50844
                    | FStar_Pervasives_Native.Some
                        (FStar_Parser_AST.NoLetQualifier ) -> str "let"
                    | uu____50850 -> str "and"  in
                  let doc_pat = p_letlhs doc_let_or_and (pat, e2) true  in
                  let uu____50856 = p_term_sep false false e2  in
                  (match uu____50856 with
                   | (comm,doc_expr) ->
                       let doc_expr1 =
                         inline_comment_or_above comm doc_expr
                           FStar_Pprint.empty
                          in
                       let uu____50866 =
                         if is_last
                         then
                           let uu____50868 =
                             FStar_Pprint.flow break1
                               [doc_pat; FStar_Pprint.equals]
                              in
                           let uu____50869 = str "in"  in
                           FStar_Pprint.surround (Prims.parse_int "2")
                             (Prims.parse_int "1") uu____50868 doc_expr1
                             uu____50869
                         else
                           (let uu____50875 =
                              FStar_Pprint.flow break1
                                [doc_pat; FStar_Pprint.equals; doc_expr1]
                               in
                            FStar_Pprint.hang (Prims.parse_int "2")
                              uu____50875)
                          in
                       FStar_Pprint.op_Hat_Hat attrs uu____50866)
               in
            let l = FStar_List.length lbs  in
            let lbs_docs =
              FStar_List.mapi
                (fun i  ->
                   fun lb  ->
                     if i = (Prims.parse_int "0")
                     then
                       let uu____50926 =
                         p_lb (FStar_Pervasives_Native.Some q) lb
                           (i = (l - (Prims.parse_int "1")))
                          in
                       FStar_Pprint.group uu____50926
                     else
                       (let uu____50937 =
                          p_lb FStar_Pervasives_Native.None lb
                            (i = (l - (Prims.parse_int "1")))
                           in
                        FStar_Pprint.group uu____50937)) lbs
               in
            let lbs_doc =
              let uu____50947 = FStar_Pprint.separate break1 lbs_docs  in
              FStar_Pprint.group uu____50947  in
            let uu____50948 =
              let uu____50949 =
                let uu____50950 =
                  let uu____50951 = p_term false pb e1  in
                  FStar_Pprint.op_Hat_Hat FStar_Pprint.hardline uu____50951
                   in
                FStar_Pprint.op_Hat_Hat lbs_doc uu____50950  in
              FStar_Pprint.group uu____50949  in
            let uu____50953 = paren_if ps  in uu____50953 uu____50948
        | FStar_Parser_AST.Abs
            ({ FStar_Parser_AST.pat = FStar_Parser_AST.PatVar (x,typ_opt);
               FStar_Parser_AST.prange = uu____50960;_}::[],{
                                                              FStar_Parser_AST.tm
                                                                =
                                                                FStar_Parser_AST.Match
                                                                (maybe_x,branches);
                                                              FStar_Parser_AST.range
                                                                = uu____50963;
                                                              FStar_Parser_AST.level
                                                                = uu____50964;_})
            when matches_var maybe_x x ->
            let uu____50991 =
              let uu____50992 =
                let uu____50993 = str "function"  in
                let uu____50995 =
                  separate_map_last FStar_Pprint.hardline p_patternBranch
                    branches
                   in
                FStar_Pprint.op_Hat_Slash_Hat uu____50993 uu____50995  in
              FStar_Pprint.group uu____50992  in
            let uu____51004 = paren_if (ps || pb)  in uu____51004 uu____50991
        | FStar_Parser_AST.Quote (e1,FStar_Parser_AST.Dynamic ) ->
            let uu____51010 =
              let uu____51011 = str "quote"  in
              let uu____51013 = p_noSeqTermAndComment ps pb e1  in
              FStar_Pprint.op_Hat_Slash_Hat uu____51011 uu____51013  in
            FStar_Pprint.group uu____51010
        | FStar_Parser_AST.Quote (e1,FStar_Parser_AST.Static ) ->
            let uu____51015 =
              let uu____51016 = str "`"  in
              let uu____51018 = p_noSeqTermAndComment ps pb e1  in
              FStar_Pprint.op_Hat_Hat uu____51016 uu____51018  in
            FStar_Pprint.group uu____51015
        | FStar_Parser_AST.VQuote e1 ->
            let uu____51020 =
              let uu____51021 = str "`%"  in
              let uu____51023 = p_noSeqTermAndComment ps pb e1  in
              FStar_Pprint.op_Hat_Hat uu____51021 uu____51023  in
            FStar_Pprint.group uu____51020
        | FStar_Parser_AST.Antiquote
            {
              FStar_Parser_AST.tm = FStar_Parser_AST.Quote
                (e1,FStar_Parser_AST.Dynamic );
              FStar_Parser_AST.range = uu____51025;
              FStar_Parser_AST.level = uu____51026;_}
            ->
            let uu____51027 =
              let uu____51028 = str "`@"  in
              let uu____51030 = p_noSeqTermAndComment ps pb e1  in
              FStar_Pprint.op_Hat_Hat uu____51028 uu____51030  in
            FStar_Pprint.group uu____51027
        | FStar_Parser_AST.Antiquote e1 ->
            let uu____51032 =
              let uu____51033 = str "`#"  in
              let uu____51035 = p_noSeqTermAndComment ps pb e1  in
              FStar_Pprint.op_Hat_Hat uu____51033 uu____51035  in
            FStar_Pprint.group uu____51032
        | FStar_Parser_AST.CalcProof (rel,init1,steps) ->
            let head1 =
              let uu____51044 = str "calc"  in
              let uu____51046 =
                let uu____51047 =
                  let uu____51048 = p_noSeqTermAndComment false false rel  in
                  let uu____51051 =
                    FStar_Pprint.op_Hat_Hat FStar_Pprint.space
                      FStar_Pprint.lbrace
                     in
                  FStar_Pprint.op_Hat_Hat uu____51048 uu____51051  in
                FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____51047  in
              FStar_Pprint.op_Hat_Hat uu____51044 uu____51046  in
            let bot = FStar_Pprint.rbrace  in
            let uu____51053 =
              FStar_Pprint.op_Hat_Hat FStar_Pprint.hardline bot  in
            let uu____51054 =
              let uu____51055 =
                let uu____51056 =
                  let uu____51057 = p_noSeqTermAndComment false false init1
                     in
                  let uu____51060 =
                    let uu____51061 = str ";"  in
                    let uu____51063 =
                      let uu____51064 =
                        separate_map_last FStar_Pprint.hardline p_calcStep
                          steps
                         in
                      FStar_Pprint.op_Hat_Hat FStar_Pprint.hardline
                        uu____51064
                       in
                    FStar_Pprint.op_Hat_Hat uu____51061 uu____51063  in
                  FStar_Pprint.op_Hat_Hat uu____51057 uu____51060  in
                FStar_Pprint.op_Hat_Hat FStar_Pprint.hardline uu____51056  in
              FStar_All.pipe_left (FStar_Pprint.nest (Prims.parse_int "2"))
                uu____51055
               in
            FStar_Pprint.enclose head1 uu____51053 uu____51054
        | uu____51066 -> p_typ ps pb e

and (p_calcStep :
  Prims.bool -> FStar_Parser_AST.calc_step -> FStar_Pprint.document) =
  fun uu____51067  ->
    fun uu____51068  ->
      match uu____51068 with
      | FStar_Parser_AST.CalcStep (rel,just,next) ->
          let uu____51073 =
            let uu____51074 = p_noSeqTermAndComment false false rel  in
            let uu____51077 =
              let uu____51078 =
                let uu____51079 =
                  let uu____51080 =
                    let uu____51081 = p_noSeqTermAndComment false false just
                       in
                    let uu____51084 =
                      let uu____51085 =
                        let uu____51086 =
                          let uu____51087 =
                            let uu____51088 =
                              p_noSeqTermAndComment false false next  in
                            let uu____51091 = str ";"  in
                            FStar_Pprint.op_Hat_Hat uu____51088 uu____51091
                             in
                          FStar_Pprint.op_Hat_Hat FStar_Pprint.hardline
                            uu____51087
                           in
                        FStar_Pprint.op_Hat_Hat FStar_Pprint.rbrace
                          uu____51086
                         in
                      FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____51085
                       in
                    FStar_Pprint.op_Hat_Hat uu____51081 uu____51084  in
                  FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____51080  in
                FStar_Pprint.op_Hat_Hat FStar_Pprint.lbrace uu____51079  in
              FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____51078  in
            FStar_Pprint.op_Hat_Hat uu____51074 uu____51077  in
          FStar_Pprint.group uu____51073

and (p_attrs_opt :
  FStar_Parser_AST.term Prims.list FStar_Pervasives_Native.option ->
    FStar_Pprint.document)
  =
  fun uu___335_51093  ->
    match uu___335_51093 with
    | FStar_Pervasives_Native.None  -> FStar_Pprint.empty
    | FStar_Pervasives_Native.Some terms ->
        let uu____51105 =
          let uu____51106 = str "[@"  in
          let uu____51108 =
            let uu____51109 =
              FStar_Pprint.separate_map break1 p_atomicTerm terms  in
            let uu____51110 = str "]"  in
            FStar_Pprint.op_Hat_Slash_Hat uu____51109 uu____51110  in
          FStar_Pprint.op_Hat_Slash_Hat uu____51106 uu____51108  in
        FStar_Pprint.group uu____51105

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
                 let uu____51147 =
                   let uu____51148 =
                     let uu____51149 = p_quantifier e  in
                     FStar_Pprint.op_Hat_Hat uu____51149 FStar_Pprint.space
                      in
                   FStar_Pprint.soft_surround (Prims.parse_int "2")
                     (Prims.parse_int "0") uu____51148 binders_doc
                     FStar_Pprint.dot
                    in
                 prefix2 uu____51147 term_doc
             | pats ->
                 let uu____51157 =
                   let uu____51158 =
                     let uu____51159 =
                       let uu____51160 =
                         let uu____51161 = p_quantifier e  in
                         FStar_Pprint.op_Hat_Hat uu____51161
                           FStar_Pprint.space
                          in
                       FStar_Pprint.soft_surround (Prims.parse_int "2")
                         (Prims.parse_int "0") uu____51160 binders_doc
                         FStar_Pprint.dot
                        in
                     let uu____51164 = p_trigger trigger  in
                     prefix2 uu____51159 uu____51164  in
                   FStar_Pprint.group uu____51158  in
                 prefix2 uu____51157 term_doc)
        | FStar_Parser_AST.QExists (bs,trigger,e1) ->
            let binders_doc = p_binders true bs  in
            let term_doc = p_noSeqTermAndComment ps pb e1  in
            (match trigger with
             | [] ->
                 let uu____51185 =
                   let uu____51186 =
                     let uu____51187 = p_quantifier e  in
                     FStar_Pprint.op_Hat_Hat uu____51187 FStar_Pprint.space
                      in
                   FStar_Pprint.soft_surround (Prims.parse_int "2")
                     (Prims.parse_int "0") uu____51186 binders_doc
                     FStar_Pprint.dot
                    in
                 prefix2 uu____51185 term_doc
             | pats ->
                 let uu____51195 =
                   let uu____51196 =
                     let uu____51197 =
                       let uu____51198 =
                         let uu____51199 = p_quantifier e  in
                         FStar_Pprint.op_Hat_Hat uu____51199
                           FStar_Pprint.space
                          in
                       FStar_Pprint.soft_surround (Prims.parse_int "2")
                         (Prims.parse_int "0") uu____51198 binders_doc
                         FStar_Pprint.dot
                        in
                     let uu____51202 = p_trigger trigger  in
                     prefix2 uu____51197 uu____51202  in
                   FStar_Pprint.group uu____51196  in
                 prefix2 uu____51195 term_doc)
        | uu____51203 -> p_simpleTerm ps pb e

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
      let uu____51224 = all_binders_annot t  in
      if uu____51224
      then
        let uu____51227 =
          p_typ_top
            (Binders ((Prims.parse_int "4"), (Prims.parse_int "0"), true))
            false false t
           in
        FStar_Pprint.op_Hat_Hat s uu____51227
      else
        (let uu____51238 =
           let uu____51239 =
             let uu____51240 =
               p_typ_top
                 (Arrows ((Prims.parse_int "2"), (Prims.parse_int "2")))
                 false false t
                in
             FStar_Pprint.op_Hat_Hat s uu____51240  in
           FStar_Pprint.op_Hat_Hat FStar_Pprint.colon uu____51239  in
         FStar_Pprint.group uu____51238)

and (collapse_pats :
  (FStar_Pprint.document * FStar_Pprint.document) Prims.list ->
    FStar_Pprint.document Prims.list)
  =
  fun pats  ->
    let fold_fun bs x =
      let uu____51299 = x  in
      match uu____51299 with
      | (b1,t1) ->
          (match bs with
           | [] -> [([b1], t1)]
           | hd1::tl1 ->
               let uu____51364 = hd1  in
               (match uu____51364 with
                | (b2s,t2) ->
                    if t1 = t2
                    then ((FStar_List.append b2s [b1]), t1) :: tl1
                    else ([b1], t1) :: hd1 :: tl1))
       in
    let p_collapsed_binder cb =
      let uu____51436 = cb  in
      match uu____51436 with
      | (bs,typ) ->
          (match bs with
           | [] -> failwith "Impossible"
           | b::[] -> cat_with_colon b typ
           | hd1::tl1 ->
               let uu____51455 =
                 FStar_List.fold_left
                   (fun x  ->
                      fun y  ->
                        let uu____51461 =
                          FStar_Pprint.op_Hat_Hat FStar_Pprint.space y  in
                        FStar_Pprint.op_Hat_Hat x uu____51461) hd1 tl1
                  in
               cat_with_colon uu____51455 typ)
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
                 FStar_Parser_AST.brange = uu____51540;
                 FStar_Parser_AST.blevel = uu____51541;
                 FStar_Parser_AST.aqual = uu____51542;_},phi))
               when lid.FStar_Ident.idText = lid'.FStar_Ident.idText ->
               let uu____51551 =
                 let uu____51556 = p_ident lid  in
                 p_refinement' aqual uu____51556 t1 phi  in
               FStar_Pervasives_Native.Some uu____51551
           | (FStar_Parser_AST.PatVar (lid,aqual),uu____51563) ->
               let uu____51568 =
                 let uu____51573 =
                   let uu____51574 = FStar_Pprint.optional p_aqual aqual  in
                   let uu____51575 = p_ident lid  in
                   FStar_Pprint.op_Hat_Hat uu____51574 uu____51575  in
                 let uu____51576 = p_tmEqNoRefinement t  in
                 (uu____51573, uu____51576)  in
               FStar_Pervasives_Native.Some uu____51568
           | uu____51581 -> FStar_Pervasives_Native.None)
      | uu____51590 -> FStar_Pervasives_Native.None  in
    let all_unbound p =
      match p.FStar_Parser_AST.pat with
      | FStar_Parser_AST.PatAscribed uu____51603 -> false
      | uu____51615 -> true  in
    let uu____51617 = map_if_all all_binders pats  in
    match uu____51617 with
    | FStar_Pervasives_Native.Some bs ->
        let uu____51649 = collapse_pats bs  in
        (uu____51649,
          (Binders ((Prims.parse_int "4"), (Prims.parse_int "0"), true)))
    | FStar_Pervasives_Native.None  ->
        let uu____51666 = FStar_List.map p_atomicPattern pats  in
        (uu____51666,
          (Binders ((Prims.parse_int "4"), (Prims.parse_int "0"), false)))

and (p_quantifier : FStar_Parser_AST.term -> FStar_Pprint.document) =
  fun e  ->
    match e.FStar_Parser_AST.tm with
    | FStar_Parser_AST.QForall uu____51678 -> str "forall"
    | FStar_Parser_AST.QExists uu____51692 -> str "exists"
    | uu____51706 ->
        failwith "Imposible : p_quantifier called on a non-quantifier term"

and (p_trigger :
  FStar_Parser_AST.term Prims.list Prims.list -> FStar_Pprint.document) =
  fun uu___336_51708  ->
    match uu___336_51708 with
    | [] -> FStar_Pprint.empty
    | pats ->
        let uu____51720 =
          let uu____51721 =
            let uu____51722 =
              let uu____51723 = str "pattern"  in
              let uu____51725 =
                let uu____51726 =
                  let uu____51727 = p_disjunctivePats pats  in
                  FStar_Pprint.jump (Prims.parse_int "2")
                    (Prims.parse_int "0") uu____51727
                   in
                FStar_Pprint.op_Hat_Hat uu____51726 FStar_Pprint.rbrace  in
              FStar_Pprint.op_Hat_Slash_Hat uu____51723 uu____51725  in
            FStar_Pprint.op_Hat_Hat FStar_Pprint.colon uu____51722  in
          FStar_Pprint.op_Hat_Hat FStar_Pprint.lbrace uu____51721  in
        FStar_Pprint.group uu____51720

and (p_disjunctivePats :
  FStar_Parser_AST.term Prims.list Prims.list -> FStar_Pprint.document) =
  fun pats  ->
    let uu____51735 = str "\\/"  in
    FStar_Pprint.separate_map uu____51735 p_conjunctivePats pats

and (p_conjunctivePats :
  FStar_Parser_AST.term Prims.list -> FStar_Pprint.document) =
  fun pats  ->
    let uu____51742 =
      let uu____51743 = FStar_Pprint.op_Hat_Hat FStar_Pprint.semi break1  in
      FStar_Pprint.separate_map uu____51743 p_appTerm pats  in
    FStar_Pprint.group uu____51742

and (p_simpleTerm :
  Prims.bool -> Prims.bool -> FStar_Parser_AST.term -> FStar_Pprint.document)
  =
  fun ps  ->
    fun pb  ->
      fun e  ->
        match e.FStar_Parser_AST.tm with
        | FStar_Parser_AST.Abs (pats,e1) ->
            let uu____51755 = p_term_sep false pb e1  in
            (match uu____51755 with
             | (comm,doc1) ->
                 let prefix1 =
                   let uu____51764 = str "fun"  in
                   let uu____51766 =
                     let uu____51767 =
                       FStar_Pprint.separate_map break1 p_atomicPattern pats
                        in
                     FStar_Pprint.op_Hat_Slash_Hat uu____51767
                       FStar_Pprint.rarrow
                      in
                   op_Hat_Slash_Plus_Hat uu____51764 uu____51766  in
                 let uu____51768 =
                   if comm <> FStar_Pprint.empty
                   then
                     let uu____51770 =
                       let uu____51771 =
                         let uu____51772 =
                           FStar_Pprint.op_Hat_Hat FStar_Pprint.hardline doc1
                            in
                         FStar_Pprint.op_Hat_Hat comm uu____51772  in
                       FStar_Pprint.op_Hat_Hat FStar_Pprint.hardline
                         uu____51771
                        in
                     FStar_Pprint.op_Hat_Hat prefix1 uu____51770
                   else
                     (let uu____51775 = op_Hat_Slash_Plus_Hat prefix1 doc1
                         in
                      FStar_Pprint.group uu____51775)
                    in
                 let uu____51776 = paren_if ps  in uu____51776 uu____51768)
        | uu____51781 -> p_tmIff e

and (p_maybeFocusArrow : Prims.bool -> FStar_Pprint.document) =
  fun b  -> if b then str "~>" else FStar_Pprint.rarrow

and (p_patternBranch :
  Prims.bool ->
    (FStar_Parser_AST.pattern * FStar_Parser_AST.term
      FStar_Pervasives_Native.option * FStar_Parser_AST.term) ->
      FStar_Pprint.document)
  =
  fun pb  ->
    fun uu____51789  ->
      match uu____51789 with
      | (pat,when_opt,e) ->
          let one_pattern_branch p =
            let branch =
              match when_opt with
              | FStar_Pervasives_Native.None  ->
                  let uu____51813 =
                    let uu____51814 =
                      let uu____51815 =
                        let uu____51816 = p_tuplePattern p  in
                        let uu____51817 =
                          FStar_Pprint.op_Hat_Hat FStar_Pprint.space
                            FStar_Pprint.rarrow
                           in
                        FStar_Pprint.op_Hat_Hat uu____51816 uu____51817  in
                      FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____51815
                       in
                    FStar_Pprint.op_Hat_Hat FStar_Pprint.bar uu____51814  in
                  FStar_Pprint.group uu____51813
              | FStar_Pervasives_Native.Some f ->
                  let uu____51819 =
                    let uu____51820 =
                      let uu____51821 =
                        let uu____51822 =
                          let uu____51823 =
                            let uu____51824 = p_tuplePattern p  in
                            let uu____51825 = str "when"  in
                            FStar_Pprint.op_Hat_Slash_Hat uu____51824
                              uu____51825
                             in
                          FStar_Pprint.group uu____51823  in
                        let uu____51827 =
                          let uu____51828 =
                            let uu____51831 = p_tmFormula f  in
                            [uu____51831; FStar_Pprint.rarrow]  in
                          FStar_Pprint.flow break1 uu____51828  in
                        FStar_Pprint.op_Hat_Slash_Hat uu____51822 uu____51827
                         in
                      FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____51821
                       in
                    FStar_Pprint.op_Hat_Hat FStar_Pprint.bar uu____51820  in
                  FStar_Pprint.hang (Prims.parse_int "2") uu____51819
               in
            let uu____51833 = p_term_sep false pb e  in
            match uu____51833 with
            | (comm,doc1) ->
                if pb
                then
                  (if comm = FStar_Pprint.empty
                   then
                     let uu____51843 = op_Hat_Slash_Plus_Hat branch doc1  in
                     FStar_Pprint.group uu____51843
                   else
                     (let uu____51846 =
                        let uu____51847 =
                          let uu____51848 =
                            let uu____51849 =
                              let uu____51850 =
                                FStar_Pprint.op_Hat_Hat break1 comm  in
                              FStar_Pprint.op_Hat_Hat doc1 uu____51850  in
                            op_Hat_Slash_Plus_Hat branch uu____51849  in
                          FStar_Pprint.group uu____51848  in
                        let uu____51851 =
                          let uu____51852 =
                            let uu____51853 =
                              inline_comment_or_above comm doc1
                                FStar_Pprint.empty
                               in
                            jump2 uu____51853  in
                          FStar_Pprint.op_Hat_Hat branch uu____51852  in
                        FStar_Pprint.ifflat uu____51847 uu____51851  in
                      FStar_Pprint.group uu____51846))
                else
                  if comm <> FStar_Pprint.empty
                  then
                    (let uu____51857 =
                       let uu____51858 =
                         FStar_Pprint.op_Hat_Hat FStar_Pprint.hardline doc1
                          in
                       FStar_Pprint.op_Hat_Hat comm uu____51858  in
                     op_Hat_Slash_Plus_Hat branch uu____51857)
                  else op_Hat_Slash_Plus_Hat branch doc1
             in
          (match pat.FStar_Parser_AST.pat with
           | FStar_Parser_AST.PatOr pats ->
               (match FStar_List.rev pats with
                | hd1::tl1 ->
                    let last_pat_branch = one_pattern_branch hd1  in
                    let uu____51869 =
                      let uu____51870 =
                        let uu____51871 =
                          let uu____51872 =
                            let uu____51873 =
                              let uu____51874 =
                                FStar_Pprint.op_Hat_Hat FStar_Pprint.bar
                                  FStar_Pprint.space
                                 in
                              FStar_Pprint.op_Hat_Hat break1 uu____51874  in
                            FStar_Pprint.separate_map uu____51873
                              p_tuplePattern (FStar_List.rev tl1)
                             in
                          FStar_Pprint.op_Hat_Slash_Hat uu____51872
                            last_pat_branch
                           in
                        FStar_Pprint.op_Hat_Hat FStar_Pprint.space
                          uu____51871
                         in
                      FStar_Pprint.op_Hat_Hat FStar_Pprint.bar uu____51870
                       in
                    FStar_Pprint.group uu____51869
                | [] ->
                    failwith "Impossible: disjunctive pattern can't be empty")
           | uu____51876 -> one_pattern_branch pat)

and (p_tmIff : FStar_Parser_AST.term -> FStar_Pprint.document) =
  fun e  ->
    match e.FStar_Parser_AST.tm with
    | FStar_Parser_AST.Op
        ({ FStar_Ident.idText = "<==>"; FStar_Ident.idRange = uu____51878;_},e1::e2::[])
        ->
        let uu____51884 = str "<==>"  in
        let uu____51886 = p_tmImplies e1  in
        let uu____51887 = p_tmIff e2  in
        infix0 uu____51884 uu____51886 uu____51887
    | uu____51888 -> p_tmImplies e

and (p_tmImplies : FStar_Parser_AST.term -> FStar_Pprint.document) =
  fun e  ->
    match e.FStar_Parser_AST.tm with
    | FStar_Parser_AST.Op
        ({ FStar_Ident.idText = "==>"; FStar_Ident.idRange = uu____51890;_},e1::e2::[])
        ->
        let uu____51896 = str "==>"  in
        let uu____51898 =
          p_tmArrow (Arrows ((Prims.parse_int "2"), (Prims.parse_int "2")))
            false p_tmFormula e1
           in
        let uu____51904 = p_tmImplies e2  in
        infix0 uu____51896 uu____51898 uu____51904
    | uu____51905 ->
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
          let uu____51919 =
            FStar_List.splitAt
              ((FStar_List.length terms) - (Prims.parse_int "1")) terms
             in
          match uu____51919 with
          | (terms',last1) ->
              let uu____51939 =
                match style with
                | Arrows (n1,ln) ->
                    let uu____51974 =
                      let uu____51975 =
                        FStar_Pprint.op_Hat_Hat FStar_Pprint.rarrow break1
                         in
                      FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____51975
                       in
                    let uu____51976 =
                      FStar_Pprint.op_Hat_Hat FStar_Pprint.rarrow
                        FStar_Pprint.space
                       in
                    (n1, ln, terms', uu____51974, uu____51976)
                | Binders (n1,ln,parens1) ->
                    let uu____51990 =
                      if parens1
                      then FStar_List.map soft_parens_with_nesting terms'
                      else terms'  in
                    let uu____51998 =
                      FStar_Pprint.op_Hat_Hat FStar_Pprint.colon
                        FStar_Pprint.space
                       in
                    (n1, ln, uu____51990, break1, uu____51998)
                 in
              (match uu____51939 with
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
                    | _52031 when _52031 = (Prims.parse_int "1") ->
                        FStar_List.hd terms
                    | uu____52032 ->
                        let uu____52033 =
                          let uu____52034 =
                            let uu____52035 =
                              let uu____52036 =
                                FStar_Pprint.separate sep terms'1  in
                              let uu____52037 =
                                let uu____52038 =
                                  FStar_Pprint.op_Hat_Hat last_op1 last2  in
                                FStar_Pprint.op_Hat_Hat one_line_space
                                  uu____52038
                                 in
                              FStar_Pprint.op_Hat_Hat uu____52036 uu____52037
                               in
                            FStar_Pprint.op_Hat_Hat fs uu____52035  in
                          let uu____52039 =
                            let uu____52040 =
                              let uu____52041 =
                                let uu____52042 =
                                  let uu____52043 =
                                    FStar_Pprint.separate sep terms'1  in
                                  FStar_Pprint.op_Hat_Hat fs uu____52043  in
                                let uu____52044 =
                                  let uu____52045 =
                                    let uu____52046 =
                                      let uu____52047 =
                                        FStar_Pprint.op_Hat_Hat sep
                                          single_line_arg_indent
                                         in
                                      let uu____52048 =
                                        FStar_List.map
                                          (fun x  ->
                                             let uu____52054 =
                                               FStar_Pprint.hang
                                                 (Prims.parse_int "2") x
                                                in
                                             FStar_Pprint.align uu____52054)
                                          terms'1
                                         in
                                      FStar_Pprint.separate uu____52047
                                        uu____52048
                                       in
                                    FStar_Pprint.op_Hat_Hat
                                      single_line_arg_indent uu____52046
                                     in
                                  jump2 uu____52045  in
                                FStar_Pprint.ifflat uu____52042 uu____52044
                                 in
                              FStar_Pprint.group uu____52041  in
                            let uu____52056 =
                              let uu____52057 =
                                let uu____52058 =
                                  FStar_Pprint.op_Hat_Hat last_op1 last2  in
                                FStar_Pprint.hang last_n uu____52058  in
                              FStar_Pprint.align uu____52057  in
                            FStar_Pprint.prefix n1 (Prims.parse_int "1")
                              uu____52040 uu____52056
                             in
                          FStar_Pprint.ifflat uu____52034 uu____52039  in
                        FStar_Pprint.group uu____52033))

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
            | Arrows uu____52072 -> p_tmArrow' p_Tm e
            | Binders uu____52079 -> collapse_binders p_Tm e  in
          format_sig style terms false flat_space

and (p_tmArrow' :
  (FStar_Parser_AST.term -> FStar_Pprint.document) ->
    FStar_Parser_AST.term -> FStar_Pprint.document Prims.list)
  =
  fun p_Tm  ->
    fun e  ->
      match e.FStar_Parser_AST.tm with
      | FStar_Parser_AST.Product (bs,tgt) ->
          let uu____52102 = FStar_List.map (fun b  -> p_binder false b) bs
             in
          let uu____52108 = p_tmArrow' p_Tm tgt  in
          FStar_List.append uu____52102 uu____52108
      | uu____52111 -> let uu____52112 = p_Tm e  in [uu____52112]

and (collapse_binders :
  (FStar_Parser_AST.term -> FStar_Pprint.document) ->
    FStar_Parser_AST.term -> FStar_Pprint.document Prims.list)
  =
  fun p_Tm  ->
    fun e  ->
      let rec accumulate_binders p_Tm1 e1 =
        match e1.FStar_Parser_AST.tm with
        | FStar_Parser_AST.Product (bs,tgt) ->
            let uu____52165 = FStar_List.map (fun b  -> p_binder' false b) bs
               in
            let uu____52191 = accumulate_binders p_Tm1 tgt  in
            FStar_List.append uu____52165 uu____52191
        | uu____52214 ->
            let uu____52215 =
              let uu____52226 = p_Tm1 e1  in
              (uu____52226, FStar_Pervasives_Native.None, cat_with_colon)  in
            [uu____52215]
         in
      let fold_fun bs x =
        let uu____52324 = x  in
        match uu____52324 with
        | (b1,t1,f1) ->
            (match bs with
             | [] -> [([b1], t1, f1)]
             | hd1::tl1 ->
                 let uu____52460 = hd1  in
                 (match uu____52460 with
                  | (b2s,t2,uu____52489) ->
                      (match (t1, t2) with
                       | (FStar_Pervasives_Native.Some
                          typ1,FStar_Pervasives_Native.Some typ2) ->
                           if typ1 = typ2
                           then ((FStar_List.append b2s [b1]), t1, f1) :: tl1
                           else ([b1], t1, f1) :: hd1 :: tl1
                       | uu____52599 -> ([b1], t1, f1) :: bs)))
         in
      let p_collapsed_binder cb =
        let uu____52660 = cb  in
        match uu____52660 with
        | (bs,t,f) ->
            (match t with
             | FStar_Pervasives_Native.None  ->
                 (match bs with
                  | b::[] -> b
                  | uu____52689 -> failwith "Impossible")
             | FStar_Pervasives_Native.Some typ ->
                 (match bs with
                  | [] -> failwith "Impossible"
                  | b::[] -> f b typ
                  | hd1::tl1 ->
                      let uu____52702 =
                        FStar_List.fold_left
                          (fun x  ->
                             fun y  ->
                               let uu____52708 =
                                 FStar_Pprint.op_Hat_Hat FStar_Pprint.space y
                                  in
                               FStar_Pprint.op_Hat_Hat x uu____52708) hd1 tl1
                         in
                      f uu____52702 typ))
         in
      let binders =
        let uu____52726 = accumulate_binders p_Tm e  in
        FStar_List.fold_left fold_fun [] uu____52726  in
      map_rev p_collapsed_binder binders

and (p_tmFormula : FStar_Parser_AST.term -> FStar_Pprint.document) =
  fun e  ->
    let conj =
      let uu____52789 =
        let uu____52790 = str "/\\"  in
        FStar_Pprint.op_Hat_Hat uu____52790 break1  in
      FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____52789  in
    let disj =
      let uu____52793 =
        let uu____52794 = str "\\/"  in
        FStar_Pprint.op_Hat_Hat uu____52794 break1  in
      FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____52793  in
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
        ({ FStar_Ident.idText = "\\/"; FStar_Ident.idRange = uu____52814;_},e1::e2::[])
        ->
        let uu____52820 = p_tmDisjunction e1  in
        let uu____52825 =
          let uu____52830 = p_tmConjunction e2  in [uu____52830]  in
        FStar_List.append uu____52820 uu____52825
    | uu____52839 -> let uu____52840 = p_tmConjunction e  in [uu____52840]

and (p_tmConjunction :
  FStar_Parser_AST.term -> FStar_Pprint.document Prims.list) =
  fun e  ->
    match e.FStar_Parser_AST.tm with
    | FStar_Parser_AST.Op
        ({ FStar_Ident.idText = "/\\"; FStar_Ident.idRange = uu____52850;_},e1::e2::[])
        ->
        let uu____52856 = p_tmConjunction e1  in
        let uu____52859 = let uu____52862 = p_tmTuple e2  in [uu____52862]
           in
        FStar_List.append uu____52856 uu____52859
    | uu____52863 -> let uu____52864 = p_tmTuple e  in [uu____52864]

and (p_tmTuple : FStar_Parser_AST.term -> FStar_Pprint.document) =
  fun e  -> with_comment p_tmTuple' e e.FStar_Parser_AST.range

and (p_tmTuple' : FStar_Parser_AST.term -> FStar_Pprint.document) =
  fun e  ->
    match e.FStar_Parser_AST.tm with
    | FStar_Parser_AST.Construct (lid,args) when
        (is_tuple_constructor lid) && (all_explicit args) ->
        let uu____52881 = FStar_Pprint.op_Hat_Hat FStar_Pprint.comma break1
           in
        FStar_Pprint.separate_map uu____52881
          (fun uu____52889  ->
             match uu____52889 with | (e1,uu____52895) -> p_tmEq e1) args
    | uu____52896 -> p_tmEq e

and (paren_if_gt :
  Prims.int -> Prims.int -> FStar_Pprint.document -> FStar_Pprint.document) =
  fun curr  ->
    fun mine  ->
      fun doc1  ->
        if mine <= curr
        then doc1
        else
          (let uu____52905 =
             let uu____52906 =
               FStar_Pprint.op_Hat_Hat doc1 FStar_Pprint.rparen  in
             FStar_Pprint.op_Hat_Hat FStar_Pprint.lparen uu____52906  in
           FStar_Pprint.group uu____52905)

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
               (let uu____52925 = FStar_Ident.text_of_id op  in
                uu____52925 = "="))
              ||
              (let uu____52930 = FStar_Ident.text_of_id op  in
               uu____52930 = "|>")
            ->
            let op1 = FStar_Ident.text_of_id op  in
            let uu____52936 = levels op1  in
            (match uu____52936 with
             | (left1,mine,right1) ->
                 let uu____52955 =
                   let uu____52956 = FStar_All.pipe_left str op1  in
                   let uu____52958 = p_tmEqWith' p_X left1 e1  in
                   let uu____52959 = p_tmEqWith' p_X right1 e2  in
                   infix0 uu____52956 uu____52958 uu____52959  in
                 paren_if_gt curr mine uu____52955)
        | FStar_Parser_AST.Op
            ({ FStar_Ident.idText = ":=";
               FStar_Ident.idRange = uu____52960;_},e1::e2::[])
            ->
            let uu____52966 =
              let uu____52967 = p_tmEqWith p_X e1  in
              let uu____52968 =
                let uu____52969 =
                  let uu____52970 =
                    let uu____52971 = p_tmEqWith p_X e2  in
                    op_Hat_Slash_Plus_Hat FStar_Pprint.equals uu____52971  in
                  FStar_Pprint.op_Hat_Hat FStar_Pprint.colon uu____52970  in
                FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____52969  in
              FStar_Pprint.op_Hat_Hat uu____52967 uu____52968  in
            FStar_Pprint.group uu____52966
        | FStar_Parser_AST.Op
            ({ FStar_Ident.idText = "-"; FStar_Ident.idRange = uu____52972;_},e1::[])
            ->
            let uu____52977 = levels "-"  in
            (match uu____52977 with
             | (left1,mine,right1) ->
                 let uu____52997 = p_tmEqWith' p_X mine e1  in
                 FStar_Pprint.op_Hat_Slash_Hat FStar_Pprint.minus uu____52997)
        | uu____52998 -> p_tmNoEqWith p_X e

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
              (lid,(e1,uu____53046)::(e2,uu____53048)::[]) when
              (FStar_Ident.lid_equals lid FStar_Parser_Const.cons_lid) &&
                (let uu____53068 = is_list e  in
                 Prims.op_Negation uu____53068)
              ->
              let op = "::"  in
              let uu____53073 = levels op  in
              (match uu____53073 with
               | (left1,mine,right1) ->
                   let uu____53092 =
                     let uu____53093 = str op  in
                     let uu____53094 = p_tmNoEqWith' false p_X left1 e1  in
                     let uu____53096 = p_tmNoEqWith' false p_X right1 e2  in
                     infix0 uu____53093 uu____53094 uu____53096  in
                   paren_if_gt curr mine uu____53092)
          | FStar_Parser_AST.Sum (binders,res) ->
              let op = "&"  in
              let uu____53115 = levels op  in
              (match uu____53115 with
               | (left1,mine,right1) ->
                   let p_dsumfst bt =
                     match bt with
                     | FStar_Util.Inl b ->
                         let uu____53149 = p_binder false b  in
                         let uu____53151 =
                           let uu____53152 =
                             let uu____53153 = str op  in
                             FStar_Pprint.op_Hat_Hat uu____53153 break1  in
                           FStar_Pprint.op_Hat_Hat FStar_Pprint.space
                             uu____53152
                            in
                         FStar_Pprint.op_Hat_Hat uu____53149 uu____53151
                     | FStar_Util.Inr t ->
                         let uu____53155 = p_tmNoEqWith' false p_X left1 t
                            in
                         let uu____53157 =
                           let uu____53158 =
                             let uu____53159 = str op  in
                             FStar_Pprint.op_Hat_Hat uu____53159 break1  in
                           FStar_Pprint.op_Hat_Hat FStar_Pprint.space
                             uu____53158
                            in
                         FStar_Pprint.op_Hat_Hat uu____53155 uu____53157
                      in
                   let uu____53160 =
                     let uu____53161 =
                       FStar_Pprint.concat_map p_dsumfst binders  in
                     let uu____53166 = p_tmNoEqWith' false p_X right1 res  in
                     FStar_Pprint.op_Hat_Hat uu____53161 uu____53166  in
                   paren_if_gt curr mine uu____53160)
          | FStar_Parser_AST.Op
              ({ FStar_Ident.idText = "*";
                 FStar_Ident.idRange = uu____53168;_},e1::e2::[])
              when FStar_ST.op_Bang unfold_tuples ->
              let op = "*"  in
              let uu____53198 = levels op  in
              (match uu____53198 with
               | (left1,mine,right1) ->
                   if inside_tuple
                   then
                     let uu____53218 = str op  in
                     let uu____53219 = p_tmNoEqWith' true p_X left1 e1  in
                     let uu____53221 = p_tmNoEqWith' true p_X right1 e2  in
                     infix0 uu____53218 uu____53219 uu____53221
                   else
                     (let uu____53225 =
                        let uu____53226 = str op  in
                        let uu____53227 = p_tmNoEqWith' true p_X left1 e1  in
                        let uu____53229 = p_tmNoEqWith' true p_X right1 e2
                           in
                        infix0 uu____53226 uu____53227 uu____53229  in
                      paren_if_gt curr mine uu____53225))
          | FStar_Parser_AST.Op (op,e1::e2::[]) when is_operatorInfix34 op ->
              let op1 = FStar_Ident.text_of_id op  in
              let uu____53238 = levels op1  in
              (match uu____53238 with
               | (left1,mine,right1) ->
                   let uu____53257 =
                     let uu____53258 = str op1  in
                     let uu____53259 = p_tmNoEqWith' false p_X left1 e1  in
                     let uu____53261 = p_tmNoEqWith' false p_X right1 e2  in
                     infix0 uu____53258 uu____53259 uu____53261  in
                   paren_if_gt curr mine uu____53257)
          | FStar_Parser_AST.Record (with_opt,record_fields) ->
              let uu____53281 =
                let uu____53282 =
                  default_or_map FStar_Pprint.empty p_with_clause with_opt
                   in
                let uu____53283 =
                  let uu____53284 =
                    FStar_Pprint.op_Hat_Hat FStar_Pprint.semi break1  in
                  separate_map_last uu____53284 p_simpleDef record_fields  in
                FStar_Pprint.op_Hat_Hat uu____53282 uu____53283  in
              braces_with_nesting uu____53281
          | FStar_Parser_AST.Op
              ({ FStar_Ident.idText = "~";
                 FStar_Ident.idRange = uu____53289;_},e1::[])
              ->
              let uu____53294 =
                let uu____53295 = str "~"  in
                let uu____53297 = p_atomicTerm e1  in
                FStar_Pprint.op_Hat_Hat uu____53295 uu____53297  in
              FStar_Pprint.group uu____53294
          | FStar_Parser_AST.Paren p when inside_tuple ->
              (match p.FStar_Parser_AST.tm with
               | FStar_Parser_AST.Op
                   ({ FStar_Ident.idText = "*";
                      FStar_Ident.idRange = uu____53299;_},e1::e2::[])
                   ->
                   let op = "*"  in
                   let uu____53308 = levels op  in
                   (match uu____53308 with
                    | (left1,mine,right1) ->
                        let uu____53327 =
                          let uu____53328 = str op  in
                          let uu____53329 = p_tmNoEqWith' true p_X left1 e1
                             in
                          let uu____53331 = p_tmNoEqWith' true p_X right1 e2
                             in
                          infix0 uu____53328 uu____53329 uu____53331  in
                        paren_if_gt curr mine uu____53327)
               | uu____53333 -> p_X e)
          | uu____53334 -> p_X e

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
        let uu____53341 =
          let uu____53342 = p_lident lid  in
          let uu____53343 =
            let uu____53344 = p_appTerm e1  in
            FStar_Pprint.op_Hat_Slash_Hat FStar_Pprint.colon uu____53344  in
          FStar_Pprint.op_Hat_Slash_Hat uu____53342 uu____53343  in
        FStar_Pprint.group uu____53341
    | FStar_Parser_AST.Refine (b,phi) -> p_refinedBinder b phi
    | uu____53347 -> p_appTerm e

and (p_with_clause : FStar_Parser_AST.term -> FStar_Pprint.document) =
  fun e  ->
    let uu____53349 = p_appTerm e  in
    let uu____53350 =
      let uu____53351 =
        let uu____53352 = str "with"  in
        FStar_Pprint.op_Hat_Hat uu____53352 break1  in
      FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____53351  in
    FStar_Pprint.op_Hat_Hat uu____53349 uu____53350

and (p_refinedBinder :
  FStar_Parser_AST.binder -> FStar_Parser_AST.term -> FStar_Pprint.document)
  =
  fun b  ->
    fun phi  ->
      match b.FStar_Parser_AST.b with
      | FStar_Parser_AST.Annotated (lid,t) ->
          let uu____53358 = p_lident lid  in
          p_refinement b.FStar_Parser_AST.aqual uu____53358 t phi
      | FStar_Parser_AST.TAnnotated uu____53359 ->
          failwith "Is this still used ?"
      | FStar_Parser_AST.Variable uu____53365 ->
          let uu____53366 =
            let uu____53368 = FStar_Parser_AST.binder_to_string b  in
            FStar_Util.format1
              "Imposible : a refined binder ought to be annotated %s"
              uu____53368
             in
          failwith uu____53366
      | FStar_Parser_AST.TVariable uu____53371 ->
          let uu____53372 =
            let uu____53374 = FStar_Parser_AST.binder_to_string b  in
            FStar_Util.format1
              "Imposible : a refined binder ought to be annotated %s"
              uu____53374
             in
          failwith uu____53372
      | FStar_Parser_AST.NoName uu____53377 ->
          let uu____53378 =
            let uu____53380 = FStar_Parser_AST.binder_to_string b  in
            FStar_Util.format1
              "Imposible : a refined binder ought to be annotated %s"
              uu____53380
             in
          failwith uu____53378

and (p_simpleDef :
  Prims.bool ->
    (FStar_Ident.lid * FStar_Parser_AST.term) -> FStar_Pprint.document)
  =
  fun ps  ->
    fun uu____53384  ->
      match uu____53384 with
      | (lid,e) ->
          let uu____53392 =
            let uu____53393 = p_qlident lid  in
            let uu____53394 =
              let uu____53395 = p_noSeqTermAndComment ps false e  in
              FStar_Pprint.op_Hat_Slash_Hat FStar_Pprint.equals uu____53395
               in
            FStar_Pprint.op_Hat_Slash_Hat uu____53393 uu____53394  in
          FStar_Pprint.group uu____53392

and (p_appTerm : FStar_Parser_AST.term -> FStar_Pprint.document) =
  fun e  ->
    match e.FStar_Parser_AST.tm with
    | FStar_Parser_AST.App uu____53398 when is_general_application e ->
        let uu____53405 = head_and_args e  in
        (match uu____53405 with
         | (head1,args) ->
             (match args with
              | e1::e2::[] when
                  (FStar_Pervasives_Native.snd e1) = FStar_Parser_AST.Infix
                  ->
                  let uu____53452 = p_argTerm e1  in
                  let uu____53453 =
                    let uu____53454 =
                      let uu____53455 =
                        let uu____53456 = str "`"  in
                        let uu____53458 =
                          let uu____53459 = p_indexingTerm head1  in
                          let uu____53460 = str "`"  in
                          FStar_Pprint.op_Hat_Hat uu____53459 uu____53460  in
                        FStar_Pprint.op_Hat_Hat uu____53456 uu____53458  in
                      FStar_Pprint.group uu____53455  in
                    let uu____53462 = p_argTerm e2  in
                    FStar_Pprint.op_Hat_Slash_Hat uu____53454 uu____53462  in
                  FStar_Pprint.op_Hat_Slash_Hat uu____53452 uu____53453
              | uu____53463 ->
                  let uu____53470 =
                    let uu____53481 =
                      FStar_ST.op_Bang should_print_fs_typ_app  in
                    if uu____53481
                    then
                      let uu____53515 =
                        FStar_Util.take
                          (fun uu____53539  ->
                             match uu____53539 with
                             | (uu____53545,aq) ->
                                 aq = FStar_Parser_AST.FsTypApp) args
                         in
                      match uu____53515 with
                      | (fs_typ_args,args1) ->
                          let uu____53583 =
                            let uu____53584 = p_indexingTerm head1  in
                            let uu____53585 =
                              let uu____53586 =
                                FStar_Pprint.op_Hat_Hat FStar_Pprint.comma
                                  break1
                                 in
                              soft_surround_map_or_flow (Prims.parse_int "2")
                                (Prims.parse_int "0") FStar_Pprint.empty
                                FStar_Pprint.langle uu____53586
                                FStar_Pprint.rangle p_fsTypArg fs_typ_args
                               in
                            FStar_Pprint.op_Hat_Hat uu____53584 uu____53585
                             in
                          (uu____53583, args1)
                    else
                      (let uu____53601 = p_indexingTerm head1  in
                       (uu____53601, args))
                     in
                  (match uu____53470 with
                   | (head_doc,args1) ->
                       let uu____53622 =
                         let uu____53623 =
                           FStar_Pprint.op_Hat_Hat head_doc
                             FStar_Pprint.space
                            in
                         soft_surround_map_or_flow (Prims.parse_int "2")
                           (Prims.parse_int "0") head_doc uu____53623 break1
                           FStar_Pprint.empty p_argTerm args1
                          in
                       FStar_Pprint.group uu____53622)))
    | FStar_Parser_AST.Construct (lid,args) when
        (is_general_construction e) &&
          (let uu____53645 = is_dtuple_constructor lid  in
           Prims.op_Negation uu____53645)
        ->
        (match args with
         | [] -> p_quident lid
         | arg::[] ->
             let uu____53664 =
               let uu____53665 = p_quident lid  in
               let uu____53666 = p_argTerm arg  in
               FStar_Pprint.op_Hat_Slash_Hat uu____53665 uu____53666  in
             FStar_Pprint.group uu____53664
         | hd1::tl1 ->
             let uu____53683 =
               let uu____53684 =
                 let uu____53685 =
                   let uu____53686 = p_quident lid  in
                   let uu____53687 = p_argTerm hd1  in
                   prefix2 uu____53686 uu____53687  in
                 FStar_Pprint.group uu____53685  in
               let uu____53688 =
                 let uu____53689 =
                   FStar_Pprint.separate_map break1 p_argTerm tl1  in
                 jump2 uu____53689  in
               FStar_Pprint.op_Hat_Hat uu____53684 uu____53688  in
             FStar_Pprint.group uu____53683)
    | uu____53694 -> p_indexingTerm e

and (p_argTerm :
  (FStar_Parser_AST.term * FStar_Parser_AST.imp) -> FStar_Pprint.document) =
  fun arg_imp  ->
    match arg_imp with
    | (u,FStar_Parser_AST.UnivApp ) -> p_universe u
    | (e,FStar_Parser_AST.FsTypApp ) ->
        (FStar_Errors.log_issue e.FStar_Parser_AST.range
           (FStar_Errors.Warning_UnexpectedFsTypApp,
             "Unexpected FsTypApp, output might not be formatted correctly.");
         (let uu____53705 = p_indexingTerm e  in
          FStar_Pprint.surround (Prims.parse_int "2") (Prims.parse_int "1")
            FStar_Pprint.langle uu____53705 FStar_Pprint.rangle))
    | (e,FStar_Parser_AST.Hash ) ->
        let uu____53709 = str "#"  in
        let uu____53711 = p_indexingTerm e  in
        FStar_Pprint.op_Hat_Hat uu____53709 uu____53711
    | (e,FStar_Parser_AST.HashBrace t) ->
        let uu____53714 = str "#["  in
        let uu____53716 =
          let uu____53717 = p_indexingTerm t  in
          let uu____53718 =
            let uu____53719 = str "]"  in
            let uu____53721 = p_indexingTerm e  in
            FStar_Pprint.op_Hat_Hat uu____53719 uu____53721  in
          FStar_Pprint.op_Hat_Hat uu____53717 uu____53718  in
        FStar_Pprint.op_Hat_Hat uu____53714 uu____53716
    | (e,FStar_Parser_AST.Infix ) -> p_indexingTerm e
    | (e,FStar_Parser_AST.Nothing ) -> p_indexingTerm e

and (p_fsTypArg :
  (FStar_Parser_AST.term * FStar_Parser_AST.imp) -> FStar_Pprint.document) =
  fun uu____53724  ->
    match uu____53724 with | (e,uu____53730) -> p_indexingTerm e

and (p_indexingTerm_aux :
  (FStar_Parser_AST.term -> FStar_Pprint.document) ->
    FStar_Parser_AST.term -> FStar_Pprint.document)
  =
  fun exit1  ->
    fun e  ->
      match e.FStar_Parser_AST.tm with
      | FStar_Parser_AST.Op
          ({ FStar_Ident.idText = ".()"; FStar_Ident.idRange = uu____53735;_},e1::e2::[])
          ->
          let uu____53741 =
            let uu____53742 = p_indexingTerm_aux p_atomicTermNotQUident e1
               in
            let uu____53743 =
              let uu____53744 =
                let uu____53745 = p_term false false e2  in
                soft_parens_with_nesting uu____53745  in
              FStar_Pprint.op_Hat_Hat FStar_Pprint.dot uu____53744  in
            FStar_Pprint.op_Hat_Hat uu____53742 uu____53743  in
          FStar_Pprint.group uu____53741
      | FStar_Parser_AST.Op
          ({ FStar_Ident.idText = ".[]"; FStar_Ident.idRange = uu____53748;_},e1::e2::[])
          ->
          let uu____53754 =
            let uu____53755 = p_indexingTerm_aux p_atomicTermNotQUident e1
               in
            let uu____53756 =
              let uu____53757 =
                let uu____53758 = p_term false false e2  in
                soft_brackets_with_nesting uu____53758  in
              FStar_Pprint.op_Hat_Hat FStar_Pprint.dot uu____53757  in
            FStar_Pprint.op_Hat_Hat uu____53755 uu____53756  in
          FStar_Pprint.group uu____53754
      | uu____53761 -> exit1 e

and (p_indexingTerm : FStar_Parser_AST.term -> FStar_Pprint.document) =
  fun e  -> p_indexingTerm_aux p_atomicTerm e

and (p_atomicTerm : FStar_Parser_AST.term -> FStar_Pprint.document) =
  fun e  ->
    match e.FStar_Parser_AST.tm with
    | FStar_Parser_AST.LetOpen (lid,e1) ->
        let uu____53766 = p_quident lid  in
        let uu____53767 =
          let uu____53768 =
            let uu____53769 = p_term false false e1  in
            soft_parens_with_nesting uu____53769  in
          FStar_Pprint.op_Hat_Hat FStar_Pprint.dot uu____53768  in
        FStar_Pprint.op_Hat_Hat uu____53766 uu____53767
    | FStar_Parser_AST.Name lid -> p_quident lid
    | FStar_Parser_AST.Op (op,e1::[]) when is_general_prefix_op op ->
        let uu____53777 =
          let uu____53778 = FStar_Ident.text_of_id op  in str uu____53778  in
        let uu____53780 = p_atomicTerm e1  in
        FStar_Pprint.op_Hat_Hat uu____53777 uu____53780
    | uu____53781 -> p_atomicTermNotQUident e

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
         | uu____53794 -> p_constant c)
    | FStar_Parser_AST.Name lid when
        FStar_Ident.lid_equals lid FStar_Parser_Const.true_lid -> str "True"
    | FStar_Parser_AST.Name lid when
        FStar_Ident.lid_equals lid FStar_Parser_Const.false_lid ->
        str "False"
    | FStar_Parser_AST.Op (op,e1::[]) when is_general_prefix_op op ->
        let uu____53803 =
          let uu____53804 = FStar_Ident.text_of_id op  in str uu____53804  in
        let uu____53806 = p_atomicTermNotQUident e1  in
        FStar_Pprint.op_Hat_Hat uu____53803 uu____53806
    | FStar_Parser_AST.Op (op,[]) ->
        let uu____53810 =
          let uu____53811 =
            let uu____53812 =
              let uu____53813 = FStar_Ident.text_of_id op  in str uu____53813
               in
            let uu____53815 =
              FStar_Pprint.op_Hat_Hat FStar_Pprint.space FStar_Pprint.rparen
               in
            FStar_Pprint.op_Hat_Hat uu____53812 uu____53815  in
          FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____53811  in
        FStar_Pprint.op_Hat_Hat FStar_Pprint.lparen uu____53810
    | FStar_Parser_AST.Construct (lid,args) when is_dtuple_constructor lid ->
        let uu____53830 = all_explicit args  in
        if uu____53830
        then
          let uu____53833 =
            FStar_Pprint.op_Hat_Hat FStar_Pprint.lparen FStar_Pprint.bar  in
          let uu____53834 =
            let uu____53835 =
              FStar_Pprint.op_Hat_Hat FStar_Pprint.comma break1  in
            let uu____53836 = FStar_List.map FStar_Pervasives_Native.fst args
               in
            FStar_Pprint.separate_map uu____53835 p_tmEq uu____53836  in
          let uu____53843 =
            FStar_Pprint.op_Hat_Hat FStar_Pprint.bar FStar_Pprint.rparen  in
          FStar_Pprint.surround (Prims.parse_int "2") (Prims.parse_int "1")
            uu____53833 uu____53834 uu____53843
        else
          (match args with
           | [] -> p_quident lid
           | arg::[] ->
               let uu____53865 =
                 let uu____53866 = p_quident lid  in
                 let uu____53867 = p_argTerm arg  in
                 FStar_Pprint.op_Hat_Slash_Hat uu____53866 uu____53867  in
               FStar_Pprint.group uu____53865
           | hd1::tl1 ->
               let uu____53884 =
                 let uu____53885 =
                   let uu____53886 =
                     let uu____53887 = p_quident lid  in
                     let uu____53888 = p_argTerm hd1  in
                     prefix2 uu____53887 uu____53888  in
                   FStar_Pprint.group uu____53886  in
                 let uu____53889 =
                   let uu____53890 =
                     FStar_Pprint.separate_map break1 p_argTerm tl1  in
                   jump2 uu____53890  in
                 FStar_Pprint.op_Hat_Hat uu____53885 uu____53889  in
               FStar_Pprint.group uu____53884)
    | FStar_Parser_AST.Project (e1,lid) ->
        let uu____53897 =
          let uu____53898 = p_atomicTermNotQUident e1  in
          let uu____53899 =
            let uu____53900 = p_qlident lid  in
            FStar_Pprint.op_Hat_Hat FStar_Pprint.dot uu____53900  in
          FStar_Pprint.prefix (Prims.parse_int "2") (Prims.parse_int "0")
            uu____53898 uu____53899
           in
        FStar_Pprint.group uu____53897
    | uu____53903 -> p_projectionLHS e

and (p_projectionLHS : FStar_Parser_AST.term -> FStar_Pprint.document) =
  fun e  ->
    match e.FStar_Parser_AST.tm with
    | FStar_Parser_AST.Var lid -> p_qlident lid
    | FStar_Parser_AST.Projector (constr_lid,field_lid) ->
        let uu____53908 = p_quident constr_lid  in
        let uu____53909 =
          let uu____53910 =
            let uu____53911 = p_lident field_lid  in
            FStar_Pprint.op_Hat_Hat FStar_Pprint.dot uu____53911  in
          FStar_Pprint.op_Hat_Hat FStar_Pprint.qmark uu____53910  in
        FStar_Pprint.op_Hat_Hat uu____53908 uu____53909
    | FStar_Parser_AST.Discrim constr_lid ->
        let uu____53913 = p_quident constr_lid  in
        FStar_Pprint.op_Hat_Hat uu____53913 FStar_Pprint.qmark
    | FStar_Parser_AST.Paren e1 ->
        let uu____53915 = p_term_sep false false e1  in
        (match uu____53915 with
         | (comm,t) ->
             let doc1 = soft_parens_with_nesting t  in
             if comm = FStar_Pprint.empty
             then doc1
             else
               (let uu____53928 =
                  FStar_Pprint.op_Hat_Hat FStar_Pprint.hardline doc1  in
                FStar_Pprint.op_Hat_Hat comm uu____53928))
    | uu____53929 when is_array e ->
        let es = extract_from_list e  in
        let uu____53933 =
          FStar_Pprint.op_Hat_Hat FStar_Pprint.lbracket FStar_Pprint.bar  in
        let uu____53934 =
          let uu____53935 = FStar_Pprint.op_Hat_Hat FStar_Pprint.semi break1
             in
          separate_map_or_flow_last uu____53935
            (fun ps  -> p_noSeqTermAndComment ps false) es
           in
        let uu____53940 =
          FStar_Pprint.op_Hat_Hat FStar_Pprint.bar FStar_Pprint.rbracket  in
        FStar_Pprint.surround (Prims.parse_int "2") (Prims.parse_int "0")
          uu____53933 uu____53934 uu____53940
    | uu____53943 when is_list e ->
        let uu____53944 =
          let uu____53945 = FStar_Pprint.op_Hat_Hat FStar_Pprint.semi break1
             in
          let uu____53946 = extract_from_list e  in
          separate_map_or_flow_last uu____53945
            (fun ps  -> p_noSeqTermAndComment ps false) uu____53946
           in
        FStar_Pprint.surround (Prims.parse_int "2") (Prims.parse_int "0")
          FStar_Pprint.lbracket uu____53944 FStar_Pprint.rbracket
    | uu____53955 when is_lex_list e ->
        let uu____53956 =
          FStar_Pprint.op_Hat_Hat FStar_Pprint.percent FStar_Pprint.lbracket
           in
        let uu____53957 =
          let uu____53958 = FStar_Pprint.op_Hat_Hat FStar_Pprint.semi break1
             in
          let uu____53959 = extract_from_list e  in
          separate_map_or_flow_last uu____53958
            (fun ps  -> p_noSeqTermAndComment ps false) uu____53959
           in
        FStar_Pprint.surround (Prims.parse_int "2") (Prims.parse_int "1")
          uu____53956 uu____53957 FStar_Pprint.rbracket
    | uu____53968 when is_ref_set e ->
        let es = extract_from_ref_set e  in
        let uu____53972 =
          FStar_Pprint.op_Hat_Hat FStar_Pprint.bang FStar_Pprint.lbrace  in
        let uu____53973 =
          let uu____53974 = FStar_Pprint.op_Hat_Hat FStar_Pprint.comma break1
             in
          separate_map_or_flow uu____53974 p_appTerm es  in
        FStar_Pprint.surround (Prims.parse_int "2") (Prims.parse_int "0")
          uu____53972 uu____53973 FStar_Pprint.rbrace
    | FStar_Parser_AST.Labeled (e1,s,b) ->
        let uu____53984 = str (Prims.op_Hat "(*" (Prims.op_Hat s "*)"))  in
        let uu____53987 = p_term false false e1  in
        FStar_Pprint.op_Hat_Slash_Hat uu____53984 uu____53987
    | FStar_Parser_AST.Op (op,args) when
        let uu____53996 = handleable_op op args  in
        Prims.op_Negation uu____53996 ->
        let uu____53998 =
          let uu____54000 =
            let uu____54002 = FStar_Ident.text_of_id op  in
            let uu____54004 =
              let uu____54006 =
                let uu____54008 =
                  FStar_Util.string_of_int (FStar_List.length args)  in
                Prims.op_Hat uu____54008
                  " arguments couldn't be handled by the pretty printer"
                 in
              Prims.op_Hat " with " uu____54006  in
            Prims.op_Hat uu____54002 uu____54004  in
          Prims.op_Hat "Operation " uu____54000  in
        failwith uu____53998
    | FStar_Parser_AST.Uvar id1 ->
        failwith "Unexpected universe variable out of universe context"
    | FStar_Parser_AST.Wild  ->
        let uu____54015 = p_term false false e  in
        soft_parens_with_nesting uu____54015
    | FStar_Parser_AST.Const uu____54018 ->
        let uu____54019 = p_term false false e  in
        soft_parens_with_nesting uu____54019
    | FStar_Parser_AST.Op uu____54022 ->
        let uu____54029 = p_term false false e  in
        soft_parens_with_nesting uu____54029
    | FStar_Parser_AST.Tvar uu____54032 ->
        let uu____54033 = p_term false false e  in
        soft_parens_with_nesting uu____54033
    | FStar_Parser_AST.Var uu____54036 ->
        let uu____54037 = p_term false false e  in
        soft_parens_with_nesting uu____54037
    | FStar_Parser_AST.Name uu____54040 ->
        let uu____54041 = p_term false false e  in
        soft_parens_with_nesting uu____54041
    | FStar_Parser_AST.Construct uu____54044 ->
        let uu____54055 = p_term false false e  in
        soft_parens_with_nesting uu____54055
    | FStar_Parser_AST.Abs uu____54058 ->
        let uu____54065 = p_term false false e  in
        soft_parens_with_nesting uu____54065
    | FStar_Parser_AST.App uu____54068 ->
        let uu____54075 = p_term false false e  in
        soft_parens_with_nesting uu____54075
    | FStar_Parser_AST.Let uu____54078 ->
        let uu____54099 = p_term false false e  in
        soft_parens_with_nesting uu____54099
    | FStar_Parser_AST.LetOpen uu____54102 ->
        let uu____54107 = p_term false false e  in
        soft_parens_with_nesting uu____54107
    | FStar_Parser_AST.Seq uu____54110 ->
        let uu____54115 = p_term false false e  in
        soft_parens_with_nesting uu____54115
    | FStar_Parser_AST.Bind uu____54118 ->
        let uu____54125 = p_term false false e  in
        soft_parens_with_nesting uu____54125
    | FStar_Parser_AST.If uu____54128 ->
        let uu____54135 = p_term false false e  in
        soft_parens_with_nesting uu____54135
    | FStar_Parser_AST.Match uu____54138 ->
        let uu____54153 = p_term false false e  in
        soft_parens_with_nesting uu____54153
    | FStar_Parser_AST.TryWith uu____54156 ->
        let uu____54171 = p_term false false e  in
        soft_parens_with_nesting uu____54171
    | FStar_Parser_AST.Ascribed uu____54174 ->
        let uu____54183 = p_term false false e  in
        soft_parens_with_nesting uu____54183
    | FStar_Parser_AST.Record uu____54186 ->
        let uu____54199 = p_term false false e  in
        soft_parens_with_nesting uu____54199
    | FStar_Parser_AST.Project uu____54202 ->
        let uu____54207 = p_term false false e  in
        soft_parens_with_nesting uu____54207
    | FStar_Parser_AST.Product uu____54210 ->
        let uu____54217 = p_term false false e  in
        soft_parens_with_nesting uu____54217
    | FStar_Parser_AST.Sum uu____54220 ->
        let uu____54231 = p_term false false e  in
        soft_parens_with_nesting uu____54231
    | FStar_Parser_AST.QForall uu____54234 ->
        let uu____54247 = p_term false false e  in
        soft_parens_with_nesting uu____54247
    | FStar_Parser_AST.QExists uu____54250 ->
        let uu____54263 = p_term false false e  in
        soft_parens_with_nesting uu____54263
    | FStar_Parser_AST.Refine uu____54266 ->
        let uu____54271 = p_term false false e  in
        soft_parens_with_nesting uu____54271
    | FStar_Parser_AST.NamedTyp uu____54274 ->
        let uu____54279 = p_term false false e  in
        soft_parens_with_nesting uu____54279
    | FStar_Parser_AST.Requires uu____54282 ->
        let uu____54290 = p_term false false e  in
        soft_parens_with_nesting uu____54290
    | FStar_Parser_AST.Ensures uu____54293 ->
        let uu____54301 = p_term false false e  in
        soft_parens_with_nesting uu____54301
    | FStar_Parser_AST.Attributes uu____54304 ->
        let uu____54307 = p_term false false e  in
        soft_parens_with_nesting uu____54307
    | FStar_Parser_AST.Quote uu____54310 ->
        let uu____54315 = p_term false false e  in
        soft_parens_with_nesting uu____54315
    | FStar_Parser_AST.VQuote uu____54318 ->
        let uu____54319 = p_term false false e  in
        soft_parens_with_nesting uu____54319
    | FStar_Parser_AST.Antiquote uu____54322 ->
        let uu____54323 = p_term false false e  in
        soft_parens_with_nesting uu____54323
    | FStar_Parser_AST.CalcProof uu____54326 ->
        let uu____54335 = p_term false false e  in
        soft_parens_with_nesting uu____54335

and (p_constant : FStar_Const.sconst -> FStar_Pprint.document) =
  fun uu___339_54338  ->
    match uu___339_54338 with
    | FStar_Const.Const_effect  -> str "Effect"
    | FStar_Const.Const_unit  -> str "()"
    | FStar_Const.Const_bool b -> FStar_Pprint.doc_of_bool b
    | FStar_Const.Const_real r -> str (Prims.op_Hat r "R")
    | FStar_Const.Const_float x -> str (FStar_Util.string_of_float x)
    | FStar_Const.Const_char x -> FStar_Pprint.doc_of_char x
    | FStar_Const.Const_string (s,uu____54350) ->
        let uu____54353 = str (FStar_String.escaped s)  in
        FStar_Pprint.dquotes uu____54353
    | FStar_Const.Const_bytearray (bytes,uu____54355) ->
        let uu____54360 =
          let uu____54361 = str (FStar_Util.string_of_bytes bytes)  in
          FStar_Pprint.dquotes uu____54361  in
        let uu____54362 = str "B"  in
        FStar_Pprint.op_Hat_Hat uu____54360 uu____54362
    | FStar_Const.Const_int (repr,sign_width_opt) ->
        let signedness uu___337_54385 =
          match uu___337_54385 with
          | FStar_Const.Unsigned  -> str "u"
          | FStar_Const.Signed  -> FStar_Pprint.empty  in
        let width uu___338_54392 =
          match uu___338_54392 with
          | FStar_Const.Int8  -> str "y"
          | FStar_Const.Int16  -> str "s"
          | FStar_Const.Int32  -> str "l"
          | FStar_Const.Int64  -> str "L"  in
        let ending =
          default_or_map FStar_Pprint.empty
            (fun uu____54407  ->
               match uu____54407 with
               | (s,w) ->
                   let uu____54414 = signedness s  in
                   let uu____54415 = width w  in
                   FStar_Pprint.op_Hat_Hat uu____54414 uu____54415)
            sign_width_opt
           in
        let uu____54416 = str repr  in
        FStar_Pprint.op_Hat_Hat uu____54416 ending
    | FStar_Const.Const_range_of  -> str "range_of"
    | FStar_Const.Const_set_range_of  -> str "set_range_of"
    | FStar_Const.Const_range r ->
        let uu____54420 = FStar_Range.string_of_range r  in str uu____54420
    | FStar_Const.Const_reify  -> str "reify"
    | FStar_Const.Const_reflect lid ->
        let uu____54424 = p_quident lid  in
        let uu____54425 =
          let uu____54426 =
            let uu____54427 = str "reflect"  in
            FStar_Pprint.op_Hat_Hat FStar_Pprint.dot uu____54427  in
          FStar_Pprint.op_Hat_Hat FStar_Pprint.qmark uu____54426  in
        FStar_Pprint.op_Hat_Hat uu____54424 uu____54425

and (p_universe : FStar_Parser_AST.term -> FStar_Pprint.document) =
  fun u  ->
    let uu____54430 = str "u#"  in
    let uu____54432 = p_atomicUniverse u  in
    FStar_Pprint.op_Hat_Hat uu____54430 uu____54432

and (p_universeFrom : FStar_Parser_AST.term -> FStar_Pprint.document) =
  fun u  ->
    match u.FStar_Parser_AST.tm with
    | FStar_Parser_AST.Op
        ({ FStar_Ident.idText = "+"; FStar_Ident.idRange = uu____54434;_},u1::u2::[])
        ->
        let uu____54440 =
          let uu____54441 = p_universeFrom u1  in
          let uu____54442 =
            let uu____54443 = p_universeFrom u2  in
            FStar_Pprint.op_Hat_Slash_Hat FStar_Pprint.plus uu____54443  in
          FStar_Pprint.op_Hat_Slash_Hat uu____54441 uu____54442  in
        FStar_Pprint.group uu____54440
    | FStar_Parser_AST.App uu____54444 ->
        let uu____54451 = head_and_args u  in
        (match uu____54451 with
         | (head1,args) ->
             (match head1.FStar_Parser_AST.tm with
              | FStar_Parser_AST.Var maybe_max_lid when
                  FStar_Ident.lid_equals maybe_max_lid
                    FStar_Parser_Const.max_lid
                  ->
                  let uu____54477 =
                    let uu____54478 = p_qlident FStar_Parser_Const.max_lid
                       in
                    let uu____54479 =
                      FStar_Pprint.separate_map FStar_Pprint.space
                        (fun uu____54487  ->
                           match uu____54487 with
                           | (u1,uu____54493) -> p_atomicUniverse u1) args
                       in
                    op_Hat_Slash_Plus_Hat uu____54478 uu____54479  in
                  FStar_Pprint.group uu____54477
              | uu____54494 ->
                  let uu____54495 =
                    let uu____54497 = FStar_Parser_AST.term_to_string u  in
                    FStar_Util.format1 "Invalid term in universe context %s"
                      uu____54497
                     in
                  failwith uu____54495))
    | uu____54500 -> p_atomicUniverse u

and (p_atomicUniverse : FStar_Parser_AST.term -> FStar_Pprint.document) =
  fun u  ->
    match u.FStar_Parser_AST.tm with
    | FStar_Parser_AST.Wild  -> FStar_Pprint.underscore
    | FStar_Parser_AST.Const (FStar_Const.Const_int (r,sw)) ->
        p_constant (FStar_Const.Const_int (r, sw))
    | FStar_Parser_AST.Uvar id1 ->
        let uu____54526 = FStar_Ident.text_of_id id1  in str uu____54526
    | FStar_Parser_AST.Paren u1 ->
        let uu____54529 = p_universeFrom u1  in
        soft_parens_with_nesting uu____54529
    | FStar_Parser_AST.Op
        ({ FStar_Ident.idText = "+"; FStar_Ident.idRange = uu____54530;_},uu____54531::uu____54532::[])
        ->
        let uu____54536 = p_universeFrom u  in
        soft_parens_with_nesting uu____54536
    | FStar_Parser_AST.App uu____54537 ->
        let uu____54544 = p_universeFrom u  in
        soft_parens_with_nesting uu____54544
    | uu____54545 ->
        let uu____54546 =
          let uu____54548 = FStar_Parser_AST.term_to_string u  in
          FStar_Util.format1 "Invalid term in universe context %s"
            uu____54548
           in
        failwith uu____54546

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
       | FStar_Parser_AST.Module (uu____54637,decls) ->
           let uu____54643 =
             FStar_All.pipe_right decls (FStar_List.map decl_to_document)  in
           FStar_All.pipe_right uu____54643
             (FStar_Pprint.separate FStar_Pprint.hardline)
       | FStar_Parser_AST.Interface (uu____54652,decls,uu____54654) ->
           let uu____54661 =
             FStar_All.pipe_right decls (FStar_List.map decl_to_document)  in
           FStar_All.pipe_right uu____54661
             (FStar_Pprint.separate FStar_Pprint.hardline)
        in
     FStar_ST.op_Colon_Equals should_print_fs_typ_app false; res)
  
let (comments_to_document :
  (Prims.string * FStar_Range.range) Prims.list -> FStar_Pprint.document) =
  fun comments  ->
    FStar_Pprint.separate_map FStar_Pprint.hardline
      (fun uu____54721  ->
         match uu____54721 with | (comment,range) -> str comment) comments
  
let (extract_decl_range : FStar_Parser_AST.decl -> decl_meta) =
  fun d  ->
    let has_qs =
      match ((d.FStar_Parser_AST.quals), (d.FStar_Parser_AST.d)) with
      | ((FStar_Parser_AST.Assumption )::[],FStar_Parser_AST.Assume
         (id1,uu____54743)) -> false
      | ([],uu____54747) -> false
      | uu____54751 -> true  in
    {
      r = (d.FStar_Parser_AST.drange);
      has_qs;
      has_attrs =
        (Prims.op_Negation (FStar_List.isEmpty d.FStar_Parser_AST.attrs));
      has_fsdoc = (FStar_Util.is_some d.FStar_Parser_AST.doc);
      is_fsdoc =
        (match d.FStar_Parser_AST.d with
         | FStar_Parser_AST.Fsdoc uu____54761 -> true
         | uu____54763 -> false)
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
        | FStar_Parser_AST.Module (uu____54806,decls) -> decls
        | FStar_Parser_AST.Interface (uu____54812,decls,uu____54814) -> decls
         in
      FStar_ST.op_Colon_Equals should_print_fs_typ_app false;
      (match decls with
       | [] -> (FStar_Pprint.empty, comments)
       | d::ds ->
           let uu____54866 =
             match ds with
             | {
                 FStar_Parser_AST.d = FStar_Parser_AST.Pragma
                   (FStar_Parser_AST.LightOff );
                 FStar_Parser_AST.drange = uu____54879;
                 FStar_Parser_AST.doc = uu____54880;
                 FStar_Parser_AST.quals = uu____54881;
                 FStar_Parser_AST.attrs = uu____54882;_}::uu____54883 ->
                 let d0 = FStar_List.hd ds  in
                 let uu____54889 =
                   let uu____54892 =
                     let uu____54895 = FStar_List.tl ds  in d :: uu____54895
                      in
                   d0 :: uu____54892  in
                 (uu____54889, (d0.FStar_Parser_AST.drange))
             | uu____54900 -> ((d :: ds), (d.FStar_Parser_AST.drange))  in
           (match uu____54866 with
            | (decls1,first_range) ->
                (FStar_ST.op_Colon_Equals comment_stack comments;
                 (let initial_comment =
                    let uu____54957 = FStar_Range.start_of_range first_range
                       in
                    place_comments_until_pos (Prims.parse_int "0")
                      (Prims.parse_int "1") uu____54957 dummy_meta
                      FStar_Pprint.empty false true
                     in
                  let doc1 =
                    separate_map_with_comments FStar_Pprint.empty
                      FStar_Pprint.empty p_decl decls1 extract_decl_range
                     in
                  let comments1 = FStar_ST.op_Bang comment_stack  in
                  FStar_ST.op_Colon_Equals comment_stack [];
                  FStar_ST.op_Colon_Equals should_print_fs_typ_app false;
                  (let uu____55066 =
                     FStar_Pprint.op_Hat_Hat initial_comment doc1  in
                   (uu____55066, comments1))))))
  