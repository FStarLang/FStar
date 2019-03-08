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
            let uu____38967 = let uu____38970 = f x  in uu____38970 :: acc
               in
            aux xs uu____38967
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
            let uu____39037 = f x  in
            (match uu____39037 with
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
          let uu____39093 = f x  in if uu____39093 then all f xs else false
  
let (all_explicit :
  (FStar_Parser_AST.term * FStar_Parser_AST.imp) Prims.list -> Prims.bool) =
  fun args  ->
    FStar_Util.for_all
      (fun uu___324_39126  ->
         match uu___324_39126 with
         | (uu____39132,FStar_Parser_AST.Nothing ) -> true
         | uu____39134 -> false) args
  
let (should_print_fs_typ_app : Prims.bool FStar_ST.ref) =
  FStar_Util.mk_ref false 
let (unfold_tuples : Prims.bool FStar_ST.ref) = FStar_Util.mk_ref true 
let with_fs_typ_app :
  'Auu____39163 'Auu____39164 .
    Prims.bool ->
      ('Auu____39163 -> 'Auu____39164) -> 'Auu____39163 -> 'Auu____39164
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
  'Auu____39274 'Auu____39275 .
    'Auu____39274 ->
      ('Auu____39275 -> 'Auu____39274) ->
        'Auu____39275 FStar_Pervasives_Native.option -> 'Auu____39274
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
  'Auu____39388 .
    FStar_Pprint.document ->
      ('Auu____39388 -> FStar_Pprint.document) ->
        'Auu____39388 Prims.list -> FStar_Pprint.document
  =
  fun sep  ->
    fun f  ->
      fun l  ->
        let uu____39413 =
          let uu____39414 =
            let uu____39415 = FStar_Pprint.op_Hat_Hat sep break1  in
            FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____39415  in
          FStar_Pprint.separate_map uu____39414 f l  in
        FStar_Pprint.group uu____39413
  
let precede_break_separate_map :
  'Auu____39427 .
    FStar_Pprint.document ->
      FStar_Pprint.document ->
        ('Auu____39427 -> FStar_Pprint.document) ->
          'Auu____39427 Prims.list -> FStar_Pprint.document
  =
  fun prec  ->
    fun sep  ->
      fun f  ->
        fun l  ->
          let uu____39457 =
            let uu____39458 = FStar_Pprint.op_Hat_Hat prec FStar_Pprint.space
               in
            let uu____39459 =
              let uu____39460 = FStar_List.hd l  in
              FStar_All.pipe_right uu____39460 f  in
            FStar_Pprint.precede uu____39458 uu____39459  in
          let uu____39461 =
            let uu____39462 = FStar_List.tl l  in
            FStar_Pprint.concat_map
              (fun x  ->
                 let uu____39468 =
                   let uu____39469 =
                     let uu____39470 = f x  in
                     FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____39470
                      in
                   FStar_Pprint.op_Hat_Hat sep uu____39469  in
                 FStar_Pprint.op_Hat_Hat break1 uu____39468) uu____39462
             in
          FStar_Pprint.op_Hat_Hat uu____39457 uu____39461
  
let concat_break_map :
  'Auu____39478 .
    ('Auu____39478 -> FStar_Pprint.document) ->
      'Auu____39478 Prims.list -> FStar_Pprint.document
  =
  fun f  ->
    fun l  ->
      let uu____39498 =
        FStar_Pprint.concat_map
          (fun x  ->
             let uu____39502 = f x  in
             FStar_Pprint.op_Hat_Hat uu____39502 break1) l
         in
      FStar_Pprint.group uu____39498
  
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
    let uu____39565 = str "begin"  in
    let uu____39567 = str "end"  in
    FStar_Pprint.soft_surround (Prims.parse_int "2") (Prims.parse_int "1")
      uu____39565 contents uu____39567
  
let separate_map_last :
  'Auu____39580 .
    FStar_Pprint.document ->
      (Prims.bool -> 'Auu____39580 -> FStar_Pprint.document) ->
        'Auu____39580 Prims.list -> FStar_Pprint.document
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
  'Auu____39632 .
    FStar_Pprint.document ->
      (Prims.bool -> 'Auu____39632 -> FStar_Pprint.document) ->
        'Auu____39632 Prims.list -> FStar_Pprint.document
  =
  fun sep  ->
    fun f  ->
      fun l  ->
        let uu____39664 =
          let uu____39665 =
            let uu____39666 = FStar_Pprint.op_Hat_Hat sep break1  in
            FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____39666  in
          separate_map_last uu____39665 f l  in
        FStar_Pprint.group uu____39664
  
let separate_map_or_flow :
  'Auu____39676 .
    FStar_Pprint.document ->
      ('Auu____39676 -> FStar_Pprint.document) ->
        'Auu____39676 Prims.list -> FStar_Pprint.document
  =
  fun sep  ->
    fun f  ->
      fun l  ->
        if (FStar_List.length l) < (Prims.parse_int "10")
        then FStar_Pprint.separate_map sep f l
        else FStar_Pprint.flow_map sep f l
  
let flow_map_last :
  'Auu____39714 .
    FStar_Pprint.document ->
      (Prims.bool -> 'Auu____39714 -> FStar_Pprint.document) ->
        'Auu____39714 Prims.list -> FStar_Pprint.document
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
  'Auu____39766 .
    FStar_Pprint.document ->
      (Prims.bool -> 'Auu____39766 -> FStar_Pprint.document) ->
        'Auu____39766 Prims.list -> FStar_Pprint.document
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
              let uu____39848 = FStar_Pprint.op_Hat_Slash_Hat doc1 doc3  in
              FStar_Pprint.group uu____39848
            else FStar_Pprint.surround n1 b doc1 doc2 doc3
  
let soft_surround_separate_map :
  'Auu____39870 .
    Prims.int ->
      Prims.int ->
        FStar_Pprint.document ->
          FStar_Pprint.document ->
            FStar_Pprint.document ->
              FStar_Pprint.document ->
                ('Auu____39870 -> FStar_Pprint.document) ->
                  'Auu____39870 Prims.list -> FStar_Pprint.document
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
                    (let uu____39929 = FStar_Pprint.separate_map sep f xs  in
                     FStar_Pprint.soft_surround n1 b opening uu____39929
                       closing)
  
let soft_surround_map_or_flow :
  'Auu____39949 .
    Prims.int ->
      Prims.int ->
        FStar_Pprint.document ->
          FStar_Pprint.document ->
            FStar_Pprint.document ->
              FStar_Pprint.document ->
                ('Auu____39949 -> FStar_Pprint.document) ->
                  'Auu____39949 Prims.list -> FStar_Pprint.document
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
                    (let uu____40008 = separate_map_or_flow sep f xs  in
                     FStar_Pprint.soft_surround n1 b opening uu____40008
                       closing)
  
let (doc_of_fsdoc :
  (Prims.string * (Prims.string * Prims.string) Prims.list) ->
    FStar_Pprint.document)
  =
  fun uu____40027  ->
    match uu____40027 with
    | (comment,keywords) ->
        let uu____40061 =
          let uu____40062 =
            let uu____40065 = str comment  in
            let uu____40066 =
              let uu____40069 =
                let uu____40072 =
                  FStar_Pprint.separate_map FStar_Pprint.comma
                    (fun uu____40083  ->
                       match uu____40083 with
                       | (k,v1) ->
                           let uu____40096 =
                             let uu____40099 = str k  in
                             let uu____40100 =
                               let uu____40103 =
                                 let uu____40106 = str v1  in [uu____40106]
                                  in
                               FStar_Pprint.rarrow :: uu____40103  in
                             uu____40099 :: uu____40100  in
                           FStar_Pprint.concat uu____40096) keywords
                   in
                [uu____40072]  in
              FStar_Pprint.space :: uu____40069  in
            uu____40065 :: uu____40066  in
          FStar_Pprint.concat uu____40062  in
        FStar_Pprint.group uu____40061
  
let (is_unit : FStar_Parser_AST.term -> Prims.bool) =
  fun e  ->
    match e.FStar_Parser_AST.tm with
    | FStar_Parser_AST.Const (FStar_Const.Const_unit ) -> true
    | uu____40116 -> false
  
let (matches_var : FStar_Parser_AST.term -> FStar_Ident.ident -> Prims.bool)
  =
  fun t  ->
    fun x  ->
      match t.FStar_Parser_AST.tm with
      | FStar_Parser_AST.Var y ->
          let uu____40132 = FStar_Ident.text_of_lid y  in
          x.FStar_Ident.idText = uu____40132
      | uu____40135 -> false
  
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
        | FStar_Parser_AST.Construct (lid,uu____40186::(e2,uu____40188)::[])
            -> (FStar_Ident.lid_equals lid cons_lid1) && (aux e2)
        | uu____40211 -> false  in
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
    | FStar_Parser_AST.Construct (uu____40235,[]) -> []
    | FStar_Parser_AST.Construct
        (uu____40246,(e1,FStar_Parser_AST.Nothing )::(e2,FStar_Parser_AST.Nothing
                                                      )::[])
        -> let uu____40267 = extract_from_list e2  in e1 :: uu____40267
    | uu____40270 ->
        let uu____40271 =
          let uu____40273 = FStar_Parser_AST.term_to_string e  in
          FStar_Util.format1 "Not a list %s" uu____40273  in
        failwith uu____40271
  
let (is_array : FStar_Parser_AST.term -> Prims.bool) =
  fun e  ->
    match e.FStar_Parser_AST.tm with
    | FStar_Parser_AST.App
        ({ FStar_Parser_AST.tm = FStar_Parser_AST.Var lid;
           FStar_Parser_AST.range = uu____40287;
           FStar_Parser_AST.level = uu____40288;_},l,FStar_Parser_AST.Nothing
         )
        ->
        (FStar_Ident.lid_equals lid FStar_Parser_Const.array_mk_array_lid) &&
          (is_list l)
    | uu____40290 -> false
  
let rec (is_ref_set : FStar_Parser_AST.term -> Prims.bool) =
  fun e  ->
    match e.FStar_Parser_AST.tm with
    | FStar_Parser_AST.Var maybe_empty_lid ->
        FStar_Ident.lid_equals maybe_empty_lid FStar_Parser_Const.set_empty
    | FStar_Parser_AST.App
        ({ FStar_Parser_AST.tm = FStar_Parser_AST.Var maybe_singleton_lid;
           FStar_Parser_AST.range = uu____40302;
           FStar_Parser_AST.level = uu____40303;_},{
                                                     FStar_Parser_AST.tm =
                                                       FStar_Parser_AST.App
                                                       ({
                                                          FStar_Parser_AST.tm
                                                            =
                                                            FStar_Parser_AST.Var
                                                            maybe_addr_of_lid;
                                                          FStar_Parser_AST.range
                                                            = uu____40305;
                                                          FStar_Parser_AST.level
                                                            = uu____40306;_},e1,FStar_Parser_AST.Nothing
                                                        );
                                                     FStar_Parser_AST.range =
                                                       uu____40308;
                                                     FStar_Parser_AST.level =
                                                       uu____40309;_},FStar_Parser_AST.Nothing
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
                FStar_Parser_AST.range = uu____40311;
                FStar_Parser_AST.level = uu____40312;_},e1,FStar_Parser_AST.Nothing
              );
           FStar_Parser_AST.range = uu____40314;
           FStar_Parser_AST.level = uu____40315;_},e2,FStar_Parser_AST.Nothing
         )
        ->
        ((FStar_Ident.lid_equals maybe_union_lid FStar_Parser_Const.set_union)
           && (is_ref_set e1))
          && (is_ref_set e2)
    | uu____40317 -> false
  
let rec (extract_from_ref_set :
  FStar_Parser_AST.term -> FStar_Parser_AST.term Prims.list) =
  fun e  ->
    match e.FStar_Parser_AST.tm with
    | FStar_Parser_AST.Var uu____40329 -> []
    | FStar_Parser_AST.App
        ({ FStar_Parser_AST.tm = FStar_Parser_AST.Var uu____40330;
           FStar_Parser_AST.range = uu____40331;
           FStar_Parser_AST.level = uu____40332;_},{
                                                     FStar_Parser_AST.tm =
                                                       FStar_Parser_AST.App
                                                       ({
                                                          FStar_Parser_AST.tm
                                                            =
                                                            FStar_Parser_AST.Var
                                                            uu____40333;
                                                          FStar_Parser_AST.range
                                                            = uu____40334;
                                                          FStar_Parser_AST.level
                                                            = uu____40335;_},e1,FStar_Parser_AST.Nothing
                                                        );
                                                     FStar_Parser_AST.range =
                                                       uu____40337;
                                                     FStar_Parser_AST.level =
                                                       uu____40338;_},FStar_Parser_AST.Nothing
         )
        -> [e1]
    | FStar_Parser_AST.App
        ({
           FStar_Parser_AST.tm = FStar_Parser_AST.App
             ({ FStar_Parser_AST.tm = FStar_Parser_AST.Var uu____40339;
                FStar_Parser_AST.range = uu____40340;
                FStar_Parser_AST.level = uu____40341;_},e1,FStar_Parser_AST.Nothing
              );
           FStar_Parser_AST.range = uu____40343;
           FStar_Parser_AST.level = uu____40344;_},e2,FStar_Parser_AST.Nothing
         )
        ->
        let uu____40346 = extract_from_ref_set e1  in
        let uu____40349 = extract_from_ref_set e2  in
        FStar_List.append uu____40346 uu____40349
    | uu____40352 ->
        let uu____40353 =
          let uu____40355 = FStar_Parser_AST.term_to_string e  in
          FStar_Util.format1 "Not a ref set %s" uu____40355  in
        failwith uu____40353
  
let (is_general_application : FStar_Parser_AST.term -> Prims.bool) =
  fun e  ->
    let uu____40367 = (is_array e) || (is_ref_set e)  in
    Prims.op_Negation uu____40367
  
let (is_general_construction : FStar_Parser_AST.term -> Prims.bool) =
  fun e  ->
    let uu____40376 = (is_list e) || (is_lex_list e)  in
    Prims.op_Negation uu____40376
  
let (is_general_prefix_op : FStar_Ident.ident -> Prims.bool) =
  fun op  ->
    let op_starting_char =
      let uu____40387 = FStar_Ident.text_of_id op  in
      FStar_Util.char_at uu____40387 (Prims.parse_int "0")  in
    ((op_starting_char = 33) || (op_starting_char = 63)) ||
      ((op_starting_char = 126) &&
         (let uu____40397 = FStar_Ident.text_of_id op  in uu____40397 <> "~"))
  
let (head_and_args :
  FStar_Parser_AST.term ->
    (FStar_Parser_AST.term * (FStar_Parser_AST.term * FStar_Parser_AST.imp)
      Prims.list))
  =
  fun e  ->
    let rec aux e1 acc =
      match e1.FStar_Parser_AST.tm with
      | FStar_Parser_AST.App (head1,arg,imp) -> aux head1 ((arg, imp) :: acc)
      | uu____40467 -> (e1, acc)  in
    aux e []
  
type associativity =
  | Left 
  | Right 
  | NonAssoc 
let (uu___is_Left : associativity -> Prims.bool) =
  fun projectee  ->
    match projectee with | Left  -> true | uu____40487 -> false
  
let (uu___is_Right : associativity -> Prims.bool) =
  fun projectee  ->
    match projectee with | Right  -> true | uu____40498 -> false
  
let (uu___is_NonAssoc : associativity -> Prims.bool) =
  fun projectee  ->
    match projectee with | NonAssoc  -> true | uu____40509 -> false
  
type token = (FStar_Char.char,Prims.string) FStar_Util.either
type associativity_level = (associativity * token Prims.list)
let (token_to_string :
  (FStar_BaseTypes.char,Prims.string) FStar_Util.either -> Prims.string) =
  fun uu___325_40535  ->
    match uu___325_40535 with
    | FStar_Util.Inl c -> Prims.op_Hat (FStar_Util.string_of_char c) ".*"
    | FStar_Util.Inr s -> s
  
let (matches_token :
  Prims.string ->
    (FStar_Char.char,Prims.string) FStar_Util.either -> Prims.bool)
  =
  fun s  ->
    fun uu___326_40570  ->
      match uu___326_40570 with
      | FStar_Util.Inl c ->
          let uu____40583 = FStar_String.get s (Prims.parse_int "0")  in
          uu____40583 = c
      | FStar_Util.Inr s' -> s = s'
  
let matches_level :
  'Auu____40599 .
    Prims.string ->
      ('Auu____40599 * (FStar_Char.char,Prims.string) FStar_Util.either
        Prims.list) -> Prims.bool
  =
  fun s  ->
    fun uu____40623  ->
      match uu____40623 with
      | (assoc_levels,tokens) ->
          let uu____40655 = FStar_List.tryFind (matches_token s) tokens  in
          uu____40655 <> FStar_Pervasives_Native.None
  
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
  let levels_from_associativity l uu___327_40827 =
    match uu___327_40827 with
    | Left  -> (l, l, (l - (Prims.parse_int "1")))
    | Right  -> ((l - (Prims.parse_int "1")), l, l)
    | NonAssoc  ->
        ((l - (Prims.parse_int "1")), l, (l - (Prims.parse_int "1")))
     in
  FStar_List.mapi
    (fun i  ->
       fun uu____40877  ->
         match uu____40877 with
         | (assoc1,tokens) -> ((levels_from_associativity i assoc1), tokens))
    level_associativity_spec
  
let (assign_levels :
  associativity_level Prims.list ->
    Prims.string -> (Prims.int * Prims.int * Prims.int))
  =
  fun token_associativity_spec  ->
    fun s  ->
      let uu____40952 = FStar_List.tryFind (matches_level s) level_table  in
      match uu____40952 with
      | FStar_Pervasives_Native.Some (assoc_levels,uu____41004) ->
          assoc_levels
      | uu____41042 -> failwith (Prims.op_Hat "Unrecognized operator " s)
  
let max_level :
  'Auu____41075 . ('Auu____41075 * token Prims.list) Prims.list -> Prims.int
  =
  fun l  ->
    let find_level_and_max n1 level =
      let uu____41124 =
        FStar_List.tryFind
          (fun uu____41160  ->
             match uu____41160 with
             | (uu____41177,tokens) ->
                 tokens = (FStar_Pervasives_Native.snd level)) level_table
         in
      match uu____41124 with
      | FStar_Pervasives_Native.Some
          ((uu____41206,l1,uu____41208),uu____41209) -> max n1 l1
      | FStar_Pervasives_Native.None  ->
          let uu____41259 =
            let uu____41261 =
              let uu____41263 =
                FStar_List.map token_to_string
                  (FStar_Pervasives_Native.snd level)
                 in
              FStar_String.concat "," uu____41263  in
            FStar_Util.format1 "Undefined associativity level %s" uu____41261
             in
          failwith uu____41259
       in
    FStar_List.fold_left find_level_and_max (Prims.parse_int "0") l
  
let (levels : Prims.string -> (Prims.int * Prims.int * Prims.int)) =
  fun op  ->
    let uu____41298 = assign_levels level_associativity_spec op  in
    match uu____41298 with
    | (left1,mine,right1) ->
        if op = "*"
        then ((left1 - (Prims.parse_int "1")), mine, right1)
        else (left1, mine, right1)
  
let (operatorInfix0ad12 : associativity_level Prims.list) =
  [opinfix0a; opinfix0b; opinfix0c; opinfix0d; opinfix1; opinfix2] 
let (is_operatorInfix0ad12 : FStar_Ident.ident -> Prims.bool) =
  fun op  ->
    let uu____41357 =
      let uu____41360 =
        let uu____41366 = FStar_Ident.text_of_id op  in
        FStar_All.pipe_left matches_level uu____41366  in
      FStar_List.tryFind uu____41360 operatorInfix0ad12  in
    uu____41357 <> FStar_Pervasives_Native.None
  
let (is_operatorInfix34 : FStar_Ident.ident -> Prims.bool) =
  let opinfix34 = [opinfix3; opinfix4]  in
  fun op  ->
    let uu____41433 =
      let uu____41448 =
        let uu____41466 = FStar_Ident.text_of_id op  in
        FStar_All.pipe_left matches_level uu____41466  in
      FStar_List.tryFind uu____41448 opinfix34  in
    uu____41433 <> FStar_Pervasives_Native.None
  
let (handleable_args_length : FStar_Ident.ident -> Prims.int) =
  fun op  ->
    let op_s = FStar_Ident.text_of_id op  in
    let uu____41532 =
      (is_general_prefix_op op) || (FStar_List.mem op_s ["-"; "~"])  in
    if uu____41532
    then (Prims.parse_int "1")
    else
      (let uu____41545 =
         ((is_operatorInfix0ad12 op) || (is_operatorInfix34 op)) ||
           (FStar_List.mem op_s
              ["<==>"; "==>"; "\\/"; "/\\"; "="; "|>"; ":="; ".()"; ".[]"])
          in
       if uu____41545
       then (Prims.parse_int "2")
       else
         if FStar_List.mem op_s [".()<-"; ".[]<-"]
         then (Prims.parse_int "3")
         else (Prims.parse_int "0"))
  
let handleable_op :
  'Auu____41591 . FStar_Ident.ident -> 'Auu____41591 Prims.list -> Prims.bool
  =
  fun op  ->
    fun args  ->
      match FStar_List.length args with
      | _41607 when _41607 = (Prims.parse_int "0") -> true
      | _41609 when _41609 = (Prims.parse_int "1") ->
          (is_general_prefix_op op) ||
            (let uu____41611 = FStar_Ident.text_of_id op  in
             FStar_List.mem uu____41611 ["-"; "~"])
      | _41619 when _41619 = (Prims.parse_int "2") ->
          ((is_operatorInfix0ad12 op) || (is_operatorInfix34 op)) ||
            (let uu____41621 = FStar_Ident.text_of_id op  in
             FStar_List.mem uu____41621
               ["<==>"; "==>"; "\\/"; "/\\"; "="; "|>"; ":="; ".()"; ".[]"])
      | _41643 when _41643 = (Prims.parse_int "3") ->
          let uu____41644 = FStar_Ident.text_of_id op  in
          FStar_List.mem uu____41644 [".()<-"; ".[]<-"]
      | uu____41652 -> false
  
type annotation_style =
  | Binders of (Prims.int * Prims.int * Prims.bool) 
  | Arrows of (Prims.int * Prims.int) 
let (uu___is_Binders : annotation_style -> Prims.bool) =
  fun projectee  ->
    match projectee with | Binders _0 -> true | uu____41698 -> false
  
let (__proj__Binders__item___0 :
  annotation_style -> (Prims.int * Prims.int * Prims.bool)) =
  fun projectee  -> match projectee with | Binders _0 -> _0 
let (uu___is_Arrows : annotation_style -> Prims.bool) =
  fun projectee  ->
    match projectee with | Arrows _0 -> true | uu____41750 -> false
  
let (__proj__Arrows__item___0 : annotation_style -> (Prims.int * Prims.int))
  = fun projectee  -> match projectee with | Arrows _0 -> _0 
let (all_binders_annot : FStar_Parser_AST.term -> Prims.bool) =
  fun e  ->
    let is_binder_annot b =
      match b.FStar_Parser_AST.b with
      | FStar_Parser_AST.Annotated uu____41792 -> true
      | uu____41798 -> false  in
    let rec all_binders e1 l =
      match e1.FStar_Parser_AST.tm with
      | FStar_Parser_AST.Product (bs,tgt) ->
          let uu____41831 = FStar_List.for_all is_binder_annot bs  in
          if uu____41831
          then all_binders tgt (l + (FStar_List.length bs))
          else (false, (Prims.parse_int "0"))
      | uu____41846 -> (true, (l + (Prims.parse_int "1")))  in
    let uu____41851 = all_binders e (Prims.parse_int "0")  in
    match uu____41851 with
    | (b,l) -> if b && (l > (Prims.parse_int "1")) then true else false
  
type catf =
  FStar_Pprint.document -> FStar_Pprint.document -> FStar_Pprint.document
let (cat_with_colon :
  FStar_Pprint.document -> FStar_Pprint.document -> FStar_Pprint.document) =
  fun x  ->
    fun y  ->
      let uu____41890 = FStar_Pprint.op_Hat_Slash_Hat FStar_Pprint.colon y
         in
      FStar_Pprint.op_Hat_Hat x uu____41890
  
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
  'Auu____42039 .
    ('Auu____42039 -> FStar_Pprint.document) ->
      'Auu____42039 -> FStar_Range.range -> FStar_Pprint.document
  =
  fun printer  ->
    fun tm  ->
      fun tmrange  ->
        let rec comments_before_pos acc print_pos lookahead_pos =
          let uu____42081 = FStar_ST.op_Bang comment_stack  in
          match uu____42081 with
          | [] -> (acc, false)
          | (c,crange)::cs ->
              let comment =
                let uu____42152 = str c  in
                FStar_Pprint.op_Hat_Hat uu____42152 FStar_Pprint.hardline  in
              let uu____42153 = FStar_Range.range_before_pos crange print_pos
                 in
              if uu____42153
              then
                (FStar_ST.op_Colon_Equals comment_stack cs;
                 (let uu____42195 = FStar_Pprint.op_Hat_Hat acc comment  in
                  comments_before_pos uu____42195 print_pos lookahead_pos))
              else
                (let uu____42198 =
                   FStar_Range.range_before_pos crange lookahead_pos  in
                 (acc, uu____42198))
           in
        let uu____42201 =
          let uu____42207 =
            let uu____42208 = FStar_Range.start_of_range tmrange  in
            FStar_Range.end_of_line uu____42208  in
          let uu____42209 = FStar_Range.end_of_range tmrange  in
          comments_before_pos FStar_Pprint.empty uu____42207 uu____42209  in
        match uu____42201 with
        | (comments,has_lookahead) ->
            let printed_e = printer tm  in
            let comments1 =
              if has_lookahead
              then
                let pos = FStar_Range.end_of_range tmrange  in
                let uu____42218 = comments_before_pos comments pos pos  in
                FStar_Pervasives_Native.fst uu____42218
              else comments  in
            if comments1 = FStar_Pprint.empty
            then printed_e
            else
              (let uu____42230 = FStar_Pprint.op_Hat_Hat comments1 printed_e
                  in
               FStar_Pprint.group uu____42230)
  
let with_comment_sep :
  'Auu____42242 'Auu____42243 .
    ('Auu____42242 -> 'Auu____42243) ->
      'Auu____42242 ->
        FStar_Range.range -> (FStar_Pprint.document * 'Auu____42243)
  =
  fun printer  ->
    fun tm  ->
      fun tmrange  ->
        let rec comments_before_pos acc print_pos lookahead_pos =
          let uu____42289 = FStar_ST.op_Bang comment_stack  in
          match uu____42289 with
          | [] -> (acc, false)
          | (c,crange)::cs ->
              let comment = str c  in
              let uu____42360 = FStar_Range.range_before_pos crange print_pos
                 in
              if uu____42360
              then
                (FStar_ST.op_Colon_Equals comment_stack cs;
                 (let uu____42402 =
                    if acc = FStar_Pprint.empty
                    then comment
                    else
                      (let uu____42406 =
                         FStar_Pprint.op_Hat_Hat FStar_Pprint.hardline
                           comment
                          in
                       FStar_Pprint.op_Hat_Hat acc uu____42406)
                     in
                  comments_before_pos uu____42402 print_pos lookahead_pos))
              else
                (let uu____42409 =
                   FStar_Range.range_before_pos crange lookahead_pos  in
                 (acc, uu____42409))
           in
        let uu____42412 =
          let uu____42418 =
            let uu____42419 = FStar_Range.start_of_range tmrange  in
            FStar_Range.end_of_line uu____42419  in
          let uu____42420 = FStar_Range.end_of_range tmrange  in
          comments_before_pos FStar_Pprint.empty uu____42418 uu____42420  in
        match uu____42412 with
        | (comments,has_lookahead) ->
            let printed_e = printer tm  in
            let comments1 =
              if has_lookahead
              then
                let pos = FStar_Range.end_of_range tmrange  in
                let uu____42433 = comments_before_pos comments pos pos  in
                FStar_Pervasives_Native.fst uu____42433
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
                let uu____42486 = FStar_ST.op_Bang comment_stack  in
                match uu____42486 with
                | (comment,crange)::cs when
                    FStar_Range.range_before_pos crange pos ->
                    (FStar_ST.op_Colon_Equals comment_stack cs;
                     (let lnum =
                        let uu____42580 =
                          let uu____42582 =
                            let uu____42584 =
                              FStar_Range.start_of_range crange  in
                            FStar_Range.line_of_pos uu____42584  in
                          uu____42582 - lbegin  in
                        max k uu____42580  in
                      let lnum1 = min (Prims.parse_int "2") lnum  in
                      let doc2 =
                        let uu____42589 =
                          let uu____42590 =
                            FStar_Pprint.repeat lnum1 FStar_Pprint.hardline
                             in
                          let uu____42591 = str comment  in
                          FStar_Pprint.op_Hat_Hat uu____42590 uu____42591  in
                        FStar_Pprint.op_Hat_Hat doc1 uu____42589  in
                      let uu____42592 =
                        let uu____42594 = FStar_Range.end_of_range crange  in
                        FStar_Range.line_of_pos uu____42594  in
                      place_comments_until_pos (Prims.parse_int "1")
                        uu____42592 pos meta_decl doc2 true init1))
                | uu____42597 ->
                    if doc1 = FStar_Pprint.empty
                    then FStar_Pprint.empty
                    else
                      (let lnum =
                         let uu____42610 = FStar_Range.line_of_pos pos  in
                         uu____42610 - lbegin  in
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
                       let uu____42652 =
                         FStar_Pprint.repeat lnum7 FStar_Pprint.hardline  in
                       FStar_Pprint.op_Hat_Hat doc1 uu____42652)
  
let separate_map_with_comments :
  'Auu____42666 .
    FStar_Pprint.document ->
      FStar_Pprint.document ->
        ('Auu____42666 -> FStar_Pprint.document) ->
          'Auu____42666 Prims.list ->
            ('Auu____42666 -> decl_meta) -> FStar_Pprint.document
  =
  fun prefix1  ->
    fun sep  ->
      fun f  ->
        fun xs  ->
          fun extract_meta  ->
            let fold_fun uu____42725 x =
              match uu____42725 with
              | (last_line,doc1) ->
                  let meta_decl = extract_meta x  in
                  let r = meta_decl.r  in
                  let doc2 =
                    let uu____42744 = FStar_Range.start_of_range r  in
                    place_comments_until_pos (Prims.parse_int "1") last_line
                      uu____42744 meta_decl doc1 false false
                     in
                  let uu____42748 =
                    let uu____42750 = FStar_Range.end_of_range r  in
                    FStar_Range.line_of_pos uu____42750  in
                  let uu____42751 =
                    let uu____42752 =
                      let uu____42753 = f x  in
                      FStar_Pprint.op_Hat_Hat sep uu____42753  in
                    FStar_Pprint.op_Hat_Hat doc2 uu____42752  in
                  (uu____42748, uu____42751)
               in
            let uu____42755 =
              let uu____42762 = FStar_List.hd xs  in
              let uu____42763 = FStar_List.tl xs  in
              (uu____42762, uu____42763)  in
            match uu____42755 with
            | (x,xs1) ->
                let init1 =
                  let meta_decl = extract_meta x  in
                  let uu____42781 =
                    let uu____42783 = FStar_Range.end_of_range meta_decl.r
                       in
                    FStar_Range.line_of_pos uu____42783  in
                  let uu____42784 =
                    let uu____42785 = f x  in
                    FStar_Pprint.op_Hat_Hat prefix1 uu____42785  in
                  (uu____42781, uu____42784)  in
                let uu____42787 = FStar_List.fold_left fold_fun init1 xs1  in
                FStar_Pervasives_Native.snd uu____42787
  
let separate_map_with_comments_kw :
  'Auu____42814 'Auu____42815 .
    'Auu____42814 ->
      'Auu____42814 ->
        ('Auu____42814 -> 'Auu____42815 -> FStar_Pprint.document) ->
          'Auu____42815 Prims.list ->
            ('Auu____42815 -> decl_meta) -> FStar_Pprint.document
  =
  fun prefix1  ->
    fun sep  ->
      fun f  ->
        fun xs  ->
          fun extract_meta  ->
            let fold_fun uu____42879 x =
              match uu____42879 with
              | (last_line,doc1) ->
                  let meta_decl = extract_meta x  in
                  let r = meta_decl.r  in
                  let doc2 =
                    let uu____42898 = FStar_Range.start_of_range r  in
                    place_comments_until_pos (Prims.parse_int "1") last_line
                      uu____42898 meta_decl doc1 false false
                     in
                  let uu____42902 =
                    let uu____42904 = FStar_Range.end_of_range r  in
                    FStar_Range.line_of_pos uu____42904  in
                  let uu____42905 =
                    let uu____42906 = f sep x  in
                    FStar_Pprint.op_Hat_Hat doc2 uu____42906  in
                  (uu____42902, uu____42905)
               in
            let uu____42908 =
              let uu____42915 = FStar_List.hd xs  in
              let uu____42916 = FStar_List.tl xs  in
              (uu____42915, uu____42916)  in
            match uu____42908 with
            | (x,xs1) ->
                let init1 =
                  let meta_decl = extract_meta x  in
                  let uu____42934 =
                    let uu____42936 = FStar_Range.end_of_range meta_decl.r
                       in
                    FStar_Range.line_of_pos uu____42936  in
                  let uu____42937 = f prefix1 x  in
                  (uu____42934, uu____42937)  in
                let uu____42939 = FStar_List.fold_left fold_fun init1 xs1  in
                FStar_Pervasives_Native.snd uu____42939
  
let rec (p_decl : FStar_Parser_AST.decl -> FStar_Pprint.document) =
  fun d  ->
    let qualifiers =
      match ((d.FStar_Parser_AST.quals), (d.FStar_Parser_AST.d)) with
      | ((FStar_Parser_AST.Assumption )::[],FStar_Parser_AST.Assume
         (id1,uu____43925)) ->
          let uu____43928 =
            let uu____43930 =
              FStar_Util.char_at id1.FStar_Ident.idText (Prims.parse_int "0")
               in
            FStar_All.pipe_right uu____43930 FStar_Util.is_upper  in
          if uu____43928
          then
            let uu____43936 = p_qualifier FStar_Parser_AST.Assumption  in
            FStar_Pprint.op_Hat_Hat uu____43936 FStar_Pprint.space
          else p_qualifiers d.FStar_Parser_AST.quals
      | uu____43939 -> p_qualifiers d.FStar_Parser_AST.quals  in
    let uu____43946 =
      FStar_Pprint.optional (fun d1  -> p_fsdoc d1) d.FStar_Parser_AST.doc
       in
    let uu____43949 =
      let uu____43950 = p_attributes d.FStar_Parser_AST.attrs  in
      let uu____43951 =
        let uu____43952 = p_rawDecl d  in
        FStar_Pprint.op_Hat_Hat qualifiers uu____43952  in
      FStar_Pprint.op_Hat_Hat uu____43950 uu____43951  in
    FStar_Pprint.op_Hat_Hat uu____43946 uu____43949

and (p_attributes : FStar_Parser_AST.attributes_ -> FStar_Pprint.document) =
  fun attrs  ->
    match attrs with
    | [] -> FStar_Pprint.empty
    | uu____43954 ->
        let uu____43955 =
          let uu____43956 = str "@ "  in
          let uu____43958 =
            let uu____43959 =
              let uu____43960 =
                let uu____43961 =
                  let uu____43962 = FStar_List.map p_atomicTerm attrs  in
                  FStar_Pprint.flow break1 uu____43962  in
                FStar_Pprint.op_Hat_Hat uu____43961 FStar_Pprint.rbracket  in
              FStar_Pprint.align uu____43960  in
            FStar_Pprint.op_Hat_Hat uu____43959 FStar_Pprint.hardline  in
          FStar_Pprint.op_Hat_Hat uu____43956 uu____43958  in
        FStar_Pprint.op_Hat_Hat FStar_Pprint.lbracket uu____43955

and (p_fsdoc : FStar_Parser_AST.fsdoc -> FStar_Pprint.document) =
  fun uu____43965  ->
    match uu____43965 with
    | (doc1,kwd_args) ->
        let kwd_args_doc =
          match kwd_args with
          | [] -> FStar_Pprint.empty
          | kwd_args1 ->
              let process_kwd_arg uu____44013 =
                match uu____44013 with
                | (kwd,arg) ->
                    let uu____44026 = str "@"  in
                    let uu____44028 =
                      let uu____44029 = str kwd  in
                      let uu____44030 =
                        let uu____44031 = str arg  in
                        FStar_Pprint.op_Hat_Hat FStar_Pprint.space
                          uu____44031
                         in
                      FStar_Pprint.op_Hat_Hat uu____44029 uu____44030  in
                    FStar_Pprint.op_Hat_Hat uu____44026 uu____44028
                 in
              let uu____44032 =
                FStar_Pprint.separate_map FStar_Pprint.hardline
                  process_kwd_arg kwd_args1
                 in
              FStar_Pprint.op_Hat_Hat uu____44032 FStar_Pprint.hardline
           in
        let uu____44039 =
          let uu____44040 =
            let uu____44041 =
              let uu____44042 = str doc1  in
              let uu____44043 =
                let uu____44044 =
                  let uu____44045 =
                    FStar_Pprint.op_Hat_Hat FStar_Pprint.rparen
                      FStar_Pprint.hardline
                     in
                  FStar_Pprint.op_Hat_Hat FStar_Pprint.star uu____44045  in
                FStar_Pprint.op_Hat_Hat kwd_args_doc uu____44044  in
              FStar_Pprint.op_Hat_Hat uu____44042 uu____44043  in
            FStar_Pprint.op_Hat_Hat FStar_Pprint.star uu____44041  in
          FStar_Pprint.op_Hat_Hat FStar_Pprint.star uu____44040  in
        FStar_Pprint.op_Hat_Hat FStar_Pprint.lparen uu____44039

and (p_justSig : FStar_Parser_AST.decl -> FStar_Pprint.document) =
  fun d  ->
    match d.FStar_Parser_AST.d with
    | FStar_Parser_AST.Val (lid,t) ->
        let uu____44049 =
          let uu____44050 = str "val"  in
          let uu____44052 =
            let uu____44053 =
              let uu____44054 = p_lident lid  in
              let uu____44055 =
                FStar_Pprint.op_Hat_Hat FStar_Pprint.space FStar_Pprint.colon
                 in
              FStar_Pprint.op_Hat_Hat uu____44054 uu____44055  in
            FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____44053  in
          FStar_Pprint.op_Hat_Hat uu____44050 uu____44052  in
        let uu____44056 = p_typ false false t  in
        FStar_Pprint.op_Hat_Hat uu____44049 uu____44056
    | FStar_Parser_AST.TopLevelLet (uu____44059,lbs) ->
        FStar_Pprint.separate_map FStar_Pprint.hardline
          (fun lb  ->
             let uu____44084 =
               let uu____44085 = str "let"  in p_letlhs uu____44085 lb false
                in
             FStar_Pprint.group uu____44084) lbs
    | uu____44088 -> FStar_Pprint.empty

and (p_list :
  (FStar_Ident.ident -> FStar_Pprint.document) ->
    FStar_Pprint.document ->
      FStar_Ident.ident Prims.list -> FStar_Pprint.document)
  =
  fun f  ->
    fun sep  ->
      fun l  ->
        let rec p_list' uu___328_44103 =
          match uu___328_44103 with
          | [] -> FStar_Pprint.empty
          | x::[] -> f x
          | x::xs ->
              let uu____44111 = f x  in
              let uu____44112 =
                let uu____44113 = p_list' xs  in
                FStar_Pprint.op_Hat_Hat sep uu____44113  in
              FStar_Pprint.op_Hat_Hat uu____44111 uu____44112
           in
        let uu____44114 = str "["  in
        let uu____44116 =
          let uu____44117 = p_list' l  in
          let uu____44118 = str "]"  in
          FStar_Pprint.op_Hat_Hat uu____44117 uu____44118  in
        FStar_Pprint.op_Hat_Hat uu____44114 uu____44116

and (p_rawDecl : FStar_Parser_AST.decl -> FStar_Pprint.document) =
  fun d  ->
    match d.FStar_Parser_AST.d with
    | FStar_Parser_AST.Open uid ->
        let uu____44122 =
          let uu____44123 = str "open"  in
          let uu____44125 = p_quident uid  in
          FStar_Pprint.op_Hat_Slash_Hat uu____44123 uu____44125  in
        FStar_Pprint.group uu____44122
    | FStar_Parser_AST.Include uid ->
        let uu____44127 =
          let uu____44128 = str "include"  in
          let uu____44130 = p_quident uid  in
          FStar_Pprint.op_Hat_Slash_Hat uu____44128 uu____44130  in
        FStar_Pprint.group uu____44127
    | FStar_Parser_AST.Friend uid ->
        let uu____44132 =
          let uu____44133 = str "friend"  in
          let uu____44135 = p_quident uid  in
          FStar_Pprint.op_Hat_Slash_Hat uu____44133 uu____44135  in
        FStar_Pprint.group uu____44132
    | FStar_Parser_AST.ModuleAbbrev (uid1,uid2) ->
        let uu____44138 =
          let uu____44139 = str "module"  in
          let uu____44141 =
            let uu____44142 =
              let uu____44143 = p_uident uid1  in
              let uu____44144 =
                FStar_Pprint.op_Hat_Hat FStar_Pprint.space
                  FStar_Pprint.equals
                 in
              FStar_Pprint.op_Hat_Hat uu____44143 uu____44144  in
            FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____44142  in
          FStar_Pprint.op_Hat_Hat uu____44139 uu____44141  in
        let uu____44145 = p_quident uid2  in
        op_Hat_Slash_Plus_Hat uu____44138 uu____44145
    | FStar_Parser_AST.TopLevelModule uid ->
        let uu____44147 =
          let uu____44148 = str "module"  in
          let uu____44150 =
            let uu____44151 = p_quident uid  in
            FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____44151  in
          FStar_Pprint.op_Hat_Hat uu____44148 uu____44150  in
        FStar_Pprint.group uu____44147
    | FStar_Parser_AST.Tycon
        (true
         ,uu____44152,(FStar_Parser_AST.TyconAbbrev
                       (uid,tpars,FStar_Pervasives_Native.None ,t),FStar_Pervasives_Native.None
                       )::[])
        ->
        let effect_prefix_doc =
          let uu____44189 = str "effect"  in
          let uu____44191 =
            let uu____44192 = p_uident uid  in
            FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____44192  in
          FStar_Pprint.op_Hat_Hat uu____44189 uu____44191  in
        let uu____44193 =
          let uu____44194 = p_typars tpars  in
          FStar_Pprint.surround (Prims.parse_int "2") (Prims.parse_int "1")
            effect_prefix_doc uu____44194 FStar_Pprint.equals
           in
        let uu____44197 = p_typ false false t  in
        op_Hat_Slash_Plus_Hat uu____44193 uu____44197
    | FStar_Parser_AST.Tycon (false ,tc,tcdefs) ->
        let s = if tc then str "class" else str "type"  in
        let uu____44228 =
          let uu____44229 = FStar_List.hd tcdefs  in
          p_fsdocTypeDeclPairs s uu____44229  in
        let uu____44242 =
          let uu____44243 = FStar_List.tl tcdefs  in
          FStar_All.pipe_left
            (FStar_Pprint.concat_map
               (fun x  ->
                  let uu____44281 =
                    let uu____44282 = str "and"  in
                    p_fsdocTypeDeclPairs uu____44282 x  in
                  FStar_Pprint.op_Hat_Hat break1 uu____44281)) uu____44243
           in
        FStar_Pprint.op_Hat_Hat uu____44228 uu____44242
    | FStar_Parser_AST.TopLevelLet (q,lbs) ->
        let let_doc =
          let uu____44299 = str "let"  in
          let uu____44301 = p_letqualifier q  in
          FStar_Pprint.op_Hat_Hat uu____44299 uu____44301  in
        let uu____44302 = str "and"  in
        separate_map_with_comments_kw let_doc uu____44302 p_letbinding lbs
          (fun uu____44312  ->
             match uu____44312 with
             | (p,t) ->
                 let uu____44319 =
                   FStar_Range.union_ranges p.FStar_Parser_AST.prange
                     t.FStar_Parser_AST.range
                    in
                 {
                   r = uu____44319;
                   has_qs = false;
                   has_attrs = false;
                   has_fsdoc = (FStar_Util.is_some d.FStar_Parser_AST.doc);
                   is_fsdoc = false
                 })
    | FStar_Parser_AST.Val (lid,t) ->
        let uu____44325 =
          let uu____44326 = str "val"  in
          let uu____44328 =
            let uu____44329 =
              let uu____44330 = p_lident lid  in
              let uu____44331 = sig_as_binders_if_possible t false  in
              FStar_Pprint.op_Hat_Hat uu____44330 uu____44331  in
            FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____44329  in
          FStar_Pprint.op_Hat_Hat uu____44326 uu____44328  in
        FStar_All.pipe_left FStar_Pprint.group uu____44325
    | FStar_Parser_AST.Assume (id1,t) ->
        let decl_keyword =
          let uu____44336 =
            let uu____44338 =
              FStar_Util.char_at id1.FStar_Ident.idText (Prims.parse_int "0")
               in
            FStar_All.pipe_right uu____44338 FStar_Util.is_upper  in
          if uu____44336
          then FStar_Pprint.empty
          else
            (let uu____44346 = str "val"  in
             FStar_Pprint.op_Hat_Hat uu____44346 FStar_Pprint.space)
           in
        let uu____44348 =
          let uu____44349 = p_ident id1  in
          let uu____44350 =
            let uu____44351 =
              let uu____44352 =
                let uu____44353 = p_typ false false t  in
                FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____44353  in
              FStar_Pprint.op_Hat_Hat FStar_Pprint.colon uu____44352  in
            FStar_Pprint.group uu____44351  in
          FStar_Pprint.op_Hat_Hat uu____44349 uu____44350  in
        FStar_Pprint.op_Hat_Hat decl_keyword uu____44348
    | FStar_Parser_AST.Exception (uid,t_opt) ->
        let uu____44362 = str "exception"  in
        let uu____44364 =
          let uu____44365 =
            let uu____44366 = p_uident uid  in
            let uu____44367 =
              FStar_Pprint.optional
                (fun t  ->
                   let uu____44371 =
                     let uu____44372 = str "of"  in
                     let uu____44374 = p_typ false false t  in
                     op_Hat_Slash_Plus_Hat uu____44372 uu____44374  in
                   FStar_Pprint.op_Hat_Hat break1 uu____44371) t_opt
               in
            FStar_Pprint.op_Hat_Hat uu____44366 uu____44367  in
          FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____44365  in
        FStar_Pprint.op_Hat_Hat uu____44362 uu____44364
    | FStar_Parser_AST.NewEffect ne ->
        let uu____44378 = str "new_effect"  in
        let uu____44380 =
          let uu____44381 = p_newEffect ne  in
          FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____44381  in
        FStar_Pprint.op_Hat_Hat uu____44378 uu____44380
    | FStar_Parser_AST.SubEffect se ->
        let uu____44383 = str "sub_effect"  in
        let uu____44385 =
          let uu____44386 = p_subEffect se  in
          FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____44386  in
        FStar_Pprint.op_Hat_Hat uu____44383 uu____44385
    | FStar_Parser_AST.Pragma p -> p_pragma p
    | FStar_Parser_AST.Fsdoc doc1 -> p_fsdoc doc1
    | FStar_Parser_AST.Main uu____44389 ->
        failwith "*Main declaration* : Is that really still in use ??"
    | FStar_Parser_AST.Tycon (true ,uu____44391,uu____44392) ->
        failwith
          "Effect abbreviation is expected to be defined by an abbreviation"
    | FStar_Parser_AST.Splice (ids,t) ->
        let uu____44420 = str "%splice"  in
        let uu____44422 =
          let uu____44423 =
            let uu____44424 = str ";"  in p_list p_uident uu____44424 ids  in
          let uu____44426 =
            let uu____44427 = p_term false false t  in
            FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____44427  in
          FStar_Pprint.op_Hat_Hat uu____44423 uu____44426  in
        FStar_Pprint.op_Hat_Hat uu____44420 uu____44422

and (p_pragma : FStar_Parser_AST.pragma -> FStar_Pprint.document) =
  fun uu___329_44430  ->
    match uu___329_44430 with
    | FStar_Parser_AST.SetOptions s ->
        let uu____44433 = str "#set-options"  in
        let uu____44435 =
          let uu____44436 =
            let uu____44437 = str s  in FStar_Pprint.dquotes uu____44437  in
          FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____44436  in
        FStar_Pprint.op_Hat_Hat uu____44433 uu____44435
    | FStar_Parser_AST.ResetOptions s_opt ->
        let uu____44442 = str "#reset-options"  in
        let uu____44444 =
          FStar_Pprint.optional
            (fun s  ->
               let uu____44450 =
                 let uu____44451 = str s  in FStar_Pprint.dquotes uu____44451
                  in
               FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____44450) s_opt
           in
        FStar_Pprint.op_Hat_Hat uu____44442 uu____44444
    | FStar_Parser_AST.PushOptions s_opt ->
        let uu____44456 = str "#push-options"  in
        let uu____44458 =
          FStar_Pprint.optional
            (fun s  ->
               let uu____44464 =
                 let uu____44465 = str s  in FStar_Pprint.dquotes uu____44465
                  in
               FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____44464) s_opt
           in
        FStar_Pprint.op_Hat_Hat uu____44456 uu____44458
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
    fun uu____44496  ->
      match uu____44496 with
      | (typedecl,fsdoc_opt) ->
          let uu____44509 = p_typeDecl (kw, fsdoc_opt) typedecl  in
          (match uu____44509 with
           | (comm,decl,body,pre) ->
               if comm = FStar_Pprint.empty
               then
                 let uu____44534 = pre body  in
                 FStar_Pprint.op_Hat_Hat decl uu____44534
               else
                 (let uu____44537 =
                    let uu____44538 =
                      let uu____44539 =
                        let uu____44540 = pre body  in
                        FStar_Pprint.op_Hat_Slash_Hat uu____44540 comm  in
                      FStar_Pprint.op_Hat_Hat decl uu____44539  in
                    let uu____44541 =
                      let uu____44542 =
                        let uu____44543 =
                          let uu____44544 =
                            let uu____44545 =
                              FStar_Pprint.op_Hat_Hat FStar_Pprint.hardline
                                body
                               in
                            FStar_Pprint.op_Hat_Hat comm uu____44545  in
                          FStar_Pprint.op_Hat_Hat FStar_Pprint.hardline
                            uu____44544
                           in
                        FStar_Pprint.nest (Prims.parse_int "2") uu____44543
                         in
                      FStar_Pprint.op_Hat_Hat decl uu____44542  in
                    FStar_Pprint.ifflat uu____44538 uu____44541  in
                  FStar_All.pipe_left FStar_Pprint.group uu____44537))

and (p_typeDecl :
  (FStar_Pprint.document * FStar_Parser_AST.fsdoc
    FStar_Pervasives_Native.option) ->
    FStar_Parser_AST.tycon ->
      (FStar_Pprint.document * FStar_Pprint.document * FStar_Pprint.document
        * (FStar_Pprint.document -> FStar_Pprint.document)))
  =
  fun pre  ->
    fun uu___330_44548  ->
      match uu___330_44548 with
      | FStar_Parser_AST.TyconAbstract (lid,bs,typ_opt) ->
          let uu____44577 = p_typeDeclPrefix pre false lid bs typ_opt  in
          (FStar_Pprint.empty, uu____44577, FStar_Pprint.empty,
            FStar_Pervasives.id)
      | FStar_Parser_AST.TyconAbbrev (lid,bs,typ_opt,t) ->
          let uu____44594 = p_typ_sep false false t  in
          (match uu____44594 with
           | (comm,doc1) ->
               let uu____44614 = p_typeDeclPrefix pre true lid bs typ_opt  in
               (comm, uu____44614, doc1, jump2))
      | FStar_Parser_AST.TyconRecord (lid,bs,typ_opt,record_field_decls) ->
          let p_recordFieldAndComments ps uu____44670 =
            match uu____44670 with
            | (lid1,t,doc_opt) ->
                let uu____44687 =
                  let uu____44692 =
                    FStar_Range.extend_to_end_of_line
                      t.FStar_Parser_AST.range
                     in
                  with_comment_sep (p_recordFieldDecl ps) (lid1, t, doc_opt)
                    uu____44692
                   in
                (match uu____44687 with
                 | (comm,field) ->
                     let sep =
                       if ps then FStar_Pprint.semi else FStar_Pprint.empty
                        in
                     inline_comment_or_above comm field sep)
             in
          let p_fields =
            let uu____44710 =
              separate_map_last FStar_Pprint.hardline
                p_recordFieldAndComments record_field_decls
               in
            braces_with_nesting uu____44710  in
          let uu____44719 = p_typeDeclPrefix pre true lid bs typ_opt  in
          (FStar_Pprint.empty, uu____44719, p_fields,
            ((fun d  -> FStar_Pprint.op_Hat_Hat FStar_Pprint.space d)))
      | FStar_Parser_AST.TyconVariant (lid,bs,typ_opt,ct_decls) ->
          let p_constructorBranchAndComments uu____44786 =
            match uu____44786 with
            | (uid,t_opt,doc_opt,use_of) ->
                let range =
                  let uu____44815 =
                    let uu____44816 =
                      FStar_Util.map_opt t_opt
                        (fun t  -> t.FStar_Parser_AST.range)
                       in
                    FStar_Util.dflt uid.FStar_Ident.idRange uu____44816  in
                  FStar_Range.extend_to_end_of_line uu____44815  in
                let uu____44821 =
                  with_comment_sep p_constructorBranch
                    (uid, t_opt, doc_opt, use_of) range
                   in
                (match uu____44821 with
                 | (comm,ctor) ->
                     inline_comment_or_above comm ctor FStar_Pprint.empty)
             in
          let datacon_doc =
            FStar_Pprint.separate_map FStar_Pprint.hardline
              p_constructorBranchAndComments ct_decls
             in
          let uu____44860 = p_typeDeclPrefix pre true lid bs typ_opt  in
          (FStar_Pprint.empty, uu____44860, datacon_doc, jump2)

and (p_typeDeclPrefix :
  (FStar_Pprint.document * FStar_Parser_AST.fsdoc
    FStar_Pervasives_Native.option) ->
    Prims.bool ->
      FStar_Ident.ident ->
        FStar_Parser_AST.binder Prims.list ->
          FStar_Parser_AST.knd FStar_Pervasives_Native.option ->
            FStar_Pprint.document)
  =
  fun uu____44865  ->
    fun eq1  ->
      fun lid  ->
        fun bs  ->
          fun typ_opt  ->
            match uu____44865 with
            | (kw,fsdoc_opt) ->
                let maybe_with_fsdoc cont =
                  let lid_doc = p_ident lid  in
                  let kw_lid =
                    let uu____44900 =
                      FStar_Pprint.op_Hat_Slash_Hat kw lid_doc  in
                    FStar_Pprint.group uu____44900  in
                  match fsdoc_opt with
                  | FStar_Pervasives_Native.None  -> cont kw_lid
                  | FStar_Pervasives_Native.Some fsdoc ->
                      let uu____44902 =
                        let uu____44905 =
                          let uu____44908 = p_fsdoc fsdoc  in
                          let uu____44909 =
                            let uu____44912 = cont lid_doc  in [uu____44912]
                             in
                          uu____44908 :: uu____44909  in
                        kw :: uu____44905  in
                      FStar_Pprint.separate FStar_Pprint.hardline uu____44902
                   in
                let typ =
                  let maybe_eq =
                    if eq1 then FStar_Pprint.equals else FStar_Pprint.empty
                     in
                  match typ_opt with
                  | FStar_Pervasives_Native.None  -> maybe_eq
                  | FStar_Pervasives_Native.Some t ->
                      let uu____44919 =
                        let uu____44920 =
                          let uu____44921 = p_typ false false t  in
                          FStar_Pprint.op_Hat_Slash_Hat uu____44921 maybe_eq
                           in
                        FStar_Pprint.op_Hat_Hat FStar_Pprint.space
                          uu____44920
                         in
                      FStar_Pprint.op_Hat_Hat FStar_Pprint.colon uu____44919
                   in
                if bs = []
                then maybe_with_fsdoc (fun n1  -> prefix2 n1 typ)
                else
                  (let binders = p_binders_list true bs  in
                   maybe_with_fsdoc
                     (fun n1  ->
                        let uu____44941 =
                          let uu____44942 = FStar_Pprint.flow break1 binders
                             in
                          prefix2 n1 uu____44942  in
                        prefix2 uu____44941 typ))

and (p_recordFieldDecl :
  Prims.bool ->
    (FStar_Ident.ident * FStar_Parser_AST.term * FStar_Parser_AST.fsdoc
      FStar_Pervasives_Native.option) -> FStar_Pprint.document)
  =
  fun ps  ->
    fun uu____44944  ->
      match uu____44944 with
      | (lid,t,doc_opt) ->
          let uu____44961 =
            let uu____44962 = FStar_Pprint.optional p_fsdoc doc_opt  in
            let uu____44963 =
              let uu____44964 = p_lident lid  in
              let uu____44965 =
                let uu____44966 = p_typ ps false t  in
                FStar_Pprint.op_Hat_Hat FStar_Pprint.colon uu____44966  in
              FStar_Pprint.op_Hat_Hat uu____44964 uu____44965  in
            FStar_Pprint.op_Hat_Hat uu____44962 uu____44963  in
          FStar_Pprint.group uu____44961

and (p_constructorBranch :
  (FStar_Ident.ident * FStar_Parser_AST.term FStar_Pervasives_Native.option *
    FStar_Parser_AST.fsdoc FStar_Pervasives_Native.option * Prims.bool) ->
    FStar_Pprint.document)
  =
  fun uu____44968  ->
    match uu____44968 with
    | (uid,t_opt,doc_opt,use_of) ->
        let sep = if use_of then str "of" else FStar_Pprint.colon  in
        let uid_doc =
          let uu____45002 =
            let uu____45003 =
              let uu____45004 = p_uident uid  in
              FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____45004  in
            FStar_Pprint.op_Hat_Hat FStar_Pprint.bar uu____45003  in
          FStar_Pprint.group uu____45002  in
        let uu____45005 = FStar_Pprint.optional p_fsdoc doc_opt  in
        let uu____45006 =
          default_or_map uid_doc
            (fun t  ->
               let uu____45010 =
                 let uu____45011 =
                   let uu____45012 =
                     let uu____45013 =
                       let uu____45014 = p_typ false false t  in
                       FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____45014
                        in
                     FStar_Pprint.op_Hat_Hat sep uu____45013  in
                   FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____45012  in
                 FStar_Pprint.op_Hat_Hat uid_doc uu____45011  in
               FStar_Pprint.group uu____45010) t_opt
           in
        FStar_Pprint.op_Hat_Hat uu____45005 uu____45006

and (p_letlhs :
  FStar_Pprint.document ->
    (FStar_Parser_AST.pattern * FStar_Parser_AST.term) ->
      Prims.bool -> FStar_Pprint.document)
  =
  fun kw  ->
    fun uu____45018  ->
      fun inner_let  ->
        match uu____45018 with
        | (pat,uu____45026) ->
            let uu____45027 =
              match pat.FStar_Parser_AST.pat with
              | FStar_Parser_AST.PatAscribed
                  (pat1,(t,FStar_Pervasives_Native.None )) ->
                  (pat1,
                    (FStar_Pervasives_Native.Some (t, FStar_Pprint.empty)))
              | FStar_Parser_AST.PatAscribed
                  (pat1,(t,FStar_Pervasives_Native.Some tac)) ->
                  let uu____45079 =
                    let uu____45086 =
                      let uu____45091 =
                        let uu____45092 =
                          let uu____45093 =
                            let uu____45094 = str "by"  in
                            let uu____45096 =
                              let uu____45097 = p_atomicTerm tac  in
                              FStar_Pprint.op_Hat_Hat FStar_Pprint.space
                                uu____45097
                               in
                            FStar_Pprint.op_Hat_Hat uu____45094 uu____45096
                             in
                          FStar_Pprint.op_Hat_Hat FStar_Pprint.space
                            uu____45093
                           in
                        FStar_Pprint.group uu____45092  in
                      (t, uu____45091)  in
                    FStar_Pervasives_Native.Some uu____45086  in
                  (pat1, uu____45079)
              | uu____45108 -> (pat, FStar_Pervasives_Native.None)  in
            (match uu____45027 with
             | (pat1,ascr) ->
                 (match pat1.FStar_Parser_AST.pat with
                  | FStar_Parser_AST.PatApp
                      ({
                         FStar_Parser_AST.pat = FStar_Parser_AST.PatVar
                           (lid,uu____45134);
                         FStar_Parser_AST.prange = uu____45135;_},pats)
                      ->
                      let ascr_doc =
                        match ascr with
                        | FStar_Pervasives_Native.Some (t,tac) ->
                            let uu____45152 =
                              sig_as_binders_if_possible t true  in
                            FStar_Pprint.op_Hat_Hat uu____45152 tac
                        | FStar_Pervasives_Native.None  -> FStar_Pprint.empty
                         in
                      let uu____45158 =
                        if inner_let
                        then
                          let uu____45172 = pats_as_binders_if_possible pats
                             in
                          match uu____45172 with
                          | (bs,style) ->
                              ((FStar_List.append bs [ascr_doc]), style)
                        else
                          (let uu____45195 = pats_as_binders_if_possible pats
                              in
                           match uu____45195 with
                           | (bs,style) ->
                               ((FStar_List.append bs [ascr_doc]), style))
                         in
                      (match uu____45158 with
                       | (terms,style) ->
                           let uu____45222 =
                             let uu____45223 =
                               let uu____45224 =
                                 let uu____45225 = p_lident lid  in
                                 let uu____45226 =
                                   format_sig style terms true true  in
                                 FStar_Pprint.op_Hat_Hat uu____45225
                                   uu____45226
                                  in
                               FStar_Pprint.op_Hat_Hat FStar_Pprint.space
                                 uu____45224
                                in
                             FStar_Pprint.op_Hat_Hat kw uu____45223  in
                           FStar_All.pipe_left FStar_Pprint.group uu____45222)
                  | uu____45229 ->
                      let ascr_doc =
                        match ascr with
                        | FStar_Pervasives_Native.Some (t,tac) ->
                            let uu____45237 =
                              let uu____45238 =
                                let uu____45239 =
                                  p_typ_top
                                    (Arrows
                                       ((Prims.parse_int "2"),
                                         (Prims.parse_int "2"))) false false
                                    t
                                   in
                                FStar_Pprint.op_Hat_Hat FStar_Pprint.colon
                                  uu____45239
                                 in
                              FStar_Pprint.group uu____45238  in
                            FStar_Pprint.op_Hat_Hat uu____45237 tac
                        | FStar_Pervasives_Native.None  -> FStar_Pprint.empty
                         in
                      let uu____45250 =
                        let uu____45251 =
                          let uu____45252 =
                            let uu____45253 = p_tuplePattern pat1  in
                            FStar_Pprint.op_Hat_Slash_Hat kw uu____45253  in
                          FStar_Pprint.group uu____45252  in
                        FStar_Pprint.op_Hat_Hat uu____45251 ascr_doc  in
                      FStar_Pprint.group uu____45250))

and (p_letbinding :
  FStar_Pprint.document ->
    (FStar_Parser_AST.pattern * FStar_Parser_AST.term) ->
      FStar_Pprint.document)
  =
  fun kw  ->
    fun uu____45255  ->
      match uu____45255 with
      | (pat,e) ->
          let doc_pat = p_letlhs kw (pat, e) false  in
          let uu____45264 = p_term_sep false false e  in
          (match uu____45264 with
           | (comm,doc_expr) ->
               let doc_expr1 =
                 inline_comment_or_above comm doc_expr FStar_Pprint.empty  in
               let uu____45274 =
                 let uu____45275 =
                   FStar_Pprint.op_Hat_Slash_Hat FStar_Pprint.equals
                     doc_expr1
                    in
                 FStar_Pprint.op_Hat_Slash_Hat doc_pat uu____45275  in
               let uu____45276 =
                 let uu____45277 =
                   let uu____45278 =
                     let uu____45279 =
                       let uu____45280 = jump2 doc_expr1  in
                       FStar_Pprint.op_Hat_Hat FStar_Pprint.equals
                         uu____45280
                        in
                     FStar_Pprint.group uu____45279  in
                   FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____45278  in
                 FStar_Pprint.op_Hat_Hat doc_pat uu____45277  in
               FStar_Pprint.ifflat uu____45274 uu____45276)

and (p_newEffect : FStar_Parser_AST.effect_decl -> FStar_Pprint.document) =
  fun uu___331_45281  ->
    match uu___331_45281 with
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
        let uu____45306 = p_uident uid  in
        let uu____45307 = p_binders true bs  in
        let uu____45309 =
          let uu____45310 = p_simpleTerm false false t  in
          prefix2 FStar_Pprint.equals uu____45310  in
        surround_maybe_empty (Prims.parse_int "2") (Prims.parse_int "1")
          uu____45306 uu____45307 uu____45309

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
          let uu____45325 =
            let uu____45326 =
              let uu____45327 =
                let uu____45328 = p_uident uid  in
                let uu____45329 = p_binders true bs  in
                let uu____45331 =
                  let uu____45332 = p_typ false false t  in
                  prefix2 FStar_Pprint.colon uu____45332  in
                surround_maybe_empty (Prims.parse_int "2")
                  (Prims.parse_int "1") uu____45328 uu____45329 uu____45331
                 in
              FStar_Pprint.group uu____45327  in
            let uu____45337 =
              let uu____45338 = str "with"  in
              let uu____45340 =
                let uu____45341 =
                  let uu____45342 =
                    let uu____45343 =
                      let uu____45344 =
                        let uu____45345 =
                          FStar_Pprint.op_Hat_Hat FStar_Pprint.semi
                            FStar_Pprint.space
                           in
                        FStar_Pprint.op_Hat_Hat FStar_Pprint.hardline
                          uu____45345
                         in
                      separate_map_last uu____45344 p_effectDecl eff_decls
                       in
                    FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____45343
                     in
                  FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____45342  in
                FStar_Pprint.op_Hat_Hat FStar_Pprint.hardline uu____45341  in
              FStar_Pprint.op_Hat_Hat uu____45338 uu____45340  in
            FStar_Pprint.op_Hat_Slash_Hat uu____45326 uu____45337  in
          braces_with_nesting uu____45325

and (p_effectDecl :
  Prims.bool -> FStar_Parser_AST.decl -> FStar_Pprint.document) =
  fun ps  ->
    fun d  ->
      match d.FStar_Parser_AST.d with
      | FStar_Parser_AST.Tycon
          (false
           ,uu____45349,(FStar_Parser_AST.TyconAbbrev
                         (lid,[],FStar_Pervasives_Native.None ,e),FStar_Pervasives_Native.None
                         )::[])
          ->
          let uu____45382 =
            let uu____45383 = p_lident lid  in
            let uu____45384 =
              FStar_Pprint.op_Hat_Hat FStar_Pprint.space FStar_Pprint.equals
               in
            FStar_Pprint.op_Hat_Hat uu____45383 uu____45384  in
          let uu____45385 = p_simpleTerm ps false e  in
          prefix2 uu____45382 uu____45385
      | uu____45387 ->
          let uu____45388 =
            let uu____45390 = FStar_Parser_AST.decl_to_string d  in
            FStar_Util.format1
              "Not a declaration of an effect member... or at least I hope so : %s"
              uu____45390
             in
          failwith uu____45388

and (p_subEffect : FStar_Parser_AST.lift -> FStar_Pprint.document) =
  fun lift  ->
    let lift_op_doc =
      let lifts =
        match lift.FStar_Parser_AST.lift_op with
        | FStar_Parser_AST.NonReifiableLift t -> [("lift_wp", t)]
        | FStar_Parser_AST.ReifiableLift (t1,t2) ->
            [("lift_wp", t1); ("lift", t2)]
        | FStar_Parser_AST.LiftForFree t -> [("lift", t)]  in
      let p_lift ps uu____45473 =
        match uu____45473 with
        | (kwd,t) ->
            let uu____45484 =
              let uu____45485 = str kwd  in
              let uu____45486 =
                FStar_Pprint.op_Hat_Hat FStar_Pprint.space
                  FStar_Pprint.equals
                 in
              FStar_Pprint.op_Hat_Hat uu____45485 uu____45486  in
            let uu____45487 = p_simpleTerm ps false t  in
            prefix2 uu____45484 uu____45487
         in
      separate_break_map_last FStar_Pprint.semi p_lift lifts  in
    let uu____45494 =
      let uu____45495 =
        let uu____45496 = p_quident lift.FStar_Parser_AST.msource  in
        let uu____45497 =
          let uu____45498 = str "~>"  in
          FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____45498  in
        FStar_Pprint.op_Hat_Hat uu____45496 uu____45497  in
      let uu____45500 = p_quident lift.FStar_Parser_AST.mdest  in
      prefix2 uu____45495 uu____45500  in
    let uu____45501 =
      let uu____45502 = braces_with_nesting lift_op_doc  in
      FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____45502  in
    FStar_Pprint.op_Hat_Hat uu____45494 uu____45501

and (p_qualifier : FStar_Parser_AST.qualifier -> FStar_Pprint.document) =
  fun uu___332_45503  ->
    match uu___332_45503 with
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
        let uu____45523 = p_qualifier q  in
        FStar_Pprint.op_Hat_Hat uu____45523 FStar_Pprint.hardline
    | uu____45524 ->
        let uu____45525 =
          let uu____45526 = FStar_List.map p_qualifier qs  in
          FStar_Pprint.flow break1 uu____45526  in
        FStar_Pprint.op_Hat_Hat uu____45525 FStar_Pprint.hardline

and (p_letqualifier :
  FStar_Parser_AST.let_qualifier -> FStar_Pprint.document) =
  fun uu___333_45529  ->
    match uu___333_45529 with
    | FStar_Parser_AST.Rec  ->
        let uu____45530 = str "rec"  in
        FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____45530
    | FStar_Parser_AST.NoLetQualifier  -> FStar_Pprint.empty

and (p_aqual : FStar_Parser_AST.arg_qualifier -> FStar_Pprint.document) =
  fun uu___334_45532  ->
    match uu___334_45532 with
    | FStar_Parser_AST.Implicit  -> str "#"
    | FStar_Parser_AST.Equality  -> str "$"
    | FStar_Parser_AST.Meta t ->
        let t1 =
          match t.FStar_Parser_AST.tm with
          | FStar_Parser_AST.Abs (uu____45537,e) -> e
          | uu____45543 ->
              FStar_Parser_AST.mk_term
                (FStar_Parser_AST.App
                   (t,
                     (FStar_Parser_AST.unit_const t.FStar_Parser_AST.range),
                     FStar_Parser_AST.Nothing)) t.FStar_Parser_AST.range
                FStar_Parser_AST.Expr
           in
        let uu____45544 = str "#["  in
        let uu____45546 =
          let uu____45547 = p_term false false t1  in
          let uu____45550 =
            let uu____45551 = str "]"  in
            FStar_Pprint.op_Hat_Hat uu____45551 break1  in
          FStar_Pprint.op_Hat_Hat uu____45547 uu____45550  in
        FStar_Pprint.op_Hat_Hat uu____45544 uu____45546

and (p_disjunctivePattern :
  FStar_Parser_AST.pattern -> FStar_Pprint.document) =
  fun p  ->
    match p.FStar_Parser_AST.pat with
    | FStar_Parser_AST.PatOr pats ->
        let uu____45557 =
          let uu____45558 =
            let uu____45559 =
              FStar_Pprint.op_Hat_Hat FStar_Pprint.bar FStar_Pprint.space  in
            FStar_Pprint.op_Hat_Hat break1 uu____45559  in
          FStar_Pprint.separate_map uu____45558 p_tuplePattern pats  in
        FStar_Pprint.group uu____45557
    | uu____45560 -> p_tuplePattern p

and (p_tuplePattern : FStar_Parser_AST.pattern -> FStar_Pprint.document) =
  fun p  ->
    match p.FStar_Parser_AST.pat with
    | FStar_Parser_AST.PatTuple (pats,false ) ->
        let uu____45569 =
          let uu____45570 = FStar_Pprint.op_Hat_Hat FStar_Pprint.comma break1
             in
          FStar_Pprint.separate_map uu____45570 p_constructorPattern pats  in
        FStar_Pprint.group uu____45569
    | uu____45571 -> p_constructorPattern p

and (p_constructorPattern :
  FStar_Parser_AST.pattern -> FStar_Pprint.document) =
  fun p  ->
    match p.FStar_Parser_AST.pat with
    | FStar_Parser_AST.PatApp
        ({ FStar_Parser_AST.pat = FStar_Parser_AST.PatName maybe_cons_lid;
           FStar_Parser_AST.prange = uu____45574;_},hd1::tl1::[])
        when
        FStar_Ident.lid_equals maybe_cons_lid FStar_Parser_Const.cons_lid ->
        let uu____45579 =
          FStar_Pprint.op_Hat_Hat FStar_Pprint.colon FStar_Pprint.colon  in
        let uu____45580 = p_constructorPattern hd1  in
        let uu____45581 = p_constructorPattern tl1  in
        infix0 uu____45579 uu____45580 uu____45581
    | FStar_Parser_AST.PatApp
        ({ FStar_Parser_AST.pat = FStar_Parser_AST.PatName uid;
           FStar_Parser_AST.prange = uu____45583;_},pats)
        ->
        let uu____45589 = p_quident uid  in
        let uu____45590 =
          FStar_Pprint.separate_map break1 p_atomicPattern pats  in
        prefix2 uu____45589 uu____45590
    | uu____45591 -> p_atomicPattern p

and (p_atomicPattern : FStar_Parser_AST.pattern -> FStar_Pprint.document) =
  fun p  ->
    match p.FStar_Parser_AST.pat with
    | FStar_Parser_AST.PatAscribed (pat,(t,FStar_Pervasives_Native.None )) ->
        (match ((pat.FStar_Parser_AST.pat), (t.FStar_Parser_AST.tm)) with
         | (FStar_Parser_AST.PatVar (lid,aqual),FStar_Parser_AST.Refine
            ({ FStar_Parser_AST.b = FStar_Parser_AST.Annotated (lid',t1);
               FStar_Parser_AST.brange = uu____45607;
               FStar_Parser_AST.blevel = uu____45608;
               FStar_Parser_AST.aqual = uu____45609;_},phi))
             when lid.FStar_Ident.idText = lid'.FStar_Ident.idText ->
             let uu____45618 =
               let uu____45619 = p_ident lid  in
               p_refinement aqual uu____45619 t1 phi  in
             soft_parens_with_nesting uu____45618
         | (FStar_Parser_AST.PatWild aqual,FStar_Parser_AST.Refine
            ({ FStar_Parser_AST.b = FStar_Parser_AST.NoName t1;
               FStar_Parser_AST.brange = uu____45622;
               FStar_Parser_AST.blevel = uu____45623;
               FStar_Parser_AST.aqual = uu____45624;_},phi))
             ->
             let uu____45630 =
               p_refinement aqual FStar_Pprint.underscore t1 phi  in
             soft_parens_with_nesting uu____45630
         | uu____45631 ->
             let uu____45636 =
               let uu____45637 = p_tuplePattern pat  in
               let uu____45638 =
                 let uu____45639 = p_tmEqNoRefinement t  in
                 FStar_Pprint.op_Hat_Slash_Hat FStar_Pprint.colon uu____45639
                  in
               FStar_Pprint.op_Hat_Hat uu____45637 uu____45638  in
             soft_parens_with_nesting uu____45636)
    | FStar_Parser_AST.PatList pats ->
        let uu____45643 =
          separate_break_map FStar_Pprint.semi p_tuplePattern pats  in
        FStar_Pprint.surround (Prims.parse_int "2") (Prims.parse_int "0")
          FStar_Pprint.lbracket uu____45643 FStar_Pprint.rbracket
    | FStar_Parser_AST.PatRecord pats ->
        let p_recordFieldPat uu____45662 =
          match uu____45662 with
          | (lid,pat) ->
              let uu____45669 = p_qlident lid  in
              let uu____45670 = p_tuplePattern pat  in
              infix2 FStar_Pprint.equals uu____45669 uu____45670
           in
        let uu____45671 =
          separate_break_map FStar_Pprint.semi p_recordFieldPat pats  in
        soft_braces_with_nesting uu____45671
    | FStar_Parser_AST.PatTuple (pats,true ) ->
        let uu____45683 =
          FStar_Pprint.op_Hat_Hat FStar_Pprint.lparen FStar_Pprint.bar  in
        let uu____45684 =
          separate_break_map FStar_Pprint.comma p_constructorPattern pats  in
        let uu____45685 =
          FStar_Pprint.op_Hat_Hat FStar_Pprint.bar FStar_Pprint.rparen  in
        FStar_Pprint.surround (Prims.parse_int "2") (Prims.parse_int "1")
          uu____45683 uu____45684 uu____45685
    | FStar_Parser_AST.PatTvar (tv,arg_qualifier_opt) -> p_tvar tv
    | FStar_Parser_AST.PatOp op ->
        let uu____45696 =
          let uu____45697 =
            let uu____45698 =
              let uu____45699 = FStar_Ident.text_of_id op  in str uu____45699
               in
            let uu____45701 =
              FStar_Pprint.op_Hat_Hat FStar_Pprint.space FStar_Pprint.rparen
               in
            FStar_Pprint.op_Hat_Hat uu____45698 uu____45701  in
          FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____45697  in
        FStar_Pprint.op_Hat_Hat FStar_Pprint.lparen uu____45696
    | FStar_Parser_AST.PatWild aqual ->
        let uu____45705 = FStar_Pprint.optional p_aqual aqual  in
        FStar_Pprint.op_Hat_Hat uu____45705 FStar_Pprint.underscore
    | FStar_Parser_AST.PatConst c -> p_constant c
    | FStar_Parser_AST.PatVar (lid,aqual) ->
        let uu____45713 = FStar_Pprint.optional p_aqual aqual  in
        let uu____45714 = p_lident lid  in
        FStar_Pprint.op_Hat_Hat uu____45713 uu____45714
    | FStar_Parser_AST.PatName uid -> p_quident uid
    | FStar_Parser_AST.PatOr uu____45716 -> failwith "Inner or pattern !"
    | FStar_Parser_AST.PatApp
        ({ FStar_Parser_AST.pat = FStar_Parser_AST.PatName uu____45720;
           FStar_Parser_AST.prange = uu____45721;_},uu____45722)
        ->
        let uu____45727 = p_tuplePattern p  in
        soft_parens_with_nesting uu____45727
    | FStar_Parser_AST.PatTuple (uu____45728,false ) ->
        let uu____45735 = p_tuplePattern p  in
        soft_parens_with_nesting uu____45735
    | uu____45736 ->
        let uu____45737 =
          let uu____45739 = FStar_Parser_AST.pat_to_string p  in
          FStar_Util.format1 "Invalid pattern %s" uu____45739  in
        failwith uu____45737

and (is_typ_tuple : FStar_Parser_AST.term -> Prims.bool) =
  fun e  ->
    match e.FStar_Parser_AST.tm with
    | FStar_Parser_AST.Op
        ({ FStar_Ident.idText = "*"; FStar_Ident.idRange = uu____45744;_},uu____45745)
        -> true
    | uu____45752 -> false

and (is_meta_qualifier :
  FStar_Parser_AST.arg_qualifier FStar_Pervasives_Native.option -> Prims.bool)
  =
  fun aq  ->
    match aq with
    | FStar_Pervasives_Native.Some (FStar_Parser_AST.Meta uu____45758) ->
        true
    | uu____45760 -> false

and (p_binder :
  Prims.bool -> FStar_Parser_AST.binder -> FStar_Pprint.document) =
  fun is_atomic  ->
    fun b  ->
      let uu____45767 = p_binder' is_atomic b  in
      match uu____45767 with
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
          let uu____45804 =
            let uu____45805 =
              FStar_Pprint.optional p_aqual b.FStar_Parser_AST.aqual  in
            let uu____45806 = p_lident lid  in
            FStar_Pprint.op_Hat_Hat uu____45805 uu____45806  in
          (uu____45804, FStar_Pervasives_Native.None, cat_with_colon)
      | FStar_Parser_AST.TVariable lid ->
          let uu____45812 = p_lident lid  in
          (uu____45812, FStar_Pervasives_Native.None, cat_with_colon)
      | FStar_Parser_AST.Annotated (lid,t) ->
          let uu____45819 =
            match t.FStar_Parser_AST.tm with
            | FStar_Parser_AST.Refine
                ({ FStar_Parser_AST.b = FStar_Parser_AST.Annotated (lid',t1);
                   FStar_Parser_AST.brange = uu____45830;
                   FStar_Parser_AST.blevel = uu____45831;
                   FStar_Parser_AST.aqual = uu____45832;_},phi)
                when lid.FStar_Ident.idText = lid'.FStar_Ident.idText ->
                let uu____45837 = p_lident lid  in
                p_refinement' b.FStar_Parser_AST.aqual uu____45837 t1 phi
            | uu____45838 ->
                let t' =
                  let uu____45840 = is_typ_tuple t  in
                  if uu____45840
                  then
                    let uu____45843 = p_tmFormula t  in
                    soft_parens_with_nesting uu____45843
                  else p_tmFormula t  in
                let uu____45846 =
                  let uu____45847 =
                    FStar_Pprint.optional p_aqual b.FStar_Parser_AST.aqual
                     in
                  let uu____45848 = p_lident lid  in
                  FStar_Pprint.op_Hat_Hat uu____45847 uu____45848  in
                (uu____45846, t')
             in
          (match uu____45819 with
           | (b',t') ->
               let catf =
                 let uu____45866 =
                   is_atomic || (is_meta_qualifier b.FStar_Parser_AST.aqual)
                    in
                 if uu____45866
                 then
                   fun x  ->
                     fun y  ->
                       let uu____45873 =
                         let uu____45874 =
                           let uu____45875 = cat_with_colon x y  in
                           FStar_Pprint.op_Hat_Hat uu____45875
                             FStar_Pprint.rparen
                            in
                         FStar_Pprint.op_Hat_Hat FStar_Pprint.lparen
                           uu____45874
                          in
                       FStar_Pprint.group uu____45873
                 else
                   (fun x  ->
                      fun y  ->
                        let uu____45880 = cat_with_colon x y  in
                        FStar_Pprint.group uu____45880)
                  in
               (b', (FStar_Pervasives_Native.Some t'), catf))
      | FStar_Parser_AST.TAnnotated uu____45885 ->
          failwith "Is this still used ?"
      | FStar_Parser_AST.NoName t ->
          (match t.FStar_Parser_AST.tm with
           | FStar_Parser_AST.Refine
               ({ FStar_Parser_AST.b = FStar_Parser_AST.NoName t1;
                  FStar_Parser_AST.brange = uu____45913;
                  FStar_Parser_AST.blevel = uu____45914;
                  FStar_Parser_AST.aqual = uu____45915;_},phi)
               ->
               let uu____45919 =
                 p_refinement' b.FStar_Parser_AST.aqual
                   FStar_Pprint.underscore t1 phi
                  in
               (match uu____45919 with
                | (b',t') ->
                    (b', (FStar_Pervasives_Native.Some t'), cat_with_colon))
           | uu____45940 ->
               if is_atomic
               then
                 let uu____45952 = p_atomicTerm t  in
                 (uu____45952, FStar_Pervasives_Native.None, cat_with_colon)
               else
                 (let uu____45959 = p_appTerm t  in
                  (uu____45959, FStar_Pervasives_Native.None, cat_with_colon)))

and (p_refinement :
  FStar_Parser_AST.arg_qualifier FStar_Pervasives_Native.option ->
    FStar_Pprint.document ->
      FStar_Parser_AST.term -> FStar_Parser_AST.term -> FStar_Pprint.document)
  =
  fun aqual_opt  ->
    fun binder  ->
      fun t  ->
        fun phi  ->
          let uu____45970 = p_refinement' aqual_opt binder t phi  in
          match uu____45970 with | (b,typ) -> cat_with_colon b typ

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
            | FStar_Parser_AST.Construct uu____45986 -> false
            | FStar_Parser_AST.App uu____45998 -> false
            | FStar_Parser_AST.Op uu____46006 -> false
            | uu____46014 -> true  in
          let uu____46016 = p_noSeqTerm false false phi  in
          match uu____46016 with
          | (comm,phi1) ->
              let phi2 =
                if comm = FStar_Pprint.empty
                then phi1
                else
                  (let uu____46033 =
                     FStar_Pprint.op_Hat_Hat FStar_Pprint.hardline phi1  in
                   FStar_Pprint.op_Hat_Hat comm uu____46033)
                 in
              let jump_break =
                if is_t_atomic
                then (Prims.parse_int "0")
                else (Prims.parse_int "1")  in
              let uu____46042 =
                let uu____46043 = FStar_Pprint.optional p_aqual aqual_opt  in
                FStar_Pprint.op_Hat_Hat uu____46043 binder  in
              let uu____46044 =
                let uu____46045 = p_appTerm t  in
                let uu____46046 =
                  let uu____46047 =
                    let uu____46048 =
                      let uu____46049 = soft_braces_with_nesting_tight phi2
                         in
                      let uu____46050 = soft_braces_with_nesting phi2  in
                      FStar_Pprint.ifflat uu____46049 uu____46050  in
                    FStar_Pprint.group uu____46048  in
                  FStar_Pprint.jump (Prims.parse_int "2") jump_break
                    uu____46047
                   in
                FStar_Pprint.op_Hat_Hat uu____46045 uu____46046  in
              (uu____46042, uu____46044)

and (p_binders_list :
  Prims.bool ->
    FStar_Parser_AST.binder Prims.list -> FStar_Pprint.document Prims.list)
  = fun is_atomic  -> fun bs  -> FStar_List.map (p_binder is_atomic) bs

and (p_binders :
  Prims.bool -> FStar_Parser_AST.binder Prims.list -> FStar_Pprint.document)
  =
  fun is_atomic  ->
    fun bs  ->
      let uu____46064 = p_binders_list is_atomic bs  in
      separate_or_flow break1 uu____46064

and (text_of_id_or_underscore : FStar_Ident.ident -> FStar_Pprint.document) =
  fun lid  ->
    let uu____46068 =
      (FStar_Util.starts_with lid.FStar_Ident.idText
         FStar_Ident.reserved_prefix)
        &&
        (let uu____46071 = FStar_Options.print_real_names ()  in
         Prims.op_Negation uu____46071)
       in
    if uu____46068
    then FStar_Pprint.underscore
    else (let uu____46076 = FStar_Ident.text_of_id lid  in str uu____46076)

and (text_of_lid_or_underscore : FStar_Ident.lident -> FStar_Pprint.document)
  =
  fun lid  ->
    let uu____46079 =
      (FStar_Util.starts_with (lid.FStar_Ident.ident).FStar_Ident.idText
         FStar_Ident.reserved_prefix)
        &&
        (let uu____46082 = FStar_Options.print_real_names ()  in
         Prims.op_Negation uu____46082)
       in
    if uu____46079
    then FStar_Pprint.underscore
    else (let uu____46087 = FStar_Ident.text_of_lid lid  in str uu____46087)

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
          let uu____46108 = FStar_Pprint.op_Hat_Hat doc1 sep  in
          FStar_Pprint.group uu____46108
        else
          (let uu____46111 =
             let uu____46112 =
               let uu____46113 =
                 let uu____46114 =
                   let uu____46115 = FStar_Pprint.op_Hat_Hat break1 comm  in
                   FStar_Pprint.op_Hat_Hat sep uu____46115  in
                 FStar_Pprint.op_Hat_Hat doc1 uu____46114  in
               FStar_Pprint.group uu____46113  in
             let uu____46116 =
               let uu____46117 =
                 let uu____46118 = FStar_Pprint.op_Hat_Hat doc1 sep  in
                 FStar_Pprint.op_Hat_Hat FStar_Pprint.hardline uu____46118
                  in
               FStar_Pprint.op_Hat_Hat comm uu____46117  in
             FStar_Pprint.ifflat uu____46112 uu____46116  in
           FStar_All.pipe_left FStar_Pprint.group uu____46111)

and (p_term :
  Prims.bool -> Prims.bool -> FStar_Parser_AST.term -> FStar_Pprint.document)
  =
  fun ps  ->
    fun pb  ->
      fun e  ->
        match e.FStar_Parser_AST.tm with
        | FStar_Parser_AST.Seq (e1,e2) ->
            let uu____46126 = p_noSeqTerm true false e1  in
            (match uu____46126 with
             | (comm,t1) ->
                 let uu____46135 =
                   inline_comment_or_above comm t1 FStar_Pprint.semi  in
                 let uu____46136 =
                   let uu____46137 = p_term ps pb e2  in
                   FStar_Pprint.op_Hat_Hat FStar_Pprint.hardline uu____46137
                    in
                 FStar_Pprint.op_Hat_Hat uu____46135 uu____46136)
        | FStar_Parser_AST.Bind (x,e1,e2) ->
            let uu____46141 =
              let uu____46142 =
                let uu____46143 =
                  let uu____46144 = p_lident x  in
                  let uu____46145 =
                    FStar_Pprint.op_Hat_Hat FStar_Pprint.space
                      FStar_Pprint.long_left_arrow
                     in
                  FStar_Pprint.op_Hat_Hat uu____46144 uu____46145  in
                let uu____46146 =
                  let uu____46147 = p_noSeqTermAndComment true false e1  in
                  let uu____46150 =
                    FStar_Pprint.op_Hat_Hat FStar_Pprint.space
                      FStar_Pprint.semi
                     in
                  FStar_Pprint.op_Hat_Hat uu____46147 uu____46150  in
                op_Hat_Slash_Plus_Hat uu____46143 uu____46146  in
              FStar_Pprint.group uu____46142  in
            let uu____46151 = p_term ps pb e2  in
            FStar_Pprint.op_Hat_Slash_Hat uu____46141 uu____46151
        | uu____46152 ->
            let uu____46153 = p_noSeqTermAndComment ps pb e  in
            FStar_Pprint.group uu____46153

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
            let uu____46165 = p_noSeqTerm true false e1  in
            (match uu____46165 with
             | (comm,t1) ->
                 let uu____46178 =
                   let uu____46179 =
                     let uu____46180 =
                       FStar_Pprint.op_Hat_Hat t1 FStar_Pprint.semi  in
                     FStar_Pprint.group uu____46180  in
                   let uu____46181 =
                     let uu____46182 = p_term ps pb e2  in
                     FStar_Pprint.op_Hat_Hat FStar_Pprint.hardline
                       uu____46182
                      in
                   FStar_Pprint.op_Hat_Hat uu____46179 uu____46181  in
                 (comm, uu____46178))
        | FStar_Parser_AST.Bind (x,e1,e2) ->
            let uu____46186 =
              let uu____46187 =
                let uu____46188 =
                  let uu____46189 =
                    let uu____46190 = p_lident x  in
                    let uu____46191 =
                      FStar_Pprint.op_Hat_Hat FStar_Pprint.space
                        FStar_Pprint.long_left_arrow
                       in
                    FStar_Pprint.op_Hat_Hat uu____46190 uu____46191  in
                  let uu____46192 =
                    let uu____46193 = p_noSeqTermAndComment true false e1  in
                    let uu____46196 =
                      FStar_Pprint.op_Hat_Hat FStar_Pprint.space
                        FStar_Pprint.semi
                       in
                    FStar_Pprint.op_Hat_Hat uu____46193 uu____46196  in
                  op_Hat_Slash_Plus_Hat uu____46189 uu____46192  in
                FStar_Pprint.group uu____46188  in
              let uu____46197 = p_term ps pb e2  in
              FStar_Pprint.op_Hat_Slash_Hat uu____46187 uu____46197  in
            (FStar_Pprint.empty, uu____46186)
        | uu____46198 -> p_noSeqTerm ps pb e

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
            let uu____46218 =
              let uu____46219 = p_tmIff e1  in
              let uu____46220 =
                let uu____46221 =
                  let uu____46222 = p_typ ps pb t  in
                  FStar_Pprint.op_Hat_Slash_Hat FStar_Pprint.colon
                    uu____46222
                   in
                FStar_Pprint.op_Hat_Hat FStar_Pprint.langle uu____46221  in
              FStar_Pprint.op_Hat_Slash_Hat uu____46219 uu____46220  in
            FStar_Pprint.group uu____46218
        | FStar_Parser_AST.Ascribed (e1,t,FStar_Pervasives_Native.Some tac)
            ->
            let uu____46228 =
              let uu____46229 = p_tmIff e1  in
              let uu____46230 =
                let uu____46231 =
                  let uu____46232 =
                    let uu____46233 = p_typ false false t  in
                    let uu____46236 =
                      let uu____46237 = str "by"  in
                      let uu____46239 = p_typ ps pb tac  in
                      FStar_Pprint.op_Hat_Slash_Hat uu____46237 uu____46239
                       in
                    FStar_Pprint.op_Hat_Slash_Hat uu____46233 uu____46236  in
                  FStar_Pprint.op_Hat_Slash_Hat FStar_Pprint.colon
                    uu____46232
                   in
                FStar_Pprint.op_Hat_Hat FStar_Pprint.langle uu____46231  in
              FStar_Pprint.op_Hat_Slash_Hat uu____46229 uu____46230  in
            FStar_Pprint.group uu____46228
        | FStar_Parser_AST.Op
            ({ FStar_Ident.idText = ".()<-";
               FStar_Ident.idRange = uu____46240;_},e1::e2::e3::[])
            ->
            let uu____46247 =
              let uu____46248 =
                let uu____46249 =
                  let uu____46250 = p_atomicTermNotQUident e1  in
                  let uu____46251 =
                    let uu____46252 =
                      let uu____46253 =
                        let uu____46254 = p_term false false e2  in
                        soft_parens_with_nesting uu____46254  in
                      let uu____46257 =
                        FStar_Pprint.op_Hat_Hat FStar_Pprint.space
                          FStar_Pprint.larrow
                         in
                      FStar_Pprint.op_Hat_Hat uu____46253 uu____46257  in
                    FStar_Pprint.op_Hat_Hat FStar_Pprint.dot uu____46252  in
                  FStar_Pprint.op_Hat_Hat uu____46250 uu____46251  in
                FStar_Pprint.group uu____46249  in
              let uu____46258 =
                let uu____46259 = p_noSeqTermAndComment ps pb e3  in
                jump2 uu____46259  in
              FStar_Pprint.op_Hat_Hat uu____46248 uu____46258  in
            FStar_Pprint.group uu____46247
        | FStar_Parser_AST.Op
            ({ FStar_Ident.idText = ".[]<-";
               FStar_Ident.idRange = uu____46260;_},e1::e2::e3::[])
            ->
            let uu____46267 =
              let uu____46268 =
                let uu____46269 =
                  let uu____46270 = p_atomicTermNotQUident e1  in
                  let uu____46271 =
                    let uu____46272 =
                      let uu____46273 =
                        let uu____46274 = p_term false false e2  in
                        soft_brackets_with_nesting uu____46274  in
                      let uu____46277 =
                        FStar_Pprint.op_Hat_Hat FStar_Pprint.space
                          FStar_Pprint.larrow
                         in
                      FStar_Pprint.op_Hat_Hat uu____46273 uu____46277  in
                    FStar_Pprint.op_Hat_Hat FStar_Pprint.dot uu____46272  in
                  FStar_Pprint.op_Hat_Hat uu____46270 uu____46271  in
                FStar_Pprint.group uu____46269  in
              let uu____46278 =
                let uu____46279 = p_noSeqTermAndComment ps pb e3  in
                jump2 uu____46279  in
              FStar_Pprint.op_Hat_Hat uu____46268 uu____46278  in
            FStar_Pprint.group uu____46267
        | FStar_Parser_AST.Requires (e1,wtf) ->
            let uu____46289 =
              let uu____46290 = str "requires"  in
              let uu____46292 = p_typ ps pb e1  in
              FStar_Pprint.op_Hat_Slash_Hat uu____46290 uu____46292  in
            FStar_Pprint.group uu____46289
        | FStar_Parser_AST.Ensures (e1,wtf) ->
            let uu____46302 =
              let uu____46303 = str "ensures"  in
              let uu____46305 = p_typ ps pb e1  in
              FStar_Pprint.op_Hat_Slash_Hat uu____46303 uu____46305  in
            FStar_Pprint.group uu____46302
        | FStar_Parser_AST.Attributes es ->
            let uu____46309 =
              let uu____46310 = str "attributes"  in
              let uu____46312 =
                FStar_Pprint.separate_map break1 p_atomicTerm es  in
              FStar_Pprint.op_Hat_Slash_Hat uu____46310 uu____46312  in
            FStar_Pprint.group uu____46309
        | FStar_Parser_AST.If (e1,e2,e3) ->
            if is_unit e3
            then
              let uu____46317 =
                let uu____46318 =
                  let uu____46319 = str "if"  in
                  let uu____46321 = p_noSeqTermAndComment false false e1  in
                  op_Hat_Slash_Plus_Hat uu____46319 uu____46321  in
                let uu____46324 =
                  let uu____46325 = str "then"  in
                  let uu____46327 = p_noSeqTermAndComment ps pb e2  in
                  op_Hat_Slash_Plus_Hat uu____46325 uu____46327  in
                FStar_Pprint.op_Hat_Slash_Hat uu____46318 uu____46324  in
              FStar_Pprint.group uu____46317
            else
              (let e2_doc =
                 match e2.FStar_Parser_AST.tm with
                 | FStar_Parser_AST.If (uu____46331,uu____46332,e31) when
                     is_unit e31 ->
                     let uu____46334 = p_noSeqTermAndComment false false e2
                        in
                     soft_parens_with_nesting uu____46334
                 | uu____46337 -> p_noSeqTermAndComment false false e2  in
               let uu____46340 =
                 let uu____46341 =
                   let uu____46342 = str "if"  in
                   let uu____46344 = p_noSeqTermAndComment false false e1  in
                   op_Hat_Slash_Plus_Hat uu____46342 uu____46344  in
                 let uu____46347 =
                   let uu____46348 =
                     let uu____46349 = str "then"  in
                     op_Hat_Slash_Plus_Hat uu____46349 e2_doc  in
                   let uu____46351 =
                     let uu____46352 = str "else"  in
                     let uu____46354 = p_noSeqTermAndComment ps pb e3  in
                     op_Hat_Slash_Plus_Hat uu____46352 uu____46354  in
                   FStar_Pprint.op_Hat_Slash_Hat uu____46348 uu____46351  in
                 FStar_Pprint.op_Hat_Slash_Hat uu____46341 uu____46347  in
               FStar_Pprint.group uu____46340)
        | FStar_Parser_AST.TryWith (e1,branches) ->
            let uu____46377 =
              let uu____46378 =
                let uu____46379 =
                  let uu____46380 = str "try"  in
                  let uu____46382 = p_noSeqTermAndComment false false e1  in
                  prefix2 uu____46380 uu____46382  in
                let uu____46385 =
                  let uu____46386 = str "with"  in
                  let uu____46388 =
                    separate_map_last FStar_Pprint.hardline p_patternBranch
                      branches
                     in
                  FStar_Pprint.op_Hat_Slash_Hat uu____46386 uu____46388  in
                FStar_Pprint.op_Hat_Slash_Hat uu____46379 uu____46385  in
              FStar_Pprint.group uu____46378  in
            let uu____46397 = paren_if (ps || pb)  in uu____46397 uu____46377
        | FStar_Parser_AST.Match (e1,branches) ->
            let uu____46424 =
              let uu____46425 =
                let uu____46426 =
                  let uu____46427 = str "match"  in
                  let uu____46429 = p_noSeqTermAndComment false false e1  in
                  let uu____46432 = str "with"  in
                  FStar_Pprint.surround (Prims.parse_int "2")
                    (Prims.parse_int "1") uu____46427 uu____46429 uu____46432
                   in
                let uu____46436 =
                  separate_map_last FStar_Pprint.hardline p_patternBranch
                    branches
                   in
                FStar_Pprint.op_Hat_Slash_Hat uu____46426 uu____46436  in
              FStar_Pprint.group uu____46425  in
            let uu____46445 = paren_if (ps || pb)  in uu____46445 uu____46424
        | FStar_Parser_AST.LetOpen (uid,e1) ->
            let uu____46452 =
              let uu____46453 =
                let uu____46454 =
                  let uu____46455 = str "let open"  in
                  let uu____46457 = p_quident uid  in
                  let uu____46458 = str "in"  in
                  FStar_Pprint.surround (Prims.parse_int "2")
                    (Prims.parse_int "1") uu____46455 uu____46457 uu____46458
                   in
                let uu____46462 = p_term false pb e1  in
                FStar_Pprint.op_Hat_Slash_Hat uu____46454 uu____46462  in
              FStar_Pprint.group uu____46453  in
            let uu____46464 = paren_if ps  in uu____46464 uu____46452
        | FStar_Parser_AST.Let (q,lbs,e1) ->
            let p_lb q1 uu____46529 is_last =
              match uu____46529 with
              | (a,(pat,e2)) ->
                  let attrs = p_attrs_opt a  in
                  let doc_let_or_and =
                    match q1 with
                    | FStar_Pervasives_Native.Some (FStar_Parser_AST.Rec ) ->
                        let uu____46563 =
                          let uu____46564 = str "let"  in
                          let uu____46566 = str "rec"  in
                          FStar_Pprint.op_Hat_Slash_Hat uu____46564
                            uu____46566
                           in
                        FStar_Pprint.group uu____46563
                    | FStar_Pervasives_Native.Some
                        (FStar_Parser_AST.NoLetQualifier ) -> str "let"
                    | uu____46569 -> str "and"  in
                  let doc_pat = p_letlhs doc_let_or_and (pat, e2) true  in
                  let uu____46575 = p_term_sep false false e2  in
                  (match uu____46575 with
                   | (comm,doc_expr) ->
                       let doc_expr1 =
                         inline_comment_or_above comm doc_expr
                           FStar_Pprint.empty
                          in
                       let uu____46585 =
                         if is_last
                         then
                           let uu____46587 =
                             FStar_Pprint.flow break1
                               [doc_pat; FStar_Pprint.equals]
                              in
                           let uu____46588 = str "in"  in
                           FStar_Pprint.surround (Prims.parse_int "2")
                             (Prims.parse_int "1") uu____46587 doc_expr1
                             uu____46588
                         else
                           (let uu____46594 =
                              FStar_Pprint.flow break1
                                [doc_pat; FStar_Pprint.equals; doc_expr1]
                               in
                            FStar_Pprint.hang (Prims.parse_int "2")
                              uu____46594)
                          in
                       FStar_Pprint.op_Hat_Hat attrs uu____46585)
               in
            let l = FStar_List.length lbs  in
            let lbs_docs =
              FStar_List.mapi
                (fun i  ->
                   fun lb  ->
                     if i = (Prims.parse_int "0")
                     then
                       let uu____46645 =
                         p_lb (FStar_Pervasives_Native.Some q) lb
                           (i = (l - (Prims.parse_int "1")))
                          in
                       FStar_Pprint.group uu____46645
                     else
                       (let uu____46650 =
                          p_lb FStar_Pervasives_Native.None lb
                            (i = (l - (Prims.parse_int "1")))
                           in
                        FStar_Pprint.group uu____46650)) lbs
               in
            let lbs_doc =
              let uu____46654 = FStar_Pprint.separate break1 lbs_docs  in
              FStar_Pprint.group uu____46654  in
            let uu____46655 =
              let uu____46656 =
                let uu____46657 =
                  let uu____46658 = p_term false pb e1  in
                  FStar_Pprint.op_Hat_Hat FStar_Pprint.hardline uu____46658
                   in
                FStar_Pprint.op_Hat_Hat lbs_doc uu____46657  in
              FStar_Pprint.group uu____46656  in
            let uu____46660 = paren_if ps  in uu____46660 uu____46655
        | FStar_Parser_AST.Abs
            ({ FStar_Parser_AST.pat = FStar_Parser_AST.PatVar (x,typ_opt);
               FStar_Parser_AST.prange = uu____46667;_}::[],{
                                                              FStar_Parser_AST.tm
                                                                =
                                                                FStar_Parser_AST.Match
                                                                (maybe_x,branches);
                                                              FStar_Parser_AST.range
                                                                = uu____46670;
                                                              FStar_Parser_AST.level
                                                                = uu____46671;_})
            when matches_var maybe_x x ->
            let uu____46698 =
              let uu____46699 =
                let uu____46700 = str "function"  in
                let uu____46702 =
                  separate_map_last FStar_Pprint.hardline p_patternBranch
                    branches
                   in
                FStar_Pprint.op_Hat_Slash_Hat uu____46700 uu____46702  in
              FStar_Pprint.group uu____46699  in
            let uu____46711 = paren_if (ps || pb)  in uu____46711 uu____46698
        | FStar_Parser_AST.Quote (e1,FStar_Parser_AST.Dynamic ) ->
            let uu____46717 =
              let uu____46718 = str "quote"  in
              let uu____46720 = p_noSeqTermAndComment ps pb e1  in
              FStar_Pprint.op_Hat_Slash_Hat uu____46718 uu____46720  in
            FStar_Pprint.group uu____46717
        | FStar_Parser_AST.Quote (e1,FStar_Parser_AST.Static ) ->
            let uu____46722 =
              let uu____46723 = str "`"  in
              let uu____46725 = p_noSeqTermAndComment ps pb e1  in
              FStar_Pprint.op_Hat_Hat uu____46723 uu____46725  in
            FStar_Pprint.group uu____46722
        | FStar_Parser_AST.VQuote e1 ->
            let uu____46727 =
              let uu____46728 = str "`%"  in
              let uu____46730 = p_noSeqTermAndComment ps pb e1  in
              FStar_Pprint.op_Hat_Hat uu____46728 uu____46730  in
            FStar_Pprint.group uu____46727
        | FStar_Parser_AST.Antiquote
            {
              FStar_Parser_AST.tm = FStar_Parser_AST.Quote
                (e1,FStar_Parser_AST.Dynamic );
              FStar_Parser_AST.range = uu____46732;
              FStar_Parser_AST.level = uu____46733;_}
            ->
            let uu____46734 =
              let uu____46735 = str "`@"  in
              let uu____46737 = p_noSeqTermAndComment ps pb e1  in
              FStar_Pprint.op_Hat_Hat uu____46735 uu____46737  in
            FStar_Pprint.group uu____46734
        | FStar_Parser_AST.Antiquote e1 ->
            let uu____46739 =
              let uu____46740 = str "`#"  in
              let uu____46742 = p_noSeqTermAndComment ps pb e1  in
              FStar_Pprint.op_Hat_Hat uu____46740 uu____46742  in
            FStar_Pprint.group uu____46739
        | FStar_Parser_AST.CalcProof (rel,init1,steps) ->
            let head1 =
              let uu____46751 = str "calc"  in
              let uu____46753 =
                let uu____46754 =
                  let uu____46755 = p_noSeqTermAndComment false false rel  in
                  let uu____46758 =
                    FStar_Pprint.op_Hat_Hat FStar_Pprint.space
                      FStar_Pprint.lbrace
                     in
                  FStar_Pprint.op_Hat_Hat uu____46755 uu____46758  in
                FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____46754  in
              FStar_Pprint.op_Hat_Hat uu____46751 uu____46753  in
            let bot = FStar_Pprint.rbrace  in
            let uu____46760 =
              FStar_Pprint.op_Hat_Hat FStar_Pprint.hardline bot  in
            let uu____46761 =
              let uu____46762 =
                let uu____46763 =
                  let uu____46764 = p_noSeqTermAndComment false false init1
                     in
                  let uu____46767 =
                    let uu____46768 = str ";"  in
                    let uu____46770 =
                      let uu____46771 =
                        separate_map_last FStar_Pprint.hardline p_calcStep
                          steps
                         in
                      FStar_Pprint.op_Hat_Hat FStar_Pprint.hardline
                        uu____46771
                       in
                    FStar_Pprint.op_Hat_Hat uu____46768 uu____46770  in
                  FStar_Pprint.op_Hat_Hat uu____46764 uu____46767  in
                FStar_Pprint.op_Hat_Hat FStar_Pprint.hardline uu____46763  in
              FStar_All.pipe_left (FStar_Pprint.nest (Prims.parse_int "2"))
                uu____46762
               in
            FStar_Pprint.enclose head1 uu____46760 uu____46761
        | uu____46773 -> p_typ ps pb e

and (p_calcStep :
  Prims.bool -> FStar_Parser_AST.calc_step -> FStar_Pprint.document) =
  fun uu____46774  ->
    fun uu____46775  ->
      match uu____46775 with
      | FStar_Parser_AST.CalcStep (rel,just,next) ->
          let uu____46780 =
            let uu____46781 = p_noSeqTermAndComment false false rel  in
            let uu____46784 =
              let uu____46785 =
                let uu____46786 =
                  let uu____46787 =
                    let uu____46788 = p_noSeqTermAndComment false false just
                       in
                    let uu____46791 =
                      let uu____46792 =
                        let uu____46793 =
                          let uu____46794 =
                            let uu____46795 =
                              p_noSeqTermAndComment false false next  in
                            let uu____46798 = str ";"  in
                            FStar_Pprint.op_Hat_Hat uu____46795 uu____46798
                             in
                          FStar_Pprint.op_Hat_Hat FStar_Pprint.hardline
                            uu____46794
                           in
                        FStar_Pprint.op_Hat_Hat FStar_Pprint.rbrace
                          uu____46793
                         in
                      FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____46792
                       in
                    FStar_Pprint.op_Hat_Hat uu____46788 uu____46791  in
                  FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____46787  in
                FStar_Pprint.op_Hat_Hat FStar_Pprint.lbrace uu____46786  in
              FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____46785  in
            FStar_Pprint.op_Hat_Hat uu____46781 uu____46784  in
          FStar_Pprint.group uu____46780

and (p_attrs_opt :
  FStar_Parser_AST.term Prims.list FStar_Pervasives_Native.option ->
    FStar_Pprint.document)
  =
  fun uu___335_46800  ->
    match uu___335_46800 with
    | FStar_Pervasives_Native.None  -> FStar_Pprint.empty
    | FStar_Pervasives_Native.Some terms ->
        let uu____46812 =
          let uu____46813 = str "[@"  in
          let uu____46815 =
            let uu____46816 =
              FStar_Pprint.separate_map break1 p_atomicTerm terms  in
            let uu____46817 = str "]"  in
            FStar_Pprint.op_Hat_Slash_Hat uu____46816 uu____46817  in
          FStar_Pprint.op_Hat_Slash_Hat uu____46813 uu____46815  in
        FStar_Pprint.group uu____46812

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
                 let uu____46854 =
                   let uu____46855 =
                     let uu____46856 = p_quantifier e  in
                     FStar_Pprint.op_Hat_Hat uu____46856 FStar_Pprint.space
                      in
                   FStar_Pprint.soft_surround (Prims.parse_int "2")
                     (Prims.parse_int "0") uu____46855 binders_doc
                     FStar_Pprint.dot
                    in
                 prefix2 uu____46854 term_doc
             | pats ->
                 let uu____46864 =
                   let uu____46865 =
                     let uu____46866 =
                       let uu____46867 =
                         let uu____46868 = p_quantifier e  in
                         FStar_Pprint.op_Hat_Hat uu____46868
                           FStar_Pprint.space
                          in
                       FStar_Pprint.soft_surround (Prims.parse_int "2")
                         (Prims.parse_int "0") uu____46867 binders_doc
                         FStar_Pprint.dot
                        in
                     let uu____46871 = p_trigger trigger  in
                     prefix2 uu____46866 uu____46871  in
                   FStar_Pprint.group uu____46865  in
                 prefix2 uu____46864 term_doc)
        | FStar_Parser_AST.QExists (bs,trigger,e1) ->
            let binders_doc = p_binders true bs  in
            let term_doc = p_noSeqTermAndComment ps pb e1  in
            (match trigger with
             | [] ->
                 let uu____46892 =
                   let uu____46893 =
                     let uu____46894 = p_quantifier e  in
                     FStar_Pprint.op_Hat_Hat uu____46894 FStar_Pprint.space
                      in
                   FStar_Pprint.soft_surround (Prims.parse_int "2")
                     (Prims.parse_int "0") uu____46893 binders_doc
                     FStar_Pprint.dot
                    in
                 prefix2 uu____46892 term_doc
             | pats ->
                 let uu____46902 =
                   let uu____46903 =
                     let uu____46904 =
                       let uu____46905 =
                         let uu____46906 = p_quantifier e  in
                         FStar_Pprint.op_Hat_Hat uu____46906
                           FStar_Pprint.space
                          in
                       FStar_Pprint.soft_surround (Prims.parse_int "2")
                         (Prims.parse_int "0") uu____46905 binders_doc
                         FStar_Pprint.dot
                        in
                     let uu____46909 = p_trigger trigger  in
                     prefix2 uu____46904 uu____46909  in
                   FStar_Pprint.group uu____46903  in
                 prefix2 uu____46902 term_doc)
        | uu____46910 -> p_simpleTerm ps pb e

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
      let uu____46931 = all_binders_annot t  in
      if uu____46931
      then
        let uu____46934 =
          p_typ_top
            (Binders ((Prims.parse_int "4"), (Prims.parse_int "0"), true))
            false false t
           in
        FStar_Pprint.op_Hat_Hat s uu____46934
      else
        (let uu____46945 =
           let uu____46946 =
             let uu____46947 =
               p_typ_top
                 (Arrows ((Prims.parse_int "2"), (Prims.parse_int "2")))
                 false false t
                in
             FStar_Pprint.op_Hat_Hat s uu____46947  in
           FStar_Pprint.op_Hat_Hat FStar_Pprint.colon uu____46946  in
         FStar_Pprint.group uu____46945)

and (collapse_pats :
  (FStar_Pprint.document * FStar_Pprint.document) Prims.list ->
    FStar_Pprint.document Prims.list)
  =
  fun pats  ->
    let fold_fun bs x =
      let uu____47006 = x  in
      match uu____47006 with
      | (b1,t1) ->
          (match bs with
           | [] -> [([b1], t1)]
           | hd1::tl1 ->
               let uu____47071 = hd1  in
               (match uu____47071 with
                | (b2s,t2) ->
                    if t1 = t2
                    then ((FStar_List.append b2s [b1]), t1) :: tl1
                    else ([b1], t1) :: hd1 :: tl1))
       in
    let p_collapsed_binder cb =
      let uu____47143 = cb  in
      match uu____47143 with
      | (bs,typ) ->
          (match bs with
           | [] -> failwith "Impossible"
           | b::[] -> cat_with_colon b typ
           | hd1::tl1 ->
               let uu____47162 =
                 FStar_List.fold_left
                   (fun x  ->
                      fun y  ->
                        let uu____47168 =
                          FStar_Pprint.op_Hat_Hat FStar_Pprint.space y  in
                        FStar_Pprint.op_Hat_Hat x uu____47168) hd1 tl1
                  in
               cat_with_colon uu____47162 typ)
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
                 FStar_Parser_AST.brange = uu____47247;
                 FStar_Parser_AST.blevel = uu____47248;
                 FStar_Parser_AST.aqual = uu____47249;_},phi))
               when lid.FStar_Ident.idText = lid'.FStar_Ident.idText ->
               let uu____47258 =
                 let uu____47263 = p_ident lid  in
                 p_refinement' aqual uu____47263 t1 phi  in
               FStar_Pervasives_Native.Some uu____47258
           | (FStar_Parser_AST.PatVar (lid,aqual),uu____47270) ->
               let uu____47275 =
                 let uu____47280 =
                   let uu____47281 = FStar_Pprint.optional p_aqual aqual  in
                   let uu____47282 = p_ident lid  in
                   FStar_Pprint.op_Hat_Hat uu____47281 uu____47282  in
                 let uu____47283 = p_tmEqNoRefinement t  in
                 (uu____47280, uu____47283)  in
               FStar_Pervasives_Native.Some uu____47275
           | uu____47288 -> FStar_Pervasives_Native.None)
      | uu____47297 -> FStar_Pervasives_Native.None  in
    let all_unbound p =
      match p.FStar_Parser_AST.pat with
      | FStar_Parser_AST.PatAscribed uu____47310 -> false
      | uu____47322 -> true  in
    let uu____47324 = map_if_all all_binders pats  in
    match uu____47324 with
    | FStar_Pervasives_Native.Some bs ->
        let uu____47356 = collapse_pats bs  in
        (uu____47356,
          (Binders ((Prims.parse_int "4"), (Prims.parse_int "0"), true)))
    | FStar_Pervasives_Native.None  ->
        let uu____47373 = FStar_List.map p_atomicPattern pats  in
        (uu____47373,
          (Binders ((Prims.parse_int "4"), (Prims.parse_int "0"), false)))

and (p_quantifier : FStar_Parser_AST.term -> FStar_Pprint.document) =
  fun e  ->
    match e.FStar_Parser_AST.tm with
    | FStar_Parser_AST.QForall uu____47385 -> str "forall"
    | FStar_Parser_AST.QExists uu____47399 -> str "exists"
    | uu____47413 ->
        failwith "Imposible : p_quantifier called on a non-quantifier term"

and (p_trigger :
  FStar_Parser_AST.term Prims.list Prims.list -> FStar_Pprint.document) =
  fun uu___336_47415  ->
    match uu___336_47415 with
    | [] -> FStar_Pprint.empty
    | pats ->
        let uu____47427 =
          let uu____47428 =
            let uu____47429 =
              let uu____47430 = str "pattern"  in
              let uu____47432 =
                let uu____47433 =
                  let uu____47434 = p_disjunctivePats pats  in
                  FStar_Pprint.jump (Prims.parse_int "2")
                    (Prims.parse_int "0") uu____47434
                   in
                FStar_Pprint.op_Hat_Hat uu____47433 FStar_Pprint.rbrace  in
              FStar_Pprint.op_Hat_Slash_Hat uu____47430 uu____47432  in
            FStar_Pprint.op_Hat_Hat FStar_Pprint.colon uu____47429  in
          FStar_Pprint.op_Hat_Hat FStar_Pprint.lbrace uu____47428  in
        FStar_Pprint.group uu____47427

and (p_disjunctivePats :
  FStar_Parser_AST.term Prims.list Prims.list -> FStar_Pprint.document) =
  fun pats  ->
    let uu____47442 = str "\\/"  in
    FStar_Pprint.separate_map uu____47442 p_conjunctivePats pats

and (p_conjunctivePats :
  FStar_Parser_AST.term Prims.list -> FStar_Pprint.document) =
  fun pats  ->
    let uu____47449 =
      let uu____47450 = FStar_Pprint.op_Hat_Hat FStar_Pprint.semi break1  in
      FStar_Pprint.separate_map uu____47450 p_appTerm pats  in
    FStar_Pprint.group uu____47449

and (p_simpleTerm :
  Prims.bool -> Prims.bool -> FStar_Parser_AST.term -> FStar_Pprint.document)
  =
  fun ps  ->
    fun pb  ->
      fun e  ->
        match e.FStar_Parser_AST.tm with
        | FStar_Parser_AST.Abs (pats,e1) ->
            let uu____47462 = p_term_sep false pb e1  in
            (match uu____47462 with
             | (comm,doc1) ->
                 let prefix1 =
                   let uu____47471 = str "fun"  in
                   let uu____47473 =
                     let uu____47474 =
                       FStar_Pprint.separate_map break1 p_atomicPattern pats
                        in
                     FStar_Pprint.op_Hat_Slash_Hat uu____47474
                       FStar_Pprint.rarrow
                      in
                   op_Hat_Slash_Plus_Hat uu____47471 uu____47473  in
                 let uu____47475 =
                   if comm <> FStar_Pprint.empty
                   then
                     let uu____47477 =
                       let uu____47478 =
                         let uu____47479 =
                           FStar_Pprint.op_Hat_Hat FStar_Pprint.hardline doc1
                            in
                         FStar_Pprint.op_Hat_Hat comm uu____47479  in
                       FStar_Pprint.op_Hat_Hat FStar_Pprint.hardline
                         uu____47478
                        in
                     FStar_Pprint.op_Hat_Hat prefix1 uu____47477
                   else
                     (let uu____47482 = op_Hat_Slash_Plus_Hat prefix1 doc1
                         in
                      FStar_Pprint.group uu____47482)
                    in
                 let uu____47483 = paren_if ps  in uu____47483 uu____47475)
        | uu____47488 -> p_tmIff e

and (p_maybeFocusArrow : Prims.bool -> FStar_Pprint.document) =
  fun b  -> if b then str "~>" else FStar_Pprint.rarrow

and (p_patternBranch :
  Prims.bool ->
    (FStar_Parser_AST.pattern * FStar_Parser_AST.term
      FStar_Pervasives_Native.option * FStar_Parser_AST.term) ->
      FStar_Pprint.document)
  =
  fun pb  ->
    fun uu____47496  ->
      match uu____47496 with
      | (pat,when_opt,e) ->
          let one_pattern_branch p =
            let branch =
              match when_opt with
              | FStar_Pervasives_Native.None  ->
                  let uu____47520 =
                    let uu____47521 =
                      let uu____47522 =
                        let uu____47523 = p_tuplePattern p  in
                        let uu____47524 =
                          FStar_Pprint.op_Hat_Hat FStar_Pprint.space
                            FStar_Pprint.rarrow
                           in
                        FStar_Pprint.op_Hat_Hat uu____47523 uu____47524  in
                      FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____47522
                       in
                    FStar_Pprint.op_Hat_Hat FStar_Pprint.bar uu____47521  in
                  FStar_Pprint.group uu____47520
              | FStar_Pervasives_Native.Some f ->
                  let uu____47526 =
                    let uu____47527 =
                      let uu____47528 =
                        let uu____47529 =
                          let uu____47530 =
                            let uu____47531 = p_tuplePattern p  in
                            let uu____47532 = str "when"  in
                            FStar_Pprint.op_Hat_Slash_Hat uu____47531
                              uu____47532
                             in
                          FStar_Pprint.group uu____47530  in
                        let uu____47534 =
                          let uu____47535 =
                            let uu____47538 = p_tmFormula f  in
                            [uu____47538; FStar_Pprint.rarrow]  in
                          FStar_Pprint.flow break1 uu____47535  in
                        FStar_Pprint.op_Hat_Slash_Hat uu____47529 uu____47534
                         in
                      FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____47528
                       in
                    FStar_Pprint.op_Hat_Hat FStar_Pprint.bar uu____47527  in
                  FStar_Pprint.hang (Prims.parse_int "2") uu____47526
               in
            let uu____47540 = p_term_sep false pb e  in
            match uu____47540 with
            | (comm,doc1) ->
                if pb
                then
                  (if comm = FStar_Pprint.empty
                   then
                     let uu____47550 = op_Hat_Slash_Plus_Hat branch doc1  in
                     FStar_Pprint.group uu____47550
                   else
                     (let uu____47553 =
                        let uu____47554 =
                          let uu____47555 =
                            let uu____47556 =
                              let uu____47557 =
                                FStar_Pprint.op_Hat_Hat break1 comm  in
                              FStar_Pprint.op_Hat_Hat doc1 uu____47557  in
                            op_Hat_Slash_Plus_Hat branch uu____47556  in
                          FStar_Pprint.group uu____47555  in
                        let uu____47558 =
                          let uu____47559 =
                            let uu____47560 =
                              inline_comment_or_above comm doc1
                                FStar_Pprint.empty
                               in
                            jump2 uu____47560  in
                          FStar_Pprint.op_Hat_Hat branch uu____47559  in
                        FStar_Pprint.ifflat uu____47554 uu____47558  in
                      FStar_Pprint.group uu____47553))
                else
                  if comm <> FStar_Pprint.empty
                  then
                    (let uu____47564 =
                       let uu____47565 =
                         FStar_Pprint.op_Hat_Hat FStar_Pprint.hardline doc1
                          in
                       FStar_Pprint.op_Hat_Hat comm uu____47565  in
                     op_Hat_Slash_Plus_Hat branch uu____47564)
                  else op_Hat_Slash_Plus_Hat branch doc1
             in
          (match pat.FStar_Parser_AST.pat with
           | FStar_Parser_AST.PatOr pats ->
               (match FStar_List.rev pats with
                | hd1::tl1 ->
                    let last_pat_branch = one_pattern_branch hd1  in
                    let uu____47576 =
                      let uu____47577 =
                        let uu____47578 =
                          let uu____47579 =
                            let uu____47580 =
                              let uu____47581 =
                                FStar_Pprint.op_Hat_Hat FStar_Pprint.bar
                                  FStar_Pprint.space
                                 in
                              FStar_Pprint.op_Hat_Hat break1 uu____47581  in
                            FStar_Pprint.separate_map uu____47580
                              p_tuplePattern (FStar_List.rev tl1)
                             in
                          FStar_Pprint.op_Hat_Slash_Hat uu____47579
                            last_pat_branch
                           in
                        FStar_Pprint.op_Hat_Hat FStar_Pprint.space
                          uu____47578
                         in
                      FStar_Pprint.op_Hat_Hat FStar_Pprint.bar uu____47577
                       in
                    FStar_Pprint.group uu____47576
                | [] ->
                    failwith "Impossible: disjunctive pattern can't be empty")
           | uu____47583 -> one_pattern_branch pat)

and (p_tmIff : FStar_Parser_AST.term -> FStar_Pprint.document) =
  fun e  ->
    match e.FStar_Parser_AST.tm with
    | FStar_Parser_AST.Op
        ({ FStar_Ident.idText = "<==>"; FStar_Ident.idRange = uu____47585;_},e1::e2::[])
        ->
        let uu____47591 = str "<==>"  in
        let uu____47593 = p_tmImplies e1  in
        let uu____47594 = p_tmIff e2  in
        infix0 uu____47591 uu____47593 uu____47594
    | uu____47595 -> p_tmImplies e

and (p_tmImplies : FStar_Parser_AST.term -> FStar_Pprint.document) =
  fun e  ->
    match e.FStar_Parser_AST.tm with
    | FStar_Parser_AST.Op
        ({ FStar_Ident.idText = "==>"; FStar_Ident.idRange = uu____47597;_},e1::e2::[])
        ->
        let uu____47603 = str "==>"  in
        let uu____47605 =
          p_tmArrow (Arrows ((Prims.parse_int "2"), (Prims.parse_int "2")))
            false p_tmFormula e1
           in
        let uu____47611 = p_tmImplies e2  in
        infix0 uu____47603 uu____47605 uu____47611
    | uu____47612 ->
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
          let uu____47626 =
            FStar_List.splitAt
              ((FStar_List.length terms) - (Prims.parse_int "1")) terms
             in
          match uu____47626 with
          | (terms',last1) ->
              let uu____47646 =
                match style with
                | Arrows (n1,ln) ->
                    let uu____47681 =
                      let uu____47682 =
                        FStar_Pprint.op_Hat_Hat FStar_Pprint.rarrow break1
                         in
                      FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____47682
                       in
                    let uu____47683 =
                      FStar_Pprint.op_Hat_Hat FStar_Pprint.rarrow
                        FStar_Pprint.space
                       in
                    (n1, ln, terms', uu____47681, uu____47683)
                | Binders (n1,ln,parens1) ->
                    let uu____47697 =
                      if parens1
                      then FStar_List.map soft_parens_with_nesting terms'
                      else terms'  in
                    let uu____47705 =
                      FStar_Pprint.op_Hat_Hat FStar_Pprint.colon
                        FStar_Pprint.space
                       in
                    (n1, ln, uu____47697, break1, uu____47705)
                 in
              (match uu____47646 with
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
                    | _47738 when _47738 = (Prims.parse_int "1") ->
                        FStar_List.hd terms
                    | uu____47739 ->
                        let uu____47740 =
                          let uu____47741 =
                            let uu____47742 =
                              let uu____47743 =
                                FStar_Pprint.separate sep terms'1  in
                              let uu____47744 =
                                let uu____47745 =
                                  FStar_Pprint.op_Hat_Hat last_op1 last2  in
                                FStar_Pprint.op_Hat_Hat one_line_space
                                  uu____47745
                                 in
                              FStar_Pprint.op_Hat_Hat uu____47743 uu____47744
                               in
                            FStar_Pprint.op_Hat_Hat fs uu____47742  in
                          let uu____47746 =
                            let uu____47747 =
                              let uu____47748 =
                                let uu____47749 =
                                  let uu____47750 =
                                    FStar_Pprint.separate sep terms'1  in
                                  FStar_Pprint.op_Hat_Hat fs uu____47750  in
                                let uu____47751 =
                                  let uu____47752 =
                                    let uu____47753 =
                                      let uu____47754 =
                                        FStar_Pprint.op_Hat_Hat sep
                                          single_line_arg_indent
                                         in
                                      let uu____47755 =
                                        FStar_List.map
                                          (fun x  ->
                                             let uu____47761 =
                                               FStar_Pprint.hang
                                                 (Prims.parse_int "2") x
                                                in
                                             FStar_Pprint.align uu____47761)
                                          terms'1
                                         in
                                      FStar_Pprint.separate uu____47754
                                        uu____47755
                                       in
                                    FStar_Pprint.op_Hat_Hat
                                      single_line_arg_indent uu____47753
                                     in
                                  jump2 uu____47752  in
                                FStar_Pprint.ifflat uu____47749 uu____47751
                                 in
                              FStar_Pprint.group uu____47748  in
                            let uu____47763 =
                              let uu____47764 =
                                let uu____47765 =
                                  FStar_Pprint.op_Hat_Hat last_op1 last2  in
                                FStar_Pprint.hang last_n uu____47765  in
                              FStar_Pprint.align uu____47764  in
                            FStar_Pprint.prefix n1 (Prims.parse_int "1")
                              uu____47747 uu____47763
                             in
                          FStar_Pprint.ifflat uu____47741 uu____47746  in
                        FStar_Pprint.group uu____47740))

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
            | Arrows uu____47779 -> p_tmArrow' p_Tm e
            | Binders uu____47786 -> collapse_binders p_Tm e  in
          format_sig style terms false flat_space

and (p_tmArrow' :
  (FStar_Parser_AST.term -> FStar_Pprint.document) ->
    FStar_Parser_AST.term -> FStar_Pprint.document Prims.list)
  =
  fun p_Tm  ->
    fun e  ->
      match e.FStar_Parser_AST.tm with
      | FStar_Parser_AST.Product (bs,tgt) ->
          let uu____47809 = FStar_List.map (fun b  -> p_binder false b) bs
             in
          let uu____47815 = p_tmArrow' p_Tm tgt  in
          FStar_List.append uu____47809 uu____47815
      | uu____47818 -> let uu____47819 = p_Tm e  in [uu____47819]

and (collapse_binders :
  (FStar_Parser_AST.term -> FStar_Pprint.document) ->
    FStar_Parser_AST.term -> FStar_Pprint.document Prims.list)
  =
  fun p_Tm  ->
    fun e  ->
      let rec accumulate_binders p_Tm1 e1 =
        match e1.FStar_Parser_AST.tm with
        | FStar_Parser_AST.Product (bs,tgt) ->
            let uu____47872 = FStar_List.map (fun b  -> p_binder' false b) bs
               in
            let uu____47898 = accumulate_binders p_Tm1 tgt  in
            FStar_List.append uu____47872 uu____47898
        | uu____47921 ->
            let uu____47922 =
              let uu____47933 = p_Tm1 e1  in
              (uu____47933, FStar_Pervasives_Native.None, cat_with_colon)  in
            [uu____47922]
         in
      let fold_fun bs x =
        let uu____48031 = x  in
        match uu____48031 with
        | (b1,t1,f1) ->
            (match bs with
             | [] -> [([b1], t1, f1)]
             | hd1::tl1 ->
                 let uu____48163 = hd1  in
                 (match uu____48163 with
                  | (b2s,t2,uu____48192) ->
                      (match (t1, t2) with
                       | (FStar_Pervasives_Native.Some
                          typ1,FStar_Pervasives_Native.Some typ2) ->
                           if typ1 = typ2
                           then ((FStar_List.append b2s [b1]), t1, f1) :: tl1
                           else ([b1], t1, f1) :: hd1 :: tl1
                       | uu____48294 -> ([b1], t1, f1) :: bs)))
         in
      let p_collapsed_binder cb =
        let uu____48351 = cb  in
        match uu____48351 with
        | (bs,t,f) ->
            (match t with
             | FStar_Pervasives_Native.None  ->
                 (match bs with
                  | b::[] -> b
                  | uu____48380 -> failwith "Impossible")
             | FStar_Pervasives_Native.Some typ ->
                 (match bs with
                  | [] -> failwith "Impossible"
                  | b::[] -> f b typ
                  | hd1::tl1 ->
                      let uu____48391 =
                        FStar_List.fold_left
                          (fun x  ->
                             fun y  ->
                               let uu____48397 =
                                 FStar_Pprint.op_Hat_Hat FStar_Pprint.space y
                                  in
                               FStar_Pprint.op_Hat_Hat x uu____48397) hd1 tl1
                         in
                      f uu____48391 typ))
         in
      let binders =
        let uu____48413 = accumulate_binders p_Tm e  in
        FStar_List.fold_left fold_fun [] uu____48413  in
      map_rev p_collapsed_binder binders

and (p_tmFormula : FStar_Parser_AST.term -> FStar_Pprint.document) =
  fun e  ->
    let conj =
      let uu____48476 =
        let uu____48477 = str "/\\"  in
        FStar_Pprint.op_Hat_Hat uu____48477 break1  in
      FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____48476  in
    let disj =
      let uu____48480 =
        let uu____48481 = str "\\/"  in
        FStar_Pprint.op_Hat_Hat uu____48481 break1  in
      FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____48480  in
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
        ({ FStar_Ident.idText = "\\/"; FStar_Ident.idRange = uu____48501;_},e1::e2::[])
        ->
        let uu____48507 = p_tmDisjunction e1  in
        let uu____48512 =
          let uu____48517 = p_tmConjunction e2  in [uu____48517]  in
        FStar_List.append uu____48507 uu____48512
    | uu____48526 -> let uu____48527 = p_tmConjunction e  in [uu____48527]

and (p_tmConjunction :
  FStar_Parser_AST.term -> FStar_Pprint.document Prims.list) =
  fun e  ->
    match e.FStar_Parser_AST.tm with
    | FStar_Parser_AST.Op
        ({ FStar_Ident.idText = "/\\"; FStar_Ident.idRange = uu____48537;_},e1::e2::[])
        ->
        let uu____48543 = p_tmConjunction e1  in
        let uu____48546 = let uu____48549 = p_tmTuple e2  in [uu____48549]
           in
        FStar_List.append uu____48543 uu____48546
    | uu____48550 -> let uu____48551 = p_tmTuple e  in [uu____48551]

and (p_tmTuple : FStar_Parser_AST.term -> FStar_Pprint.document) =
  fun e  -> with_comment p_tmTuple' e e.FStar_Parser_AST.range

and (p_tmTuple' : FStar_Parser_AST.term -> FStar_Pprint.document) =
  fun e  ->
    match e.FStar_Parser_AST.tm with
    | FStar_Parser_AST.Construct (lid,args) when
        (is_tuple_constructor lid) && (all_explicit args) ->
        let uu____48568 = FStar_Pprint.op_Hat_Hat FStar_Pprint.comma break1
           in
        FStar_Pprint.separate_map uu____48568
          (fun uu____48576  ->
             match uu____48576 with | (e1,uu____48582) -> p_tmEq e1) args
    | uu____48583 -> p_tmEq e

and (paren_if_gt :
  Prims.int -> Prims.int -> FStar_Pprint.document -> FStar_Pprint.document) =
  fun curr  ->
    fun mine  ->
      fun doc1  ->
        if mine <= curr
        then doc1
        else
          (let uu____48592 =
             let uu____48593 =
               FStar_Pprint.op_Hat_Hat doc1 FStar_Pprint.rparen  in
             FStar_Pprint.op_Hat_Hat FStar_Pprint.lparen uu____48593  in
           FStar_Pprint.group uu____48592)

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
               (let uu____48612 = FStar_Ident.text_of_id op  in
                uu____48612 = "="))
              ||
              (let uu____48617 = FStar_Ident.text_of_id op  in
               uu____48617 = "|>")
            ->
            let op1 = FStar_Ident.text_of_id op  in
            let uu____48623 = levels op1  in
            (match uu____48623 with
             | (left1,mine,right1) ->
                 let uu____48642 =
                   let uu____48643 = FStar_All.pipe_left str op1  in
                   let uu____48645 = p_tmEqWith' p_X left1 e1  in
                   let uu____48646 = p_tmEqWith' p_X right1 e2  in
                   infix0 uu____48643 uu____48645 uu____48646  in
                 paren_if_gt curr mine uu____48642)
        | FStar_Parser_AST.Op
            ({ FStar_Ident.idText = ":=";
               FStar_Ident.idRange = uu____48647;_},e1::e2::[])
            ->
            let uu____48653 =
              let uu____48654 = p_tmEqWith p_X e1  in
              let uu____48655 =
                let uu____48656 =
                  let uu____48657 =
                    let uu____48658 = p_tmEqWith p_X e2  in
                    op_Hat_Slash_Plus_Hat FStar_Pprint.equals uu____48658  in
                  FStar_Pprint.op_Hat_Hat FStar_Pprint.colon uu____48657  in
                FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____48656  in
              FStar_Pprint.op_Hat_Hat uu____48654 uu____48655  in
            FStar_Pprint.group uu____48653
        | FStar_Parser_AST.Op
            ({ FStar_Ident.idText = "-"; FStar_Ident.idRange = uu____48659;_},e1::[])
            ->
            let uu____48664 = levels "-"  in
            (match uu____48664 with
             | (left1,mine,right1) ->
                 let uu____48684 = p_tmEqWith' p_X mine e1  in
                 FStar_Pprint.op_Hat_Slash_Hat FStar_Pprint.minus uu____48684)
        | uu____48685 -> p_tmNoEqWith p_X e

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
              (lid,(e1,uu____48733)::(e2,uu____48735)::[]) when
              (FStar_Ident.lid_equals lid FStar_Parser_Const.cons_lid) &&
                (let uu____48755 = is_list e  in
                 Prims.op_Negation uu____48755)
              ->
              let op = "::"  in
              let uu____48760 = levels op  in
              (match uu____48760 with
               | (left1,mine,right1) ->
                   let uu____48779 =
                     let uu____48780 = str op  in
                     let uu____48781 = p_tmNoEqWith' false p_X left1 e1  in
                     let uu____48783 = p_tmNoEqWith' false p_X right1 e2  in
                     infix0 uu____48780 uu____48781 uu____48783  in
                   paren_if_gt curr mine uu____48779)
          | FStar_Parser_AST.Sum (binders,res) ->
              let op = "&"  in
              let uu____48802 = levels op  in
              (match uu____48802 with
               | (left1,mine,right1) ->
                   let p_dsumfst bt =
                     match bt with
                     | FStar_Util.Inl b ->
                         let uu____48836 = p_binder false b  in
                         let uu____48838 =
                           let uu____48839 =
                             let uu____48840 = str op  in
                             FStar_Pprint.op_Hat_Hat uu____48840 break1  in
                           FStar_Pprint.op_Hat_Hat FStar_Pprint.space
                             uu____48839
                            in
                         FStar_Pprint.op_Hat_Hat uu____48836 uu____48838
                     | FStar_Util.Inr t ->
                         let uu____48842 = p_tmNoEqWith' false p_X left1 t
                            in
                         let uu____48844 =
                           let uu____48845 =
                             let uu____48846 = str op  in
                             FStar_Pprint.op_Hat_Hat uu____48846 break1  in
                           FStar_Pprint.op_Hat_Hat FStar_Pprint.space
                             uu____48845
                            in
                         FStar_Pprint.op_Hat_Hat uu____48842 uu____48844
                      in
                   let uu____48847 =
                     let uu____48848 =
                       FStar_Pprint.concat_map p_dsumfst binders  in
                     let uu____48853 = p_tmNoEqWith' false p_X right1 res  in
                     FStar_Pprint.op_Hat_Hat uu____48848 uu____48853  in
                   paren_if_gt curr mine uu____48847)
          | FStar_Parser_AST.Op
              ({ FStar_Ident.idText = "*";
                 FStar_Ident.idRange = uu____48855;_},e1::e2::[])
              when FStar_ST.op_Bang unfold_tuples ->
              let op = "*"  in
              let uu____48885 = levels op  in
              (match uu____48885 with
               | (left1,mine,right1) ->
                   if inside_tuple
                   then
                     let uu____48905 = str op  in
                     let uu____48906 = p_tmNoEqWith' true p_X left1 e1  in
                     let uu____48908 = p_tmNoEqWith' true p_X right1 e2  in
                     infix0 uu____48905 uu____48906 uu____48908
                   else
                     (let uu____48912 =
                        let uu____48913 = str op  in
                        let uu____48914 = p_tmNoEqWith' true p_X left1 e1  in
                        let uu____48916 = p_tmNoEqWith' true p_X right1 e2
                           in
                        infix0 uu____48913 uu____48914 uu____48916  in
                      paren_if_gt curr mine uu____48912))
          | FStar_Parser_AST.Op (op,e1::e2::[]) when is_operatorInfix34 op ->
              let op1 = FStar_Ident.text_of_id op  in
              let uu____48925 = levels op1  in
              (match uu____48925 with
               | (left1,mine,right1) ->
                   let uu____48944 =
                     let uu____48945 = str op1  in
                     let uu____48946 = p_tmNoEqWith' false p_X left1 e1  in
                     let uu____48948 = p_tmNoEqWith' false p_X right1 e2  in
                     infix0 uu____48945 uu____48946 uu____48948  in
                   paren_if_gt curr mine uu____48944)
          | FStar_Parser_AST.Record (with_opt,record_fields) ->
              let uu____48968 =
                let uu____48969 =
                  default_or_map FStar_Pprint.empty p_with_clause with_opt
                   in
                let uu____48970 =
                  let uu____48971 =
                    FStar_Pprint.op_Hat_Hat FStar_Pprint.semi break1  in
                  separate_map_last uu____48971 p_simpleDef record_fields  in
                FStar_Pprint.op_Hat_Hat uu____48969 uu____48970  in
              braces_with_nesting uu____48968
          | FStar_Parser_AST.Op
              ({ FStar_Ident.idText = "~";
                 FStar_Ident.idRange = uu____48976;_},e1::[])
              ->
              let uu____48981 =
                let uu____48982 = str "~"  in
                let uu____48984 = p_atomicTerm e1  in
                FStar_Pprint.op_Hat_Hat uu____48982 uu____48984  in
              FStar_Pprint.group uu____48981
          | FStar_Parser_AST.Paren p when inside_tuple ->
              (match p.FStar_Parser_AST.tm with
               | FStar_Parser_AST.Op
                   ({ FStar_Ident.idText = "*";
                      FStar_Ident.idRange = uu____48986;_},e1::e2::[])
                   ->
                   let op = "*"  in
                   let uu____48995 = levels op  in
                   (match uu____48995 with
                    | (left1,mine,right1) ->
                        let uu____49014 =
                          let uu____49015 = str op  in
                          let uu____49016 = p_tmNoEqWith' true p_X left1 e1
                             in
                          let uu____49018 = p_tmNoEqWith' true p_X right1 e2
                             in
                          infix0 uu____49015 uu____49016 uu____49018  in
                        paren_if_gt curr mine uu____49014)
               | uu____49020 -> p_X e)
          | uu____49021 -> p_X e

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
        let uu____49028 =
          let uu____49029 = p_lident lid  in
          let uu____49030 =
            let uu____49031 = p_appTerm e1  in
            FStar_Pprint.op_Hat_Slash_Hat FStar_Pprint.colon uu____49031  in
          FStar_Pprint.op_Hat_Slash_Hat uu____49029 uu____49030  in
        FStar_Pprint.group uu____49028
    | FStar_Parser_AST.Refine (b,phi) -> p_refinedBinder b phi
    | uu____49034 -> p_appTerm e

and (p_with_clause : FStar_Parser_AST.term -> FStar_Pprint.document) =
  fun e  ->
    let uu____49036 = p_appTerm e  in
    let uu____49037 =
      let uu____49038 =
        let uu____49039 = str "with"  in
        FStar_Pprint.op_Hat_Hat uu____49039 break1  in
      FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____49038  in
    FStar_Pprint.op_Hat_Hat uu____49036 uu____49037

and (p_refinedBinder :
  FStar_Parser_AST.binder -> FStar_Parser_AST.term -> FStar_Pprint.document)
  =
  fun b  ->
    fun phi  ->
      match b.FStar_Parser_AST.b with
      | FStar_Parser_AST.Annotated (lid,t) ->
          let uu____49045 = p_lident lid  in
          p_refinement b.FStar_Parser_AST.aqual uu____49045 t phi
      | FStar_Parser_AST.TAnnotated uu____49046 ->
          failwith "Is this still used ?"
      | FStar_Parser_AST.Variable uu____49052 ->
          let uu____49053 =
            let uu____49055 = FStar_Parser_AST.binder_to_string b  in
            FStar_Util.format1
              "Imposible : a refined binder ought to be annotated %s"
              uu____49055
             in
          failwith uu____49053
      | FStar_Parser_AST.TVariable uu____49058 ->
          let uu____49059 =
            let uu____49061 = FStar_Parser_AST.binder_to_string b  in
            FStar_Util.format1
              "Imposible : a refined binder ought to be annotated %s"
              uu____49061
             in
          failwith uu____49059
      | FStar_Parser_AST.NoName uu____49064 ->
          let uu____49065 =
            let uu____49067 = FStar_Parser_AST.binder_to_string b  in
            FStar_Util.format1
              "Imposible : a refined binder ought to be annotated %s"
              uu____49067
             in
          failwith uu____49065

and (p_simpleDef :
  Prims.bool ->
    (FStar_Ident.lid * FStar_Parser_AST.term) -> FStar_Pprint.document)
  =
  fun ps  ->
    fun uu____49071  ->
      match uu____49071 with
      | (lid,e) ->
          let uu____49079 =
            let uu____49080 = p_qlident lid  in
            let uu____49081 =
              let uu____49082 = p_noSeqTermAndComment ps false e  in
              FStar_Pprint.op_Hat_Slash_Hat FStar_Pprint.equals uu____49082
               in
            FStar_Pprint.op_Hat_Slash_Hat uu____49080 uu____49081  in
          FStar_Pprint.group uu____49079

and (p_appTerm : FStar_Parser_AST.term -> FStar_Pprint.document) =
  fun e  ->
    match e.FStar_Parser_AST.tm with
    | FStar_Parser_AST.App uu____49085 when is_general_application e ->
        let uu____49092 = head_and_args e  in
        (match uu____49092 with
         | (head1,args) ->
             (match args with
              | e1::e2::[] when
                  (FStar_Pervasives_Native.snd e1) = FStar_Parser_AST.Infix
                  ->
                  let uu____49139 = p_argTerm e1  in
                  let uu____49140 =
                    let uu____49141 =
                      let uu____49142 =
                        let uu____49143 = str "`"  in
                        let uu____49145 =
                          let uu____49146 = p_indexingTerm head1  in
                          let uu____49147 = str "`"  in
                          FStar_Pprint.op_Hat_Hat uu____49146 uu____49147  in
                        FStar_Pprint.op_Hat_Hat uu____49143 uu____49145  in
                      FStar_Pprint.group uu____49142  in
                    let uu____49149 = p_argTerm e2  in
                    FStar_Pprint.op_Hat_Slash_Hat uu____49141 uu____49149  in
                  FStar_Pprint.op_Hat_Slash_Hat uu____49139 uu____49140
              | uu____49150 ->
                  let uu____49157 =
                    let uu____49168 =
                      FStar_ST.op_Bang should_print_fs_typ_app  in
                    if uu____49168
                    then
                      let uu____49202 =
                        FStar_Util.take
                          (fun uu____49226  ->
                             match uu____49226 with
                             | (uu____49232,aq) ->
                                 aq = FStar_Parser_AST.FsTypApp) args
                         in
                      match uu____49202 with
                      | (fs_typ_args,args1) ->
                          let uu____49270 =
                            let uu____49271 = p_indexingTerm head1  in
                            let uu____49272 =
                              let uu____49273 =
                                FStar_Pprint.op_Hat_Hat FStar_Pprint.comma
                                  break1
                                 in
                              soft_surround_map_or_flow (Prims.parse_int "2")
                                (Prims.parse_int "0") FStar_Pprint.empty
                                FStar_Pprint.langle uu____49273
                                FStar_Pprint.rangle p_fsTypArg fs_typ_args
                               in
                            FStar_Pprint.op_Hat_Hat uu____49271 uu____49272
                             in
                          (uu____49270, args1)
                    else
                      (let uu____49288 = p_indexingTerm head1  in
                       (uu____49288, args))
                     in
                  (match uu____49157 with
                   | (head_doc,args1) ->
                       let uu____49309 =
                         let uu____49310 =
                           FStar_Pprint.op_Hat_Hat head_doc
                             FStar_Pprint.space
                            in
                         soft_surround_map_or_flow (Prims.parse_int "2")
                           (Prims.parse_int "0") head_doc uu____49310 break1
                           FStar_Pprint.empty p_argTerm args1
                          in
                       FStar_Pprint.group uu____49309)))
    | FStar_Parser_AST.Construct (lid,args) when
        (is_general_construction e) &&
          (let uu____49332 = is_dtuple_constructor lid  in
           Prims.op_Negation uu____49332)
        ->
        (match args with
         | [] -> p_quident lid
         | arg::[] ->
             let uu____49351 =
               let uu____49352 = p_quident lid  in
               let uu____49353 = p_argTerm arg  in
               FStar_Pprint.op_Hat_Slash_Hat uu____49352 uu____49353  in
             FStar_Pprint.group uu____49351
         | hd1::tl1 ->
             let uu____49370 =
               let uu____49371 =
                 let uu____49372 =
                   let uu____49373 = p_quident lid  in
                   let uu____49374 = p_argTerm hd1  in
                   prefix2 uu____49373 uu____49374  in
                 FStar_Pprint.group uu____49372  in
               let uu____49375 =
                 let uu____49376 =
                   FStar_Pprint.separate_map break1 p_argTerm tl1  in
                 jump2 uu____49376  in
               FStar_Pprint.op_Hat_Hat uu____49371 uu____49375  in
             FStar_Pprint.group uu____49370)
    | uu____49381 -> p_indexingTerm e

and (p_argTerm :
  (FStar_Parser_AST.term * FStar_Parser_AST.imp) -> FStar_Pprint.document) =
  fun arg_imp  ->
    match arg_imp with
    | (u,FStar_Parser_AST.UnivApp ) -> p_universe u
    | (e,FStar_Parser_AST.FsTypApp ) ->
        (FStar_Errors.log_issue e.FStar_Parser_AST.range
           (FStar_Errors.Warning_UnexpectedFsTypApp,
             "Unexpected FsTypApp, output might not be formatted correctly.");
         (let uu____49392 = p_indexingTerm e  in
          FStar_Pprint.surround (Prims.parse_int "2") (Prims.parse_int "1")
            FStar_Pprint.langle uu____49392 FStar_Pprint.rangle))
    | (e,FStar_Parser_AST.Hash ) ->
        let uu____49396 = str "#"  in
        let uu____49398 = p_indexingTerm e  in
        FStar_Pprint.op_Hat_Hat uu____49396 uu____49398
    | (e,FStar_Parser_AST.HashBrace t) ->
        let uu____49401 = str "#["  in
        let uu____49403 =
          let uu____49404 = p_indexingTerm t  in
          let uu____49405 =
            let uu____49406 = str "]"  in
            let uu____49408 = p_indexingTerm e  in
            FStar_Pprint.op_Hat_Hat uu____49406 uu____49408  in
          FStar_Pprint.op_Hat_Hat uu____49404 uu____49405  in
        FStar_Pprint.op_Hat_Hat uu____49401 uu____49403
    | (e,FStar_Parser_AST.Infix ) -> p_indexingTerm e
    | (e,FStar_Parser_AST.Nothing ) -> p_indexingTerm e

and (p_fsTypArg :
  (FStar_Parser_AST.term * FStar_Parser_AST.imp) -> FStar_Pprint.document) =
  fun uu____49411  ->
    match uu____49411 with | (e,uu____49417) -> p_indexingTerm e

and (p_indexingTerm_aux :
  (FStar_Parser_AST.term -> FStar_Pprint.document) ->
    FStar_Parser_AST.term -> FStar_Pprint.document)
  =
  fun exit1  ->
    fun e  ->
      match e.FStar_Parser_AST.tm with
      | FStar_Parser_AST.Op
          ({ FStar_Ident.idText = ".()"; FStar_Ident.idRange = uu____49422;_},e1::e2::[])
          ->
          let uu____49428 =
            let uu____49429 = p_indexingTerm_aux p_atomicTermNotQUident e1
               in
            let uu____49430 =
              let uu____49431 =
                let uu____49432 = p_term false false e2  in
                soft_parens_with_nesting uu____49432  in
              FStar_Pprint.op_Hat_Hat FStar_Pprint.dot uu____49431  in
            FStar_Pprint.op_Hat_Hat uu____49429 uu____49430  in
          FStar_Pprint.group uu____49428
      | FStar_Parser_AST.Op
          ({ FStar_Ident.idText = ".[]"; FStar_Ident.idRange = uu____49435;_},e1::e2::[])
          ->
          let uu____49441 =
            let uu____49442 = p_indexingTerm_aux p_atomicTermNotQUident e1
               in
            let uu____49443 =
              let uu____49444 =
                let uu____49445 = p_term false false e2  in
                soft_brackets_with_nesting uu____49445  in
              FStar_Pprint.op_Hat_Hat FStar_Pprint.dot uu____49444  in
            FStar_Pprint.op_Hat_Hat uu____49442 uu____49443  in
          FStar_Pprint.group uu____49441
      | uu____49448 -> exit1 e

and (p_indexingTerm : FStar_Parser_AST.term -> FStar_Pprint.document) =
  fun e  -> p_indexingTerm_aux p_atomicTerm e

and (p_atomicTerm : FStar_Parser_AST.term -> FStar_Pprint.document) =
  fun e  ->
    match e.FStar_Parser_AST.tm with
    | FStar_Parser_AST.LetOpen (lid,e1) ->
        let uu____49453 = p_quident lid  in
        let uu____49454 =
          let uu____49455 =
            let uu____49456 = p_term false false e1  in
            soft_parens_with_nesting uu____49456  in
          FStar_Pprint.op_Hat_Hat FStar_Pprint.dot uu____49455  in
        FStar_Pprint.op_Hat_Hat uu____49453 uu____49454
    | FStar_Parser_AST.Name lid -> p_quident lid
    | FStar_Parser_AST.Op (op,e1::[]) when is_general_prefix_op op ->
        let uu____49464 =
          let uu____49465 = FStar_Ident.text_of_id op  in str uu____49465  in
        let uu____49467 = p_atomicTerm e1  in
        FStar_Pprint.op_Hat_Hat uu____49464 uu____49467
    | uu____49468 -> p_atomicTermNotQUident e

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
         | uu____49481 -> p_constant c)
    | FStar_Parser_AST.Name lid when
        FStar_Ident.lid_equals lid FStar_Parser_Const.true_lid -> str "True"
    | FStar_Parser_AST.Name lid when
        FStar_Ident.lid_equals lid FStar_Parser_Const.false_lid ->
        str "False"
    | FStar_Parser_AST.Op (op,e1::[]) when is_general_prefix_op op ->
        let uu____49490 =
          let uu____49491 = FStar_Ident.text_of_id op  in str uu____49491  in
        let uu____49493 = p_atomicTermNotQUident e1  in
        FStar_Pprint.op_Hat_Hat uu____49490 uu____49493
    | FStar_Parser_AST.Op (op,[]) ->
        let uu____49497 =
          let uu____49498 =
            let uu____49499 =
              let uu____49500 = FStar_Ident.text_of_id op  in str uu____49500
               in
            let uu____49502 =
              FStar_Pprint.op_Hat_Hat FStar_Pprint.space FStar_Pprint.rparen
               in
            FStar_Pprint.op_Hat_Hat uu____49499 uu____49502  in
          FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____49498  in
        FStar_Pprint.op_Hat_Hat FStar_Pprint.lparen uu____49497
    | FStar_Parser_AST.Construct (lid,args) when is_dtuple_constructor lid ->
        let uu____49517 = all_explicit args  in
        if uu____49517
        then
          let uu____49520 =
            FStar_Pprint.op_Hat_Hat FStar_Pprint.lparen FStar_Pprint.bar  in
          let uu____49521 =
            let uu____49522 =
              FStar_Pprint.op_Hat_Hat FStar_Pprint.comma break1  in
            let uu____49523 = FStar_List.map FStar_Pervasives_Native.fst args
               in
            FStar_Pprint.separate_map uu____49522 p_tmEq uu____49523  in
          let uu____49530 =
            FStar_Pprint.op_Hat_Hat FStar_Pprint.bar FStar_Pprint.rparen  in
          FStar_Pprint.surround (Prims.parse_int "2") (Prims.parse_int "1")
            uu____49520 uu____49521 uu____49530
        else
          (match args with
           | [] -> p_quident lid
           | arg::[] ->
               let uu____49552 =
                 let uu____49553 = p_quident lid  in
                 let uu____49554 = p_argTerm arg  in
                 FStar_Pprint.op_Hat_Slash_Hat uu____49553 uu____49554  in
               FStar_Pprint.group uu____49552
           | hd1::tl1 ->
               let uu____49571 =
                 let uu____49572 =
                   let uu____49573 =
                     let uu____49574 = p_quident lid  in
                     let uu____49575 = p_argTerm hd1  in
                     prefix2 uu____49574 uu____49575  in
                   FStar_Pprint.group uu____49573  in
                 let uu____49576 =
                   let uu____49577 =
                     FStar_Pprint.separate_map break1 p_argTerm tl1  in
                   jump2 uu____49577  in
                 FStar_Pprint.op_Hat_Hat uu____49572 uu____49576  in
               FStar_Pprint.group uu____49571)
    | FStar_Parser_AST.Project (e1,lid) ->
        let uu____49584 =
          let uu____49585 = p_atomicTermNotQUident e1  in
          let uu____49586 =
            let uu____49587 = p_qlident lid  in
            FStar_Pprint.op_Hat_Hat FStar_Pprint.dot uu____49587  in
          FStar_Pprint.prefix (Prims.parse_int "2") (Prims.parse_int "0")
            uu____49585 uu____49586
           in
        FStar_Pprint.group uu____49584
    | uu____49590 -> p_projectionLHS e

and (p_projectionLHS : FStar_Parser_AST.term -> FStar_Pprint.document) =
  fun e  ->
    match e.FStar_Parser_AST.tm with
    | FStar_Parser_AST.Var lid -> p_qlident lid
    | FStar_Parser_AST.Projector (constr_lid,field_lid) ->
        let uu____49595 = p_quident constr_lid  in
        let uu____49596 =
          let uu____49597 =
            let uu____49598 = p_lident field_lid  in
            FStar_Pprint.op_Hat_Hat FStar_Pprint.dot uu____49598  in
          FStar_Pprint.op_Hat_Hat FStar_Pprint.qmark uu____49597  in
        FStar_Pprint.op_Hat_Hat uu____49595 uu____49596
    | FStar_Parser_AST.Discrim constr_lid ->
        let uu____49600 = p_quident constr_lid  in
        FStar_Pprint.op_Hat_Hat uu____49600 FStar_Pprint.qmark
    | FStar_Parser_AST.Paren e1 ->
        let uu____49602 = p_term_sep false false e1  in
        (match uu____49602 with
         | (comm,t) ->
             let doc1 = soft_parens_with_nesting t  in
             if comm = FStar_Pprint.empty
             then doc1
             else
               (let uu____49615 =
                  FStar_Pprint.op_Hat_Hat FStar_Pprint.hardline doc1  in
                FStar_Pprint.op_Hat_Hat comm uu____49615))
    | uu____49616 when is_array e ->
        let es = extract_from_list e  in
        let uu____49620 =
          FStar_Pprint.op_Hat_Hat FStar_Pprint.lbracket FStar_Pprint.bar  in
        let uu____49621 =
          let uu____49622 = FStar_Pprint.op_Hat_Hat FStar_Pprint.semi break1
             in
          separate_map_or_flow_last uu____49622
            (fun ps  -> p_noSeqTermAndComment ps false) es
           in
        let uu____49627 =
          FStar_Pprint.op_Hat_Hat FStar_Pprint.bar FStar_Pprint.rbracket  in
        FStar_Pprint.surround (Prims.parse_int "2") (Prims.parse_int "0")
          uu____49620 uu____49621 uu____49627
    | uu____49630 when is_list e ->
        let uu____49631 =
          let uu____49632 = FStar_Pprint.op_Hat_Hat FStar_Pprint.semi break1
             in
          let uu____49633 = extract_from_list e  in
          separate_map_or_flow_last uu____49632
            (fun ps  -> p_noSeqTermAndComment ps false) uu____49633
           in
        FStar_Pprint.surround (Prims.parse_int "2") (Prims.parse_int "0")
          FStar_Pprint.lbracket uu____49631 FStar_Pprint.rbracket
    | uu____49642 when is_lex_list e ->
        let uu____49643 =
          FStar_Pprint.op_Hat_Hat FStar_Pprint.percent FStar_Pprint.lbracket
           in
        let uu____49644 =
          let uu____49645 = FStar_Pprint.op_Hat_Hat FStar_Pprint.semi break1
             in
          let uu____49646 = extract_from_list e  in
          separate_map_or_flow_last uu____49645
            (fun ps  -> p_noSeqTermAndComment ps false) uu____49646
           in
        FStar_Pprint.surround (Prims.parse_int "2") (Prims.parse_int "1")
          uu____49643 uu____49644 FStar_Pprint.rbracket
    | uu____49655 when is_ref_set e ->
        let es = extract_from_ref_set e  in
        let uu____49659 =
          FStar_Pprint.op_Hat_Hat FStar_Pprint.bang FStar_Pprint.lbrace  in
        let uu____49660 =
          let uu____49661 = FStar_Pprint.op_Hat_Hat FStar_Pprint.comma break1
             in
          separate_map_or_flow uu____49661 p_appTerm es  in
        FStar_Pprint.surround (Prims.parse_int "2") (Prims.parse_int "0")
          uu____49659 uu____49660 FStar_Pprint.rbrace
    | FStar_Parser_AST.Labeled (e1,s,b) ->
        let uu____49671 = str (Prims.op_Hat "(*" (Prims.op_Hat s "*)"))  in
        let uu____49674 = p_term false false e1  in
        FStar_Pprint.op_Hat_Slash_Hat uu____49671 uu____49674
    | FStar_Parser_AST.Op (op,args) when
        let uu____49683 = handleable_op op args  in
        Prims.op_Negation uu____49683 ->
        let uu____49685 =
          let uu____49687 =
            let uu____49689 = FStar_Ident.text_of_id op  in
            let uu____49691 =
              let uu____49693 =
                let uu____49695 =
                  FStar_Util.string_of_int (FStar_List.length args)  in
                Prims.op_Hat uu____49695
                  " arguments couldn't be handled by the pretty printer"
                 in
              Prims.op_Hat " with " uu____49693  in
            Prims.op_Hat uu____49689 uu____49691  in
          Prims.op_Hat "Operation " uu____49687  in
        failwith uu____49685
    | FStar_Parser_AST.Uvar id1 ->
        failwith "Unexpected universe variable out of universe context"
    | FStar_Parser_AST.Wild  ->
        let uu____49702 = p_term false false e  in
        soft_parens_with_nesting uu____49702
    | FStar_Parser_AST.Const uu____49705 ->
        let uu____49706 = p_term false false e  in
        soft_parens_with_nesting uu____49706
    | FStar_Parser_AST.Op uu____49709 ->
        let uu____49716 = p_term false false e  in
        soft_parens_with_nesting uu____49716
    | FStar_Parser_AST.Tvar uu____49719 ->
        let uu____49720 = p_term false false e  in
        soft_parens_with_nesting uu____49720
    | FStar_Parser_AST.Var uu____49723 ->
        let uu____49724 = p_term false false e  in
        soft_parens_with_nesting uu____49724
    | FStar_Parser_AST.Name uu____49727 ->
        let uu____49728 = p_term false false e  in
        soft_parens_with_nesting uu____49728
    | FStar_Parser_AST.Construct uu____49731 ->
        let uu____49742 = p_term false false e  in
        soft_parens_with_nesting uu____49742
    | FStar_Parser_AST.Abs uu____49745 ->
        let uu____49752 = p_term false false e  in
        soft_parens_with_nesting uu____49752
    | FStar_Parser_AST.App uu____49755 ->
        let uu____49762 = p_term false false e  in
        soft_parens_with_nesting uu____49762
    | FStar_Parser_AST.Let uu____49765 ->
        let uu____49786 = p_term false false e  in
        soft_parens_with_nesting uu____49786
    | FStar_Parser_AST.LetOpen uu____49789 ->
        let uu____49794 = p_term false false e  in
        soft_parens_with_nesting uu____49794
    | FStar_Parser_AST.Seq uu____49797 ->
        let uu____49802 = p_term false false e  in
        soft_parens_with_nesting uu____49802
    | FStar_Parser_AST.Bind uu____49805 ->
        let uu____49812 = p_term false false e  in
        soft_parens_with_nesting uu____49812
    | FStar_Parser_AST.If uu____49815 ->
        let uu____49822 = p_term false false e  in
        soft_parens_with_nesting uu____49822
    | FStar_Parser_AST.Match uu____49825 ->
        let uu____49840 = p_term false false e  in
        soft_parens_with_nesting uu____49840
    | FStar_Parser_AST.TryWith uu____49843 ->
        let uu____49858 = p_term false false e  in
        soft_parens_with_nesting uu____49858
    | FStar_Parser_AST.Ascribed uu____49861 ->
        let uu____49870 = p_term false false e  in
        soft_parens_with_nesting uu____49870
    | FStar_Parser_AST.Record uu____49873 ->
        let uu____49886 = p_term false false e  in
        soft_parens_with_nesting uu____49886
    | FStar_Parser_AST.Project uu____49889 ->
        let uu____49894 = p_term false false e  in
        soft_parens_with_nesting uu____49894
    | FStar_Parser_AST.Product uu____49897 ->
        let uu____49904 = p_term false false e  in
        soft_parens_with_nesting uu____49904
    | FStar_Parser_AST.Sum uu____49907 ->
        let uu____49918 = p_term false false e  in
        soft_parens_with_nesting uu____49918
    | FStar_Parser_AST.QForall uu____49921 ->
        let uu____49934 = p_term false false e  in
        soft_parens_with_nesting uu____49934
    | FStar_Parser_AST.QExists uu____49937 ->
        let uu____49950 = p_term false false e  in
        soft_parens_with_nesting uu____49950
    | FStar_Parser_AST.Refine uu____49953 ->
        let uu____49958 = p_term false false e  in
        soft_parens_with_nesting uu____49958
    | FStar_Parser_AST.NamedTyp uu____49961 ->
        let uu____49966 = p_term false false e  in
        soft_parens_with_nesting uu____49966
    | FStar_Parser_AST.Requires uu____49969 ->
        let uu____49977 = p_term false false e  in
        soft_parens_with_nesting uu____49977
    | FStar_Parser_AST.Ensures uu____49980 ->
        let uu____49988 = p_term false false e  in
        soft_parens_with_nesting uu____49988
    | FStar_Parser_AST.Attributes uu____49991 ->
        let uu____49994 = p_term false false e  in
        soft_parens_with_nesting uu____49994
    | FStar_Parser_AST.Quote uu____49997 ->
        let uu____50002 = p_term false false e  in
        soft_parens_with_nesting uu____50002
    | FStar_Parser_AST.VQuote uu____50005 ->
        let uu____50006 = p_term false false e  in
        soft_parens_with_nesting uu____50006
    | FStar_Parser_AST.Antiquote uu____50009 ->
        let uu____50010 = p_term false false e  in
        soft_parens_with_nesting uu____50010
    | FStar_Parser_AST.CalcProof uu____50013 ->
        let uu____50022 = p_term false false e  in
        soft_parens_with_nesting uu____50022

and (p_constant : FStar_Const.sconst -> FStar_Pprint.document) =
  fun uu___339_50025  ->
    match uu___339_50025 with
    | FStar_Const.Const_effect  -> str "Effect"
    | FStar_Const.Const_unit  -> str "()"
    | FStar_Const.Const_bool b -> FStar_Pprint.doc_of_bool b
    | FStar_Const.Const_real r -> str (Prims.op_Hat r "R")
    | FStar_Const.Const_float x -> str (FStar_Util.string_of_float x)
    | FStar_Const.Const_char x -> FStar_Pprint.doc_of_char x
    | FStar_Const.Const_string (s,uu____50037) ->
        let uu____50040 = str (FStar_String.escaped s)  in
        FStar_Pprint.dquotes uu____50040
    | FStar_Const.Const_bytearray (bytes,uu____50042) ->
        let uu____50047 =
          let uu____50048 = str (FStar_Util.string_of_bytes bytes)  in
          FStar_Pprint.dquotes uu____50048  in
        let uu____50049 = str "B"  in
        FStar_Pprint.op_Hat_Hat uu____50047 uu____50049
    | FStar_Const.Const_int (repr,sign_width_opt) ->
        let signedness uu___337_50072 =
          match uu___337_50072 with
          | FStar_Const.Unsigned  -> str "u"
          | FStar_Const.Signed  -> FStar_Pprint.empty  in
        let width uu___338_50079 =
          match uu___338_50079 with
          | FStar_Const.Int8  -> str "y"
          | FStar_Const.Int16  -> str "s"
          | FStar_Const.Int32  -> str "l"
          | FStar_Const.Int64  -> str "L"  in
        let ending =
          default_or_map FStar_Pprint.empty
            (fun uu____50094  ->
               match uu____50094 with
               | (s,w) ->
                   let uu____50101 = signedness s  in
                   let uu____50102 = width w  in
                   FStar_Pprint.op_Hat_Hat uu____50101 uu____50102)
            sign_width_opt
           in
        let uu____50103 = str repr  in
        FStar_Pprint.op_Hat_Hat uu____50103 ending
    | FStar_Const.Const_range_of  -> str "range_of"
    | FStar_Const.Const_set_range_of  -> str "set_range_of"
    | FStar_Const.Const_range r ->
        let uu____50107 = FStar_Range.string_of_range r  in str uu____50107
    | FStar_Const.Const_reify  -> str "reify"
    | FStar_Const.Const_reflect lid ->
        let uu____50111 = p_quident lid  in
        let uu____50112 =
          let uu____50113 =
            let uu____50114 = str "reflect"  in
            FStar_Pprint.op_Hat_Hat FStar_Pprint.dot uu____50114  in
          FStar_Pprint.op_Hat_Hat FStar_Pprint.qmark uu____50113  in
        FStar_Pprint.op_Hat_Hat uu____50111 uu____50112

and (p_universe : FStar_Parser_AST.term -> FStar_Pprint.document) =
  fun u  ->
    let uu____50117 = str "u#"  in
    let uu____50119 = p_atomicUniverse u  in
    FStar_Pprint.op_Hat_Hat uu____50117 uu____50119

and (p_universeFrom : FStar_Parser_AST.term -> FStar_Pprint.document) =
  fun u  ->
    match u.FStar_Parser_AST.tm with
    | FStar_Parser_AST.Op
        ({ FStar_Ident.idText = "+"; FStar_Ident.idRange = uu____50121;_},u1::u2::[])
        ->
        let uu____50127 =
          let uu____50128 = p_universeFrom u1  in
          let uu____50129 =
            let uu____50130 = p_universeFrom u2  in
            FStar_Pprint.op_Hat_Slash_Hat FStar_Pprint.plus uu____50130  in
          FStar_Pprint.op_Hat_Slash_Hat uu____50128 uu____50129  in
        FStar_Pprint.group uu____50127
    | FStar_Parser_AST.App uu____50131 ->
        let uu____50138 = head_and_args u  in
        (match uu____50138 with
         | (head1,args) ->
             (match head1.FStar_Parser_AST.tm with
              | FStar_Parser_AST.Var maybe_max_lid when
                  FStar_Ident.lid_equals maybe_max_lid
                    FStar_Parser_Const.max_lid
                  ->
                  let uu____50164 =
                    let uu____50165 = p_qlident FStar_Parser_Const.max_lid
                       in
                    let uu____50166 =
                      FStar_Pprint.separate_map FStar_Pprint.space
                        (fun uu____50174  ->
                           match uu____50174 with
                           | (u1,uu____50180) -> p_atomicUniverse u1) args
                       in
                    op_Hat_Slash_Plus_Hat uu____50165 uu____50166  in
                  FStar_Pprint.group uu____50164
              | uu____50181 ->
                  let uu____50182 =
                    let uu____50184 = FStar_Parser_AST.term_to_string u  in
                    FStar_Util.format1 "Invalid term in universe context %s"
                      uu____50184
                     in
                  failwith uu____50182))
    | uu____50187 -> p_atomicUniverse u

and (p_atomicUniverse : FStar_Parser_AST.term -> FStar_Pprint.document) =
  fun u  ->
    match u.FStar_Parser_AST.tm with
    | FStar_Parser_AST.Wild  -> FStar_Pprint.underscore
    | FStar_Parser_AST.Const (FStar_Const.Const_int (r,sw)) ->
        p_constant (FStar_Const.Const_int (r, sw))
    | FStar_Parser_AST.Uvar id1 ->
        let uu____50213 = FStar_Ident.text_of_id id1  in str uu____50213
    | FStar_Parser_AST.Paren u1 ->
        let uu____50216 = p_universeFrom u1  in
        soft_parens_with_nesting uu____50216
    | FStar_Parser_AST.Op
        ({ FStar_Ident.idText = "+"; FStar_Ident.idRange = uu____50217;_},uu____50218::uu____50219::[])
        ->
        let uu____50223 = p_universeFrom u  in
        soft_parens_with_nesting uu____50223
    | FStar_Parser_AST.App uu____50224 ->
        let uu____50231 = p_universeFrom u  in
        soft_parens_with_nesting uu____50231
    | uu____50232 ->
        let uu____50233 =
          let uu____50235 = FStar_Parser_AST.term_to_string u  in
          FStar_Util.format1 "Invalid term in universe context %s"
            uu____50235
           in
        failwith uu____50233

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
       | FStar_Parser_AST.Module (uu____50324,decls) ->
           let uu____50330 =
             FStar_All.pipe_right decls (FStar_List.map decl_to_document)  in
           FStar_All.pipe_right uu____50330
             (FStar_Pprint.separate FStar_Pprint.hardline)
       | FStar_Parser_AST.Interface (uu____50339,decls,uu____50341) ->
           let uu____50348 =
             FStar_All.pipe_right decls (FStar_List.map decl_to_document)  in
           FStar_All.pipe_right uu____50348
             (FStar_Pprint.separate FStar_Pprint.hardline)
        in
     FStar_ST.op_Colon_Equals should_print_fs_typ_app false; res)
  
let (comments_to_document :
  (Prims.string * FStar_Range.range) Prims.list -> FStar_Pprint.document) =
  fun comments  ->
    FStar_Pprint.separate_map FStar_Pprint.hardline
      (fun uu____50408  ->
         match uu____50408 with | (comment,range) -> str comment) comments
  
let (extract_decl_range : FStar_Parser_AST.decl -> decl_meta) =
  fun d  ->
    let has_qs =
      match ((d.FStar_Parser_AST.quals), (d.FStar_Parser_AST.d)) with
      | ((FStar_Parser_AST.Assumption )::[],FStar_Parser_AST.Assume
         (id1,uu____50430)) -> false
      | ([],uu____50434) -> false
      | uu____50438 -> true  in
    {
      r = (d.FStar_Parser_AST.drange);
      has_qs;
      has_attrs =
        (Prims.op_Negation (FStar_List.isEmpty d.FStar_Parser_AST.attrs));
      has_fsdoc = (FStar_Util.is_some d.FStar_Parser_AST.doc);
      is_fsdoc =
        (match d.FStar_Parser_AST.d with
         | FStar_Parser_AST.Fsdoc uu____50448 -> true
         | uu____50450 -> false)
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
        | FStar_Parser_AST.Module (uu____50493,decls) -> decls
        | FStar_Parser_AST.Interface (uu____50499,decls,uu____50501) -> decls
         in
      FStar_ST.op_Colon_Equals should_print_fs_typ_app false;
      (match decls with
       | [] -> (FStar_Pprint.empty, comments)
       | d::ds ->
           let uu____50553 =
             match ds with
             | {
                 FStar_Parser_AST.d = FStar_Parser_AST.Pragma
                   (FStar_Parser_AST.LightOff );
                 FStar_Parser_AST.drange = uu____50566;
                 FStar_Parser_AST.doc = uu____50567;
                 FStar_Parser_AST.quals = uu____50568;
                 FStar_Parser_AST.attrs = uu____50569;_}::uu____50570 ->
                 let d0 = FStar_List.hd ds  in
                 let uu____50576 =
                   let uu____50579 =
                     let uu____50582 = FStar_List.tl ds  in d :: uu____50582
                      in
                   d0 :: uu____50579  in
                 (uu____50576, (d0.FStar_Parser_AST.drange))
             | uu____50587 -> ((d :: ds), (d.FStar_Parser_AST.drange))  in
           (match uu____50553 with
            | (decls1,first_range) ->
                (FStar_ST.op_Colon_Equals comment_stack comments;
                 (let initial_comment =
                    let uu____50644 = FStar_Range.start_of_range first_range
                       in
                    place_comments_until_pos (Prims.parse_int "0")
                      (Prims.parse_int "1") uu____50644 dummy_meta
                      FStar_Pprint.empty false true
                     in
                  let doc1 =
                    separate_map_with_comments FStar_Pprint.empty
                      FStar_Pprint.empty p_decl decls1 extract_decl_range
                     in
                  let comments1 = FStar_ST.op_Bang comment_stack  in
                  FStar_ST.op_Colon_Equals comment_stack [];
                  FStar_ST.op_Colon_Equals should_print_fs_typ_app false;
                  (let uu____50753 =
                     FStar_Pprint.op_Hat_Hat initial_comment doc1  in
                   (uu____50753, comments1))))))
  