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
            let uu____43190 = let uu____43193 = f x  in uu____43193 :: acc
               in
            aux xs uu____43190
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
            let uu____43260 = f x  in
            (match uu____43260 with
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
          let uu____43316 = f x  in if uu____43316 then all f xs else false
  
let (all_explicit :
  (FStar_Parser_AST.term * FStar_Parser_AST.imp) Prims.list -> Prims.bool) =
  fun args  ->
    FStar_Util.for_all
      (fun uu___324_43349  ->
         match uu___324_43349 with
         | (uu____43355,FStar_Parser_AST.Nothing ) -> true
         | uu____43357 -> false) args
  
let (should_print_fs_typ_app : Prims.bool FStar_ST.ref) =
  FStar_Util.mk_ref false 
let (unfold_tuples : Prims.bool FStar_ST.ref) = FStar_Util.mk_ref true 
let with_fs_typ_app :
  'Auu____43408 'Auu____43409 .
    Prims.bool ->
      ('Auu____43408 -> 'Auu____43409) -> 'Auu____43408 -> 'Auu____43409
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
  'Auu____43519 'Auu____43520 .
    'Auu____43519 ->
      ('Auu____43520 -> 'Auu____43519) ->
        'Auu____43520 FStar_Pervasives_Native.option -> 'Auu____43519
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
  'Auu____43633 .
    FStar_Pprint.document ->
      ('Auu____43633 -> FStar_Pprint.document) ->
        'Auu____43633 Prims.list -> FStar_Pprint.document
  =
  fun sep  ->
    fun f  ->
      fun l  ->
        let uu____43658 =
          let uu____43659 =
            let uu____43660 = FStar_Pprint.op_Hat_Hat sep break1  in
            FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____43660  in
          FStar_Pprint.separate_map uu____43659 f l  in
        FStar_Pprint.group uu____43658
  
let precede_break_separate_map :
  'Auu____43672 .
    FStar_Pprint.document ->
      FStar_Pprint.document ->
        ('Auu____43672 -> FStar_Pprint.document) ->
          'Auu____43672 Prims.list -> FStar_Pprint.document
  =
  fun prec  ->
    fun sep  ->
      fun f  ->
        fun l  ->
          let uu____43702 =
            let uu____43703 = FStar_Pprint.op_Hat_Hat prec FStar_Pprint.space
               in
            let uu____43704 =
              let uu____43705 = FStar_List.hd l  in
              FStar_All.pipe_right uu____43705 f  in
            FStar_Pprint.precede uu____43703 uu____43704  in
          let uu____43706 =
            let uu____43707 = FStar_List.tl l  in
            FStar_Pprint.concat_map
              (fun x  ->
                 let uu____43713 =
                   let uu____43714 =
                     let uu____43715 = f x  in
                     FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____43715
                      in
                   FStar_Pprint.op_Hat_Hat sep uu____43714  in
                 FStar_Pprint.op_Hat_Hat break1 uu____43713) uu____43707
             in
          FStar_Pprint.op_Hat_Hat uu____43702 uu____43706
  
let concat_break_map :
  'Auu____43723 .
    ('Auu____43723 -> FStar_Pprint.document) ->
      'Auu____43723 Prims.list -> FStar_Pprint.document
  =
  fun f  ->
    fun l  ->
      let uu____43743 =
        FStar_Pprint.concat_map
          (fun x  ->
             let uu____43747 = f x  in
             FStar_Pprint.op_Hat_Hat uu____43747 break1) l
         in
      FStar_Pprint.group uu____43743
  
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
    let uu____43810 = str "begin"  in
    let uu____43812 = str "end"  in
    FStar_Pprint.soft_surround (Prims.parse_int "2") (Prims.parse_int "1")
      uu____43810 contents uu____43812
  
let separate_map_last :
  'Auu____43825 .
    FStar_Pprint.document ->
      (Prims.bool -> 'Auu____43825 -> FStar_Pprint.document) ->
        'Auu____43825 Prims.list -> FStar_Pprint.document
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
  'Auu____43883 .
    FStar_Pprint.document ->
      (Prims.bool -> 'Auu____43883 -> FStar_Pprint.document) ->
        'Auu____43883 Prims.list -> FStar_Pprint.document
  =
  fun sep  ->
    fun f  ->
      fun l  ->
        let uu____43915 =
          let uu____43916 =
            let uu____43917 = FStar_Pprint.op_Hat_Hat sep break1  in
            FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____43917  in
          separate_map_last uu____43916 f l  in
        FStar_Pprint.group uu____43915
  
let separate_map_or_flow :
  'Auu____43927 .
    FStar_Pprint.document ->
      ('Auu____43927 -> FStar_Pprint.document) ->
        'Auu____43927 Prims.list -> FStar_Pprint.document
  =
  fun sep  ->
    fun f  ->
      fun l  ->
        if (FStar_List.length l) < (Prims.parse_int "10")
        then FStar_Pprint.separate_map sep f l
        else FStar_Pprint.flow_map sep f l
  
let flow_map_last :
  'Auu____43965 .
    FStar_Pprint.document ->
      (Prims.bool -> 'Auu____43965 -> FStar_Pprint.document) ->
        'Auu____43965 Prims.list -> FStar_Pprint.document
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
  'Auu____44023 .
    FStar_Pprint.document ->
      (Prims.bool -> 'Auu____44023 -> FStar_Pprint.document) ->
        'Auu____44023 Prims.list -> FStar_Pprint.document
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
              let uu____44105 = FStar_Pprint.op_Hat_Slash_Hat doc1 doc3  in
              FStar_Pprint.group uu____44105
            else FStar_Pprint.surround n1 b doc1 doc2 doc3
  
let soft_surround_separate_map :
  'Auu____44127 .
    Prims.int ->
      Prims.int ->
        FStar_Pprint.document ->
          FStar_Pprint.document ->
            FStar_Pprint.document ->
              FStar_Pprint.document ->
                ('Auu____44127 -> FStar_Pprint.document) ->
                  'Auu____44127 Prims.list -> FStar_Pprint.document
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
                    (let uu____44186 = FStar_Pprint.separate_map sep f xs  in
                     FStar_Pprint.soft_surround n1 b opening uu____44186
                       closing)
  
let soft_surround_map_or_flow :
  'Auu____44206 .
    Prims.int ->
      Prims.int ->
        FStar_Pprint.document ->
          FStar_Pprint.document ->
            FStar_Pprint.document ->
              FStar_Pprint.document ->
                ('Auu____44206 -> FStar_Pprint.document) ->
                  'Auu____44206 Prims.list -> FStar_Pprint.document
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
                    (let uu____44265 = separate_map_or_flow sep f xs  in
                     FStar_Pprint.soft_surround n1 b opening uu____44265
                       closing)
  
let (doc_of_fsdoc :
  (Prims.string * (Prims.string * Prims.string) Prims.list) ->
    FStar_Pprint.document)
  =
  fun uu____44284  ->
    match uu____44284 with
    | (comment,keywords) ->
        let uu____44318 =
          let uu____44319 =
            let uu____44322 = str comment  in
            let uu____44323 =
              let uu____44326 =
                let uu____44329 =
                  FStar_Pprint.separate_map FStar_Pprint.comma
                    (fun uu____44340  ->
                       match uu____44340 with
                       | (k,v1) ->
                           let uu____44353 =
                             let uu____44356 = str k  in
                             let uu____44357 =
                               let uu____44360 =
                                 let uu____44363 = str v1  in [uu____44363]
                                  in
                               FStar_Pprint.rarrow :: uu____44360  in
                             uu____44356 :: uu____44357  in
                           FStar_Pprint.concat uu____44353) keywords
                   in
                [uu____44329]  in
              FStar_Pprint.space :: uu____44326  in
            uu____44322 :: uu____44323  in
          FStar_Pprint.concat uu____44319  in
        FStar_Pprint.group uu____44318
  
let (is_unit : FStar_Parser_AST.term -> Prims.bool) =
  fun e  ->
    match e.FStar_Parser_AST.tm with
    | FStar_Parser_AST.Const (FStar_Const.Const_unit ) -> true
    | uu____44373 -> false
  
let (matches_var : FStar_Parser_AST.term -> FStar_Ident.ident -> Prims.bool)
  =
  fun t  ->
    fun x  ->
      match t.FStar_Parser_AST.tm with
      | FStar_Parser_AST.Var y ->
          let uu____44389 = FStar_Ident.text_of_lid y  in
          x.FStar_Ident.idText = uu____44389
      | uu____44392 -> false
  
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
        | FStar_Parser_AST.Construct (lid,uu____44443::(e2,uu____44445)::[])
            -> (FStar_Ident.lid_equals lid cons_lid1) && (aux e2)
        | uu____44468 -> false  in
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
    | FStar_Parser_AST.Construct (uu____44492,[]) -> []
    | FStar_Parser_AST.Construct
        (uu____44503,(e1,FStar_Parser_AST.Nothing )::(e2,FStar_Parser_AST.Nothing
                                                      )::[])
        -> let uu____44524 = extract_from_list e2  in e1 :: uu____44524
    | uu____44527 ->
        let uu____44528 =
          let uu____44530 = FStar_Parser_AST.term_to_string e  in
          FStar_Util.format1 "Not a list %s" uu____44530  in
        failwith uu____44528
  
let (is_array : FStar_Parser_AST.term -> Prims.bool) =
  fun e  ->
    match e.FStar_Parser_AST.tm with
    | FStar_Parser_AST.App
        ({ FStar_Parser_AST.tm = FStar_Parser_AST.Var lid;
           FStar_Parser_AST.range = uu____44544;
           FStar_Parser_AST.level = uu____44545;_},l,FStar_Parser_AST.Nothing
         )
        ->
        (FStar_Ident.lid_equals lid FStar_Parser_Const.array_mk_array_lid) &&
          (is_list l)
    | uu____44547 -> false
  
let rec (is_ref_set : FStar_Parser_AST.term -> Prims.bool) =
  fun e  ->
    match e.FStar_Parser_AST.tm with
    | FStar_Parser_AST.Var maybe_empty_lid ->
        FStar_Ident.lid_equals maybe_empty_lid FStar_Parser_Const.set_empty
    | FStar_Parser_AST.App
        ({ FStar_Parser_AST.tm = FStar_Parser_AST.Var maybe_singleton_lid;
           FStar_Parser_AST.range = uu____44559;
           FStar_Parser_AST.level = uu____44560;_},{
                                                     FStar_Parser_AST.tm =
                                                       FStar_Parser_AST.App
                                                       ({
                                                          FStar_Parser_AST.tm
                                                            =
                                                            FStar_Parser_AST.Var
                                                            maybe_addr_of_lid;
                                                          FStar_Parser_AST.range
                                                            = uu____44562;
                                                          FStar_Parser_AST.level
                                                            = uu____44563;_},e1,FStar_Parser_AST.Nothing
                                                        );
                                                     FStar_Parser_AST.range =
                                                       uu____44565;
                                                     FStar_Parser_AST.level =
                                                       uu____44566;_},FStar_Parser_AST.Nothing
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
                FStar_Parser_AST.range = uu____44568;
                FStar_Parser_AST.level = uu____44569;_},e1,FStar_Parser_AST.Nothing
              );
           FStar_Parser_AST.range = uu____44571;
           FStar_Parser_AST.level = uu____44572;_},e2,FStar_Parser_AST.Nothing
         )
        ->
        ((FStar_Ident.lid_equals maybe_union_lid FStar_Parser_Const.set_union)
           && (is_ref_set e1))
          && (is_ref_set e2)
    | uu____44574 -> false
  
let rec (extract_from_ref_set :
  FStar_Parser_AST.term -> FStar_Parser_AST.term Prims.list) =
  fun e  ->
    match e.FStar_Parser_AST.tm with
    | FStar_Parser_AST.Var uu____44586 -> []
    | FStar_Parser_AST.App
        ({ FStar_Parser_AST.tm = FStar_Parser_AST.Var uu____44587;
           FStar_Parser_AST.range = uu____44588;
           FStar_Parser_AST.level = uu____44589;_},{
                                                     FStar_Parser_AST.tm =
                                                       FStar_Parser_AST.App
                                                       ({
                                                          FStar_Parser_AST.tm
                                                            =
                                                            FStar_Parser_AST.Var
                                                            uu____44590;
                                                          FStar_Parser_AST.range
                                                            = uu____44591;
                                                          FStar_Parser_AST.level
                                                            = uu____44592;_},e1,FStar_Parser_AST.Nothing
                                                        );
                                                     FStar_Parser_AST.range =
                                                       uu____44594;
                                                     FStar_Parser_AST.level =
                                                       uu____44595;_},FStar_Parser_AST.Nothing
         )
        -> [e1]
    | FStar_Parser_AST.App
        ({
           FStar_Parser_AST.tm = FStar_Parser_AST.App
             ({ FStar_Parser_AST.tm = FStar_Parser_AST.Var uu____44596;
                FStar_Parser_AST.range = uu____44597;
                FStar_Parser_AST.level = uu____44598;_},e1,FStar_Parser_AST.Nothing
              );
           FStar_Parser_AST.range = uu____44600;
           FStar_Parser_AST.level = uu____44601;_},e2,FStar_Parser_AST.Nothing
         )
        ->
        let uu____44603 = extract_from_ref_set e1  in
        let uu____44606 = extract_from_ref_set e2  in
        FStar_List.append uu____44603 uu____44606
    | uu____44609 ->
        let uu____44610 =
          let uu____44612 = FStar_Parser_AST.term_to_string e  in
          FStar_Util.format1 "Not a ref set %s" uu____44612  in
        failwith uu____44610
  
let (is_general_application : FStar_Parser_AST.term -> Prims.bool) =
  fun e  ->
    let uu____44624 = (is_array e) || (is_ref_set e)  in
    Prims.op_Negation uu____44624
  
let (is_general_construction : FStar_Parser_AST.term -> Prims.bool) =
  fun e  ->
    let uu____44633 = (is_list e) || (is_lex_list e)  in
    Prims.op_Negation uu____44633
  
let (is_general_prefix_op : FStar_Ident.ident -> Prims.bool) =
  fun op  ->
    let op_starting_char =
      let uu____44644 = FStar_Ident.text_of_id op  in
      FStar_Util.char_at uu____44644 (Prims.parse_int "0")  in
    ((op_starting_char = 33) || (op_starting_char = 63)) ||
      ((op_starting_char = 126) &&
         (let uu____44654 = FStar_Ident.text_of_id op  in uu____44654 <> "~"))
  
let (head_and_args :
  FStar_Parser_AST.term ->
    (FStar_Parser_AST.term * (FStar_Parser_AST.term * FStar_Parser_AST.imp)
      Prims.list))
  =
  fun e  ->
    let rec aux e1 acc =
      match e1.FStar_Parser_AST.tm with
      | FStar_Parser_AST.App (head1,arg,imp) -> aux head1 ((arg, imp) :: acc)
      | uu____44724 -> (e1, acc)  in
    aux e []
  
type associativity =
  | Left 
  | Right 
  | NonAssoc 
let (uu___is_Left : associativity -> Prims.bool) =
  fun projectee  ->
    match projectee with | Left  -> true | uu____44744 -> false
  
let (uu___is_Right : associativity -> Prims.bool) =
  fun projectee  ->
    match projectee with | Right  -> true | uu____44755 -> false
  
let (uu___is_NonAssoc : associativity -> Prims.bool) =
  fun projectee  ->
    match projectee with | NonAssoc  -> true | uu____44766 -> false
  
type token = (FStar_Char.char,Prims.string) FStar_Util.either
type associativity_level = (associativity * token Prims.list)
let (token_to_string :
  (FStar_BaseTypes.char,Prims.string) FStar_Util.either -> Prims.string) =
  fun uu___325_44792  ->
    match uu___325_44792 with
    | FStar_Util.Inl c -> Prims.op_Hat (FStar_Util.string_of_char c) ".*"
    | FStar_Util.Inr s -> s
  
let (matches_token :
  Prims.string ->
    (FStar_Char.char,Prims.string) FStar_Util.either -> Prims.bool)
  =
  fun s  ->
    fun uu___326_44827  ->
      match uu___326_44827 with
      | FStar_Util.Inl c ->
          let uu____44840 = FStar_String.get s (Prims.parse_int "0")  in
          uu____44840 = c
      | FStar_Util.Inr s' -> s = s'
  
let matches_level :
  'Auu____44856 .
    Prims.string ->
      ('Auu____44856 * (FStar_Char.char,Prims.string) FStar_Util.either
        Prims.list) -> Prims.bool
  =
  fun s  ->
    fun uu____44880  ->
      match uu____44880 with
      | (assoc_levels,tokens) ->
          let uu____44912 = FStar_List.tryFind (matches_token s) tokens  in
          uu____44912 <> FStar_Pervasives_Native.None
  
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
  let levels_from_associativity l uu___327_45084 =
    match uu___327_45084 with
    | Left  -> (l, l, (l - (Prims.parse_int "1")))
    | Right  -> ((l - (Prims.parse_int "1")), l, l)
    | NonAssoc  ->
        ((l - (Prims.parse_int "1")), l, (l - (Prims.parse_int "1")))
     in
  FStar_List.mapi
    (fun i  ->
       fun uu____45134  ->
         match uu____45134 with
         | (assoc1,tokens) -> ((levels_from_associativity i assoc1), tokens))
    level_associativity_spec
  
let (assign_levels :
  associativity_level Prims.list ->
    Prims.string -> (Prims.int * Prims.int * Prims.int))
  =
  fun token_associativity_spec  ->
    fun s  ->
      let uu____45209 = FStar_List.tryFind (matches_level s) level_table  in
      match uu____45209 with
      | FStar_Pervasives_Native.Some (assoc_levels,uu____45261) ->
          assoc_levels
      | uu____45299 -> failwith (Prims.op_Hat "Unrecognized operator " s)
  
let max_level :
  'Auu____45332 . ('Auu____45332 * token Prims.list) Prims.list -> Prims.int
  =
  fun l  ->
    let find_level_and_max n1 level =
      let uu____45381 =
        FStar_List.tryFind
          (fun uu____45417  ->
             match uu____45417 with
             | (uu____45434,tokens) ->
                 tokens = (FStar_Pervasives_Native.snd level)) level_table
         in
      match uu____45381 with
      | FStar_Pervasives_Native.Some
          ((uu____45463,l1,uu____45465),uu____45466) -> max n1 l1
      | FStar_Pervasives_Native.None  ->
          let uu____45516 =
            let uu____45518 =
              let uu____45520 =
                FStar_List.map token_to_string
                  (FStar_Pervasives_Native.snd level)
                 in
              FStar_String.concat "," uu____45520  in
            FStar_Util.format1 "Undefined associativity level %s" uu____45518
             in
          failwith uu____45516
       in
    FStar_List.fold_left find_level_and_max (Prims.parse_int "0") l
  
let (levels : Prims.string -> (Prims.int * Prims.int * Prims.int)) =
  fun op  ->
    let uu____45555 = assign_levels level_associativity_spec op  in
    match uu____45555 with
    | (left1,mine,right1) ->
        if op = "*"
        then ((left1 - (Prims.parse_int "1")), mine, right1)
        else (left1, mine, right1)
  
let (operatorInfix0ad12 : associativity_level Prims.list) =
  [opinfix0a; opinfix0b; opinfix0c; opinfix0d; opinfix1; opinfix2] 
let (is_operatorInfix0ad12 : FStar_Ident.ident -> Prims.bool) =
  fun op  ->
    let uu____45614 =
      let uu____45617 =
        let uu____45623 = FStar_Ident.text_of_id op  in
        FStar_All.pipe_left matches_level uu____45623  in
      FStar_List.tryFind uu____45617 operatorInfix0ad12  in
    uu____45614 <> FStar_Pervasives_Native.None
  
let (is_operatorInfix34 : FStar_Ident.ident -> Prims.bool) =
  let opinfix34 = [opinfix3; opinfix4]  in
  fun op  ->
    let uu____45690 =
      let uu____45705 =
        let uu____45723 = FStar_Ident.text_of_id op  in
        FStar_All.pipe_left matches_level uu____45723  in
      FStar_List.tryFind uu____45705 opinfix34  in
    uu____45690 <> FStar_Pervasives_Native.None
  
let (handleable_args_length : FStar_Ident.ident -> Prims.int) =
  fun op  ->
    let op_s = FStar_Ident.text_of_id op  in
    let uu____45789 =
      (is_general_prefix_op op) || (FStar_List.mem op_s ["-"; "~"])  in
    if uu____45789
    then (Prims.parse_int "1")
    else
      (let uu____45802 =
         ((is_operatorInfix0ad12 op) || (is_operatorInfix34 op)) ||
           (FStar_List.mem op_s
              ["<==>"; "==>"; "\\/"; "/\\"; "="; "|>"; ":="; ".()"; ".[]"])
          in
       if uu____45802
       then (Prims.parse_int "2")
       else
         if FStar_List.mem op_s [".()<-"; ".[]<-"]
         then (Prims.parse_int "3")
         else (Prims.parse_int "0"))
  
let handleable_op :
  'Auu____45848 . FStar_Ident.ident -> 'Auu____45848 Prims.list -> Prims.bool
  =
  fun op  ->
    fun args  ->
      match FStar_List.length args with
      | _45864 when _45864 = (Prims.parse_int "0") -> true
      | _45866 when _45866 = (Prims.parse_int "1") ->
          (is_general_prefix_op op) ||
            (let uu____45868 = FStar_Ident.text_of_id op  in
             FStar_List.mem uu____45868 ["-"; "~"])
      | _45876 when _45876 = (Prims.parse_int "2") ->
          ((is_operatorInfix0ad12 op) || (is_operatorInfix34 op)) ||
            (let uu____45878 = FStar_Ident.text_of_id op  in
             FStar_List.mem uu____45878
               ["<==>"; "==>"; "\\/"; "/\\"; "="; "|>"; ":="; ".()"; ".[]"])
      | _45900 when _45900 = (Prims.parse_int "3") ->
          let uu____45901 = FStar_Ident.text_of_id op  in
          FStar_List.mem uu____45901 [".()<-"; ".[]<-"]
      | uu____45909 -> false
  
type annotation_style =
  | Binders of (Prims.int * Prims.int * Prims.bool) 
  | Arrows of (Prims.int * Prims.int) 
let (uu___is_Binders : annotation_style -> Prims.bool) =
  fun projectee  ->
    match projectee with | Binders _0 -> true | uu____45955 -> false
  
let (__proj__Binders__item___0 :
  annotation_style -> (Prims.int * Prims.int * Prims.bool)) =
  fun projectee  -> match projectee with | Binders _0 -> _0 
let (uu___is_Arrows : annotation_style -> Prims.bool) =
  fun projectee  ->
    match projectee with | Arrows _0 -> true | uu____46008 -> false
  
let (__proj__Arrows__item___0 : annotation_style -> (Prims.int * Prims.int))
  = fun projectee  -> match projectee with | Arrows _0 -> _0 
let (all_binders_annot : FStar_Parser_AST.term -> Prims.bool) =
  fun e  ->
    let is_binder_annot b =
      match b.FStar_Parser_AST.b with
      | FStar_Parser_AST.Annotated uu____46051 -> true
      | uu____46057 -> false  in
    let rec all_binders e1 l =
      match e1.FStar_Parser_AST.tm with
      | FStar_Parser_AST.Product (bs,tgt) ->
          let uu____46090 = FStar_List.for_all is_binder_annot bs  in
          if uu____46090
          then all_binders tgt (l + (FStar_List.length bs))
          else (false, (Prims.parse_int "0"))
      | uu____46105 -> (true, (l + (Prims.parse_int "1")))  in
    let uu____46110 = all_binders e (Prims.parse_int "0")  in
    match uu____46110 with
    | (b,l) -> if b && (l > (Prims.parse_int "1")) then true else false
  
type catf =
  FStar_Pprint.document -> FStar_Pprint.document -> FStar_Pprint.document
let (cat_with_colon :
  FStar_Pprint.document -> FStar_Pprint.document -> FStar_Pprint.document) =
  fun x  ->
    fun y  ->
      let uu____46149 = FStar_Pprint.op_Hat_Slash_Hat FStar_Pprint.colon y
         in
      FStar_Pprint.op_Hat_Hat x uu____46149
  
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
  'Auu____46309 .
    ('Auu____46309 -> FStar_Pprint.document) ->
      'Auu____46309 -> FStar_Range.range -> FStar_Pprint.document
  =
  fun printer  ->
    fun tm  ->
      fun tmrange  ->
        let rec comments_before_pos acc print_pos lookahead_pos =
          let uu____46351 = FStar_ST.op_Bang comment_stack  in
          match uu____46351 with
          | [] -> (acc, false)
          | (c,crange)::cs ->
              let comment =
                let uu____46422 = str c  in
                FStar_Pprint.op_Hat_Hat uu____46422 FStar_Pprint.hardline  in
              let uu____46423 = FStar_Range.range_before_pos crange print_pos
                 in
              if uu____46423
              then
                (FStar_ST.op_Colon_Equals comment_stack cs;
                 (let uu____46465 = FStar_Pprint.op_Hat_Hat acc comment  in
                  comments_before_pos uu____46465 print_pos lookahead_pos))
              else
                (let uu____46468 =
                   FStar_Range.range_before_pos crange lookahead_pos  in
                 (acc, uu____46468))
           in
        let uu____46471 =
          let uu____46477 =
            let uu____46478 = FStar_Range.start_of_range tmrange  in
            FStar_Range.end_of_line uu____46478  in
          let uu____46479 = FStar_Range.end_of_range tmrange  in
          comments_before_pos FStar_Pprint.empty uu____46477 uu____46479  in
        match uu____46471 with
        | (comments,has_lookahead) ->
            let printed_e = printer tm  in
            let comments1 =
              if has_lookahead
              then
                let pos = FStar_Range.end_of_range tmrange  in
                let uu____46488 = comments_before_pos comments pos pos  in
                FStar_Pervasives_Native.fst uu____46488
              else comments  in
            if comments1 = FStar_Pprint.empty
            then printed_e
            else
              (let uu____46500 = FStar_Pprint.op_Hat_Hat comments1 printed_e
                  in
               FStar_Pprint.group uu____46500)
  
let with_comment_sep :
  'Auu____46512 'Auu____46513 .
    ('Auu____46512 -> 'Auu____46513) ->
      'Auu____46512 ->
        FStar_Range.range -> (FStar_Pprint.document * 'Auu____46513)
  =
  fun printer  ->
    fun tm  ->
      fun tmrange  ->
        let rec comments_before_pos acc print_pos lookahead_pos =
          let uu____46559 = FStar_ST.op_Bang comment_stack  in
          match uu____46559 with
          | [] -> (acc, false)
          | (c,crange)::cs ->
              let comment = str c  in
              let uu____46630 = FStar_Range.range_before_pos crange print_pos
                 in
              if uu____46630
              then
                (FStar_ST.op_Colon_Equals comment_stack cs;
                 (let uu____46672 =
                    if acc = FStar_Pprint.empty
                    then comment
                    else
                      (let uu____46676 =
                         FStar_Pprint.op_Hat_Hat FStar_Pprint.hardline
                           comment
                          in
                       FStar_Pprint.op_Hat_Hat acc uu____46676)
                     in
                  comments_before_pos uu____46672 print_pos lookahead_pos))
              else
                (let uu____46679 =
                   FStar_Range.range_before_pos crange lookahead_pos  in
                 (acc, uu____46679))
           in
        let uu____46682 =
          let uu____46688 =
            let uu____46689 = FStar_Range.start_of_range tmrange  in
            FStar_Range.end_of_line uu____46689  in
          let uu____46690 = FStar_Range.end_of_range tmrange  in
          comments_before_pos FStar_Pprint.empty uu____46688 uu____46690  in
        match uu____46682 with
        | (comments,has_lookahead) ->
            let printed_e = printer tm  in
            let comments1 =
              if has_lookahead
              then
                let pos = FStar_Range.end_of_range tmrange  in
                let uu____46703 = comments_before_pos comments pos pos  in
                FStar_Pervasives_Native.fst uu____46703
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
                let uu____46756 = FStar_ST.op_Bang comment_stack  in
                match uu____46756 with
                | (comment,crange)::cs when
                    FStar_Range.range_before_pos crange pos ->
                    (FStar_ST.op_Colon_Equals comment_stack cs;
                     (let lnum =
                        let uu____46850 =
                          let uu____46852 =
                            let uu____46854 =
                              FStar_Range.start_of_range crange  in
                            FStar_Range.line_of_pos uu____46854  in
                          uu____46852 - lbegin  in
                        max k uu____46850  in
                      let lnum1 = min (Prims.parse_int "2") lnum  in
                      let doc2 =
                        let uu____46859 =
                          let uu____46860 =
                            FStar_Pprint.repeat lnum1 FStar_Pprint.hardline
                             in
                          let uu____46861 = str comment  in
                          FStar_Pprint.op_Hat_Hat uu____46860 uu____46861  in
                        FStar_Pprint.op_Hat_Hat doc1 uu____46859  in
                      let uu____46862 =
                        let uu____46864 = FStar_Range.end_of_range crange  in
                        FStar_Range.line_of_pos uu____46864  in
                      place_comments_until_pos (Prims.parse_int "1")
                        uu____46862 pos meta_decl doc2 true init1))
                | uu____46867 ->
                    if doc1 = FStar_Pprint.empty
                    then FStar_Pprint.empty
                    else
                      (let lnum =
                         let uu____46880 = FStar_Range.line_of_pos pos  in
                         uu____46880 - lbegin  in
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
                       let uu____46922 =
                         FStar_Pprint.repeat lnum7 FStar_Pprint.hardline  in
                       FStar_Pprint.op_Hat_Hat doc1 uu____46922)
  
let separate_map_with_comments :
  'Auu____46936 .
    FStar_Pprint.document ->
      FStar_Pprint.document ->
        ('Auu____46936 -> FStar_Pprint.document) ->
          'Auu____46936 Prims.list ->
            ('Auu____46936 -> decl_meta) -> FStar_Pprint.document
  =
  fun prefix1  ->
    fun sep  ->
      fun f  ->
        fun xs  ->
          fun extract_meta  ->
            let fold_fun uu____46995 x =
              match uu____46995 with
              | (last_line,doc1) ->
                  let meta_decl = extract_meta x  in
                  let r = meta_decl.r  in
                  let doc2 =
                    let uu____47014 = FStar_Range.start_of_range r  in
                    place_comments_until_pos (Prims.parse_int "1") last_line
                      uu____47014 meta_decl doc1 false false
                     in
                  let uu____47018 =
                    let uu____47020 = FStar_Range.end_of_range r  in
                    FStar_Range.line_of_pos uu____47020  in
                  let uu____47021 =
                    let uu____47022 =
                      let uu____47023 = f x  in
                      FStar_Pprint.op_Hat_Hat sep uu____47023  in
                    FStar_Pprint.op_Hat_Hat doc2 uu____47022  in
                  (uu____47018, uu____47021)
               in
            let uu____47025 =
              let uu____47032 = FStar_List.hd xs  in
              let uu____47033 = FStar_List.tl xs  in
              (uu____47032, uu____47033)  in
            match uu____47025 with
            | (x,xs1) ->
                let init1 =
                  let meta_decl = extract_meta x  in
                  let uu____47051 =
                    let uu____47053 = FStar_Range.end_of_range meta_decl.r
                       in
                    FStar_Range.line_of_pos uu____47053  in
                  let uu____47054 =
                    let uu____47055 = f x  in
                    FStar_Pprint.op_Hat_Hat prefix1 uu____47055  in
                  (uu____47051, uu____47054)  in
                let uu____47057 = FStar_List.fold_left fold_fun init1 xs1  in
                FStar_Pervasives_Native.snd uu____47057
  
let separate_map_with_comments_kw :
  'Auu____47084 'Auu____47085 .
    'Auu____47084 ->
      'Auu____47084 ->
        ('Auu____47084 -> 'Auu____47085 -> FStar_Pprint.document) ->
          'Auu____47085 Prims.list ->
            ('Auu____47085 -> decl_meta) -> FStar_Pprint.document
  =
  fun prefix1  ->
    fun sep  ->
      fun f  ->
        fun xs  ->
          fun extract_meta  ->
            let fold_fun uu____47149 x =
              match uu____47149 with
              | (last_line,doc1) ->
                  let meta_decl = extract_meta x  in
                  let r = meta_decl.r  in
                  let doc2 =
                    let uu____47168 = FStar_Range.start_of_range r  in
                    place_comments_until_pos (Prims.parse_int "1") last_line
                      uu____47168 meta_decl doc1 false false
                     in
                  let uu____47172 =
                    let uu____47174 = FStar_Range.end_of_range r  in
                    FStar_Range.line_of_pos uu____47174  in
                  let uu____47175 =
                    let uu____47176 = f sep x  in
                    FStar_Pprint.op_Hat_Hat doc2 uu____47176  in
                  (uu____47172, uu____47175)
               in
            let uu____47178 =
              let uu____47185 = FStar_List.hd xs  in
              let uu____47186 = FStar_List.tl xs  in
              (uu____47185, uu____47186)  in
            match uu____47178 with
            | (x,xs1) ->
                let init1 =
                  let meta_decl = extract_meta x  in
                  let uu____47204 =
                    let uu____47206 = FStar_Range.end_of_range meta_decl.r
                       in
                    FStar_Range.line_of_pos uu____47206  in
                  let uu____47207 = f prefix1 x  in
                  (uu____47204, uu____47207)  in
                let uu____47209 = FStar_List.fold_left fold_fun init1 xs1  in
                FStar_Pervasives_Native.snd uu____47209
  
let rec (p_decl : FStar_Parser_AST.decl -> FStar_Pprint.document) =
  fun d  ->
    let qualifiers =
      match ((d.FStar_Parser_AST.quals), (d.FStar_Parser_AST.d)) with
      | ((FStar_Parser_AST.Assumption )::[],FStar_Parser_AST.Assume
         (id1,uu____48195)) ->
          let uu____48198 =
            let uu____48200 =
              FStar_Util.char_at id1.FStar_Ident.idText (Prims.parse_int "0")
               in
            FStar_All.pipe_right uu____48200 FStar_Util.is_upper  in
          if uu____48198
          then
            let uu____48206 = p_qualifier FStar_Parser_AST.Assumption  in
            FStar_Pprint.op_Hat_Hat uu____48206 FStar_Pprint.space
          else p_qualifiers d.FStar_Parser_AST.quals
      | uu____48209 -> p_qualifiers d.FStar_Parser_AST.quals  in
    let uu____48216 =
      FStar_Pprint.optional (fun d1  -> p_fsdoc d1) d.FStar_Parser_AST.doc
       in
    let uu____48219 =
      let uu____48220 = p_attributes d.FStar_Parser_AST.attrs  in
      let uu____48221 =
        let uu____48222 = p_rawDecl d  in
        FStar_Pprint.op_Hat_Hat qualifiers uu____48222  in
      FStar_Pprint.op_Hat_Hat uu____48220 uu____48221  in
    FStar_Pprint.op_Hat_Hat uu____48216 uu____48219

and (p_attributes : FStar_Parser_AST.attributes_ -> FStar_Pprint.document) =
  fun attrs  ->
    match attrs with
    | [] -> FStar_Pprint.empty
    | uu____48224 ->
        let uu____48225 =
          let uu____48226 = str "@ "  in
          let uu____48228 =
            let uu____48229 =
              let uu____48230 =
                let uu____48231 =
                  let uu____48232 = FStar_List.map p_atomicTerm attrs  in
                  FStar_Pprint.flow break1 uu____48232  in
                FStar_Pprint.op_Hat_Hat uu____48231 FStar_Pprint.rbracket  in
              FStar_Pprint.align uu____48230  in
            FStar_Pprint.op_Hat_Hat uu____48229 FStar_Pprint.hardline  in
          FStar_Pprint.op_Hat_Hat uu____48226 uu____48228  in
        FStar_Pprint.op_Hat_Hat FStar_Pprint.lbracket uu____48225

and (p_fsdoc : FStar_Parser_AST.fsdoc -> FStar_Pprint.document) =
  fun uu____48235  ->
    match uu____48235 with
    | (doc1,kwd_args) ->
        let kwd_args_doc =
          match kwd_args with
          | [] -> FStar_Pprint.empty
          | kwd_args1 ->
              let process_kwd_arg uu____48283 =
                match uu____48283 with
                | (kwd,arg) ->
                    let uu____48296 = str "@"  in
                    let uu____48298 =
                      let uu____48299 = str kwd  in
                      let uu____48300 =
                        let uu____48301 = str arg  in
                        FStar_Pprint.op_Hat_Hat FStar_Pprint.space
                          uu____48301
                         in
                      FStar_Pprint.op_Hat_Hat uu____48299 uu____48300  in
                    FStar_Pprint.op_Hat_Hat uu____48296 uu____48298
                 in
              let uu____48302 =
                FStar_Pprint.separate_map FStar_Pprint.hardline
                  process_kwd_arg kwd_args1
                 in
              FStar_Pprint.op_Hat_Hat uu____48302 FStar_Pprint.hardline
           in
        let uu____48309 =
          let uu____48310 =
            let uu____48311 =
              let uu____48312 = str doc1  in
              let uu____48313 =
                let uu____48314 =
                  let uu____48315 =
                    FStar_Pprint.op_Hat_Hat FStar_Pprint.rparen
                      FStar_Pprint.hardline
                     in
                  FStar_Pprint.op_Hat_Hat FStar_Pprint.star uu____48315  in
                FStar_Pprint.op_Hat_Hat kwd_args_doc uu____48314  in
              FStar_Pprint.op_Hat_Hat uu____48312 uu____48313  in
            FStar_Pprint.op_Hat_Hat FStar_Pprint.star uu____48311  in
          FStar_Pprint.op_Hat_Hat FStar_Pprint.star uu____48310  in
        FStar_Pprint.op_Hat_Hat FStar_Pprint.lparen uu____48309

and (p_justSig : FStar_Parser_AST.decl -> FStar_Pprint.document) =
  fun d  ->
    match d.FStar_Parser_AST.d with
    | FStar_Parser_AST.Val (lid,t) ->
        let uu____48319 =
          let uu____48320 = str "val"  in
          let uu____48322 =
            let uu____48323 =
              let uu____48324 = p_lident lid  in
              let uu____48325 =
                FStar_Pprint.op_Hat_Hat FStar_Pprint.space FStar_Pprint.colon
                 in
              FStar_Pprint.op_Hat_Hat uu____48324 uu____48325  in
            FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____48323  in
          FStar_Pprint.op_Hat_Hat uu____48320 uu____48322  in
        let uu____48326 = p_typ false false t  in
        FStar_Pprint.op_Hat_Hat uu____48319 uu____48326
    | FStar_Parser_AST.TopLevelLet (uu____48329,lbs) ->
        FStar_Pprint.separate_map FStar_Pprint.hardline
          (fun lb  ->
             let uu____48354 =
               let uu____48355 = str "let"  in p_letlhs uu____48355 lb false
                in
             FStar_Pprint.group uu____48354) lbs
    | uu____48358 -> FStar_Pprint.empty

and (p_list :
  (FStar_Ident.ident -> FStar_Pprint.document) ->
    FStar_Pprint.document ->
      FStar_Ident.ident Prims.list -> FStar_Pprint.document)
  =
  fun f  ->
    fun sep  ->
      fun l  ->
        let rec p_list' uu___328_48373 =
          match uu___328_48373 with
          | [] -> FStar_Pprint.empty
          | x::[] -> f x
          | x::xs ->
              let uu____48381 = f x  in
              let uu____48382 =
                let uu____48383 = p_list' xs  in
                FStar_Pprint.op_Hat_Hat sep uu____48383  in
              FStar_Pprint.op_Hat_Hat uu____48381 uu____48382
           in
        let uu____48384 = str "["  in
        let uu____48386 =
          let uu____48387 = p_list' l  in
          let uu____48388 = str "]"  in
          FStar_Pprint.op_Hat_Hat uu____48387 uu____48388  in
        FStar_Pprint.op_Hat_Hat uu____48384 uu____48386

and (p_rawDecl : FStar_Parser_AST.decl -> FStar_Pprint.document) =
  fun d  ->
    match d.FStar_Parser_AST.d with
    | FStar_Parser_AST.Open uid ->
        let uu____48392 =
          let uu____48393 = str "open"  in
          let uu____48395 = p_quident uid  in
          FStar_Pprint.op_Hat_Slash_Hat uu____48393 uu____48395  in
        FStar_Pprint.group uu____48392
    | FStar_Parser_AST.Include uid ->
        let uu____48397 =
          let uu____48398 = str "include"  in
          let uu____48400 = p_quident uid  in
          FStar_Pprint.op_Hat_Slash_Hat uu____48398 uu____48400  in
        FStar_Pprint.group uu____48397
    | FStar_Parser_AST.Friend uid ->
        let uu____48402 =
          let uu____48403 = str "friend"  in
          let uu____48405 = p_quident uid  in
          FStar_Pprint.op_Hat_Slash_Hat uu____48403 uu____48405  in
        FStar_Pprint.group uu____48402
    | FStar_Parser_AST.ModuleAbbrev (uid1,uid2) ->
        let uu____48408 =
          let uu____48409 = str "module"  in
          let uu____48411 =
            let uu____48412 =
              let uu____48413 = p_uident uid1  in
              let uu____48414 =
                FStar_Pprint.op_Hat_Hat FStar_Pprint.space
                  FStar_Pprint.equals
                 in
              FStar_Pprint.op_Hat_Hat uu____48413 uu____48414  in
            FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____48412  in
          FStar_Pprint.op_Hat_Hat uu____48409 uu____48411  in
        let uu____48415 = p_quident uid2  in
        op_Hat_Slash_Plus_Hat uu____48408 uu____48415
    | FStar_Parser_AST.TopLevelModule uid ->
        let uu____48417 =
          let uu____48418 = str "module"  in
          let uu____48420 =
            let uu____48421 = p_quident uid  in
            FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____48421  in
          FStar_Pprint.op_Hat_Hat uu____48418 uu____48420  in
        FStar_Pprint.group uu____48417
    | FStar_Parser_AST.Tycon
        (true
         ,uu____48422,(FStar_Parser_AST.TyconAbbrev
                       (uid,tpars,FStar_Pervasives_Native.None ,t),FStar_Pervasives_Native.None
                       )::[])
        ->
        let effect_prefix_doc =
          let uu____48459 = str "effect"  in
          let uu____48461 =
            let uu____48462 = p_uident uid  in
            FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____48462  in
          FStar_Pprint.op_Hat_Hat uu____48459 uu____48461  in
        let uu____48463 =
          let uu____48464 = p_typars tpars  in
          FStar_Pprint.surround (Prims.parse_int "2") (Prims.parse_int "1")
            effect_prefix_doc uu____48464 FStar_Pprint.equals
           in
        let uu____48467 = p_typ false false t  in
        op_Hat_Slash_Plus_Hat uu____48463 uu____48467
    | FStar_Parser_AST.Tycon (false ,tc,tcdefs) ->
        let s = if tc then str "class" else str "type"  in
        let uu____48498 =
          let uu____48499 = FStar_List.hd tcdefs  in
          p_fsdocTypeDeclPairs s uu____48499  in
        let uu____48512 =
          let uu____48513 = FStar_List.tl tcdefs  in
          FStar_All.pipe_left
            (FStar_Pprint.concat_map
               (fun x  ->
                  let uu____48551 =
                    let uu____48552 = str "and"  in
                    p_fsdocTypeDeclPairs uu____48552 x  in
                  FStar_Pprint.op_Hat_Hat break1 uu____48551)) uu____48513
           in
        FStar_Pprint.op_Hat_Hat uu____48498 uu____48512
    | FStar_Parser_AST.TopLevelLet (q,lbs) ->
        let let_doc =
          let uu____48569 = str "let"  in
          let uu____48571 = p_letqualifier q  in
          FStar_Pprint.op_Hat_Hat uu____48569 uu____48571  in
        let uu____48572 = str "and"  in
        separate_map_with_comments_kw let_doc uu____48572 p_letbinding lbs
          (fun uu____48582  ->
             match uu____48582 with
             | (p,t) ->
                 let uu____48589 =
                   FStar_Range.union_ranges p.FStar_Parser_AST.prange
                     t.FStar_Parser_AST.range
                    in
                 {
                   r = uu____48589;
                   has_qs = false;
                   has_attrs = false;
                   has_fsdoc = (FStar_Util.is_some d.FStar_Parser_AST.doc);
                   is_fsdoc = false
                 })
    | FStar_Parser_AST.Val (lid,t) ->
        let uu____48595 =
          let uu____48596 = str "val"  in
          let uu____48598 =
            let uu____48599 =
              let uu____48600 = p_lident lid  in
              let uu____48601 = sig_as_binders_if_possible t false  in
              FStar_Pprint.op_Hat_Hat uu____48600 uu____48601  in
            FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____48599  in
          FStar_Pprint.op_Hat_Hat uu____48596 uu____48598  in
        FStar_All.pipe_left FStar_Pprint.group uu____48595
    | FStar_Parser_AST.Assume (id1,t) ->
        let decl_keyword =
          let uu____48606 =
            let uu____48608 =
              FStar_Util.char_at id1.FStar_Ident.idText (Prims.parse_int "0")
               in
            FStar_All.pipe_right uu____48608 FStar_Util.is_upper  in
          if uu____48606
          then FStar_Pprint.empty
          else
            (let uu____48616 = str "val"  in
             FStar_Pprint.op_Hat_Hat uu____48616 FStar_Pprint.space)
           in
        let uu____48618 =
          let uu____48619 = p_ident id1  in
          let uu____48620 =
            let uu____48621 =
              let uu____48622 =
                let uu____48623 = p_typ false false t  in
                FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____48623  in
              FStar_Pprint.op_Hat_Hat FStar_Pprint.colon uu____48622  in
            FStar_Pprint.group uu____48621  in
          FStar_Pprint.op_Hat_Hat uu____48619 uu____48620  in
        FStar_Pprint.op_Hat_Hat decl_keyword uu____48618
    | FStar_Parser_AST.Exception (uid,t_opt) ->
        let uu____48632 = str "exception"  in
        let uu____48634 =
          let uu____48635 =
            let uu____48636 = p_uident uid  in
            let uu____48637 =
              FStar_Pprint.optional
                (fun t  ->
                   let uu____48641 =
                     let uu____48642 = str "of"  in
                     let uu____48644 = p_typ false false t  in
                     op_Hat_Slash_Plus_Hat uu____48642 uu____48644  in
                   FStar_Pprint.op_Hat_Hat break1 uu____48641) t_opt
               in
            FStar_Pprint.op_Hat_Hat uu____48636 uu____48637  in
          FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____48635  in
        FStar_Pprint.op_Hat_Hat uu____48632 uu____48634
    | FStar_Parser_AST.NewEffect ne ->
        let uu____48648 = str "new_effect"  in
        let uu____48650 =
          let uu____48651 = p_newEffect ne  in
          FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____48651  in
        FStar_Pprint.op_Hat_Hat uu____48648 uu____48650
    | FStar_Parser_AST.SubEffect se ->
        let uu____48653 = str "sub_effect"  in
        let uu____48655 =
          let uu____48656 = p_subEffect se  in
          FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____48656  in
        FStar_Pprint.op_Hat_Hat uu____48653 uu____48655
    | FStar_Parser_AST.Pragma p -> p_pragma p
    | FStar_Parser_AST.Fsdoc doc1 -> p_fsdoc doc1
    | FStar_Parser_AST.Main uu____48659 ->
        failwith "*Main declaration* : Is that really still in use ??"
    | FStar_Parser_AST.Tycon (true ,uu____48661,uu____48662) ->
        failwith
          "Effect abbreviation is expected to be defined by an abbreviation"
    | FStar_Parser_AST.Splice (ids,t) ->
        let uu____48690 = str "%splice"  in
        let uu____48692 =
          let uu____48693 =
            let uu____48694 = str ";"  in p_list p_uident uu____48694 ids  in
          let uu____48696 =
            let uu____48697 = p_term false false t  in
            FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____48697  in
          FStar_Pprint.op_Hat_Hat uu____48693 uu____48696  in
        FStar_Pprint.op_Hat_Hat uu____48690 uu____48692

and (p_pragma : FStar_Parser_AST.pragma -> FStar_Pprint.document) =
  fun uu___329_48700  ->
    match uu___329_48700 with
    | FStar_Parser_AST.SetOptions s ->
        let uu____48703 = str "#set-options"  in
        let uu____48705 =
          let uu____48706 =
            let uu____48707 = str s  in FStar_Pprint.dquotes uu____48707  in
          FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____48706  in
        FStar_Pprint.op_Hat_Hat uu____48703 uu____48705
    | FStar_Parser_AST.ResetOptions s_opt ->
        let uu____48712 = str "#reset-options"  in
        let uu____48714 =
          FStar_Pprint.optional
            (fun s  ->
               let uu____48720 =
                 let uu____48721 = str s  in FStar_Pprint.dquotes uu____48721
                  in
               FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____48720) s_opt
           in
        FStar_Pprint.op_Hat_Hat uu____48712 uu____48714
    | FStar_Parser_AST.PushOptions s_opt ->
        let uu____48726 = str "#push-options"  in
        let uu____48728 =
          FStar_Pprint.optional
            (fun s  ->
               let uu____48734 =
                 let uu____48735 = str s  in FStar_Pprint.dquotes uu____48735
                  in
               FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____48734) s_opt
           in
        FStar_Pprint.op_Hat_Hat uu____48726 uu____48728
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
    fun uu____48766  ->
      match uu____48766 with
      | (typedecl,fsdoc_opt) ->
          let uu____48779 = p_typeDecl (kw, fsdoc_opt) typedecl  in
          (match uu____48779 with
           | (comm,decl,body,pre) ->
               if comm = FStar_Pprint.empty
               then
                 let uu____48804 = pre body  in
                 FStar_Pprint.op_Hat_Hat decl uu____48804
               else
                 (let uu____48807 =
                    let uu____48808 =
                      let uu____48809 =
                        let uu____48810 = pre body  in
                        FStar_Pprint.op_Hat_Slash_Hat uu____48810 comm  in
                      FStar_Pprint.op_Hat_Hat decl uu____48809  in
                    let uu____48811 =
                      let uu____48812 =
                        let uu____48813 =
                          let uu____48814 =
                            let uu____48815 =
                              FStar_Pprint.op_Hat_Hat FStar_Pprint.hardline
                                body
                               in
                            FStar_Pprint.op_Hat_Hat comm uu____48815  in
                          FStar_Pprint.op_Hat_Hat FStar_Pprint.hardline
                            uu____48814
                           in
                        FStar_Pprint.nest (Prims.parse_int "2") uu____48813
                         in
                      FStar_Pprint.op_Hat_Hat decl uu____48812  in
                    FStar_Pprint.ifflat uu____48808 uu____48811  in
                  FStar_All.pipe_left FStar_Pprint.group uu____48807))

and (p_typeDecl :
  (FStar_Pprint.document * FStar_Parser_AST.fsdoc
    FStar_Pervasives_Native.option) ->
    FStar_Parser_AST.tycon ->
      (FStar_Pprint.document * FStar_Pprint.document * FStar_Pprint.document
        * (FStar_Pprint.document -> FStar_Pprint.document)))
  =
  fun pre  ->
    fun uu___330_48818  ->
      match uu___330_48818 with
      | FStar_Parser_AST.TyconAbstract (lid,bs,typ_opt) ->
          let uu____48847 = p_typeDeclPrefix pre false lid bs typ_opt  in
          (FStar_Pprint.empty, uu____48847, FStar_Pprint.empty,
            FStar_Pervasives.id)
      | FStar_Parser_AST.TyconAbbrev (lid,bs,typ_opt,t) ->
          let uu____48864 = p_typ_sep false false t  in
          (match uu____48864 with
           | (comm,doc1) ->
               let uu____48884 = p_typeDeclPrefix pre true lid bs typ_opt  in
               (comm, uu____48884, doc1, jump2))
      | FStar_Parser_AST.TyconRecord (lid,bs,typ_opt,record_field_decls) ->
          let p_recordFieldAndComments ps uu____48940 =
            match uu____48940 with
            | (lid1,t,doc_opt) ->
                let uu____48957 =
                  let uu____48962 =
                    FStar_Range.extend_to_end_of_line
                      t.FStar_Parser_AST.range
                     in
                  with_comment_sep (p_recordFieldDecl ps) (lid1, t, doc_opt)
                    uu____48962
                   in
                (match uu____48957 with
                 | (comm,field) ->
                     let sep =
                       if ps then FStar_Pprint.semi else FStar_Pprint.empty
                        in
                     inline_comment_or_above comm field sep)
             in
          let p_fields =
            let uu____48980 =
              separate_map_last FStar_Pprint.hardline
                p_recordFieldAndComments record_field_decls
               in
            braces_with_nesting uu____48980  in
          let uu____48989 = p_typeDeclPrefix pre true lid bs typ_opt  in
          (FStar_Pprint.empty, uu____48989, p_fields,
            ((fun d  -> FStar_Pprint.op_Hat_Hat FStar_Pprint.space d)))
      | FStar_Parser_AST.TyconVariant (lid,bs,typ_opt,ct_decls) ->
          let p_constructorBranchAndComments uu____49056 =
            match uu____49056 with
            | (uid,t_opt,doc_opt,use_of) ->
                let range =
                  let uu____49085 =
                    let uu____49086 =
                      FStar_Util.map_opt t_opt
                        (fun t  -> t.FStar_Parser_AST.range)
                       in
                    FStar_Util.dflt uid.FStar_Ident.idRange uu____49086  in
                  FStar_Range.extend_to_end_of_line uu____49085  in
                let uu____49091 =
                  with_comment_sep p_constructorBranch
                    (uid, t_opt, doc_opt, use_of) range
                   in
                (match uu____49091 with
                 | (comm,ctor) ->
                     inline_comment_or_above comm ctor FStar_Pprint.empty)
             in
          let datacon_doc =
            FStar_Pprint.separate_map FStar_Pprint.hardline
              p_constructorBranchAndComments ct_decls
             in
          let uu____49130 = p_typeDeclPrefix pre true lid bs typ_opt  in
          (FStar_Pprint.empty, uu____49130, datacon_doc, jump2)

and (p_typeDeclPrefix :
  (FStar_Pprint.document * FStar_Parser_AST.fsdoc
    FStar_Pervasives_Native.option) ->
    Prims.bool ->
      FStar_Ident.ident ->
        FStar_Parser_AST.binder Prims.list ->
          FStar_Parser_AST.knd FStar_Pervasives_Native.option ->
            FStar_Pprint.document)
  =
  fun uu____49135  ->
    fun eq1  ->
      fun lid  ->
        fun bs  ->
          fun typ_opt  ->
            match uu____49135 with
            | (kw,fsdoc_opt) ->
                let maybe_with_fsdoc cont =
                  let lid_doc = p_ident lid  in
                  let kw_lid =
                    let uu____49170 =
                      FStar_Pprint.op_Hat_Slash_Hat kw lid_doc  in
                    FStar_Pprint.group uu____49170  in
                  match fsdoc_opt with
                  | FStar_Pervasives_Native.None  -> cont kw_lid
                  | FStar_Pervasives_Native.Some fsdoc ->
                      let uu____49172 =
                        let uu____49175 =
                          let uu____49178 = p_fsdoc fsdoc  in
                          let uu____49179 =
                            let uu____49182 = cont lid_doc  in [uu____49182]
                             in
                          uu____49178 :: uu____49179  in
                        kw :: uu____49175  in
                      FStar_Pprint.separate FStar_Pprint.hardline uu____49172
                   in
                let typ =
                  let maybe_eq =
                    if eq1 then FStar_Pprint.equals else FStar_Pprint.empty
                     in
                  match typ_opt with
                  | FStar_Pervasives_Native.None  -> maybe_eq
                  | FStar_Pervasives_Native.Some t ->
                      let uu____49189 =
                        let uu____49190 =
                          let uu____49191 = p_typ false false t  in
                          FStar_Pprint.op_Hat_Slash_Hat uu____49191 maybe_eq
                           in
                        FStar_Pprint.op_Hat_Hat FStar_Pprint.space
                          uu____49190
                         in
                      FStar_Pprint.op_Hat_Hat FStar_Pprint.colon uu____49189
                   in
                if bs = []
                then maybe_with_fsdoc (fun n1  -> prefix2 n1 typ)
                else
                  (let binders = p_binders_list true bs  in
                   maybe_with_fsdoc
                     (fun n1  ->
                        let uu____49211 =
                          let uu____49212 = FStar_Pprint.flow break1 binders
                             in
                          prefix2 n1 uu____49212  in
                        prefix2 uu____49211 typ))

and (p_recordFieldDecl :
  Prims.bool ->
    (FStar_Ident.ident * FStar_Parser_AST.term * FStar_Parser_AST.fsdoc
      FStar_Pervasives_Native.option) -> FStar_Pprint.document)
  =
  fun ps  ->
    fun uu____49214  ->
      match uu____49214 with
      | (lid,t,doc_opt) ->
          let uu____49231 =
            let uu____49232 = FStar_Pprint.optional p_fsdoc doc_opt  in
            let uu____49233 =
              let uu____49234 = p_lident lid  in
              let uu____49235 =
                let uu____49236 = p_typ ps false t  in
                FStar_Pprint.op_Hat_Hat FStar_Pprint.colon uu____49236  in
              FStar_Pprint.op_Hat_Hat uu____49234 uu____49235  in
            FStar_Pprint.op_Hat_Hat uu____49232 uu____49233  in
          FStar_Pprint.group uu____49231

and (p_constructorBranch :
  (FStar_Ident.ident * FStar_Parser_AST.term FStar_Pervasives_Native.option *
    FStar_Parser_AST.fsdoc FStar_Pervasives_Native.option * Prims.bool) ->
    FStar_Pprint.document)
  =
  fun uu____49238  ->
    match uu____49238 with
    | (uid,t_opt,doc_opt,use_of) ->
        let sep = if use_of then str "of" else FStar_Pprint.colon  in
        let uid_doc =
          let uu____49272 =
            let uu____49273 =
              let uu____49274 = p_uident uid  in
              FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____49274  in
            FStar_Pprint.op_Hat_Hat FStar_Pprint.bar uu____49273  in
          FStar_Pprint.group uu____49272  in
        let uu____49275 = FStar_Pprint.optional p_fsdoc doc_opt  in
        let uu____49276 =
          default_or_map uid_doc
            (fun t  ->
               let uu____49280 =
                 let uu____49281 =
                   let uu____49282 =
                     let uu____49283 =
                       let uu____49284 = p_typ false false t  in
                       FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____49284
                        in
                     FStar_Pprint.op_Hat_Hat sep uu____49283  in
                   FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____49282  in
                 FStar_Pprint.op_Hat_Hat uid_doc uu____49281  in
               FStar_Pprint.group uu____49280) t_opt
           in
        FStar_Pprint.op_Hat_Hat uu____49275 uu____49276

and (p_letlhs :
  FStar_Pprint.document ->
    (FStar_Parser_AST.pattern * FStar_Parser_AST.term) ->
      Prims.bool -> FStar_Pprint.document)
  =
  fun kw  ->
    fun uu____49288  ->
      fun inner_let  ->
        match uu____49288 with
        | (pat,uu____49296) ->
            let uu____49297 =
              match pat.FStar_Parser_AST.pat with
              | FStar_Parser_AST.PatAscribed
                  (pat1,(t,FStar_Pervasives_Native.None )) ->
                  (pat1,
                    (FStar_Pervasives_Native.Some (t, FStar_Pprint.empty)))
              | FStar_Parser_AST.PatAscribed
                  (pat1,(t,FStar_Pervasives_Native.Some tac)) ->
                  let uu____49349 =
                    let uu____49356 =
                      let uu____49361 =
                        let uu____49362 =
                          let uu____49363 =
                            let uu____49364 = str "by"  in
                            let uu____49366 =
                              let uu____49367 = p_atomicTerm tac  in
                              FStar_Pprint.op_Hat_Hat FStar_Pprint.space
                                uu____49367
                               in
                            FStar_Pprint.op_Hat_Hat uu____49364 uu____49366
                             in
                          FStar_Pprint.op_Hat_Hat FStar_Pprint.space
                            uu____49363
                           in
                        FStar_Pprint.group uu____49362  in
                      (t, uu____49361)  in
                    FStar_Pervasives_Native.Some uu____49356  in
                  (pat1, uu____49349)
              | uu____49378 -> (pat, FStar_Pervasives_Native.None)  in
            (match uu____49297 with
             | (pat1,ascr) ->
                 (match pat1.FStar_Parser_AST.pat with
                  | FStar_Parser_AST.PatApp
                      ({
                         FStar_Parser_AST.pat = FStar_Parser_AST.PatVar
                           (lid,uu____49404);
                         FStar_Parser_AST.prange = uu____49405;_},pats)
                      ->
                      let ascr_doc =
                        match ascr with
                        | FStar_Pervasives_Native.Some (t,tac) ->
                            let uu____49422 =
                              sig_as_binders_if_possible t true  in
                            FStar_Pprint.op_Hat_Hat uu____49422 tac
                        | FStar_Pervasives_Native.None  -> FStar_Pprint.empty
                         in
                      let uu____49428 =
                        if inner_let
                        then
                          let uu____49442 = pats_as_binders_if_possible pats
                             in
                          match uu____49442 with
                          | (bs,style) ->
                              ((FStar_List.append bs [ascr_doc]), style)
                        else
                          (let uu____49465 = pats_as_binders_if_possible pats
                              in
                           match uu____49465 with
                           | (bs,style) ->
                               ((FStar_List.append bs [ascr_doc]), style))
                         in
                      (match uu____49428 with
                       | (terms,style) ->
                           let uu____49492 =
                             let uu____49493 =
                               let uu____49494 =
                                 let uu____49495 = p_lident lid  in
                                 let uu____49496 =
                                   format_sig style terms true true  in
                                 FStar_Pprint.op_Hat_Hat uu____49495
                                   uu____49496
                                  in
                               FStar_Pprint.op_Hat_Hat FStar_Pprint.space
                                 uu____49494
                                in
                             FStar_Pprint.op_Hat_Hat kw uu____49493  in
                           FStar_All.pipe_left FStar_Pprint.group uu____49492)
                  | uu____49499 ->
                      let ascr_doc =
                        match ascr with
                        | FStar_Pervasives_Native.Some (t,tac) ->
                            let uu____49507 =
                              let uu____49508 =
                                let uu____49509 =
                                  p_typ_top
                                    (Arrows
                                       ((Prims.parse_int "2"),
                                         (Prims.parse_int "2"))) false false
                                    t
                                   in
                                FStar_Pprint.op_Hat_Hat FStar_Pprint.colon
                                  uu____49509
                                 in
                              FStar_Pprint.group uu____49508  in
                            FStar_Pprint.op_Hat_Hat uu____49507 tac
                        | FStar_Pervasives_Native.None  -> FStar_Pprint.empty
                         in
                      let uu____49520 =
                        let uu____49521 =
                          let uu____49522 =
                            let uu____49523 = p_tuplePattern pat1  in
                            FStar_Pprint.op_Hat_Slash_Hat kw uu____49523  in
                          FStar_Pprint.group uu____49522  in
                        FStar_Pprint.op_Hat_Hat uu____49521 ascr_doc  in
                      FStar_Pprint.group uu____49520))

and (p_letbinding :
  FStar_Pprint.document ->
    (FStar_Parser_AST.pattern * FStar_Parser_AST.term) ->
      FStar_Pprint.document)
  =
  fun kw  ->
    fun uu____49525  ->
      match uu____49525 with
      | (pat,e) ->
          let doc_pat = p_letlhs kw (pat, e) false  in
          let uu____49534 = p_term_sep false false e  in
          (match uu____49534 with
           | (comm,doc_expr) ->
               let doc_expr1 =
                 inline_comment_or_above comm doc_expr FStar_Pprint.empty  in
               let uu____49544 =
                 let uu____49545 =
                   FStar_Pprint.op_Hat_Slash_Hat FStar_Pprint.equals
                     doc_expr1
                    in
                 FStar_Pprint.op_Hat_Slash_Hat doc_pat uu____49545  in
               let uu____49546 =
                 let uu____49547 =
                   let uu____49548 =
                     let uu____49549 =
                       let uu____49550 = jump2 doc_expr1  in
                       FStar_Pprint.op_Hat_Hat FStar_Pprint.equals
                         uu____49550
                        in
                     FStar_Pprint.group uu____49549  in
                   FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____49548  in
                 FStar_Pprint.op_Hat_Hat doc_pat uu____49547  in
               FStar_Pprint.ifflat uu____49544 uu____49546)

and (p_newEffect : FStar_Parser_AST.effect_decl -> FStar_Pprint.document) =
  fun uu___331_49551  ->
    match uu___331_49551 with
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
        let uu____49576 = p_uident uid  in
        let uu____49577 = p_binders true bs  in
        let uu____49579 =
          let uu____49580 = p_simpleTerm false false t  in
          prefix2 FStar_Pprint.equals uu____49580  in
        surround_maybe_empty (Prims.parse_int "2") (Prims.parse_int "1")
          uu____49576 uu____49577 uu____49579

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
          let uu____49595 =
            let uu____49596 =
              let uu____49597 =
                let uu____49598 = p_uident uid  in
                let uu____49599 = p_binders true bs  in
                let uu____49601 =
                  let uu____49602 = p_typ false false t  in
                  prefix2 FStar_Pprint.colon uu____49602  in
                surround_maybe_empty (Prims.parse_int "2")
                  (Prims.parse_int "1") uu____49598 uu____49599 uu____49601
                 in
              FStar_Pprint.group uu____49597  in
            let uu____49607 =
              let uu____49608 = str "with"  in
              let uu____49610 =
                let uu____49611 =
                  let uu____49612 =
                    let uu____49613 =
                      let uu____49614 =
                        let uu____49615 =
                          FStar_Pprint.op_Hat_Hat FStar_Pprint.semi
                            FStar_Pprint.space
                           in
                        FStar_Pprint.op_Hat_Hat FStar_Pprint.hardline
                          uu____49615
                         in
                      separate_map_last uu____49614 p_effectDecl eff_decls
                       in
                    FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____49613
                     in
                  FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____49612  in
                FStar_Pprint.op_Hat_Hat FStar_Pprint.hardline uu____49611  in
              FStar_Pprint.op_Hat_Hat uu____49608 uu____49610  in
            FStar_Pprint.op_Hat_Slash_Hat uu____49596 uu____49607  in
          braces_with_nesting uu____49595

and (p_effectDecl :
  Prims.bool -> FStar_Parser_AST.decl -> FStar_Pprint.document) =
  fun ps  ->
    fun d  ->
      match d.FStar_Parser_AST.d with
      | FStar_Parser_AST.Tycon
          (false
           ,uu____49619,(FStar_Parser_AST.TyconAbbrev
                         (lid,[],FStar_Pervasives_Native.None ,e),FStar_Pervasives_Native.None
                         )::[])
          ->
          let uu____49652 =
            let uu____49653 = p_lident lid  in
            let uu____49654 =
              FStar_Pprint.op_Hat_Hat FStar_Pprint.space FStar_Pprint.equals
               in
            FStar_Pprint.op_Hat_Hat uu____49653 uu____49654  in
          let uu____49655 = p_simpleTerm ps false e  in
          prefix2 uu____49652 uu____49655
      | uu____49657 ->
          let uu____49658 =
            let uu____49660 = FStar_Parser_AST.decl_to_string d  in
            FStar_Util.format1
              "Not a declaration of an effect member... or at least I hope so : %s"
              uu____49660
             in
          failwith uu____49658

and (p_subEffect : FStar_Parser_AST.lift -> FStar_Pprint.document) =
  fun lift  ->
    let lift_op_doc =
      let lifts =
        match lift.FStar_Parser_AST.lift_op with
        | FStar_Parser_AST.NonReifiableLift t -> [("lift_wp", t)]
        | FStar_Parser_AST.ReifiableLift (t1,t2) ->
            [("lift_wp", t1); ("lift", t2)]
        | FStar_Parser_AST.LiftForFree t -> [("lift", t)]  in
      let p_lift ps uu____49743 =
        match uu____49743 with
        | (kwd,t) ->
            let uu____49754 =
              let uu____49755 = str kwd  in
              let uu____49756 =
                FStar_Pprint.op_Hat_Hat FStar_Pprint.space
                  FStar_Pprint.equals
                 in
              FStar_Pprint.op_Hat_Hat uu____49755 uu____49756  in
            let uu____49757 = p_simpleTerm ps false t  in
            prefix2 uu____49754 uu____49757
         in
      separate_break_map_last FStar_Pprint.semi p_lift lifts  in
    let uu____49764 =
      let uu____49765 =
        let uu____49766 = p_quident lift.FStar_Parser_AST.msource  in
        let uu____49767 =
          let uu____49768 = str "~>"  in
          FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____49768  in
        FStar_Pprint.op_Hat_Hat uu____49766 uu____49767  in
      let uu____49770 = p_quident lift.FStar_Parser_AST.mdest  in
      prefix2 uu____49765 uu____49770  in
    let uu____49771 =
      let uu____49772 = braces_with_nesting lift_op_doc  in
      FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____49772  in
    FStar_Pprint.op_Hat_Hat uu____49764 uu____49771

and (p_qualifier : FStar_Parser_AST.qualifier -> FStar_Pprint.document) =
  fun uu___332_49773  ->
    match uu___332_49773 with
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
        let uu____49793 = p_qualifier q  in
        FStar_Pprint.op_Hat_Hat uu____49793 FStar_Pprint.hardline
    | uu____49794 ->
        let uu____49795 =
          let uu____49796 = FStar_List.map p_qualifier qs  in
          FStar_Pprint.flow break1 uu____49796  in
        FStar_Pprint.op_Hat_Hat uu____49795 FStar_Pprint.hardline

and (p_letqualifier :
  FStar_Parser_AST.let_qualifier -> FStar_Pprint.document) =
  fun uu___333_49799  ->
    match uu___333_49799 with
    | FStar_Parser_AST.Rec  ->
        let uu____49800 = str "rec"  in
        FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____49800
    | FStar_Parser_AST.NoLetQualifier  -> FStar_Pprint.empty

and (p_aqual : FStar_Parser_AST.arg_qualifier -> FStar_Pprint.document) =
  fun uu___334_49802  ->
    match uu___334_49802 with
    | FStar_Parser_AST.Implicit  -> str "#"
    | FStar_Parser_AST.Equality  -> str "$"
    | FStar_Parser_AST.Meta t ->
        let t1 =
          match t.FStar_Parser_AST.tm with
          | FStar_Parser_AST.Abs (uu____49807,e) -> e
          | uu____49813 ->
              FStar_Parser_AST.mk_term
                (FStar_Parser_AST.App
                   (t,
                     (FStar_Parser_AST.unit_const t.FStar_Parser_AST.range),
                     FStar_Parser_AST.Nothing)) t.FStar_Parser_AST.range
                FStar_Parser_AST.Expr
           in
        let uu____49814 = str "#["  in
        let uu____49816 =
          let uu____49817 = p_term false false t1  in
          let uu____49820 =
            let uu____49821 = str "]"  in
            FStar_Pprint.op_Hat_Hat uu____49821 break1  in
          FStar_Pprint.op_Hat_Hat uu____49817 uu____49820  in
        FStar_Pprint.op_Hat_Hat uu____49814 uu____49816

and (p_disjunctivePattern :
  FStar_Parser_AST.pattern -> FStar_Pprint.document) =
  fun p  ->
    match p.FStar_Parser_AST.pat with
    | FStar_Parser_AST.PatOr pats ->
        let uu____49827 =
          let uu____49828 =
            let uu____49829 =
              FStar_Pprint.op_Hat_Hat FStar_Pprint.bar FStar_Pprint.space  in
            FStar_Pprint.op_Hat_Hat break1 uu____49829  in
          FStar_Pprint.separate_map uu____49828 p_tuplePattern pats  in
        FStar_Pprint.group uu____49827
    | uu____49830 -> p_tuplePattern p

and (p_tuplePattern : FStar_Parser_AST.pattern -> FStar_Pprint.document) =
  fun p  ->
    match p.FStar_Parser_AST.pat with
    | FStar_Parser_AST.PatTuple (pats,false ) ->
        let uu____49839 =
          let uu____49840 = FStar_Pprint.op_Hat_Hat FStar_Pprint.comma break1
             in
          FStar_Pprint.separate_map uu____49840 p_constructorPattern pats  in
        FStar_Pprint.group uu____49839
    | uu____49841 -> p_constructorPattern p

and (p_constructorPattern :
  FStar_Parser_AST.pattern -> FStar_Pprint.document) =
  fun p  ->
    match p.FStar_Parser_AST.pat with
    | FStar_Parser_AST.PatApp
        ({ FStar_Parser_AST.pat = FStar_Parser_AST.PatName maybe_cons_lid;
           FStar_Parser_AST.prange = uu____49844;_},hd1::tl1::[])
        when
        FStar_Ident.lid_equals maybe_cons_lid FStar_Parser_Const.cons_lid ->
        let uu____49849 =
          FStar_Pprint.op_Hat_Hat FStar_Pprint.colon FStar_Pprint.colon  in
        let uu____49850 = p_constructorPattern hd1  in
        let uu____49851 = p_constructorPattern tl1  in
        infix0 uu____49849 uu____49850 uu____49851
    | FStar_Parser_AST.PatApp
        ({ FStar_Parser_AST.pat = FStar_Parser_AST.PatName uid;
           FStar_Parser_AST.prange = uu____49853;_},pats)
        ->
        let uu____49859 = p_quident uid  in
        let uu____49860 =
          FStar_Pprint.separate_map break1 p_atomicPattern pats  in
        prefix2 uu____49859 uu____49860
    | uu____49861 -> p_atomicPattern p

and (p_atomicPattern : FStar_Parser_AST.pattern -> FStar_Pprint.document) =
  fun p  ->
    match p.FStar_Parser_AST.pat with
    | FStar_Parser_AST.PatAscribed (pat,(t,FStar_Pervasives_Native.None )) ->
        (match ((pat.FStar_Parser_AST.pat), (t.FStar_Parser_AST.tm)) with
         | (FStar_Parser_AST.PatVar (lid,aqual),FStar_Parser_AST.Refine
            ({ FStar_Parser_AST.b = FStar_Parser_AST.Annotated (lid',t1);
               FStar_Parser_AST.brange = uu____49877;
               FStar_Parser_AST.blevel = uu____49878;
               FStar_Parser_AST.aqual = uu____49879;_},phi))
             when lid.FStar_Ident.idText = lid'.FStar_Ident.idText ->
             let uu____49888 =
               let uu____49889 = p_ident lid  in
               p_refinement aqual uu____49889 t1 phi  in
             soft_parens_with_nesting uu____49888
         | (FStar_Parser_AST.PatWild aqual,FStar_Parser_AST.Refine
            ({ FStar_Parser_AST.b = FStar_Parser_AST.NoName t1;
               FStar_Parser_AST.brange = uu____49892;
               FStar_Parser_AST.blevel = uu____49893;
               FStar_Parser_AST.aqual = uu____49894;_},phi))
             ->
             let uu____49900 =
               p_refinement aqual FStar_Pprint.underscore t1 phi  in
             soft_parens_with_nesting uu____49900
         | uu____49901 ->
             let uu____49906 =
               let uu____49907 = p_tuplePattern pat  in
               let uu____49908 =
                 let uu____49909 = p_tmEqNoRefinement t  in
                 FStar_Pprint.op_Hat_Slash_Hat FStar_Pprint.colon uu____49909
                  in
               FStar_Pprint.op_Hat_Hat uu____49907 uu____49908  in
             soft_parens_with_nesting uu____49906)
    | FStar_Parser_AST.PatList pats ->
        let uu____49913 =
          separate_break_map FStar_Pprint.semi p_tuplePattern pats  in
        FStar_Pprint.surround (Prims.parse_int "2") (Prims.parse_int "0")
          FStar_Pprint.lbracket uu____49913 FStar_Pprint.rbracket
    | FStar_Parser_AST.PatRecord pats ->
        let p_recordFieldPat uu____49932 =
          match uu____49932 with
          | (lid,pat) ->
              let uu____49939 = p_qlident lid  in
              let uu____49940 = p_tuplePattern pat  in
              infix2 FStar_Pprint.equals uu____49939 uu____49940
           in
        let uu____49941 =
          separate_break_map FStar_Pprint.semi p_recordFieldPat pats  in
        soft_braces_with_nesting uu____49941
    | FStar_Parser_AST.PatTuple (pats,true ) ->
        let uu____49953 =
          FStar_Pprint.op_Hat_Hat FStar_Pprint.lparen FStar_Pprint.bar  in
        let uu____49954 =
          separate_break_map FStar_Pprint.comma p_constructorPattern pats  in
        let uu____49955 =
          FStar_Pprint.op_Hat_Hat FStar_Pprint.bar FStar_Pprint.rparen  in
        FStar_Pprint.surround (Prims.parse_int "2") (Prims.parse_int "1")
          uu____49953 uu____49954 uu____49955
    | FStar_Parser_AST.PatTvar (tv,arg_qualifier_opt) -> p_tvar tv
    | FStar_Parser_AST.PatOp op ->
        let uu____49966 =
          let uu____49967 =
            let uu____49968 =
              let uu____49969 = FStar_Ident.text_of_id op  in str uu____49969
               in
            let uu____49971 =
              FStar_Pprint.op_Hat_Hat FStar_Pprint.space FStar_Pprint.rparen
               in
            FStar_Pprint.op_Hat_Hat uu____49968 uu____49971  in
          FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____49967  in
        FStar_Pprint.op_Hat_Hat FStar_Pprint.lparen uu____49966
    | FStar_Parser_AST.PatWild aqual ->
        let uu____49975 = FStar_Pprint.optional p_aqual aqual  in
        FStar_Pprint.op_Hat_Hat uu____49975 FStar_Pprint.underscore
    | FStar_Parser_AST.PatConst c -> p_constant c
    | FStar_Parser_AST.PatVar (lid,aqual) ->
        let uu____49983 = FStar_Pprint.optional p_aqual aqual  in
        let uu____49984 = p_lident lid  in
        FStar_Pprint.op_Hat_Hat uu____49983 uu____49984
    | FStar_Parser_AST.PatName uid -> p_quident uid
    | FStar_Parser_AST.PatOr uu____49986 -> failwith "Inner or pattern !"
    | FStar_Parser_AST.PatApp
        ({ FStar_Parser_AST.pat = FStar_Parser_AST.PatName uu____49990;
           FStar_Parser_AST.prange = uu____49991;_},uu____49992)
        ->
        let uu____49997 = p_tuplePattern p  in
        soft_parens_with_nesting uu____49997
    | FStar_Parser_AST.PatTuple (uu____49998,false ) ->
        let uu____50005 = p_tuplePattern p  in
        soft_parens_with_nesting uu____50005
    | uu____50006 ->
        let uu____50007 =
          let uu____50009 = FStar_Parser_AST.pat_to_string p  in
          FStar_Util.format1 "Invalid pattern %s" uu____50009  in
        failwith uu____50007

and (is_typ_tuple : FStar_Parser_AST.term -> Prims.bool) =
  fun e  ->
    match e.FStar_Parser_AST.tm with
    | FStar_Parser_AST.Op
        ({ FStar_Ident.idText = "*"; FStar_Ident.idRange = uu____50014;_},uu____50015)
        -> true
    | uu____50022 -> false

and (is_meta_qualifier :
  FStar_Parser_AST.arg_qualifier FStar_Pervasives_Native.option -> Prims.bool)
  =
  fun aq  ->
    match aq with
    | FStar_Pervasives_Native.Some (FStar_Parser_AST.Meta uu____50028) ->
        true
    | uu____50030 -> false

and (p_binder :
  Prims.bool -> FStar_Parser_AST.binder -> FStar_Pprint.document) =
  fun is_atomic  ->
    fun b  ->
      let uu____50037 = p_binder' is_atomic b  in
      match uu____50037 with
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
          let uu____50076 =
            let uu____50077 =
              FStar_Pprint.optional p_aqual b.FStar_Parser_AST.aqual  in
            let uu____50078 = p_lident lid  in
            FStar_Pprint.op_Hat_Hat uu____50077 uu____50078  in
          (uu____50076, FStar_Pervasives_Native.None, cat_with_colon)
      | FStar_Parser_AST.TVariable lid ->
          let uu____50084 = p_lident lid  in
          (uu____50084, FStar_Pervasives_Native.None, cat_with_colon)
      | FStar_Parser_AST.Annotated (lid,t) ->
          let uu____50091 =
            match t.FStar_Parser_AST.tm with
            | FStar_Parser_AST.Refine
                ({ FStar_Parser_AST.b = FStar_Parser_AST.Annotated (lid',t1);
                   FStar_Parser_AST.brange = uu____50102;
                   FStar_Parser_AST.blevel = uu____50103;
                   FStar_Parser_AST.aqual = uu____50104;_},phi)
                when lid.FStar_Ident.idText = lid'.FStar_Ident.idText ->
                let uu____50109 = p_lident lid  in
                p_refinement' b.FStar_Parser_AST.aqual uu____50109 t1 phi
            | uu____50110 ->
                let t' =
                  let uu____50112 = is_typ_tuple t  in
                  if uu____50112
                  then
                    let uu____50115 = p_tmFormula t  in
                    soft_parens_with_nesting uu____50115
                  else p_tmFormula t  in
                let uu____50118 =
                  let uu____50119 =
                    FStar_Pprint.optional p_aqual b.FStar_Parser_AST.aqual
                     in
                  let uu____50120 = p_lident lid  in
                  FStar_Pprint.op_Hat_Hat uu____50119 uu____50120  in
                (uu____50118, t')
             in
          (match uu____50091 with
           | (b',t') ->
               let catf =
                 let uu____50138 =
                   is_atomic || (is_meta_qualifier b.FStar_Parser_AST.aqual)
                    in
                 if uu____50138
                 then
                   fun x  ->
                     fun y  ->
                       let uu____50145 =
                         let uu____50146 =
                           let uu____50147 = cat_with_colon x y  in
                           FStar_Pprint.op_Hat_Hat uu____50147
                             FStar_Pprint.rparen
                            in
                         FStar_Pprint.op_Hat_Hat FStar_Pprint.lparen
                           uu____50146
                          in
                       FStar_Pprint.group uu____50145
                 else
                   (fun x  ->
                      fun y  ->
                        let uu____50152 = cat_with_colon x y  in
                        FStar_Pprint.group uu____50152)
                  in
               (b', (FStar_Pervasives_Native.Some t'), catf))
      | FStar_Parser_AST.TAnnotated uu____50161 ->
          failwith "Is this still used ?"
      | FStar_Parser_AST.NoName t ->
          (match t.FStar_Parser_AST.tm with
           | FStar_Parser_AST.Refine
               ({ FStar_Parser_AST.b = FStar_Parser_AST.NoName t1;
                  FStar_Parser_AST.brange = uu____50189;
                  FStar_Parser_AST.blevel = uu____50190;
                  FStar_Parser_AST.aqual = uu____50191;_},phi)
               ->
               let uu____50195 =
                 p_refinement' b.FStar_Parser_AST.aqual
                   FStar_Pprint.underscore t1 phi
                  in
               (match uu____50195 with
                | (b',t') ->
                    (b', (FStar_Pervasives_Native.Some t'), cat_with_colon))
           | uu____50216 ->
               if is_atomic
               then
                 let uu____50228 = p_atomicTerm t  in
                 (uu____50228, FStar_Pervasives_Native.None, cat_with_colon)
               else
                 (let uu____50235 = p_appTerm t  in
                  (uu____50235, FStar_Pervasives_Native.None, cat_with_colon)))

and (p_refinement :
  FStar_Parser_AST.arg_qualifier FStar_Pervasives_Native.option ->
    FStar_Pprint.document ->
      FStar_Parser_AST.term -> FStar_Parser_AST.term -> FStar_Pprint.document)
  =
  fun aqual_opt  ->
    fun binder  ->
      fun t  ->
        fun phi  ->
          let uu____50246 = p_refinement' aqual_opt binder t phi  in
          match uu____50246 with | (b,typ) -> cat_with_colon b typ

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
            | FStar_Parser_AST.Construct uu____50262 -> false
            | FStar_Parser_AST.App uu____50274 -> false
            | FStar_Parser_AST.Op uu____50282 -> false
            | uu____50290 -> true  in
          let uu____50292 = p_noSeqTerm false false phi  in
          match uu____50292 with
          | (comm,phi1) ->
              let phi2 =
                if comm = FStar_Pprint.empty
                then phi1
                else
                  (let uu____50309 =
                     FStar_Pprint.op_Hat_Hat FStar_Pprint.hardline phi1  in
                   FStar_Pprint.op_Hat_Hat comm uu____50309)
                 in
              let jump_break =
                if is_t_atomic
                then (Prims.parse_int "0")
                else (Prims.parse_int "1")  in
              let uu____50318 =
                let uu____50319 = FStar_Pprint.optional p_aqual aqual_opt  in
                FStar_Pprint.op_Hat_Hat uu____50319 binder  in
              let uu____50320 =
                let uu____50321 = p_appTerm t  in
                let uu____50322 =
                  let uu____50323 =
                    let uu____50324 =
                      let uu____50325 = soft_braces_with_nesting_tight phi2
                         in
                      let uu____50326 = soft_braces_with_nesting phi2  in
                      FStar_Pprint.ifflat uu____50325 uu____50326  in
                    FStar_Pprint.group uu____50324  in
                  FStar_Pprint.jump (Prims.parse_int "2") jump_break
                    uu____50323
                   in
                FStar_Pprint.op_Hat_Hat uu____50321 uu____50322  in
              (uu____50318, uu____50320)

and (p_binders_list :
  Prims.bool ->
    FStar_Parser_AST.binder Prims.list -> FStar_Pprint.document Prims.list)
  = fun is_atomic  -> fun bs  -> FStar_List.map (p_binder is_atomic) bs

and (p_binders :
  Prims.bool -> FStar_Parser_AST.binder Prims.list -> FStar_Pprint.document)
  =
  fun is_atomic  ->
    fun bs  ->
      let uu____50340 = p_binders_list is_atomic bs  in
      separate_or_flow break1 uu____50340

and (text_of_id_or_underscore : FStar_Ident.ident -> FStar_Pprint.document) =
  fun lid  ->
    let uu____50344 =
      (FStar_Util.starts_with lid.FStar_Ident.idText
         FStar_Ident.reserved_prefix)
        &&
        (let uu____50347 = FStar_Options.print_real_names ()  in
         Prims.op_Negation uu____50347)
       in
    if uu____50344
    then FStar_Pprint.underscore
    else (let uu____50352 = FStar_Ident.text_of_id lid  in str uu____50352)

and (text_of_lid_or_underscore : FStar_Ident.lident -> FStar_Pprint.document)
  =
  fun lid  ->
    let uu____50355 =
      (FStar_Util.starts_with (lid.FStar_Ident.ident).FStar_Ident.idText
         FStar_Ident.reserved_prefix)
        &&
        (let uu____50358 = FStar_Options.print_real_names ()  in
         Prims.op_Negation uu____50358)
       in
    if uu____50355
    then FStar_Pprint.underscore
    else (let uu____50363 = FStar_Ident.text_of_lid lid  in str uu____50363)

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
          let uu____50384 = FStar_Pprint.op_Hat_Hat doc1 sep  in
          FStar_Pprint.group uu____50384
        else
          (let uu____50387 =
             let uu____50388 =
               let uu____50389 =
                 let uu____50390 =
                   let uu____50391 = FStar_Pprint.op_Hat_Hat break1 comm  in
                   FStar_Pprint.op_Hat_Hat sep uu____50391  in
                 FStar_Pprint.op_Hat_Hat doc1 uu____50390  in
               FStar_Pprint.group uu____50389  in
             let uu____50392 =
               let uu____50393 =
                 let uu____50394 = FStar_Pprint.op_Hat_Hat doc1 sep  in
                 FStar_Pprint.op_Hat_Hat FStar_Pprint.hardline uu____50394
                  in
               FStar_Pprint.op_Hat_Hat comm uu____50393  in
             FStar_Pprint.ifflat uu____50388 uu____50392  in
           FStar_All.pipe_left FStar_Pprint.group uu____50387)

and (p_term :
  Prims.bool -> Prims.bool -> FStar_Parser_AST.term -> FStar_Pprint.document)
  =
  fun ps  ->
    fun pb  ->
      fun e  ->
        match e.FStar_Parser_AST.tm with
        | FStar_Parser_AST.Seq (e1,e2) ->
            let uu____50402 = p_noSeqTerm true false e1  in
            (match uu____50402 with
             | (comm,t1) ->
                 let uu____50411 =
                   inline_comment_or_above comm t1 FStar_Pprint.semi  in
                 let uu____50412 =
                   let uu____50413 = p_term ps pb e2  in
                   FStar_Pprint.op_Hat_Hat FStar_Pprint.hardline uu____50413
                    in
                 FStar_Pprint.op_Hat_Hat uu____50411 uu____50412)
        | FStar_Parser_AST.Bind (x,e1,e2) ->
            let uu____50417 =
              let uu____50418 =
                let uu____50419 =
                  let uu____50420 = p_lident x  in
                  let uu____50421 =
                    FStar_Pprint.op_Hat_Hat FStar_Pprint.space
                      FStar_Pprint.long_left_arrow
                     in
                  FStar_Pprint.op_Hat_Hat uu____50420 uu____50421  in
                let uu____50422 =
                  let uu____50423 = p_noSeqTermAndComment true false e1  in
                  let uu____50426 =
                    FStar_Pprint.op_Hat_Hat FStar_Pprint.space
                      FStar_Pprint.semi
                     in
                  FStar_Pprint.op_Hat_Hat uu____50423 uu____50426  in
                op_Hat_Slash_Plus_Hat uu____50419 uu____50422  in
              FStar_Pprint.group uu____50418  in
            let uu____50427 = p_term ps pb e2  in
            FStar_Pprint.op_Hat_Slash_Hat uu____50417 uu____50427
        | uu____50428 ->
            let uu____50429 = p_noSeqTermAndComment ps pb e  in
            FStar_Pprint.group uu____50429

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
            let uu____50441 = p_noSeqTerm true false e1  in
            (match uu____50441 with
             | (comm,t1) ->
                 let uu____50454 =
                   let uu____50455 =
                     let uu____50456 =
                       FStar_Pprint.op_Hat_Hat t1 FStar_Pprint.semi  in
                     FStar_Pprint.group uu____50456  in
                   let uu____50457 =
                     let uu____50458 = p_term ps pb e2  in
                     FStar_Pprint.op_Hat_Hat FStar_Pprint.hardline
                       uu____50458
                      in
                   FStar_Pprint.op_Hat_Hat uu____50455 uu____50457  in
                 (comm, uu____50454))
        | FStar_Parser_AST.Bind (x,e1,e2) ->
            let uu____50462 =
              let uu____50463 =
                let uu____50464 =
                  let uu____50465 =
                    let uu____50466 = p_lident x  in
                    let uu____50467 =
                      FStar_Pprint.op_Hat_Hat FStar_Pprint.space
                        FStar_Pprint.long_left_arrow
                       in
                    FStar_Pprint.op_Hat_Hat uu____50466 uu____50467  in
                  let uu____50468 =
                    let uu____50469 = p_noSeqTermAndComment true false e1  in
                    let uu____50472 =
                      FStar_Pprint.op_Hat_Hat FStar_Pprint.space
                        FStar_Pprint.semi
                       in
                    FStar_Pprint.op_Hat_Hat uu____50469 uu____50472  in
                  op_Hat_Slash_Plus_Hat uu____50465 uu____50468  in
                FStar_Pprint.group uu____50464  in
              let uu____50473 = p_term ps pb e2  in
              FStar_Pprint.op_Hat_Slash_Hat uu____50463 uu____50473  in
            (FStar_Pprint.empty, uu____50462)
        | uu____50474 -> p_noSeqTerm ps pb e

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
            let uu____50494 =
              let uu____50495 = p_tmIff e1  in
              let uu____50496 =
                let uu____50497 =
                  let uu____50498 = p_typ ps pb t  in
                  FStar_Pprint.op_Hat_Slash_Hat FStar_Pprint.colon
                    uu____50498
                   in
                FStar_Pprint.op_Hat_Hat FStar_Pprint.langle uu____50497  in
              FStar_Pprint.op_Hat_Slash_Hat uu____50495 uu____50496  in
            FStar_Pprint.group uu____50494
        | FStar_Parser_AST.Ascribed (e1,t,FStar_Pervasives_Native.Some tac)
            ->
            let uu____50504 =
              let uu____50505 = p_tmIff e1  in
              let uu____50506 =
                let uu____50507 =
                  let uu____50508 =
                    let uu____50509 = p_typ false false t  in
                    let uu____50512 =
                      let uu____50513 = str "by"  in
                      let uu____50515 = p_typ ps pb tac  in
                      FStar_Pprint.op_Hat_Slash_Hat uu____50513 uu____50515
                       in
                    FStar_Pprint.op_Hat_Slash_Hat uu____50509 uu____50512  in
                  FStar_Pprint.op_Hat_Slash_Hat FStar_Pprint.colon
                    uu____50508
                   in
                FStar_Pprint.op_Hat_Hat FStar_Pprint.langle uu____50507  in
              FStar_Pprint.op_Hat_Slash_Hat uu____50505 uu____50506  in
            FStar_Pprint.group uu____50504
        | FStar_Parser_AST.Op
            ({ FStar_Ident.idText = ".()<-";
               FStar_Ident.idRange = uu____50516;_},e1::e2::e3::[])
            ->
            let uu____50523 =
              let uu____50524 =
                let uu____50525 =
                  let uu____50526 = p_atomicTermNotQUident e1  in
                  let uu____50527 =
                    let uu____50528 =
                      let uu____50529 =
                        let uu____50530 = p_term false false e2  in
                        soft_parens_with_nesting uu____50530  in
                      let uu____50533 =
                        FStar_Pprint.op_Hat_Hat FStar_Pprint.space
                          FStar_Pprint.larrow
                         in
                      FStar_Pprint.op_Hat_Hat uu____50529 uu____50533  in
                    FStar_Pprint.op_Hat_Hat FStar_Pprint.dot uu____50528  in
                  FStar_Pprint.op_Hat_Hat uu____50526 uu____50527  in
                FStar_Pprint.group uu____50525  in
              let uu____50534 =
                let uu____50535 = p_noSeqTermAndComment ps pb e3  in
                jump2 uu____50535  in
              FStar_Pprint.op_Hat_Hat uu____50524 uu____50534  in
            FStar_Pprint.group uu____50523
        | FStar_Parser_AST.Op
            ({ FStar_Ident.idText = ".[]<-";
               FStar_Ident.idRange = uu____50536;_},e1::e2::e3::[])
            ->
            let uu____50543 =
              let uu____50544 =
                let uu____50545 =
                  let uu____50546 = p_atomicTermNotQUident e1  in
                  let uu____50547 =
                    let uu____50548 =
                      let uu____50549 =
                        let uu____50550 = p_term false false e2  in
                        soft_brackets_with_nesting uu____50550  in
                      let uu____50553 =
                        FStar_Pprint.op_Hat_Hat FStar_Pprint.space
                          FStar_Pprint.larrow
                         in
                      FStar_Pprint.op_Hat_Hat uu____50549 uu____50553  in
                    FStar_Pprint.op_Hat_Hat FStar_Pprint.dot uu____50548  in
                  FStar_Pprint.op_Hat_Hat uu____50546 uu____50547  in
                FStar_Pprint.group uu____50545  in
              let uu____50554 =
                let uu____50555 = p_noSeqTermAndComment ps pb e3  in
                jump2 uu____50555  in
              FStar_Pprint.op_Hat_Hat uu____50544 uu____50554  in
            FStar_Pprint.group uu____50543
        | FStar_Parser_AST.Requires (e1,wtf) ->
            let uu____50565 =
              let uu____50566 = str "requires"  in
              let uu____50568 = p_typ ps pb e1  in
              FStar_Pprint.op_Hat_Slash_Hat uu____50566 uu____50568  in
            FStar_Pprint.group uu____50565
        | FStar_Parser_AST.Ensures (e1,wtf) ->
            let uu____50578 =
              let uu____50579 = str "ensures"  in
              let uu____50581 = p_typ ps pb e1  in
              FStar_Pprint.op_Hat_Slash_Hat uu____50579 uu____50581  in
            FStar_Pprint.group uu____50578
        | FStar_Parser_AST.Attributes es ->
            let uu____50585 =
              let uu____50586 = str "attributes"  in
              let uu____50588 =
                FStar_Pprint.separate_map break1 p_atomicTerm es  in
              FStar_Pprint.op_Hat_Slash_Hat uu____50586 uu____50588  in
            FStar_Pprint.group uu____50585
        | FStar_Parser_AST.If (e1,e2,e3) ->
            if is_unit e3
            then
              let uu____50593 =
                let uu____50594 =
                  let uu____50595 = str "if"  in
                  let uu____50597 = p_noSeqTermAndComment false false e1  in
                  op_Hat_Slash_Plus_Hat uu____50595 uu____50597  in
                let uu____50600 =
                  let uu____50601 = str "then"  in
                  let uu____50603 = p_noSeqTermAndComment ps pb e2  in
                  op_Hat_Slash_Plus_Hat uu____50601 uu____50603  in
                FStar_Pprint.op_Hat_Slash_Hat uu____50594 uu____50600  in
              FStar_Pprint.group uu____50593
            else
              (let e2_doc =
                 match e2.FStar_Parser_AST.tm with
                 | FStar_Parser_AST.If (uu____50607,uu____50608,e31) when
                     is_unit e31 ->
                     let uu____50610 = p_noSeqTermAndComment false false e2
                        in
                     soft_parens_with_nesting uu____50610
                 | uu____50613 -> p_noSeqTermAndComment false false e2  in
               let uu____50616 =
                 let uu____50617 =
                   let uu____50618 = str "if"  in
                   let uu____50620 = p_noSeqTermAndComment false false e1  in
                   op_Hat_Slash_Plus_Hat uu____50618 uu____50620  in
                 let uu____50623 =
                   let uu____50624 =
                     let uu____50625 = str "then"  in
                     op_Hat_Slash_Plus_Hat uu____50625 e2_doc  in
                   let uu____50627 =
                     let uu____50628 = str "else"  in
                     let uu____50630 = p_noSeqTermAndComment ps pb e3  in
                     op_Hat_Slash_Plus_Hat uu____50628 uu____50630  in
                   FStar_Pprint.op_Hat_Slash_Hat uu____50624 uu____50627  in
                 FStar_Pprint.op_Hat_Slash_Hat uu____50617 uu____50623  in
               FStar_Pprint.group uu____50616)
        | FStar_Parser_AST.TryWith (e1,branches) ->
            let uu____50653 =
              let uu____50654 =
                let uu____50655 =
                  let uu____50656 = str "try"  in
                  let uu____50658 = p_noSeqTermAndComment false false e1  in
                  prefix2 uu____50656 uu____50658  in
                let uu____50661 =
                  let uu____50662 = str "with"  in
                  let uu____50664 =
                    separate_map_last FStar_Pprint.hardline p_patternBranch
                      branches
                     in
                  FStar_Pprint.op_Hat_Slash_Hat uu____50662 uu____50664  in
                FStar_Pprint.op_Hat_Slash_Hat uu____50655 uu____50661  in
              FStar_Pprint.group uu____50654  in
            let uu____50673 = paren_if (ps || pb)  in uu____50673 uu____50653
        | FStar_Parser_AST.Match (e1,branches) ->
            let uu____50700 =
              let uu____50701 =
                let uu____50702 =
                  let uu____50703 = str "match"  in
                  let uu____50705 = p_noSeqTermAndComment false false e1  in
                  let uu____50708 = str "with"  in
                  FStar_Pprint.surround (Prims.parse_int "2")
                    (Prims.parse_int "1") uu____50703 uu____50705 uu____50708
                   in
                let uu____50712 =
                  separate_map_last FStar_Pprint.hardline p_patternBranch
                    branches
                   in
                FStar_Pprint.op_Hat_Slash_Hat uu____50702 uu____50712  in
              FStar_Pprint.group uu____50701  in
            let uu____50721 = paren_if (ps || pb)  in uu____50721 uu____50700
        | FStar_Parser_AST.LetOpen (uid,e1) ->
            let uu____50728 =
              let uu____50729 =
                let uu____50730 =
                  let uu____50731 = str "let open"  in
                  let uu____50733 = p_quident uid  in
                  let uu____50734 = str "in"  in
                  FStar_Pprint.surround (Prims.parse_int "2")
                    (Prims.parse_int "1") uu____50731 uu____50733 uu____50734
                   in
                let uu____50738 = p_term false pb e1  in
                FStar_Pprint.op_Hat_Slash_Hat uu____50730 uu____50738  in
              FStar_Pprint.group uu____50729  in
            let uu____50740 = paren_if ps  in uu____50740 uu____50728
        | FStar_Parser_AST.Let (q,lbs,e1) ->
            let p_lb q1 uu____50805 is_last =
              match uu____50805 with
              | (a,(pat,e2)) ->
                  let attrs = p_attrs_opt a  in
                  let doc_let_or_and =
                    match q1 with
                    | FStar_Pervasives_Native.Some (FStar_Parser_AST.Rec ) ->
                        let uu____50839 =
                          let uu____50840 = str "let"  in
                          let uu____50842 = str "rec"  in
                          FStar_Pprint.op_Hat_Slash_Hat uu____50840
                            uu____50842
                           in
                        FStar_Pprint.group uu____50839
                    | FStar_Pervasives_Native.Some
                        (FStar_Parser_AST.NoLetQualifier ) -> str "let"
                    | uu____50845 -> str "and"  in
                  let doc_pat = p_letlhs doc_let_or_and (pat, e2) true  in
                  let uu____50851 = p_term_sep false false e2  in
                  (match uu____50851 with
                   | (comm,doc_expr) ->
                       let doc_expr1 =
                         inline_comment_or_above comm doc_expr
                           FStar_Pprint.empty
                          in
                       let uu____50861 =
                         if is_last
                         then
                           let uu____50863 =
                             FStar_Pprint.flow break1
                               [doc_pat; FStar_Pprint.equals]
                              in
                           let uu____50864 = str "in"  in
                           FStar_Pprint.surround (Prims.parse_int "2")
                             (Prims.parse_int "1") uu____50863 doc_expr1
                             uu____50864
                         else
                           (let uu____50870 =
                              FStar_Pprint.flow break1
                                [doc_pat; FStar_Pprint.equals; doc_expr1]
                               in
                            FStar_Pprint.hang (Prims.parse_int "2")
                              uu____50870)
                          in
                       FStar_Pprint.op_Hat_Hat attrs uu____50861)
               in
            let l = FStar_List.length lbs  in
            let lbs_docs =
              FStar_List.mapi
                (fun i  ->
                   fun lb  ->
                     if i = (Prims.parse_int "0")
                     then
                       let uu____50921 =
                         p_lb (FStar_Pervasives_Native.Some q) lb
                           (i = (l - (Prims.parse_int "1")))
                          in
                       FStar_Pprint.group uu____50921
                     else
                       (let uu____50932 =
                          p_lb FStar_Pervasives_Native.None lb
                            (i = (l - (Prims.parse_int "1")))
                           in
                        FStar_Pprint.group uu____50932)) lbs
               in
            let lbs_doc =
              let uu____50942 = FStar_Pprint.separate break1 lbs_docs  in
              FStar_Pprint.group uu____50942  in
            let uu____50943 =
              let uu____50944 =
                let uu____50945 =
                  let uu____50946 = p_term false pb e1  in
                  FStar_Pprint.op_Hat_Hat FStar_Pprint.hardline uu____50946
                   in
                FStar_Pprint.op_Hat_Hat lbs_doc uu____50945  in
              FStar_Pprint.group uu____50944  in
            let uu____50948 = paren_if ps  in uu____50948 uu____50943
        | FStar_Parser_AST.Abs
            ({ FStar_Parser_AST.pat = FStar_Parser_AST.PatVar (x,typ_opt);
               FStar_Parser_AST.prange = uu____50955;_}::[],{
                                                              FStar_Parser_AST.tm
                                                                =
                                                                FStar_Parser_AST.Match
                                                                (maybe_x,branches);
                                                              FStar_Parser_AST.range
                                                                = uu____50958;
                                                              FStar_Parser_AST.level
                                                                = uu____50959;_})
            when matches_var maybe_x x ->
            let uu____50986 =
              let uu____50987 =
                let uu____50988 = str "function"  in
                let uu____50990 =
                  separate_map_last FStar_Pprint.hardline p_patternBranch
                    branches
                   in
                FStar_Pprint.op_Hat_Slash_Hat uu____50988 uu____50990  in
              FStar_Pprint.group uu____50987  in
            let uu____50999 = paren_if (ps || pb)  in uu____50999 uu____50986
        | FStar_Parser_AST.Quote (e1,FStar_Parser_AST.Dynamic ) ->
            let uu____51005 =
              let uu____51006 = str "quote"  in
              let uu____51008 = p_noSeqTermAndComment ps pb e1  in
              FStar_Pprint.op_Hat_Slash_Hat uu____51006 uu____51008  in
            FStar_Pprint.group uu____51005
        | FStar_Parser_AST.Quote (e1,FStar_Parser_AST.Static ) ->
            let uu____51010 =
              let uu____51011 = str "`"  in
              let uu____51013 = p_noSeqTermAndComment ps pb e1  in
              FStar_Pprint.op_Hat_Hat uu____51011 uu____51013  in
            FStar_Pprint.group uu____51010
        | FStar_Parser_AST.VQuote e1 ->
            let uu____51015 =
              let uu____51016 = str "`%"  in
              let uu____51018 = p_noSeqTermAndComment ps pb e1  in
              FStar_Pprint.op_Hat_Hat uu____51016 uu____51018  in
            FStar_Pprint.group uu____51015
        | FStar_Parser_AST.Antiquote
            {
              FStar_Parser_AST.tm = FStar_Parser_AST.Quote
                (e1,FStar_Parser_AST.Dynamic );
              FStar_Parser_AST.range = uu____51020;
              FStar_Parser_AST.level = uu____51021;_}
            ->
            let uu____51022 =
              let uu____51023 = str "`@"  in
              let uu____51025 = p_noSeqTermAndComment ps pb e1  in
              FStar_Pprint.op_Hat_Hat uu____51023 uu____51025  in
            FStar_Pprint.group uu____51022
        | FStar_Parser_AST.Antiquote e1 ->
            let uu____51027 =
              let uu____51028 = str "`#"  in
              let uu____51030 = p_noSeqTermAndComment ps pb e1  in
              FStar_Pprint.op_Hat_Hat uu____51028 uu____51030  in
            FStar_Pprint.group uu____51027
        | FStar_Parser_AST.CalcProof (rel,init1,steps) ->
            let head1 =
              let uu____51039 = str "calc"  in
              let uu____51041 =
                let uu____51042 =
                  let uu____51043 = p_noSeqTermAndComment false false rel  in
                  let uu____51046 =
                    FStar_Pprint.op_Hat_Hat FStar_Pprint.space
                      FStar_Pprint.lbrace
                     in
                  FStar_Pprint.op_Hat_Hat uu____51043 uu____51046  in
                FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____51042  in
              FStar_Pprint.op_Hat_Hat uu____51039 uu____51041  in
            let bot = FStar_Pprint.rbrace  in
            let uu____51048 =
              FStar_Pprint.op_Hat_Hat FStar_Pprint.hardline bot  in
            let uu____51049 =
              let uu____51050 =
                let uu____51051 =
                  let uu____51052 = p_noSeqTermAndComment false false init1
                     in
                  let uu____51055 =
                    let uu____51056 = str ";"  in
                    let uu____51058 =
                      let uu____51059 =
                        separate_map_last FStar_Pprint.hardline p_calcStep
                          steps
                         in
                      FStar_Pprint.op_Hat_Hat FStar_Pprint.hardline
                        uu____51059
                       in
                    FStar_Pprint.op_Hat_Hat uu____51056 uu____51058  in
                  FStar_Pprint.op_Hat_Hat uu____51052 uu____51055  in
                FStar_Pprint.op_Hat_Hat FStar_Pprint.hardline uu____51051  in
              FStar_All.pipe_left (FStar_Pprint.nest (Prims.parse_int "2"))
                uu____51050
               in
            FStar_Pprint.enclose head1 uu____51048 uu____51049
        | uu____51061 -> p_typ ps pb e

and (p_calcStep :
  Prims.bool -> FStar_Parser_AST.calc_step -> FStar_Pprint.document) =
  fun uu____51062  ->
    fun uu____51063  ->
      match uu____51063 with
      | FStar_Parser_AST.CalcStep (rel,just,next) ->
          let uu____51068 =
            let uu____51069 = p_noSeqTermAndComment false false rel  in
            let uu____51072 =
              let uu____51073 =
                let uu____51074 =
                  let uu____51075 =
                    let uu____51076 = p_noSeqTermAndComment false false just
                       in
                    let uu____51079 =
                      let uu____51080 =
                        let uu____51081 =
                          let uu____51082 =
                            let uu____51083 =
                              p_noSeqTermAndComment false false next  in
                            let uu____51086 = str ";"  in
                            FStar_Pprint.op_Hat_Hat uu____51083 uu____51086
                             in
                          FStar_Pprint.op_Hat_Hat FStar_Pprint.hardline
                            uu____51082
                           in
                        FStar_Pprint.op_Hat_Hat FStar_Pprint.rbrace
                          uu____51081
                         in
                      FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____51080
                       in
                    FStar_Pprint.op_Hat_Hat uu____51076 uu____51079  in
                  FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____51075  in
                FStar_Pprint.op_Hat_Hat FStar_Pprint.lbrace uu____51074  in
              FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____51073  in
            FStar_Pprint.op_Hat_Hat uu____51069 uu____51072  in
          FStar_Pprint.group uu____51068

and (p_attrs_opt :
  FStar_Parser_AST.term Prims.list FStar_Pervasives_Native.option ->
    FStar_Pprint.document)
  =
  fun uu___335_51088  ->
    match uu___335_51088 with
    | FStar_Pervasives_Native.None  -> FStar_Pprint.empty
    | FStar_Pervasives_Native.Some terms ->
        let uu____51100 =
          let uu____51101 = str "[@"  in
          let uu____51103 =
            let uu____51104 =
              FStar_Pprint.separate_map break1 p_atomicTerm terms  in
            let uu____51105 = str "]"  in
            FStar_Pprint.op_Hat_Slash_Hat uu____51104 uu____51105  in
          FStar_Pprint.op_Hat_Slash_Hat uu____51101 uu____51103  in
        FStar_Pprint.group uu____51100

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
                 let uu____51142 =
                   let uu____51143 =
                     let uu____51144 = p_quantifier e  in
                     FStar_Pprint.op_Hat_Hat uu____51144 FStar_Pprint.space
                      in
                   FStar_Pprint.soft_surround (Prims.parse_int "2")
                     (Prims.parse_int "0") uu____51143 binders_doc
                     FStar_Pprint.dot
                    in
                 prefix2 uu____51142 term_doc
             | pats ->
                 let uu____51152 =
                   let uu____51153 =
                     let uu____51154 =
                       let uu____51155 =
                         let uu____51156 = p_quantifier e  in
                         FStar_Pprint.op_Hat_Hat uu____51156
                           FStar_Pprint.space
                          in
                       FStar_Pprint.soft_surround (Prims.parse_int "2")
                         (Prims.parse_int "0") uu____51155 binders_doc
                         FStar_Pprint.dot
                        in
                     let uu____51159 = p_trigger trigger  in
                     prefix2 uu____51154 uu____51159  in
                   FStar_Pprint.group uu____51153  in
                 prefix2 uu____51152 term_doc)
        | FStar_Parser_AST.QExists (bs,trigger,e1) ->
            let binders_doc = p_binders true bs  in
            let term_doc = p_noSeqTermAndComment ps pb e1  in
            (match trigger with
             | [] ->
                 let uu____51180 =
                   let uu____51181 =
                     let uu____51182 = p_quantifier e  in
                     FStar_Pprint.op_Hat_Hat uu____51182 FStar_Pprint.space
                      in
                   FStar_Pprint.soft_surround (Prims.parse_int "2")
                     (Prims.parse_int "0") uu____51181 binders_doc
                     FStar_Pprint.dot
                    in
                 prefix2 uu____51180 term_doc
             | pats ->
                 let uu____51190 =
                   let uu____51191 =
                     let uu____51192 =
                       let uu____51193 =
                         let uu____51194 = p_quantifier e  in
                         FStar_Pprint.op_Hat_Hat uu____51194
                           FStar_Pprint.space
                          in
                       FStar_Pprint.soft_surround (Prims.parse_int "2")
                         (Prims.parse_int "0") uu____51193 binders_doc
                         FStar_Pprint.dot
                        in
                     let uu____51197 = p_trigger trigger  in
                     prefix2 uu____51192 uu____51197  in
                   FStar_Pprint.group uu____51191  in
                 prefix2 uu____51190 term_doc)
        | uu____51198 -> p_simpleTerm ps pb e

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
      let uu____51219 = all_binders_annot t  in
      if uu____51219
      then
        let uu____51222 =
          p_typ_top
            (Binders ((Prims.parse_int "4"), (Prims.parse_int "0"), true))
            false false t
           in
        FStar_Pprint.op_Hat_Hat s uu____51222
      else
        (let uu____51233 =
           let uu____51234 =
             let uu____51235 =
               p_typ_top
                 (Arrows ((Prims.parse_int "2"), (Prims.parse_int "2")))
                 false false t
                in
             FStar_Pprint.op_Hat_Hat s uu____51235  in
           FStar_Pprint.op_Hat_Hat FStar_Pprint.colon uu____51234  in
         FStar_Pprint.group uu____51233)

and (collapse_pats :
  (FStar_Pprint.document * FStar_Pprint.document) Prims.list ->
    FStar_Pprint.document Prims.list)
  =
  fun pats  ->
    let fold_fun bs x =
      let uu____51294 = x  in
      match uu____51294 with
      | (b1,t1) ->
          (match bs with
           | [] -> [([b1], t1)]
           | hd1::tl1 ->
               let uu____51359 = hd1  in
               (match uu____51359 with
                | (b2s,t2) ->
                    if t1 = t2
                    then ((FStar_List.append b2s [b1]), t1) :: tl1
                    else ([b1], t1) :: hd1 :: tl1))
       in
    let p_collapsed_binder cb =
      let uu____51431 = cb  in
      match uu____51431 with
      | (bs,typ) ->
          (match bs with
           | [] -> failwith "Impossible"
           | b::[] -> cat_with_colon b typ
           | hd1::tl1 ->
               let uu____51450 =
                 FStar_List.fold_left
                   (fun x  ->
                      fun y  ->
                        let uu____51456 =
                          FStar_Pprint.op_Hat_Hat FStar_Pprint.space y  in
                        FStar_Pprint.op_Hat_Hat x uu____51456) hd1 tl1
                  in
               cat_with_colon uu____51450 typ)
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
                 FStar_Parser_AST.brange = uu____51535;
                 FStar_Parser_AST.blevel = uu____51536;
                 FStar_Parser_AST.aqual = uu____51537;_},phi))
               when lid.FStar_Ident.idText = lid'.FStar_Ident.idText ->
               let uu____51546 =
                 let uu____51551 = p_ident lid  in
                 p_refinement' aqual uu____51551 t1 phi  in
               FStar_Pervasives_Native.Some uu____51546
           | (FStar_Parser_AST.PatVar (lid,aqual),uu____51558) ->
               let uu____51563 =
                 let uu____51568 =
                   let uu____51569 = FStar_Pprint.optional p_aqual aqual  in
                   let uu____51570 = p_ident lid  in
                   FStar_Pprint.op_Hat_Hat uu____51569 uu____51570  in
                 let uu____51571 = p_tmEqNoRefinement t  in
                 (uu____51568, uu____51571)  in
               FStar_Pervasives_Native.Some uu____51563
           | uu____51576 -> FStar_Pervasives_Native.None)
      | uu____51585 -> FStar_Pervasives_Native.None  in
    let all_unbound p =
      match p.FStar_Parser_AST.pat with
      | FStar_Parser_AST.PatAscribed uu____51598 -> false
      | uu____51610 -> true  in
    let uu____51612 = map_if_all all_binders pats  in
    match uu____51612 with
    | FStar_Pervasives_Native.Some bs ->
        let uu____51644 = collapse_pats bs  in
        (uu____51644,
          (Binders ((Prims.parse_int "4"), (Prims.parse_int "0"), true)))
    | FStar_Pervasives_Native.None  ->
        let uu____51661 = FStar_List.map p_atomicPattern pats  in
        (uu____51661,
          (Binders ((Prims.parse_int "4"), (Prims.parse_int "0"), false)))

and (p_quantifier : FStar_Parser_AST.term -> FStar_Pprint.document) =
  fun e  ->
    match e.FStar_Parser_AST.tm with
    | FStar_Parser_AST.QForall uu____51673 -> str "forall"
    | FStar_Parser_AST.QExists uu____51687 -> str "exists"
    | uu____51701 ->
        failwith "Imposible : p_quantifier called on a non-quantifier term"

and (p_trigger :
  FStar_Parser_AST.term Prims.list Prims.list -> FStar_Pprint.document) =
  fun uu___336_51703  ->
    match uu___336_51703 with
    | [] -> FStar_Pprint.empty
    | pats ->
        let uu____51715 =
          let uu____51716 =
            let uu____51717 =
              let uu____51718 = str "pattern"  in
              let uu____51720 =
                let uu____51721 =
                  let uu____51722 = p_disjunctivePats pats  in
                  FStar_Pprint.jump (Prims.parse_int "2")
                    (Prims.parse_int "0") uu____51722
                   in
                FStar_Pprint.op_Hat_Hat uu____51721 FStar_Pprint.rbrace  in
              FStar_Pprint.op_Hat_Slash_Hat uu____51718 uu____51720  in
            FStar_Pprint.op_Hat_Hat FStar_Pprint.colon uu____51717  in
          FStar_Pprint.op_Hat_Hat FStar_Pprint.lbrace uu____51716  in
        FStar_Pprint.group uu____51715

and (p_disjunctivePats :
  FStar_Parser_AST.term Prims.list Prims.list -> FStar_Pprint.document) =
  fun pats  ->
    let uu____51730 = str "\\/"  in
    FStar_Pprint.separate_map uu____51730 p_conjunctivePats pats

and (p_conjunctivePats :
  FStar_Parser_AST.term Prims.list -> FStar_Pprint.document) =
  fun pats  ->
    let uu____51737 =
      let uu____51738 = FStar_Pprint.op_Hat_Hat FStar_Pprint.semi break1  in
      FStar_Pprint.separate_map uu____51738 p_appTerm pats  in
    FStar_Pprint.group uu____51737

and (p_simpleTerm :
  Prims.bool -> Prims.bool -> FStar_Parser_AST.term -> FStar_Pprint.document)
  =
  fun ps  ->
    fun pb  ->
      fun e  ->
        match e.FStar_Parser_AST.tm with
        | FStar_Parser_AST.Abs (pats,e1) ->
            let uu____51750 = p_term_sep false pb e1  in
            (match uu____51750 with
             | (comm,doc1) ->
                 let prefix1 =
                   let uu____51759 = str "fun"  in
                   let uu____51761 =
                     let uu____51762 =
                       FStar_Pprint.separate_map break1 p_atomicPattern pats
                        in
                     FStar_Pprint.op_Hat_Slash_Hat uu____51762
                       FStar_Pprint.rarrow
                      in
                   op_Hat_Slash_Plus_Hat uu____51759 uu____51761  in
                 let uu____51763 =
                   if comm <> FStar_Pprint.empty
                   then
                     let uu____51765 =
                       let uu____51766 =
                         let uu____51767 =
                           FStar_Pprint.op_Hat_Hat FStar_Pprint.hardline doc1
                            in
                         FStar_Pprint.op_Hat_Hat comm uu____51767  in
                       FStar_Pprint.op_Hat_Hat FStar_Pprint.hardline
                         uu____51766
                        in
                     FStar_Pprint.op_Hat_Hat prefix1 uu____51765
                   else
                     (let uu____51770 = op_Hat_Slash_Plus_Hat prefix1 doc1
                         in
                      FStar_Pprint.group uu____51770)
                    in
                 let uu____51771 = paren_if ps  in uu____51771 uu____51763)
        | uu____51776 -> p_tmIff e

and (p_maybeFocusArrow : Prims.bool -> FStar_Pprint.document) =
  fun b  -> if b then str "~>" else FStar_Pprint.rarrow

and (p_patternBranch :
  Prims.bool ->
    (FStar_Parser_AST.pattern * FStar_Parser_AST.term
      FStar_Pervasives_Native.option * FStar_Parser_AST.term) ->
      FStar_Pprint.document)
  =
  fun pb  ->
    fun uu____51784  ->
      match uu____51784 with
      | (pat,when_opt,e) ->
          let one_pattern_branch p =
            let branch =
              match when_opt with
              | FStar_Pervasives_Native.None  ->
                  let uu____51808 =
                    let uu____51809 =
                      let uu____51810 =
                        let uu____51811 = p_tuplePattern p  in
                        let uu____51812 =
                          FStar_Pprint.op_Hat_Hat FStar_Pprint.space
                            FStar_Pprint.rarrow
                           in
                        FStar_Pprint.op_Hat_Hat uu____51811 uu____51812  in
                      FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____51810
                       in
                    FStar_Pprint.op_Hat_Hat FStar_Pprint.bar uu____51809  in
                  FStar_Pprint.group uu____51808
              | FStar_Pervasives_Native.Some f ->
                  let uu____51814 =
                    let uu____51815 =
                      let uu____51816 =
                        let uu____51817 =
                          let uu____51818 =
                            let uu____51819 = p_tuplePattern p  in
                            let uu____51820 = str "when"  in
                            FStar_Pprint.op_Hat_Slash_Hat uu____51819
                              uu____51820
                             in
                          FStar_Pprint.group uu____51818  in
                        let uu____51822 =
                          let uu____51823 =
                            let uu____51826 = p_tmFormula f  in
                            [uu____51826; FStar_Pprint.rarrow]  in
                          FStar_Pprint.flow break1 uu____51823  in
                        FStar_Pprint.op_Hat_Slash_Hat uu____51817 uu____51822
                         in
                      FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____51816
                       in
                    FStar_Pprint.op_Hat_Hat FStar_Pprint.bar uu____51815  in
                  FStar_Pprint.hang (Prims.parse_int "2") uu____51814
               in
            let uu____51828 = p_term_sep false pb e  in
            match uu____51828 with
            | (comm,doc1) ->
                if pb
                then
                  (if comm = FStar_Pprint.empty
                   then
                     let uu____51838 = op_Hat_Slash_Plus_Hat branch doc1  in
                     FStar_Pprint.group uu____51838
                   else
                     (let uu____51841 =
                        let uu____51842 =
                          let uu____51843 =
                            let uu____51844 =
                              let uu____51845 =
                                FStar_Pprint.op_Hat_Hat break1 comm  in
                              FStar_Pprint.op_Hat_Hat doc1 uu____51845  in
                            op_Hat_Slash_Plus_Hat branch uu____51844  in
                          FStar_Pprint.group uu____51843  in
                        let uu____51846 =
                          let uu____51847 =
                            let uu____51848 =
                              inline_comment_or_above comm doc1
                                FStar_Pprint.empty
                               in
                            jump2 uu____51848  in
                          FStar_Pprint.op_Hat_Hat branch uu____51847  in
                        FStar_Pprint.ifflat uu____51842 uu____51846  in
                      FStar_Pprint.group uu____51841))
                else
                  if comm <> FStar_Pprint.empty
                  then
                    (let uu____51852 =
                       let uu____51853 =
                         FStar_Pprint.op_Hat_Hat FStar_Pprint.hardline doc1
                          in
                       FStar_Pprint.op_Hat_Hat comm uu____51853  in
                     op_Hat_Slash_Plus_Hat branch uu____51852)
                  else op_Hat_Slash_Plus_Hat branch doc1
             in
          (match pat.FStar_Parser_AST.pat with
           | FStar_Parser_AST.PatOr pats ->
               (match FStar_List.rev pats with
                | hd1::tl1 ->
                    let last_pat_branch = one_pattern_branch hd1  in
                    let uu____51864 =
                      let uu____51865 =
                        let uu____51866 =
                          let uu____51867 =
                            let uu____51868 =
                              let uu____51869 =
                                FStar_Pprint.op_Hat_Hat FStar_Pprint.bar
                                  FStar_Pprint.space
                                 in
                              FStar_Pprint.op_Hat_Hat break1 uu____51869  in
                            FStar_Pprint.separate_map uu____51868
                              p_tuplePattern (FStar_List.rev tl1)
                             in
                          FStar_Pprint.op_Hat_Slash_Hat uu____51867
                            last_pat_branch
                           in
                        FStar_Pprint.op_Hat_Hat FStar_Pprint.space
                          uu____51866
                         in
                      FStar_Pprint.op_Hat_Hat FStar_Pprint.bar uu____51865
                       in
                    FStar_Pprint.group uu____51864
                | [] ->
                    failwith "Impossible: disjunctive pattern can't be empty")
           | uu____51871 -> one_pattern_branch pat)

and (p_tmIff : FStar_Parser_AST.term -> FStar_Pprint.document) =
  fun e  ->
    match e.FStar_Parser_AST.tm with
    | FStar_Parser_AST.Op
        ({ FStar_Ident.idText = "<==>"; FStar_Ident.idRange = uu____51873;_},e1::e2::[])
        ->
        let uu____51879 = str "<==>"  in
        let uu____51881 = p_tmImplies e1  in
        let uu____51882 = p_tmIff e2  in
        infix0 uu____51879 uu____51881 uu____51882
    | uu____51883 -> p_tmImplies e

and (p_tmImplies : FStar_Parser_AST.term -> FStar_Pprint.document) =
  fun e  ->
    match e.FStar_Parser_AST.tm with
    | FStar_Parser_AST.Op
        ({ FStar_Ident.idText = "==>"; FStar_Ident.idRange = uu____51885;_},e1::e2::[])
        ->
        let uu____51891 = str "==>"  in
        let uu____51893 =
          p_tmArrow (Arrows ((Prims.parse_int "2"), (Prims.parse_int "2")))
            false p_tmFormula e1
           in
        let uu____51899 = p_tmImplies e2  in
        infix0 uu____51891 uu____51893 uu____51899
    | uu____51900 ->
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
          let uu____51914 =
            FStar_List.splitAt
              ((FStar_List.length terms) - (Prims.parse_int "1")) terms
             in
          match uu____51914 with
          | (terms',last1) ->
              let uu____51934 =
                match style with
                | Arrows (n1,ln) ->
                    let uu____51969 =
                      let uu____51970 =
                        FStar_Pprint.op_Hat_Hat FStar_Pprint.rarrow break1
                         in
                      FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____51970
                       in
                    let uu____51971 =
                      FStar_Pprint.op_Hat_Hat FStar_Pprint.rarrow
                        FStar_Pprint.space
                       in
                    (n1, ln, terms', uu____51969, uu____51971)
                | Binders (n1,ln,parens1) ->
                    let uu____51985 =
                      if parens1
                      then FStar_List.map soft_parens_with_nesting terms'
                      else terms'  in
                    let uu____51993 =
                      FStar_Pprint.op_Hat_Hat FStar_Pprint.colon
                        FStar_Pprint.space
                       in
                    (n1, ln, uu____51985, break1, uu____51993)
                 in
              (match uu____51934 with
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
                    | _52026 when _52026 = (Prims.parse_int "1") ->
                        FStar_List.hd terms
                    | uu____52027 ->
                        let uu____52028 =
                          let uu____52029 =
                            let uu____52030 =
                              let uu____52031 =
                                FStar_Pprint.separate sep terms'1  in
                              let uu____52032 =
                                let uu____52033 =
                                  FStar_Pprint.op_Hat_Hat last_op1 last2  in
                                FStar_Pprint.op_Hat_Hat one_line_space
                                  uu____52033
                                 in
                              FStar_Pprint.op_Hat_Hat uu____52031 uu____52032
                               in
                            FStar_Pprint.op_Hat_Hat fs uu____52030  in
                          let uu____52034 =
                            let uu____52035 =
                              let uu____52036 =
                                let uu____52037 =
                                  let uu____52038 =
                                    FStar_Pprint.separate sep terms'1  in
                                  FStar_Pprint.op_Hat_Hat fs uu____52038  in
                                let uu____52039 =
                                  let uu____52040 =
                                    let uu____52041 =
                                      let uu____52042 =
                                        FStar_Pprint.op_Hat_Hat sep
                                          single_line_arg_indent
                                         in
                                      let uu____52043 =
                                        FStar_List.map
                                          (fun x  ->
                                             let uu____52049 =
                                               FStar_Pprint.hang
                                                 (Prims.parse_int "2") x
                                                in
                                             FStar_Pprint.align uu____52049)
                                          terms'1
                                         in
                                      FStar_Pprint.separate uu____52042
                                        uu____52043
                                       in
                                    FStar_Pprint.op_Hat_Hat
                                      single_line_arg_indent uu____52041
                                     in
                                  jump2 uu____52040  in
                                FStar_Pprint.ifflat uu____52037 uu____52039
                                 in
                              FStar_Pprint.group uu____52036  in
                            let uu____52051 =
                              let uu____52052 =
                                let uu____52053 =
                                  FStar_Pprint.op_Hat_Hat last_op1 last2  in
                                FStar_Pprint.hang last_n uu____52053  in
                              FStar_Pprint.align uu____52052  in
                            FStar_Pprint.prefix n1 (Prims.parse_int "1")
                              uu____52035 uu____52051
                             in
                          FStar_Pprint.ifflat uu____52029 uu____52034  in
                        FStar_Pprint.group uu____52028))

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
            | Arrows uu____52067 -> p_tmArrow' p_Tm e
            | Binders uu____52074 -> collapse_binders p_Tm e  in
          format_sig style terms false flat_space

and (p_tmArrow' :
  (FStar_Parser_AST.term -> FStar_Pprint.document) ->
    FStar_Parser_AST.term -> FStar_Pprint.document Prims.list)
  =
  fun p_Tm  ->
    fun e  ->
      match e.FStar_Parser_AST.tm with
      | FStar_Parser_AST.Product (bs,tgt) ->
          let uu____52097 = FStar_List.map (fun b  -> p_binder false b) bs
             in
          let uu____52103 = p_tmArrow' p_Tm tgt  in
          FStar_List.append uu____52097 uu____52103
      | uu____52106 -> let uu____52107 = p_Tm e  in [uu____52107]

and (collapse_binders :
  (FStar_Parser_AST.term -> FStar_Pprint.document) ->
    FStar_Parser_AST.term -> FStar_Pprint.document Prims.list)
  =
  fun p_Tm  ->
    fun e  ->
      let rec accumulate_binders p_Tm1 e1 =
        match e1.FStar_Parser_AST.tm with
        | FStar_Parser_AST.Product (bs,tgt) ->
            let uu____52160 = FStar_List.map (fun b  -> p_binder' false b) bs
               in
            let uu____52186 = accumulate_binders p_Tm1 tgt  in
            FStar_List.append uu____52160 uu____52186
        | uu____52209 ->
            let uu____52210 =
              let uu____52221 = p_Tm1 e1  in
              (uu____52221, FStar_Pervasives_Native.None, cat_with_colon)  in
            [uu____52210]
         in
      let fold_fun bs x =
        let uu____52319 = x  in
        match uu____52319 with
        | (b1,t1,f1) ->
            (match bs with
             | [] -> [([b1], t1, f1)]
             | hd1::tl1 ->
                 let uu____52455 = hd1  in
                 (match uu____52455 with
                  | (b2s,t2,uu____52484) ->
                      (match (t1, t2) with
                       | (FStar_Pervasives_Native.Some
                          typ1,FStar_Pervasives_Native.Some typ2) ->
                           if typ1 = typ2
                           then ((FStar_List.append b2s [b1]), t1, f1) :: tl1
                           else ([b1], t1, f1) :: hd1 :: tl1
                       | uu____52594 -> ([b1], t1, f1) :: bs)))
         in
      let p_collapsed_binder cb =
        let uu____52655 = cb  in
        match uu____52655 with
        | (bs,t,f) ->
            (match t with
             | FStar_Pervasives_Native.None  ->
                 (match bs with
                  | b::[] -> b
                  | uu____52684 -> failwith "Impossible")
             | FStar_Pervasives_Native.Some typ ->
                 (match bs with
                  | [] -> failwith "Impossible"
                  | b::[] -> f b typ
                  | hd1::tl1 ->
                      let uu____52697 =
                        FStar_List.fold_left
                          (fun x  ->
                             fun y  ->
                               let uu____52703 =
                                 FStar_Pprint.op_Hat_Hat FStar_Pprint.space y
                                  in
                               FStar_Pprint.op_Hat_Hat x uu____52703) hd1 tl1
                         in
                      f uu____52697 typ))
         in
      let binders =
        let uu____52721 = accumulate_binders p_Tm e  in
        FStar_List.fold_left fold_fun [] uu____52721  in
      map_rev p_collapsed_binder binders

and (p_tmFormula : FStar_Parser_AST.term -> FStar_Pprint.document) =
  fun e  ->
    let conj =
      let uu____52784 =
        let uu____52785 = str "/\\"  in
        FStar_Pprint.op_Hat_Hat uu____52785 break1  in
      FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____52784  in
    let disj =
      let uu____52788 =
        let uu____52789 = str "\\/"  in
        FStar_Pprint.op_Hat_Hat uu____52789 break1  in
      FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____52788  in
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
        ({ FStar_Ident.idText = "\\/"; FStar_Ident.idRange = uu____52809;_},e1::e2::[])
        ->
        let uu____52815 = p_tmDisjunction e1  in
        let uu____52820 =
          let uu____52825 = p_tmConjunction e2  in [uu____52825]  in
        FStar_List.append uu____52815 uu____52820
    | uu____52834 -> let uu____52835 = p_tmConjunction e  in [uu____52835]

and (p_tmConjunction :
  FStar_Parser_AST.term -> FStar_Pprint.document Prims.list) =
  fun e  ->
    match e.FStar_Parser_AST.tm with
    | FStar_Parser_AST.Op
        ({ FStar_Ident.idText = "/\\"; FStar_Ident.idRange = uu____52845;_},e1::e2::[])
        ->
        let uu____52851 = p_tmConjunction e1  in
        let uu____52854 = let uu____52857 = p_tmTuple e2  in [uu____52857]
           in
        FStar_List.append uu____52851 uu____52854
    | uu____52858 -> let uu____52859 = p_tmTuple e  in [uu____52859]

and (p_tmTuple : FStar_Parser_AST.term -> FStar_Pprint.document) =
  fun e  -> with_comment p_tmTuple' e e.FStar_Parser_AST.range

and (p_tmTuple' : FStar_Parser_AST.term -> FStar_Pprint.document) =
  fun e  ->
    match e.FStar_Parser_AST.tm with
    | FStar_Parser_AST.Construct (lid,args) when
        (is_tuple_constructor lid) && (all_explicit args) ->
        let uu____52876 = FStar_Pprint.op_Hat_Hat FStar_Pprint.comma break1
           in
        FStar_Pprint.separate_map uu____52876
          (fun uu____52884  ->
             match uu____52884 with | (e1,uu____52890) -> p_tmEq e1) args
    | uu____52891 -> p_tmEq e

and (paren_if_gt :
  Prims.int -> Prims.int -> FStar_Pprint.document -> FStar_Pprint.document) =
  fun curr  ->
    fun mine  ->
      fun doc1  ->
        if mine <= curr
        then doc1
        else
          (let uu____52900 =
             let uu____52901 =
               FStar_Pprint.op_Hat_Hat doc1 FStar_Pprint.rparen  in
             FStar_Pprint.op_Hat_Hat FStar_Pprint.lparen uu____52901  in
           FStar_Pprint.group uu____52900)

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
               (let uu____52920 = FStar_Ident.text_of_id op  in
                uu____52920 = "="))
              ||
              (let uu____52925 = FStar_Ident.text_of_id op  in
               uu____52925 = "|>")
            ->
            let op1 = FStar_Ident.text_of_id op  in
            let uu____52931 = levels op1  in
            (match uu____52931 with
             | (left1,mine,right1) ->
                 let uu____52950 =
                   let uu____52951 = FStar_All.pipe_left str op1  in
                   let uu____52953 = p_tmEqWith' p_X left1 e1  in
                   let uu____52954 = p_tmEqWith' p_X right1 e2  in
                   infix0 uu____52951 uu____52953 uu____52954  in
                 paren_if_gt curr mine uu____52950)
        | FStar_Parser_AST.Op
            ({ FStar_Ident.idText = ":=";
               FStar_Ident.idRange = uu____52955;_},e1::e2::[])
            ->
            let uu____52961 =
              let uu____52962 = p_tmEqWith p_X e1  in
              let uu____52963 =
                let uu____52964 =
                  let uu____52965 =
                    let uu____52966 = p_tmEqWith p_X e2  in
                    op_Hat_Slash_Plus_Hat FStar_Pprint.equals uu____52966  in
                  FStar_Pprint.op_Hat_Hat FStar_Pprint.colon uu____52965  in
                FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____52964  in
              FStar_Pprint.op_Hat_Hat uu____52962 uu____52963  in
            FStar_Pprint.group uu____52961
        | FStar_Parser_AST.Op
            ({ FStar_Ident.idText = "-"; FStar_Ident.idRange = uu____52967;_},e1::[])
            ->
            let uu____52972 = levels "-"  in
            (match uu____52972 with
             | (left1,mine,right1) ->
                 let uu____52992 = p_tmEqWith' p_X mine e1  in
                 FStar_Pprint.op_Hat_Slash_Hat FStar_Pprint.minus uu____52992)
        | uu____52993 -> p_tmNoEqWith p_X e

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
              (lid,(e1,uu____53041)::(e2,uu____53043)::[]) when
              (FStar_Ident.lid_equals lid FStar_Parser_Const.cons_lid) &&
                (let uu____53063 = is_list e  in
                 Prims.op_Negation uu____53063)
              ->
              let op = "::"  in
              let uu____53068 = levels op  in
              (match uu____53068 with
               | (left1,mine,right1) ->
                   let uu____53087 =
                     let uu____53088 = str op  in
                     let uu____53089 = p_tmNoEqWith' false p_X left1 e1  in
                     let uu____53091 = p_tmNoEqWith' false p_X right1 e2  in
                     infix0 uu____53088 uu____53089 uu____53091  in
                   paren_if_gt curr mine uu____53087)
          | FStar_Parser_AST.Sum (binders,res) ->
              let op = "&"  in
              let uu____53110 = levels op  in
              (match uu____53110 with
               | (left1,mine,right1) ->
                   let p_dsumfst bt =
                     match bt with
                     | FStar_Util.Inl b ->
                         let uu____53144 = p_binder false b  in
                         let uu____53146 =
                           let uu____53147 =
                             let uu____53148 = str op  in
                             FStar_Pprint.op_Hat_Hat uu____53148 break1  in
                           FStar_Pprint.op_Hat_Hat FStar_Pprint.space
                             uu____53147
                            in
                         FStar_Pprint.op_Hat_Hat uu____53144 uu____53146
                     | FStar_Util.Inr t ->
                         let uu____53150 = p_tmNoEqWith' false p_X left1 t
                            in
                         let uu____53152 =
                           let uu____53153 =
                             let uu____53154 = str op  in
                             FStar_Pprint.op_Hat_Hat uu____53154 break1  in
                           FStar_Pprint.op_Hat_Hat FStar_Pprint.space
                             uu____53153
                            in
                         FStar_Pprint.op_Hat_Hat uu____53150 uu____53152
                      in
                   let uu____53155 =
                     let uu____53156 =
                       FStar_Pprint.concat_map p_dsumfst binders  in
                     let uu____53161 = p_tmNoEqWith' false p_X right1 res  in
                     FStar_Pprint.op_Hat_Hat uu____53156 uu____53161  in
                   paren_if_gt curr mine uu____53155)
          | FStar_Parser_AST.Op
              ({ FStar_Ident.idText = "*";
                 FStar_Ident.idRange = uu____53163;_},e1::e2::[])
              when FStar_ST.op_Bang unfold_tuples ->
              let op = "*"  in
              let uu____53193 = levels op  in
              (match uu____53193 with
               | (left1,mine,right1) ->
                   if inside_tuple
                   then
                     let uu____53213 = str op  in
                     let uu____53214 = p_tmNoEqWith' true p_X left1 e1  in
                     let uu____53216 = p_tmNoEqWith' true p_X right1 e2  in
                     infix0 uu____53213 uu____53214 uu____53216
                   else
                     (let uu____53220 =
                        let uu____53221 = str op  in
                        let uu____53222 = p_tmNoEqWith' true p_X left1 e1  in
                        let uu____53224 = p_tmNoEqWith' true p_X right1 e2
                           in
                        infix0 uu____53221 uu____53222 uu____53224  in
                      paren_if_gt curr mine uu____53220))
          | FStar_Parser_AST.Op (op,e1::e2::[]) when is_operatorInfix34 op ->
              let op1 = FStar_Ident.text_of_id op  in
              let uu____53233 = levels op1  in
              (match uu____53233 with
               | (left1,mine,right1) ->
                   let uu____53252 =
                     let uu____53253 = str op1  in
                     let uu____53254 = p_tmNoEqWith' false p_X left1 e1  in
                     let uu____53256 = p_tmNoEqWith' false p_X right1 e2  in
                     infix0 uu____53253 uu____53254 uu____53256  in
                   paren_if_gt curr mine uu____53252)
          | FStar_Parser_AST.Record (with_opt,record_fields) ->
              let uu____53276 =
                let uu____53277 =
                  default_or_map FStar_Pprint.empty p_with_clause with_opt
                   in
                let uu____53278 =
                  let uu____53279 =
                    FStar_Pprint.op_Hat_Hat FStar_Pprint.semi break1  in
                  separate_map_last uu____53279 p_simpleDef record_fields  in
                FStar_Pprint.op_Hat_Hat uu____53277 uu____53278  in
              braces_with_nesting uu____53276
          | FStar_Parser_AST.Op
              ({ FStar_Ident.idText = "~";
                 FStar_Ident.idRange = uu____53284;_},e1::[])
              ->
              let uu____53289 =
                let uu____53290 = str "~"  in
                let uu____53292 = p_atomicTerm e1  in
                FStar_Pprint.op_Hat_Hat uu____53290 uu____53292  in
              FStar_Pprint.group uu____53289
          | FStar_Parser_AST.Paren p when inside_tuple ->
              (match p.FStar_Parser_AST.tm with
               | FStar_Parser_AST.Op
                   ({ FStar_Ident.idText = "*";
                      FStar_Ident.idRange = uu____53294;_},e1::e2::[])
                   ->
                   let op = "*"  in
                   let uu____53303 = levels op  in
                   (match uu____53303 with
                    | (left1,mine,right1) ->
                        let uu____53322 =
                          let uu____53323 = str op  in
                          let uu____53324 = p_tmNoEqWith' true p_X left1 e1
                             in
                          let uu____53326 = p_tmNoEqWith' true p_X right1 e2
                             in
                          infix0 uu____53323 uu____53324 uu____53326  in
                        paren_if_gt curr mine uu____53322)
               | uu____53328 -> p_X e)
          | uu____53329 -> p_X e

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
        let uu____53336 =
          let uu____53337 = p_lident lid  in
          let uu____53338 =
            let uu____53339 = p_appTerm e1  in
            FStar_Pprint.op_Hat_Slash_Hat FStar_Pprint.colon uu____53339  in
          FStar_Pprint.op_Hat_Slash_Hat uu____53337 uu____53338  in
        FStar_Pprint.group uu____53336
    | FStar_Parser_AST.Refine (b,phi) -> p_refinedBinder b phi
    | uu____53342 -> p_appTerm e

and (p_with_clause : FStar_Parser_AST.term -> FStar_Pprint.document) =
  fun e  ->
    let uu____53344 = p_appTerm e  in
    let uu____53345 =
      let uu____53346 =
        let uu____53347 = str "with"  in
        FStar_Pprint.op_Hat_Hat uu____53347 break1  in
      FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____53346  in
    FStar_Pprint.op_Hat_Hat uu____53344 uu____53345

and (p_refinedBinder :
  FStar_Parser_AST.binder -> FStar_Parser_AST.term -> FStar_Pprint.document)
  =
  fun b  ->
    fun phi  ->
      match b.FStar_Parser_AST.b with
      | FStar_Parser_AST.Annotated (lid,t) ->
          let uu____53353 = p_lident lid  in
          p_refinement b.FStar_Parser_AST.aqual uu____53353 t phi
      | FStar_Parser_AST.TAnnotated uu____53354 ->
          failwith "Is this still used ?"
      | FStar_Parser_AST.Variable uu____53360 ->
          let uu____53361 =
            let uu____53363 = FStar_Parser_AST.binder_to_string b  in
            FStar_Util.format1
              "Imposible : a refined binder ought to be annotated %s"
              uu____53363
             in
          failwith uu____53361
      | FStar_Parser_AST.TVariable uu____53366 ->
          let uu____53367 =
            let uu____53369 = FStar_Parser_AST.binder_to_string b  in
            FStar_Util.format1
              "Imposible : a refined binder ought to be annotated %s"
              uu____53369
             in
          failwith uu____53367
      | FStar_Parser_AST.NoName uu____53372 ->
          let uu____53373 =
            let uu____53375 = FStar_Parser_AST.binder_to_string b  in
            FStar_Util.format1
              "Imposible : a refined binder ought to be annotated %s"
              uu____53375
             in
          failwith uu____53373

and (p_simpleDef :
  Prims.bool ->
    (FStar_Ident.lid * FStar_Parser_AST.term) -> FStar_Pprint.document)
  =
  fun ps  ->
    fun uu____53379  ->
      match uu____53379 with
      | (lid,e) ->
          let uu____53387 =
            let uu____53388 = p_qlident lid  in
            let uu____53389 =
              let uu____53390 = p_noSeqTermAndComment ps false e  in
              FStar_Pprint.op_Hat_Slash_Hat FStar_Pprint.equals uu____53390
               in
            FStar_Pprint.op_Hat_Slash_Hat uu____53388 uu____53389  in
          FStar_Pprint.group uu____53387

and (p_appTerm : FStar_Parser_AST.term -> FStar_Pprint.document) =
  fun e  ->
    match e.FStar_Parser_AST.tm with
    | FStar_Parser_AST.App uu____53393 when is_general_application e ->
        let uu____53400 = head_and_args e  in
        (match uu____53400 with
         | (head1,args) ->
             (match args with
              | e1::e2::[] when
                  (FStar_Pervasives_Native.snd e1) = FStar_Parser_AST.Infix
                  ->
                  let uu____53447 = p_argTerm e1  in
                  let uu____53448 =
                    let uu____53449 =
                      let uu____53450 =
                        let uu____53451 = str "`"  in
                        let uu____53453 =
                          let uu____53454 = p_indexingTerm head1  in
                          let uu____53455 = str "`"  in
                          FStar_Pprint.op_Hat_Hat uu____53454 uu____53455  in
                        FStar_Pprint.op_Hat_Hat uu____53451 uu____53453  in
                      FStar_Pprint.group uu____53450  in
                    let uu____53457 = p_argTerm e2  in
                    FStar_Pprint.op_Hat_Slash_Hat uu____53449 uu____53457  in
                  FStar_Pprint.op_Hat_Slash_Hat uu____53447 uu____53448
              | uu____53458 ->
                  let uu____53465 =
                    let uu____53476 =
                      FStar_ST.op_Bang should_print_fs_typ_app  in
                    if uu____53476
                    then
                      let uu____53510 =
                        FStar_Util.take
                          (fun uu____53534  ->
                             match uu____53534 with
                             | (uu____53540,aq) ->
                                 aq = FStar_Parser_AST.FsTypApp) args
                         in
                      match uu____53510 with
                      | (fs_typ_args,args1) ->
                          let uu____53578 =
                            let uu____53579 = p_indexingTerm head1  in
                            let uu____53580 =
                              let uu____53581 =
                                FStar_Pprint.op_Hat_Hat FStar_Pprint.comma
                                  break1
                                 in
                              soft_surround_map_or_flow (Prims.parse_int "2")
                                (Prims.parse_int "0") FStar_Pprint.empty
                                FStar_Pprint.langle uu____53581
                                FStar_Pprint.rangle p_fsTypArg fs_typ_args
                               in
                            FStar_Pprint.op_Hat_Hat uu____53579 uu____53580
                             in
                          (uu____53578, args1)
                    else
                      (let uu____53596 = p_indexingTerm head1  in
                       (uu____53596, args))
                     in
                  (match uu____53465 with
                   | (head_doc,args1) ->
                       let uu____53617 =
                         let uu____53618 =
                           FStar_Pprint.op_Hat_Hat head_doc
                             FStar_Pprint.space
                            in
                         soft_surround_map_or_flow (Prims.parse_int "2")
                           (Prims.parse_int "0") head_doc uu____53618 break1
                           FStar_Pprint.empty p_argTerm args1
                          in
                       FStar_Pprint.group uu____53617)))
    | FStar_Parser_AST.Construct (lid,args) when
        (is_general_construction e) &&
          (let uu____53640 = is_dtuple_constructor lid  in
           Prims.op_Negation uu____53640)
        ->
        (match args with
         | [] -> p_quident lid
         | arg::[] ->
             let uu____53659 =
               let uu____53660 = p_quident lid  in
               let uu____53661 = p_argTerm arg  in
               FStar_Pprint.op_Hat_Slash_Hat uu____53660 uu____53661  in
             FStar_Pprint.group uu____53659
         | hd1::tl1 ->
             let uu____53678 =
               let uu____53679 =
                 let uu____53680 =
                   let uu____53681 = p_quident lid  in
                   let uu____53682 = p_argTerm hd1  in
                   prefix2 uu____53681 uu____53682  in
                 FStar_Pprint.group uu____53680  in
               let uu____53683 =
                 let uu____53684 =
                   FStar_Pprint.separate_map break1 p_argTerm tl1  in
                 jump2 uu____53684  in
               FStar_Pprint.op_Hat_Hat uu____53679 uu____53683  in
             FStar_Pprint.group uu____53678)
    | uu____53689 -> p_indexingTerm e

and (p_argTerm :
  (FStar_Parser_AST.term * FStar_Parser_AST.imp) -> FStar_Pprint.document) =
  fun arg_imp  ->
    match arg_imp with
    | (u,FStar_Parser_AST.UnivApp ) -> p_universe u
    | (e,FStar_Parser_AST.FsTypApp ) ->
        (FStar_Errors.log_issue e.FStar_Parser_AST.range
           (FStar_Errors.Warning_UnexpectedFsTypApp,
             "Unexpected FsTypApp, output might not be formatted correctly.");
         (let uu____53700 = p_indexingTerm e  in
          FStar_Pprint.surround (Prims.parse_int "2") (Prims.parse_int "1")
            FStar_Pprint.langle uu____53700 FStar_Pprint.rangle))
    | (e,FStar_Parser_AST.Hash ) ->
        let uu____53704 = str "#"  in
        let uu____53706 = p_indexingTerm e  in
        FStar_Pprint.op_Hat_Hat uu____53704 uu____53706
    | (e,FStar_Parser_AST.HashBrace t) ->
        let uu____53709 = str "#["  in
        let uu____53711 =
          let uu____53712 = p_indexingTerm t  in
          let uu____53713 =
            let uu____53714 = str "]"  in
            let uu____53716 = p_indexingTerm e  in
            FStar_Pprint.op_Hat_Hat uu____53714 uu____53716  in
          FStar_Pprint.op_Hat_Hat uu____53712 uu____53713  in
        FStar_Pprint.op_Hat_Hat uu____53709 uu____53711
    | (e,FStar_Parser_AST.Infix ) -> p_indexingTerm e
    | (e,FStar_Parser_AST.Nothing ) -> p_indexingTerm e

and (p_fsTypArg :
  (FStar_Parser_AST.term * FStar_Parser_AST.imp) -> FStar_Pprint.document) =
  fun uu____53719  ->
    match uu____53719 with | (e,uu____53725) -> p_indexingTerm e

and (p_indexingTerm_aux :
  (FStar_Parser_AST.term -> FStar_Pprint.document) ->
    FStar_Parser_AST.term -> FStar_Pprint.document)
  =
  fun exit1  ->
    fun e  ->
      match e.FStar_Parser_AST.tm with
      | FStar_Parser_AST.Op
          ({ FStar_Ident.idText = ".()"; FStar_Ident.idRange = uu____53730;_},e1::e2::[])
          ->
          let uu____53736 =
            let uu____53737 = p_indexingTerm_aux p_atomicTermNotQUident e1
               in
            let uu____53738 =
              let uu____53739 =
                let uu____53740 = p_term false false e2  in
                soft_parens_with_nesting uu____53740  in
              FStar_Pprint.op_Hat_Hat FStar_Pprint.dot uu____53739  in
            FStar_Pprint.op_Hat_Hat uu____53737 uu____53738  in
          FStar_Pprint.group uu____53736
      | FStar_Parser_AST.Op
          ({ FStar_Ident.idText = ".[]"; FStar_Ident.idRange = uu____53743;_},e1::e2::[])
          ->
          let uu____53749 =
            let uu____53750 = p_indexingTerm_aux p_atomicTermNotQUident e1
               in
            let uu____53751 =
              let uu____53752 =
                let uu____53753 = p_term false false e2  in
                soft_brackets_with_nesting uu____53753  in
              FStar_Pprint.op_Hat_Hat FStar_Pprint.dot uu____53752  in
            FStar_Pprint.op_Hat_Hat uu____53750 uu____53751  in
          FStar_Pprint.group uu____53749
      | uu____53756 -> exit1 e

and (p_indexingTerm : FStar_Parser_AST.term -> FStar_Pprint.document) =
  fun e  -> p_indexingTerm_aux p_atomicTerm e

and (p_atomicTerm : FStar_Parser_AST.term -> FStar_Pprint.document) =
  fun e  ->
    match e.FStar_Parser_AST.tm with
    | FStar_Parser_AST.LetOpen (lid,e1) ->
        let uu____53761 = p_quident lid  in
        let uu____53762 =
          let uu____53763 =
            let uu____53764 = p_term false false e1  in
            soft_parens_with_nesting uu____53764  in
          FStar_Pprint.op_Hat_Hat FStar_Pprint.dot uu____53763  in
        FStar_Pprint.op_Hat_Hat uu____53761 uu____53762
    | FStar_Parser_AST.Name lid -> p_quident lid
    | FStar_Parser_AST.Op (op,e1::[]) when is_general_prefix_op op ->
        let uu____53772 =
          let uu____53773 = FStar_Ident.text_of_id op  in str uu____53773  in
        let uu____53775 = p_atomicTerm e1  in
        FStar_Pprint.op_Hat_Hat uu____53772 uu____53775
    | uu____53776 -> p_atomicTermNotQUident e

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
         | uu____53789 -> p_constant c)
    | FStar_Parser_AST.Name lid when
        FStar_Ident.lid_equals lid FStar_Parser_Const.true_lid -> str "True"
    | FStar_Parser_AST.Name lid when
        FStar_Ident.lid_equals lid FStar_Parser_Const.false_lid ->
        str "False"
    | FStar_Parser_AST.Op (op,e1::[]) when is_general_prefix_op op ->
        let uu____53798 =
          let uu____53799 = FStar_Ident.text_of_id op  in str uu____53799  in
        let uu____53801 = p_atomicTermNotQUident e1  in
        FStar_Pprint.op_Hat_Hat uu____53798 uu____53801
    | FStar_Parser_AST.Op (op,[]) ->
        let uu____53805 =
          let uu____53806 =
            let uu____53807 =
              let uu____53808 = FStar_Ident.text_of_id op  in str uu____53808
               in
            let uu____53810 =
              FStar_Pprint.op_Hat_Hat FStar_Pprint.space FStar_Pprint.rparen
               in
            FStar_Pprint.op_Hat_Hat uu____53807 uu____53810  in
          FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____53806  in
        FStar_Pprint.op_Hat_Hat FStar_Pprint.lparen uu____53805
    | FStar_Parser_AST.Construct (lid,args) when is_dtuple_constructor lid ->
        let uu____53825 = all_explicit args  in
        if uu____53825
        then
          let uu____53828 =
            FStar_Pprint.op_Hat_Hat FStar_Pprint.lparen FStar_Pprint.bar  in
          let uu____53829 =
            let uu____53830 =
              FStar_Pprint.op_Hat_Hat FStar_Pprint.comma break1  in
            let uu____53831 = FStar_List.map FStar_Pervasives_Native.fst args
               in
            FStar_Pprint.separate_map uu____53830 p_tmEq uu____53831  in
          let uu____53838 =
            FStar_Pprint.op_Hat_Hat FStar_Pprint.bar FStar_Pprint.rparen  in
          FStar_Pprint.surround (Prims.parse_int "2") (Prims.parse_int "1")
            uu____53828 uu____53829 uu____53838
        else
          (match args with
           | [] -> p_quident lid
           | arg::[] ->
               let uu____53860 =
                 let uu____53861 = p_quident lid  in
                 let uu____53862 = p_argTerm arg  in
                 FStar_Pprint.op_Hat_Slash_Hat uu____53861 uu____53862  in
               FStar_Pprint.group uu____53860
           | hd1::tl1 ->
               let uu____53879 =
                 let uu____53880 =
                   let uu____53881 =
                     let uu____53882 = p_quident lid  in
                     let uu____53883 = p_argTerm hd1  in
                     prefix2 uu____53882 uu____53883  in
                   FStar_Pprint.group uu____53881  in
                 let uu____53884 =
                   let uu____53885 =
                     FStar_Pprint.separate_map break1 p_argTerm tl1  in
                   jump2 uu____53885  in
                 FStar_Pprint.op_Hat_Hat uu____53880 uu____53884  in
               FStar_Pprint.group uu____53879)
    | FStar_Parser_AST.Project (e1,lid) ->
        let uu____53892 =
          let uu____53893 = p_atomicTermNotQUident e1  in
          let uu____53894 =
            let uu____53895 = p_qlident lid  in
            FStar_Pprint.op_Hat_Hat FStar_Pprint.dot uu____53895  in
          FStar_Pprint.prefix (Prims.parse_int "2") (Prims.parse_int "0")
            uu____53893 uu____53894
           in
        FStar_Pprint.group uu____53892
    | uu____53898 -> p_projectionLHS e

and (p_projectionLHS : FStar_Parser_AST.term -> FStar_Pprint.document) =
  fun e  ->
    match e.FStar_Parser_AST.tm with
    | FStar_Parser_AST.Var lid -> p_qlident lid
    | FStar_Parser_AST.Projector (constr_lid,field_lid) ->
        let uu____53903 = p_quident constr_lid  in
        let uu____53904 =
          let uu____53905 =
            let uu____53906 = p_lident field_lid  in
            FStar_Pprint.op_Hat_Hat FStar_Pprint.dot uu____53906  in
          FStar_Pprint.op_Hat_Hat FStar_Pprint.qmark uu____53905  in
        FStar_Pprint.op_Hat_Hat uu____53903 uu____53904
    | FStar_Parser_AST.Discrim constr_lid ->
        let uu____53908 = p_quident constr_lid  in
        FStar_Pprint.op_Hat_Hat uu____53908 FStar_Pprint.qmark
    | FStar_Parser_AST.Paren e1 ->
        let uu____53910 = p_term_sep false false e1  in
        (match uu____53910 with
         | (comm,t) ->
             let doc1 = soft_parens_with_nesting t  in
             if comm = FStar_Pprint.empty
             then doc1
             else
               (let uu____53923 =
                  FStar_Pprint.op_Hat_Hat FStar_Pprint.hardline doc1  in
                FStar_Pprint.op_Hat_Hat comm uu____53923))
    | uu____53924 when is_array e ->
        let es = extract_from_list e  in
        let uu____53928 =
          FStar_Pprint.op_Hat_Hat FStar_Pprint.lbracket FStar_Pprint.bar  in
        let uu____53929 =
          let uu____53930 = FStar_Pprint.op_Hat_Hat FStar_Pprint.semi break1
             in
          separate_map_or_flow_last uu____53930
            (fun ps  -> p_noSeqTermAndComment ps false) es
           in
        let uu____53935 =
          FStar_Pprint.op_Hat_Hat FStar_Pprint.bar FStar_Pprint.rbracket  in
        FStar_Pprint.surround (Prims.parse_int "2") (Prims.parse_int "0")
          uu____53928 uu____53929 uu____53935
    | uu____53938 when is_list e ->
        let uu____53939 =
          let uu____53940 = FStar_Pprint.op_Hat_Hat FStar_Pprint.semi break1
             in
          let uu____53941 = extract_from_list e  in
          separate_map_or_flow_last uu____53940
            (fun ps  -> p_noSeqTermAndComment ps false) uu____53941
           in
        FStar_Pprint.surround (Prims.parse_int "2") (Prims.parse_int "0")
          FStar_Pprint.lbracket uu____53939 FStar_Pprint.rbracket
    | uu____53950 when is_lex_list e ->
        let uu____53951 =
          FStar_Pprint.op_Hat_Hat FStar_Pprint.percent FStar_Pprint.lbracket
           in
        let uu____53952 =
          let uu____53953 = FStar_Pprint.op_Hat_Hat FStar_Pprint.semi break1
             in
          let uu____53954 = extract_from_list e  in
          separate_map_or_flow_last uu____53953
            (fun ps  -> p_noSeqTermAndComment ps false) uu____53954
           in
        FStar_Pprint.surround (Prims.parse_int "2") (Prims.parse_int "1")
          uu____53951 uu____53952 FStar_Pprint.rbracket
    | uu____53963 when is_ref_set e ->
        let es = extract_from_ref_set e  in
        let uu____53967 =
          FStar_Pprint.op_Hat_Hat FStar_Pprint.bang FStar_Pprint.lbrace  in
        let uu____53968 =
          let uu____53969 = FStar_Pprint.op_Hat_Hat FStar_Pprint.comma break1
             in
          separate_map_or_flow uu____53969 p_appTerm es  in
        FStar_Pprint.surround (Prims.parse_int "2") (Prims.parse_int "0")
          uu____53967 uu____53968 FStar_Pprint.rbrace
    | FStar_Parser_AST.Labeled (e1,s,b) ->
        let uu____53979 = str (Prims.op_Hat "(*" (Prims.op_Hat s "*)"))  in
        let uu____53982 = p_term false false e1  in
        FStar_Pprint.op_Hat_Slash_Hat uu____53979 uu____53982
    | FStar_Parser_AST.Op (op,args) when
        let uu____53991 = handleable_op op args  in
        Prims.op_Negation uu____53991 ->
        let uu____53993 =
          let uu____53995 =
            let uu____53997 = FStar_Ident.text_of_id op  in
            let uu____53999 =
              let uu____54001 =
                let uu____54003 =
                  FStar_Util.string_of_int (FStar_List.length args)  in
                Prims.op_Hat uu____54003
                  " arguments couldn't be handled by the pretty printer"
                 in
              Prims.op_Hat " with " uu____54001  in
            Prims.op_Hat uu____53997 uu____53999  in
          Prims.op_Hat "Operation " uu____53995  in
        failwith uu____53993
    | FStar_Parser_AST.Uvar id1 ->
        failwith "Unexpected universe variable out of universe context"
    | FStar_Parser_AST.Wild  ->
        let uu____54010 = p_term false false e  in
        soft_parens_with_nesting uu____54010
    | FStar_Parser_AST.Const uu____54013 ->
        let uu____54014 = p_term false false e  in
        soft_parens_with_nesting uu____54014
    | FStar_Parser_AST.Op uu____54017 ->
        let uu____54024 = p_term false false e  in
        soft_parens_with_nesting uu____54024
    | FStar_Parser_AST.Tvar uu____54027 ->
        let uu____54028 = p_term false false e  in
        soft_parens_with_nesting uu____54028
    | FStar_Parser_AST.Var uu____54031 ->
        let uu____54032 = p_term false false e  in
        soft_parens_with_nesting uu____54032
    | FStar_Parser_AST.Name uu____54035 ->
        let uu____54036 = p_term false false e  in
        soft_parens_with_nesting uu____54036
    | FStar_Parser_AST.Construct uu____54039 ->
        let uu____54050 = p_term false false e  in
        soft_parens_with_nesting uu____54050
    | FStar_Parser_AST.Abs uu____54053 ->
        let uu____54060 = p_term false false e  in
        soft_parens_with_nesting uu____54060
    | FStar_Parser_AST.App uu____54063 ->
        let uu____54070 = p_term false false e  in
        soft_parens_with_nesting uu____54070
    | FStar_Parser_AST.Let uu____54073 ->
        let uu____54094 = p_term false false e  in
        soft_parens_with_nesting uu____54094
    | FStar_Parser_AST.LetOpen uu____54097 ->
        let uu____54102 = p_term false false e  in
        soft_parens_with_nesting uu____54102
    | FStar_Parser_AST.Seq uu____54105 ->
        let uu____54110 = p_term false false e  in
        soft_parens_with_nesting uu____54110
    | FStar_Parser_AST.Bind uu____54113 ->
        let uu____54120 = p_term false false e  in
        soft_parens_with_nesting uu____54120
    | FStar_Parser_AST.If uu____54123 ->
        let uu____54130 = p_term false false e  in
        soft_parens_with_nesting uu____54130
    | FStar_Parser_AST.Match uu____54133 ->
        let uu____54148 = p_term false false e  in
        soft_parens_with_nesting uu____54148
    | FStar_Parser_AST.TryWith uu____54151 ->
        let uu____54166 = p_term false false e  in
        soft_parens_with_nesting uu____54166
    | FStar_Parser_AST.Ascribed uu____54169 ->
        let uu____54178 = p_term false false e  in
        soft_parens_with_nesting uu____54178
    | FStar_Parser_AST.Record uu____54181 ->
        let uu____54194 = p_term false false e  in
        soft_parens_with_nesting uu____54194
    | FStar_Parser_AST.Project uu____54197 ->
        let uu____54202 = p_term false false e  in
        soft_parens_with_nesting uu____54202
    | FStar_Parser_AST.Product uu____54205 ->
        let uu____54212 = p_term false false e  in
        soft_parens_with_nesting uu____54212
    | FStar_Parser_AST.Sum uu____54215 ->
        let uu____54226 = p_term false false e  in
        soft_parens_with_nesting uu____54226
    | FStar_Parser_AST.QForall uu____54229 ->
        let uu____54242 = p_term false false e  in
        soft_parens_with_nesting uu____54242
    | FStar_Parser_AST.QExists uu____54245 ->
        let uu____54258 = p_term false false e  in
        soft_parens_with_nesting uu____54258
    | FStar_Parser_AST.Refine uu____54261 ->
        let uu____54266 = p_term false false e  in
        soft_parens_with_nesting uu____54266
    | FStar_Parser_AST.NamedTyp uu____54269 ->
        let uu____54274 = p_term false false e  in
        soft_parens_with_nesting uu____54274
    | FStar_Parser_AST.Requires uu____54277 ->
        let uu____54285 = p_term false false e  in
        soft_parens_with_nesting uu____54285
    | FStar_Parser_AST.Ensures uu____54288 ->
        let uu____54296 = p_term false false e  in
        soft_parens_with_nesting uu____54296
    | FStar_Parser_AST.Attributes uu____54299 ->
        let uu____54302 = p_term false false e  in
        soft_parens_with_nesting uu____54302
    | FStar_Parser_AST.Quote uu____54305 ->
        let uu____54310 = p_term false false e  in
        soft_parens_with_nesting uu____54310
    | FStar_Parser_AST.VQuote uu____54313 ->
        let uu____54314 = p_term false false e  in
        soft_parens_with_nesting uu____54314
    | FStar_Parser_AST.Antiquote uu____54317 ->
        let uu____54318 = p_term false false e  in
        soft_parens_with_nesting uu____54318
    | FStar_Parser_AST.CalcProof uu____54321 ->
        let uu____54330 = p_term false false e  in
        soft_parens_with_nesting uu____54330

and (p_constant : FStar_Const.sconst -> FStar_Pprint.document) =
  fun uu___339_54333  ->
    match uu___339_54333 with
    | FStar_Const.Const_effect  -> str "Effect"
    | FStar_Const.Const_unit  -> str "()"
    | FStar_Const.Const_bool b -> FStar_Pprint.doc_of_bool b
    | FStar_Const.Const_real r -> str (Prims.op_Hat r "R")
    | FStar_Const.Const_float x -> str (FStar_Util.string_of_float x)
    | FStar_Const.Const_char x -> FStar_Pprint.doc_of_char x
    | FStar_Const.Const_string (s,uu____54345) ->
        let uu____54348 = str (FStar_String.escaped s)  in
        FStar_Pprint.dquotes uu____54348
    | FStar_Const.Const_bytearray (bytes,uu____54350) ->
        let uu____54355 =
          let uu____54356 = str (FStar_Util.string_of_bytes bytes)  in
          FStar_Pprint.dquotes uu____54356  in
        let uu____54357 = str "B"  in
        FStar_Pprint.op_Hat_Hat uu____54355 uu____54357
    | FStar_Const.Const_int (repr,sign_width_opt) ->
        let signedness uu___337_54380 =
          match uu___337_54380 with
          | FStar_Const.Unsigned  -> str "u"
          | FStar_Const.Signed  -> FStar_Pprint.empty  in
        let width uu___338_54387 =
          match uu___338_54387 with
          | FStar_Const.Int8  -> str "y"
          | FStar_Const.Int16  -> str "s"
          | FStar_Const.Int32  -> str "l"
          | FStar_Const.Int64  -> str "L"  in
        let ending =
          default_or_map FStar_Pprint.empty
            (fun uu____54402  ->
               match uu____54402 with
               | (s,w) ->
                   let uu____54409 = signedness s  in
                   let uu____54410 = width w  in
                   FStar_Pprint.op_Hat_Hat uu____54409 uu____54410)
            sign_width_opt
           in
        let uu____54411 = str repr  in
        FStar_Pprint.op_Hat_Hat uu____54411 ending
    | FStar_Const.Const_range_of  -> str "range_of"
    | FStar_Const.Const_set_range_of  -> str "set_range_of"
    | FStar_Const.Const_range r ->
        let uu____54415 = FStar_Range.string_of_range r  in str uu____54415
    | FStar_Const.Const_reify  -> str "reify"
    | FStar_Const.Const_reflect lid ->
        let uu____54419 = p_quident lid  in
        let uu____54420 =
          let uu____54421 =
            let uu____54422 = str "reflect"  in
            FStar_Pprint.op_Hat_Hat FStar_Pprint.dot uu____54422  in
          FStar_Pprint.op_Hat_Hat FStar_Pprint.qmark uu____54421  in
        FStar_Pprint.op_Hat_Hat uu____54419 uu____54420

and (p_universe : FStar_Parser_AST.term -> FStar_Pprint.document) =
  fun u  ->
    let uu____54425 = str "u#"  in
    let uu____54427 = p_atomicUniverse u  in
    FStar_Pprint.op_Hat_Hat uu____54425 uu____54427

and (p_universeFrom : FStar_Parser_AST.term -> FStar_Pprint.document) =
  fun u  ->
    match u.FStar_Parser_AST.tm with
    | FStar_Parser_AST.Op
        ({ FStar_Ident.idText = "+"; FStar_Ident.idRange = uu____54429;_},u1::u2::[])
        ->
        let uu____54435 =
          let uu____54436 = p_universeFrom u1  in
          let uu____54437 =
            let uu____54438 = p_universeFrom u2  in
            FStar_Pprint.op_Hat_Slash_Hat FStar_Pprint.plus uu____54438  in
          FStar_Pprint.op_Hat_Slash_Hat uu____54436 uu____54437  in
        FStar_Pprint.group uu____54435
    | FStar_Parser_AST.App uu____54439 ->
        let uu____54446 = head_and_args u  in
        (match uu____54446 with
         | (head1,args) ->
             (match head1.FStar_Parser_AST.tm with
              | FStar_Parser_AST.Var maybe_max_lid when
                  FStar_Ident.lid_equals maybe_max_lid
                    FStar_Parser_Const.max_lid
                  ->
                  let uu____54472 =
                    let uu____54473 = p_qlident FStar_Parser_Const.max_lid
                       in
                    let uu____54474 =
                      FStar_Pprint.separate_map FStar_Pprint.space
                        (fun uu____54482  ->
                           match uu____54482 with
                           | (u1,uu____54488) -> p_atomicUniverse u1) args
                       in
                    op_Hat_Slash_Plus_Hat uu____54473 uu____54474  in
                  FStar_Pprint.group uu____54472
              | uu____54489 ->
                  let uu____54490 =
                    let uu____54492 = FStar_Parser_AST.term_to_string u  in
                    FStar_Util.format1 "Invalid term in universe context %s"
                      uu____54492
                     in
                  failwith uu____54490))
    | uu____54495 -> p_atomicUniverse u

and (p_atomicUniverse : FStar_Parser_AST.term -> FStar_Pprint.document) =
  fun u  ->
    match u.FStar_Parser_AST.tm with
    | FStar_Parser_AST.Wild  -> FStar_Pprint.underscore
    | FStar_Parser_AST.Const (FStar_Const.Const_int (r,sw)) ->
        p_constant (FStar_Const.Const_int (r, sw))
    | FStar_Parser_AST.Uvar id1 ->
        let uu____54521 = FStar_Ident.text_of_id id1  in str uu____54521
    | FStar_Parser_AST.Paren u1 ->
        let uu____54524 = p_universeFrom u1  in
        soft_parens_with_nesting uu____54524
    | FStar_Parser_AST.Op
        ({ FStar_Ident.idText = "+"; FStar_Ident.idRange = uu____54525;_},uu____54526::uu____54527::[])
        ->
        let uu____54531 = p_universeFrom u  in
        soft_parens_with_nesting uu____54531
    | FStar_Parser_AST.App uu____54532 ->
        let uu____54539 = p_universeFrom u  in
        soft_parens_with_nesting uu____54539
    | uu____54540 ->
        let uu____54541 =
          let uu____54543 = FStar_Parser_AST.term_to_string u  in
          FStar_Util.format1 "Invalid term in universe context %s"
            uu____54543
           in
        failwith uu____54541

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
       | FStar_Parser_AST.Module (uu____54632,decls) ->
           let uu____54638 =
             FStar_All.pipe_right decls (FStar_List.map decl_to_document)  in
           FStar_All.pipe_right uu____54638
             (FStar_Pprint.separate FStar_Pprint.hardline)
       | FStar_Parser_AST.Interface (uu____54647,decls,uu____54649) ->
           let uu____54656 =
             FStar_All.pipe_right decls (FStar_List.map decl_to_document)  in
           FStar_All.pipe_right uu____54656
             (FStar_Pprint.separate FStar_Pprint.hardline)
        in
     FStar_ST.op_Colon_Equals should_print_fs_typ_app false; res)
  
let (comments_to_document :
  (Prims.string * FStar_Range.range) Prims.list -> FStar_Pprint.document) =
  fun comments  ->
    FStar_Pprint.separate_map FStar_Pprint.hardline
      (fun uu____54716  ->
         match uu____54716 with | (comment,range) -> str comment) comments
  
let (extract_decl_range : FStar_Parser_AST.decl -> decl_meta) =
  fun d  ->
    let has_qs =
      match ((d.FStar_Parser_AST.quals), (d.FStar_Parser_AST.d)) with
      | ((FStar_Parser_AST.Assumption )::[],FStar_Parser_AST.Assume
         (id1,uu____54738)) -> false
      | ([],uu____54742) -> false
      | uu____54746 -> true  in
    {
      r = (d.FStar_Parser_AST.drange);
      has_qs;
      has_attrs =
        (Prims.op_Negation (FStar_List.isEmpty d.FStar_Parser_AST.attrs));
      has_fsdoc = (FStar_Util.is_some d.FStar_Parser_AST.doc);
      is_fsdoc =
        (match d.FStar_Parser_AST.d with
         | FStar_Parser_AST.Fsdoc uu____54756 -> true
         | uu____54758 -> false)
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
        | FStar_Parser_AST.Module (uu____54801,decls) -> decls
        | FStar_Parser_AST.Interface (uu____54807,decls,uu____54809) -> decls
         in
      FStar_ST.op_Colon_Equals should_print_fs_typ_app false;
      (match decls with
       | [] -> (FStar_Pprint.empty, comments)
       | d::ds ->
           let uu____54861 =
             match ds with
             | {
                 FStar_Parser_AST.d = FStar_Parser_AST.Pragma
                   (FStar_Parser_AST.LightOff );
                 FStar_Parser_AST.drange = uu____54874;
                 FStar_Parser_AST.doc = uu____54875;
                 FStar_Parser_AST.quals = uu____54876;
                 FStar_Parser_AST.attrs = uu____54877;_}::uu____54878 ->
                 let d0 = FStar_List.hd ds  in
                 let uu____54884 =
                   let uu____54887 =
                     let uu____54890 = FStar_List.tl ds  in d :: uu____54890
                      in
                   d0 :: uu____54887  in
                 (uu____54884, (d0.FStar_Parser_AST.drange))
             | uu____54895 -> ((d :: ds), (d.FStar_Parser_AST.drange))  in
           (match uu____54861 with
            | (decls1,first_range) ->
                (FStar_ST.op_Colon_Equals comment_stack comments;
                 (let initial_comment =
                    let uu____54952 = FStar_Range.start_of_range first_range
                       in
                    place_comments_until_pos (Prims.parse_int "0")
                      (Prims.parse_int "1") uu____54952 dummy_meta
                      FStar_Pprint.empty false true
                     in
                  let doc1 =
                    separate_map_with_comments FStar_Pprint.empty
                      FStar_Pprint.empty p_decl decls1 extract_decl_range
                     in
                  let comments1 = FStar_ST.op_Bang comment_stack  in
                  FStar_ST.op_Colon_Equals comment_stack [];
                  FStar_ST.op_Colon_Equals should_print_fs_typ_app false;
                  (let uu____55061 =
                     FStar_Pprint.op_Hat_Hat initial_comment doc1  in
                   (uu____55061, comments1))))))
  