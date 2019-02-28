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
            let uu____43264 = let uu____43267 = f x  in uu____43267 :: acc
               in
            aux xs uu____43264
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
            let uu____43334 = f x  in
            (match uu____43334 with
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
          let uu____43390 = f x  in if uu____43390 then all f xs else false
  
let (all_explicit :
  (FStar_Parser_AST.term * FStar_Parser_AST.imp) Prims.list -> Prims.bool) =
  fun args  ->
    FStar_Util.for_all
      (fun uu___324_43423  ->
         match uu___324_43423 with
         | (uu____43429,FStar_Parser_AST.Nothing ) -> true
         | uu____43431 -> false) args
  
let (should_print_fs_typ_app : Prims.bool FStar_ST.ref) =
  FStar_Util.mk_ref false 
let (unfold_tuples : Prims.bool FStar_ST.ref) = FStar_Util.mk_ref true 
let with_fs_typ_app :
  'Auu____43482 'Auu____43483 .
    Prims.bool ->
      ('Auu____43482 -> 'Auu____43483) -> 'Auu____43482 -> 'Auu____43483
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
  'Auu____43593 'Auu____43594 .
    'Auu____43593 ->
      ('Auu____43594 -> 'Auu____43593) ->
        'Auu____43594 FStar_Pervasives_Native.option -> 'Auu____43593
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
  'Auu____43707 .
    FStar_Pprint.document ->
      ('Auu____43707 -> FStar_Pprint.document) ->
        'Auu____43707 Prims.list -> FStar_Pprint.document
  =
  fun sep  ->
    fun f  ->
      fun l  ->
        let uu____43732 =
          let uu____43733 =
            let uu____43734 = FStar_Pprint.op_Hat_Hat sep break1  in
            FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____43734  in
          FStar_Pprint.separate_map uu____43733 f l  in
        FStar_Pprint.group uu____43732
  
let precede_break_separate_map :
  'Auu____43746 .
    FStar_Pprint.document ->
      FStar_Pprint.document ->
        ('Auu____43746 -> FStar_Pprint.document) ->
          'Auu____43746 Prims.list -> FStar_Pprint.document
  =
  fun prec  ->
    fun sep  ->
      fun f  ->
        fun l  ->
          let uu____43776 =
            let uu____43777 = FStar_Pprint.op_Hat_Hat prec FStar_Pprint.space
               in
            let uu____43778 =
              let uu____43779 = FStar_List.hd l  in
              FStar_All.pipe_right uu____43779 f  in
            FStar_Pprint.precede uu____43777 uu____43778  in
          let uu____43780 =
            let uu____43781 = FStar_List.tl l  in
            FStar_Pprint.concat_map
              (fun x  ->
                 let uu____43787 =
                   let uu____43788 =
                     let uu____43789 = f x  in
                     FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____43789
                      in
                   FStar_Pprint.op_Hat_Hat sep uu____43788  in
                 FStar_Pprint.op_Hat_Hat break1 uu____43787) uu____43781
             in
          FStar_Pprint.op_Hat_Hat uu____43776 uu____43780
  
let concat_break_map :
  'Auu____43797 .
    ('Auu____43797 -> FStar_Pprint.document) ->
      'Auu____43797 Prims.list -> FStar_Pprint.document
  =
  fun f  ->
    fun l  ->
      let uu____43817 =
        FStar_Pprint.concat_map
          (fun x  ->
             let uu____43821 = f x  in
             FStar_Pprint.op_Hat_Hat uu____43821 break1) l
         in
      FStar_Pprint.group uu____43817
  
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
    let uu____43884 = str "begin"  in
    let uu____43886 = str "end"  in
    FStar_Pprint.soft_surround (Prims.parse_int "2") (Prims.parse_int "1")
      uu____43884 contents uu____43886
  
let separate_map_last :
  'Auu____43899 .
    FStar_Pprint.document ->
      (Prims.bool -> 'Auu____43899 -> FStar_Pprint.document) ->
        'Auu____43899 Prims.list -> FStar_Pprint.document
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
  'Auu____43957 .
    FStar_Pprint.document ->
      (Prims.bool -> 'Auu____43957 -> FStar_Pprint.document) ->
        'Auu____43957 Prims.list -> FStar_Pprint.document
  =
  fun sep  ->
    fun f  ->
      fun l  ->
        let uu____43989 =
          let uu____43990 =
            let uu____43991 = FStar_Pprint.op_Hat_Hat sep break1  in
            FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____43991  in
          separate_map_last uu____43990 f l  in
        FStar_Pprint.group uu____43989
  
let separate_map_or_flow :
  'Auu____44001 .
    FStar_Pprint.document ->
      ('Auu____44001 -> FStar_Pprint.document) ->
        'Auu____44001 Prims.list -> FStar_Pprint.document
  =
  fun sep  ->
    fun f  ->
      fun l  ->
        if (FStar_List.length l) < (Prims.parse_int "10")
        then FStar_Pprint.separate_map sep f l
        else FStar_Pprint.flow_map sep f l
  
let flow_map_last :
  'Auu____44039 .
    FStar_Pprint.document ->
      (Prims.bool -> 'Auu____44039 -> FStar_Pprint.document) ->
        'Auu____44039 Prims.list -> FStar_Pprint.document
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
  'Auu____44097 .
    FStar_Pprint.document ->
      (Prims.bool -> 'Auu____44097 -> FStar_Pprint.document) ->
        'Auu____44097 Prims.list -> FStar_Pprint.document
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
              let uu____44179 = FStar_Pprint.op_Hat_Slash_Hat doc1 doc3  in
              FStar_Pprint.group uu____44179
            else FStar_Pprint.surround n1 b doc1 doc2 doc3
  
let soft_surround_separate_map :
  'Auu____44201 .
    Prims.int ->
      Prims.int ->
        FStar_Pprint.document ->
          FStar_Pprint.document ->
            FStar_Pprint.document ->
              FStar_Pprint.document ->
                ('Auu____44201 -> FStar_Pprint.document) ->
                  'Auu____44201 Prims.list -> FStar_Pprint.document
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
                    (let uu____44260 = FStar_Pprint.separate_map sep f xs  in
                     FStar_Pprint.soft_surround n1 b opening uu____44260
                       closing)
  
let soft_surround_map_or_flow :
  'Auu____44280 .
    Prims.int ->
      Prims.int ->
        FStar_Pprint.document ->
          FStar_Pprint.document ->
            FStar_Pprint.document ->
              FStar_Pprint.document ->
                ('Auu____44280 -> FStar_Pprint.document) ->
                  'Auu____44280 Prims.list -> FStar_Pprint.document
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
                    (let uu____44339 = separate_map_or_flow sep f xs  in
                     FStar_Pprint.soft_surround n1 b opening uu____44339
                       closing)
  
let (doc_of_fsdoc :
  (Prims.string * (Prims.string * Prims.string) Prims.list) ->
    FStar_Pprint.document)
  =
  fun uu____44358  ->
    match uu____44358 with
    | (comment,keywords) ->
        let uu____44392 =
          let uu____44393 =
            let uu____44396 = str comment  in
            let uu____44397 =
              let uu____44400 =
                let uu____44403 =
                  FStar_Pprint.separate_map FStar_Pprint.comma
                    (fun uu____44414  ->
                       match uu____44414 with
                       | (k,v1) ->
                           let uu____44427 =
                             let uu____44430 = str k  in
                             let uu____44431 =
                               let uu____44434 =
                                 let uu____44437 = str v1  in [uu____44437]
                                  in
                               FStar_Pprint.rarrow :: uu____44434  in
                             uu____44430 :: uu____44431  in
                           FStar_Pprint.concat uu____44427) keywords
                   in
                [uu____44403]  in
              FStar_Pprint.space :: uu____44400  in
            uu____44396 :: uu____44397  in
          FStar_Pprint.concat uu____44393  in
        FStar_Pprint.group uu____44392
  
let (is_unit : FStar_Parser_AST.term -> Prims.bool) =
  fun e  ->
    match e.FStar_Parser_AST.tm with
    | FStar_Parser_AST.Const (FStar_Const.Const_unit ) -> true
    | uu____44447 -> false
  
let (matches_var : FStar_Parser_AST.term -> FStar_Ident.ident -> Prims.bool)
  =
  fun t  ->
    fun x  ->
      match t.FStar_Parser_AST.tm with
      | FStar_Parser_AST.Var y ->
          let uu____44463 = FStar_Ident.text_of_lid y  in
          x.FStar_Ident.idText = uu____44463
      | uu____44466 -> false
  
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
        | FStar_Parser_AST.Construct (lid,uu____44517::(e2,uu____44519)::[])
            -> (FStar_Ident.lid_equals lid cons_lid1) && (aux e2)
        | uu____44542 -> false  in
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
    | FStar_Parser_AST.Construct (uu____44566,[]) -> []
    | FStar_Parser_AST.Construct
        (uu____44577,(e1,FStar_Parser_AST.Nothing )::(e2,FStar_Parser_AST.Nothing
                                                      )::[])
        -> let uu____44598 = extract_from_list e2  in e1 :: uu____44598
    | uu____44601 ->
        let uu____44602 =
          let uu____44604 = FStar_Parser_AST.term_to_string e  in
          FStar_Util.format1 "Not a list %s" uu____44604  in
        failwith uu____44602
  
let (is_array : FStar_Parser_AST.term -> Prims.bool) =
  fun e  ->
    match e.FStar_Parser_AST.tm with
    | FStar_Parser_AST.App
        ({ FStar_Parser_AST.tm = FStar_Parser_AST.Var lid;
           FStar_Parser_AST.range = uu____44618;
           FStar_Parser_AST.level = uu____44619;_},l,FStar_Parser_AST.Nothing
         )
        ->
        (FStar_Ident.lid_equals lid FStar_Parser_Const.array_mk_array_lid) &&
          (is_list l)
    | uu____44621 -> false
  
let rec (is_ref_set : FStar_Parser_AST.term -> Prims.bool) =
  fun e  ->
    match e.FStar_Parser_AST.tm with
    | FStar_Parser_AST.Var maybe_empty_lid ->
        FStar_Ident.lid_equals maybe_empty_lid FStar_Parser_Const.set_empty
    | FStar_Parser_AST.App
        ({ FStar_Parser_AST.tm = FStar_Parser_AST.Var maybe_singleton_lid;
           FStar_Parser_AST.range = uu____44633;
           FStar_Parser_AST.level = uu____44634;_},{
                                                     FStar_Parser_AST.tm =
                                                       FStar_Parser_AST.App
                                                       ({
                                                          FStar_Parser_AST.tm
                                                            =
                                                            FStar_Parser_AST.Var
                                                            maybe_addr_of_lid;
                                                          FStar_Parser_AST.range
                                                            = uu____44636;
                                                          FStar_Parser_AST.level
                                                            = uu____44637;_},e1,FStar_Parser_AST.Nothing
                                                        );
                                                     FStar_Parser_AST.range =
                                                       uu____44639;
                                                     FStar_Parser_AST.level =
                                                       uu____44640;_},FStar_Parser_AST.Nothing
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
                FStar_Parser_AST.range = uu____44642;
                FStar_Parser_AST.level = uu____44643;_},e1,FStar_Parser_AST.Nothing
              );
           FStar_Parser_AST.range = uu____44645;
           FStar_Parser_AST.level = uu____44646;_},e2,FStar_Parser_AST.Nothing
         )
        ->
        ((FStar_Ident.lid_equals maybe_union_lid FStar_Parser_Const.set_union)
           && (is_ref_set e1))
          && (is_ref_set e2)
    | uu____44648 -> false
  
let rec (extract_from_ref_set :
  FStar_Parser_AST.term -> FStar_Parser_AST.term Prims.list) =
  fun e  ->
    match e.FStar_Parser_AST.tm with
    | FStar_Parser_AST.Var uu____44660 -> []
    | FStar_Parser_AST.App
        ({ FStar_Parser_AST.tm = FStar_Parser_AST.Var uu____44661;
           FStar_Parser_AST.range = uu____44662;
           FStar_Parser_AST.level = uu____44663;_},{
                                                     FStar_Parser_AST.tm =
                                                       FStar_Parser_AST.App
                                                       ({
                                                          FStar_Parser_AST.tm
                                                            =
                                                            FStar_Parser_AST.Var
                                                            uu____44664;
                                                          FStar_Parser_AST.range
                                                            = uu____44665;
                                                          FStar_Parser_AST.level
                                                            = uu____44666;_},e1,FStar_Parser_AST.Nothing
                                                        );
                                                     FStar_Parser_AST.range =
                                                       uu____44668;
                                                     FStar_Parser_AST.level =
                                                       uu____44669;_},FStar_Parser_AST.Nothing
         )
        -> [e1]
    | FStar_Parser_AST.App
        ({
           FStar_Parser_AST.tm = FStar_Parser_AST.App
             ({ FStar_Parser_AST.tm = FStar_Parser_AST.Var uu____44670;
                FStar_Parser_AST.range = uu____44671;
                FStar_Parser_AST.level = uu____44672;_},e1,FStar_Parser_AST.Nothing
              );
           FStar_Parser_AST.range = uu____44674;
           FStar_Parser_AST.level = uu____44675;_},e2,FStar_Parser_AST.Nothing
         )
        ->
        let uu____44677 = extract_from_ref_set e1  in
        let uu____44680 = extract_from_ref_set e2  in
        FStar_List.append uu____44677 uu____44680
    | uu____44683 ->
        let uu____44684 =
          let uu____44686 = FStar_Parser_AST.term_to_string e  in
          FStar_Util.format1 "Not a ref set %s" uu____44686  in
        failwith uu____44684
  
let (is_general_application : FStar_Parser_AST.term -> Prims.bool) =
  fun e  ->
    let uu____44698 = (is_array e) || (is_ref_set e)  in
    Prims.op_Negation uu____44698
  
let (is_general_construction : FStar_Parser_AST.term -> Prims.bool) =
  fun e  ->
    let uu____44707 = (is_list e) || (is_lex_list e)  in
    Prims.op_Negation uu____44707
  
let (is_general_prefix_op : FStar_Ident.ident -> Prims.bool) =
  fun op  ->
    let op_starting_char =
      let uu____44718 = FStar_Ident.text_of_id op  in
      FStar_Util.char_at uu____44718 (Prims.parse_int "0")  in
    ((op_starting_char = 33) || (op_starting_char = 63)) ||
      ((op_starting_char = 126) &&
         (let uu____44728 = FStar_Ident.text_of_id op  in uu____44728 <> "~"))
  
let (head_and_args :
  FStar_Parser_AST.term ->
    (FStar_Parser_AST.term * (FStar_Parser_AST.term * FStar_Parser_AST.imp)
      Prims.list))
  =
  fun e  ->
    let rec aux e1 acc =
      match e1.FStar_Parser_AST.tm with
      | FStar_Parser_AST.App (head1,arg,imp) -> aux head1 ((arg, imp) :: acc)
      | uu____44798 -> (e1, acc)  in
    aux e []
  
type associativity =
  | Left 
  | Right 
  | NonAssoc 
let (uu___is_Left : associativity -> Prims.bool) =
  fun projectee  ->
    match projectee with | Left  -> true | uu____44818 -> false
  
let (uu___is_Right : associativity -> Prims.bool) =
  fun projectee  ->
    match projectee with | Right  -> true | uu____44829 -> false
  
let (uu___is_NonAssoc : associativity -> Prims.bool) =
  fun projectee  ->
    match projectee with | NonAssoc  -> true | uu____44840 -> false
  
type token = (FStar_Char.char,Prims.string) FStar_Util.either
type associativity_level = (associativity * token Prims.list)
let (token_to_string :
  (FStar_BaseTypes.char,Prims.string) FStar_Util.either -> Prims.string) =
  fun uu___325_44866  ->
    match uu___325_44866 with
    | FStar_Util.Inl c -> Prims.op_Hat (FStar_Util.string_of_char c) ".*"
    | FStar_Util.Inr s -> s
  
let (matches_token :
  Prims.string ->
    (FStar_Char.char,Prims.string) FStar_Util.either -> Prims.bool)
  =
  fun s  ->
    fun uu___326_44901  ->
      match uu___326_44901 with
      | FStar_Util.Inl c ->
          let uu____44914 = FStar_String.get s (Prims.parse_int "0")  in
          uu____44914 = c
      | FStar_Util.Inr s' -> s = s'
  
let matches_level :
  'Auu____44930 .
    Prims.string ->
      ('Auu____44930 * (FStar_Char.char,Prims.string) FStar_Util.either
        Prims.list) -> Prims.bool
  =
  fun s  ->
    fun uu____44954  ->
      match uu____44954 with
      | (assoc_levels,tokens) ->
          let uu____44986 = FStar_List.tryFind (matches_token s) tokens  in
          uu____44986 <> FStar_Pervasives_Native.None
  
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
  let levels_from_associativity l uu___327_45158 =
    match uu___327_45158 with
    | Left  -> (l, l, (l - (Prims.parse_int "1")))
    | Right  -> ((l - (Prims.parse_int "1")), l, l)
    | NonAssoc  ->
        ((l - (Prims.parse_int "1")), l, (l - (Prims.parse_int "1")))
     in
  FStar_List.mapi
    (fun i  ->
       fun uu____45208  ->
         match uu____45208 with
         | (assoc1,tokens) -> ((levels_from_associativity i assoc1), tokens))
    level_associativity_spec
  
let (assign_levels :
  associativity_level Prims.list ->
    Prims.string -> (Prims.int * Prims.int * Prims.int))
  =
  fun token_associativity_spec  ->
    fun s  ->
      let uu____45283 = FStar_List.tryFind (matches_level s) level_table  in
      match uu____45283 with
      | FStar_Pervasives_Native.Some (assoc_levels,uu____45335) ->
          assoc_levels
      | uu____45373 -> failwith (Prims.op_Hat "Unrecognized operator " s)
  
let max_level :
  'Auu____45406 . ('Auu____45406 * token Prims.list) Prims.list -> Prims.int
  =
  fun l  ->
    let find_level_and_max n1 level =
      let uu____45455 =
        FStar_List.tryFind
          (fun uu____45491  ->
             match uu____45491 with
             | (uu____45508,tokens) ->
                 tokens = (FStar_Pervasives_Native.snd level)) level_table
         in
      match uu____45455 with
      | FStar_Pervasives_Native.Some
          ((uu____45537,l1,uu____45539),uu____45540) -> max n1 l1
      | FStar_Pervasives_Native.None  ->
          let uu____45590 =
            let uu____45592 =
              let uu____45594 =
                FStar_List.map token_to_string
                  (FStar_Pervasives_Native.snd level)
                 in
              FStar_String.concat "," uu____45594  in
            FStar_Util.format1 "Undefined associativity level %s" uu____45592
             in
          failwith uu____45590
       in
    FStar_List.fold_left find_level_and_max (Prims.parse_int "0") l
  
let (levels : Prims.string -> (Prims.int * Prims.int * Prims.int)) =
  fun op  ->
    let uu____45629 = assign_levels level_associativity_spec op  in
    match uu____45629 with
    | (left1,mine,right1) ->
        if op = "*"
        then ((left1 - (Prims.parse_int "1")), mine, right1)
        else (left1, mine, right1)
  
let (operatorInfix0ad12 : associativity_level Prims.list) =
  [opinfix0a; opinfix0b; opinfix0c; opinfix0d; opinfix1; opinfix2] 
let (is_operatorInfix0ad12 : FStar_Ident.ident -> Prims.bool) =
  fun op  ->
    let uu____45688 =
      let uu____45691 =
        let uu____45697 = FStar_Ident.text_of_id op  in
        FStar_All.pipe_left matches_level uu____45697  in
      FStar_List.tryFind uu____45691 operatorInfix0ad12  in
    uu____45688 <> FStar_Pervasives_Native.None
  
let (is_operatorInfix34 : FStar_Ident.ident -> Prims.bool) =
  let opinfix34 = [opinfix3; opinfix4]  in
  fun op  ->
    let uu____45764 =
      let uu____45779 =
        let uu____45797 = FStar_Ident.text_of_id op  in
        FStar_All.pipe_left matches_level uu____45797  in
      FStar_List.tryFind uu____45779 opinfix34  in
    uu____45764 <> FStar_Pervasives_Native.None
  
let (handleable_args_length : FStar_Ident.ident -> Prims.int) =
  fun op  ->
    let op_s = FStar_Ident.text_of_id op  in
    let uu____45863 =
      (is_general_prefix_op op) || (FStar_List.mem op_s ["-"; "~"])  in
    if uu____45863
    then (Prims.parse_int "1")
    else
      (let uu____45876 =
         ((is_operatorInfix0ad12 op) || (is_operatorInfix34 op)) ||
           (FStar_List.mem op_s
              ["<==>"; "==>"; "\\/"; "/\\"; "="; "|>"; ":="; ".()"; ".[]"])
          in
       if uu____45876
       then (Prims.parse_int "2")
       else
         if FStar_List.mem op_s [".()<-"; ".[]<-"]
         then (Prims.parse_int "3")
         else (Prims.parse_int "0"))
  
let handleable_op :
  'Auu____45922 . FStar_Ident.ident -> 'Auu____45922 Prims.list -> Prims.bool
  =
  fun op  ->
    fun args  ->
      match FStar_List.length args with
      | _45938 when _45938 = (Prims.parse_int "0") -> true
      | _45940 when _45940 = (Prims.parse_int "1") ->
          (is_general_prefix_op op) ||
            (let uu____45942 = FStar_Ident.text_of_id op  in
             FStar_List.mem uu____45942 ["-"; "~"])
      | _45950 when _45950 = (Prims.parse_int "2") ->
          ((is_operatorInfix0ad12 op) || (is_operatorInfix34 op)) ||
            (let uu____45952 = FStar_Ident.text_of_id op  in
             FStar_List.mem uu____45952
               ["<==>"; "==>"; "\\/"; "/\\"; "="; "|>"; ":="; ".()"; ".[]"])
      | _45974 when _45974 = (Prims.parse_int "3") ->
          let uu____45975 = FStar_Ident.text_of_id op  in
          FStar_List.mem uu____45975 [".()<-"; ".[]<-"]
      | uu____45983 -> false
  
type annotation_style =
  | Binders of (Prims.int * Prims.int * Prims.bool) 
  | Arrows of (Prims.int * Prims.int) 
let (uu___is_Binders : annotation_style -> Prims.bool) =
  fun projectee  ->
    match projectee with | Binders _0 -> true | uu____46029 -> false
  
let (__proj__Binders__item___0 :
  annotation_style -> (Prims.int * Prims.int * Prims.bool)) =
  fun projectee  -> match projectee with | Binders _0 -> _0 
let (uu___is_Arrows : annotation_style -> Prims.bool) =
  fun projectee  ->
    match projectee with | Arrows _0 -> true | uu____46082 -> false
  
let (__proj__Arrows__item___0 : annotation_style -> (Prims.int * Prims.int))
  = fun projectee  -> match projectee with | Arrows _0 -> _0 
let (all_binders_annot : FStar_Parser_AST.term -> Prims.bool) =
  fun e  ->
    let is_binder_annot b =
      match b.FStar_Parser_AST.b with
      | FStar_Parser_AST.Annotated uu____46125 -> true
      | uu____46131 -> false  in
    let rec all_binders e1 l =
      match e1.FStar_Parser_AST.tm with
      | FStar_Parser_AST.Product (bs,tgt) ->
          let uu____46164 = FStar_List.for_all is_binder_annot bs  in
          if uu____46164
          then all_binders tgt (l + (FStar_List.length bs))
          else (false, (Prims.parse_int "0"))
      | uu____46179 -> (true, (l + (Prims.parse_int "1")))  in
    let uu____46184 = all_binders e (Prims.parse_int "0")  in
    match uu____46184 with
    | (b,l) -> if b && (l > (Prims.parse_int "1")) then true else false
  
type catf =
  FStar_Pprint.document -> FStar_Pprint.document -> FStar_Pprint.document
let (cat_with_colon :
  FStar_Pprint.document -> FStar_Pprint.document -> FStar_Pprint.document) =
  fun x  ->
    fun y  ->
      let uu____46223 = FStar_Pprint.op_Hat_Slash_Hat FStar_Pprint.colon y
         in
      FStar_Pprint.op_Hat_Hat x uu____46223
  
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
  'Auu____46383 .
    ('Auu____46383 -> FStar_Pprint.document) ->
      'Auu____46383 -> FStar_Range.range -> FStar_Pprint.document
  =
  fun printer  ->
    fun tm  ->
      fun tmrange  ->
        let rec comments_before_pos acc print_pos lookahead_pos =
          let uu____46425 = FStar_ST.op_Bang comment_stack  in
          match uu____46425 with
          | [] -> (acc, false)
          | (c,crange)::cs ->
              let comment =
                let uu____46496 = str c  in
                FStar_Pprint.op_Hat_Hat uu____46496 FStar_Pprint.hardline  in
              let uu____46497 = FStar_Range.range_before_pos crange print_pos
                 in
              if uu____46497
              then
                (FStar_ST.op_Colon_Equals comment_stack cs;
                 (let uu____46539 = FStar_Pprint.op_Hat_Hat acc comment  in
                  comments_before_pos uu____46539 print_pos lookahead_pos))
              else
                (let uu____46542 =
                   FStar_Range.range_before_pos crange lookahead_pos  in
                 (acc, uu____46542))
           in
        let uu____46545 =
          let uu____46551 =
            let uu____46552 = FStar_Range.start_of_range tmrange  in
            FStar_Range.end_of_line uu____46552  in
          let uu____46553 = FStar_Range.end_of_range tmrange  in
          comments_before_pos FStar_Pprint.empty uu____46551 uu____46553  in
        match uu____46545 with
        | (comments,has_lookahead) ->
            let printed_e = printer tm  in
            let comments1 =
              if has_lookahead
              then
                let pos = FStar_Range.end_of_range tmrange  in
                let uu____46562 = comments_before_pos comments pos pos  in
                FStar_Pervasives_Native.fst uu____46562
              else comments  in
            if comments1 = FStar_Pprint.empty
            then printed_e
            else
              (let uu____46574 = FStar_Pprint.op_Hat_Hat comments1 printed_e
                  in
               FStar_Pprint.group uu____46574)
  
let with_comment_sep :
  'Auu____46586 'Auu____46587 .
    ('Auu____46586 -> 'Auu____46587) ->
      'Auu____46586 ->
        FStar_Range.range -> (FStar_Pprint.document * 'Auu____46587)
  =
  fun printer  ->
    fun tm  ->
      fun tmrange  ->
        let rec comments_before_pos acc print_pos lookahead_pos =
          let uu____46633 = FStar_ST.op_Bang comment_stack  in
          match uu____46633 with
          | [] -> (acc, false)
          | (c,crange)::cs ->
              let comment = str c  in
              let uu____46704 = FStar_Range.range_before_pos crange print_pos
                 in
              if uu____46704
              then
                (FStar_ST.op_Colon_Equals comment_stack cs;
                 (let uu____46746 =
                    if acc = FStar_Pprint.empty
                    then comment
                    else
                      (let uu____46750 =
                         FStar_Pprint.op_Hat_Hat FStar_Pprint.hardline
                           comment
                          in
                       FStar_Pprint.op_Hat_Hat acc uu____46750)
                     in
                  comments_before_pos uu____46746 print_pos lookahead_pos))
              else
                (let uu____46753 =
                   FStar_Range.range_before_pos crange lookahead_pos  in
                 (acc, uu____46753))
           in
        let uu____46756 =
          let uu____46762 =
            let uu____46763 = FStar_Range.start_of_range tmrange  in
            FStar_Range.end_of_line uu____46763  in
          let uu____46764 = FStar_Range.end_of_range tmrange  in
          comments_before_pos FStar_Pprint.empty uu____46762 uu____46764  in
        match uu____46756 with
        | (comments,has_lookahead) ->
            let printed_e = printer tm  in
            let comments1 =
              if has_lookahead
              then
                let pos = FStar_Range.end_of_range tmrange  in
                let uu____46777 = comments_before_pos comments pos pos  in
                FStar_Pervasives_Native.fst uu____46777
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
                let uu____46830 = FStar_ST.op_Bang comment_stack  in
                match uu____46830 with
                | (comment,crange)::cs when
                    FStar_Range.range_before_pos crange pos ->
                    (FStar_ST.op_Colon_Equals comment_stack cs;
                     (let lnum =
                        let uu____46924 =
                          let uu____46926 =
                            let uu____46928 =
                              FStar_Range.start_of_range crange  in
                            FStar_Range.line_of_pos uu____46928  in
                          uu____46926 - lbegin  in
                        max k uu____46924  in
                      let lnum1 = min (Prims.parse_int "2") lnum  in
                      let doc2 =
                        let uu____46933 =
                          let uu____46934 =
                            FStar_Pprint.repeat lnum1 FStar_Pprint.hardline
                             in
                          let uu____46935 = str comment  in
                          FStar_Pprint.op_Hat_Hat uu____46934 uu____46935  in
                        FStar_Pprint.op_Hat_Hat doc1 uu____46933  in
                      let uu____46936 =
                        let uu____46938 = FStar_Range.end_of_range crange  in
                        FStar_Range.line_of_pos uu____46938  in
                      place_comments_until_pos (Prims.parse_int "1")
                        uu____46936 pos meta_decl doc2 true init1))
                | uu____46941 ->
                    if doc1 = FStar_Pprint.empty
                    then FStar_Pprint.empty
                    else
                      (let lnum =
                         let uu____46954 = FStar_Range.line_of_pos pos  in
                         uu____46954 - lbegin  in
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
                       let uu____46996 =
                         FStar_Pprint.repeat lnum7 FStar_Pprint.hardline  in
                       FStar_Pprint.op_Hat_Hat doc1 uu____46996)
  
let separate_map_with_comments :
  'Auu____47010 .
    FStar_Pprint.document ->
      FStar_Pprint.document ->
        ('Auu____47010 -> FStar_Pprint.document) ->
          'Auu____47010 Prims.list ->
            ('Auu____47010 -> decl_meta) -> FStar_Pprint.document
  =
  fun prefix1  ->
    fun sep  ->
      fun f  ->
        fun xs  ->
          fun extract_meta  ->
            let fold_fun uu____47069 x =
              match uu____47069 with
              | (last_line,doc1) ->
                  let meta_decl = extract_meta x  in
                  let r = meta_decl.r  in
                  let doc2 =
                    let uu____47088 = FStar_Range.start_of_range r  in
                    place_comments_until_pos (Prims.parse_int "1") last_line
                      uu____47088 meta_decl doc1 false false
                     in
                  let uu____47092 =
                    let uu____47094 = FStar_Range.end_of_range r  in
                    FStar_Range.line_of_pos uu____47094  in
                  let uu____47095 =
                    let uu____47096 =
                      let uu____47097 = f x  in
                      FStar_Pprint.op_Hat_Hat sep uu____47097  in
                    FStar_Pprint.op_Hat_Hat doc2 uu____47096  in
                  (uu____47092, uu____47095)
               in
            let uu____47099 =
              let uu____47106 = FStar_List.hd xs  in
              let uu____47107 = FStar_List.tl xs  in
              (uu____47106, uu____47107)  in
            match uu____47099 with
            | (x,xs1) ->
                let init1 =
                  let meta_decl = extract_meta x  in
                  let uu____47125 =
                    let uu____47127 = FStar_Range.end_of_range meta_decl.r
                       in
                    FStar_Range.line_of_pos uu____47127  in
                  let uu____47128 =
                    let uu____47129 = f x  in
                    FStar_Pprint.op_Hat_Hat prefix1 uu____47129  in
                  (uu____47125, uu____47128)  in
                let uu____47131 = FStar_List.fold_left fold_fun init1 xs1  in
                FStar_Pervasives_Native.snd uu____47131
  
let separate_map_with_comments_kw :
  'Auu____47158 'Auu____47159 .
    'Auu____47158 ->
      'Auu____47158 ->
        ('Auu____47158 -> 'Auu____47159 -> FStar_Pprint.document) ->
          'Auu____47159 Prims.list ->
            ('Auu____47159 -> decl_meta) -> FStar_Pprint.document
  =
  fun prefix1  ->
    fun sep  ->
      fun f  ->
        fun xs  ->
          fun extract_meta  ->
            let fold_fun uu____47223 x =
              match uu____47223 with
              | (last_line,doc1) ->
                  let meta_decl = extract_meta x  in
                  let r = meta_decl.r  in
                  let doc2 =
                    let uu____47242 = FStar_Range.start_of_range r  in
                    place_comments_until_pos (Prims.parse_int "1") last_line
                      uu____47242 meta_decl doc1 false false
                     in
                  let uu____47246 =
                    let uu____47248 = FStar_Range.end_of_range r  in
                    FStar_Range.line_of_pos uu____47248  in
                  let uu____47249 =
                    let uu____47250 = f sep x  in
                    FStar_Pprint.op_Hat_Hat doc2 uu____47250  in
                  (uu____47246, uu____47249)
               in
            let uu____47252 =
              let uu____47259 = FStar_List.hd xs  in
              let uu____47260 = FStar_List.tl xs  in
              (uu____47259, uu____47260)  in
            match uu____47252 with
            | (x,xs1) ->
                let init1 =
                  let meta_decl = extract_meta x  in
                  let uu____47278 =
                    let uu____47280 = FStar_Range.end_of_range meta_decl.r
                       in
                    FStar_Range.line_of_pos uu____47280  in
                  let uu____47281 = f prefix1 x  in
                  (uu____47278, uu____47281)  in
                let uu____47283 = FStar_List.fold_left fold_fun init1 xs1  in
                FStar_Pervasives_Native.snd uu____47283
  
let rec (p_decl : FStar_Parser_AST.decl -> FStar_Pprint.document) =
  fun d  ->
    let qualifiers =
      match ((d.FStar_Parser_AST.quals), (d.FStar_Parser_AST.d)) with
      | ((FStar_Parser_AST.Assumption )::[],FStar_Parser_AST.Assume
         (id1,uu____48269)) ->
          let uu____48272 =
            let uu____48274 =
              FStar_Util.char_at id1.FStar_Ident.idText (Prims.parse_int "0")
               in
            FStar_All.pipe_right uu____48274 FStar_Util.is_upper  in
          if uu____48272
          then
            let uu____48280 = p_qualifier FStar_Parser_AST.Assumption  in
            FStar_Pprint.op_Hat_Hat uu____48280 FStar_Pprint.space
          else p_qualifiers d.FStar_Parser_AST.quals
      | uu____48283 -> p_qualifiers d.FStar_Parser_AST.quals  in
    let uu____48290 =
      FStar_Pprint.optional (fun d1  -> p_fsdoc d1) d.FStar_Parser_AST.doc
       in
    let uu____48293 =
      let uu____48294 = p_attributes d.FStar_Parser_AST.attrs  in
      let uu____48295 =
        let uu____48296 = p_rawDecl d  in
        FStar_Pprint.op_Hat_Hat qualifiers uu____48296  in
      FStar_Pprint.op_Hat_Hat uu____48294 uu____48295  in
    FStar_Pprint.op_Hat_Hat uu____48290 uu____48293

and (p_attributes : FStar_Parser_AST.attributes_ -> FStar_Pprint.document) =
  fun attrs  ->
    match attrs with
    | [] -> FStar_Pprint.empty
    | uu____48298 ->
        let uu____48299 =
          let uu____48300 = str "@ "  in
          let uu____48302 =
            let uu____48303 =
              let uu____48304 =
                let uu____48305 =
                  let uu____48306 = FStar_List.map p_atomicTerm attrs  in
                  FStar_Pprint.flow break1 uu____48306  in
                FStar_Pprint.op_Hat_Hat uu____48305 FStar_Pprint.rbracket  in
              FStar_Pprint.align uu____48304  in
            FStar_Pprint.op_Hat_Hat uu____48303 FStar_Pprint.hardline  in
          FStar_Pprint.op_Hat_Hat uu____48300 uu____48302  in
        FStar_Pprint.op_Hat_Hat FStar_Pprint.lbracket uu____48299

and (p_fsdoc : FStar_Parser_AST.fsdoc -> FStar_Pprint.document) =
  fun uu____48309  ->
    match uu____48309 with
    | (doc1,kwd_args) ->
        let kwd_args_doc =
          match kwd_args with
          | [] -> FStar_Pprint.empty
          | kwd_args1 ->
              let process_kwd_arg uu____48357 =
                match uu____48357 with
                | (kwd,arg) ->
                    let uu____48370 = str "@"  in
                    let uu____48372 =
                      let uu____48373 = str kwd  in
                      let uu____48374 =
                        let uu____48375 = str arg  in
                        FStar_Pprint.op_Hat_Hat FStar_Pprint.space
                          uu____48375
                         in
                      FStar_Pprint.op_Hat_Hat uu____48373 uu____48374  in
                    FStar_Pprint.op_Hat_Hat uu____48370 uu____48372
                 in
              let uu____48376 =
                FStar_Pprint.separate_map FStar_Pprint.hardline
                  process_kwd_arg kwd_args1
                 in
              FStar_Pprint.op_Hat_Hat uu____48376 FStar_Pprint.hardline
           in
        let uu____48383 =
          let uu____48384 =
            let uu____48385 =
              let uu____48386 = str doc1  in
              let uu____48387 =
                let uu____48388 =
                  let uu____48389 =
                    FStar_Pprint.op_Hat_Hat FStar_Pprint.rparen
                      FStar_Pprint.hardline
                     in
                  FStar_Pprint.op_Hat_Hat FStar_Pprint.star uu____48389  in
                FStar_Pprint.op_Hat_Hat kwd_args_doc uu____48388  in
              FStar_Pprint.op_Hat_Hat uu____48386 uu____48387  in
            FStar_Pprint.op_Hat_Hat FStar_Pprint.star uu____48385  in
          FStar_Pprint.op_Hat_Hat FStar_Pprint.star uu____48384  in
        FStar_Pprint.op_Hat_Hat FStar_Pprint.lparen uu____48383

and (p_justSig : FStar_Parser_AST.decl -> FStar_Pprint.document) =
  fun d  ->
    match d.FStar_Parser_AST.d with
    | FStar_Parser_AST.Val (lid,t) ->
        let uu____48393 =
          let uu____48394 = str "val"  in
          let uu____48396 =
            let uu____48397 =
              let uu____48398 = p_lident lid  in
              let uu____48399 =
                FStar_Pprint.op_Hat_Hat FStar_Pprint.space FStar_Pprint.colon
                 in
              FStar_Pprint.op_Hat_Hat uu____48398 uu____48399  in
            FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____48397  in
          FStar_Pprint.op_Hat_Hat uu____48394 uu____48396  in
        let uu____48400 = p_typ false false t  in
        FStar_Pprint.op_Hat_Hat uu____48393 uu____48400
    | FStar_Parser_AST.TopLevelLet (uu____48403,lbs) ->
        FStar_Pprint.separate_map FStar_Pprint.hardline
          (fun lb  ->
             let uu____48428 =
               let uu____48429 = str "let"  in p_letlhs uu____48429 lb false
                in
             FStar_Pprint.group uu____48428) lbs
    | uu____48432 -> FStar_Pprint.empty

and (p_list :
  (FStar_Ident.ident -> FStar_Pprint.document) ->
    FStar_Pprint.document ->
      FStar_Ident.ident Prims.list -> FStar_Pprint.document)
  =
  fun f  ->
    fun sep  ->
      fun l  ->
        let rec p_list' uu___328_48447 =
          match uu___328_48447 with
          | [] -> FStar_Pprint.empty
          | x::[] -> f x
          | x::xs ->
              let uu____48455 = f x  in
              let uu____48456 =
                let uu____48457 = p_list' xs  in
                FStar_Pprint.op_Hat_Hat sep uu____48457  in
              FStar_Pprint.op_Hat_Hat uu____48455 uu____48456
           in
        let uu____48458 = str "["  in
        let uu____48460 =
          let uu____48461 = p_list' l  in
          let uu____48462 = str "]"  in
          FStar_Pprint.op_Hat_Hat uu____48461 uu____48462  in
        FStar_Pprint.op_Hat_Hat uu____48458 uu____48460

and (p_rawDecl : FStar_Parser_AST.decl -> FStar_Pprint.document) =
  fun d  ->
    match d.FStar_Parser_AST.d with
    | FStar_Parser_AST.Open uid ->
        let uu____48466 =
          let uu____48467 = str "open"  in
          let uu____48469 = p_quident uid  in
          FStar_Pprint.op_Hat_Slash_Hat uu____48467 uu____48469  in
        FStar_Pprint.group uu____48466
    | FStar_Parser_AST.Include uid ->
        let uu____48471 =
          let uu____48472 = str "include"  in
          let uu____48474 = p_quident uid  in
          FStar_Pprint.op_Hat_Slash_Hat uu____48472 uu____48474  in
        FStar_Pprint.group uu____48471
    | FStar_Parser_AST.Friend uid ->
        let uu____48476 =
          let uu____48477 = str "friend"  in
          let uu____48479 = p_quident uid  in
          FStar_Pprint.op_Hat_Slash_Hat uu____48477 uu____48479  in
        FStar_Pprint.group uu____48476
    | FStar_Parser_AST.ModuleAbbrev (uid1,uid2) ->
        let uu____48482 =
          let uu____48483 = str "module"  in
          let uu____48485 =
            let uu____48486 =
              let uu____48487 = p_uident uid1  in
              let uu____48488 =
                FStar_Pprint.op_Hat_Hat FStar_Pprint.space
                  FStar_Pprint.equals
                 in
              FStar_Pprint.op_Hat_Hat uu____48487 uu____48488  in
            FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____48486  in
          FStar_Pprint.op_Hat_Hat uu____48483 uu____48485  in
        let uu____48489 = p_quident uid2  in
        op_Hat_Slash_Plus_Hat uu____48482 uu____48489
    | FStar_Parser_AST.TopLevelModule uid ->
        let uu____48491 =
          let uu____48492 = str "module"  in
          let uu____48494 =
            let uu____48495 = p_quident uid  in
            FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____48495  in
          FStar_Pprint.op_Hat_Hat uu____48492 uu____48494  in
        FStar_Pprint.group uu____48491
    | FStar_Parser_AST.Tycon
        (true
         ,uu____48496,(FStar_Parser_AST.TyconAbbrev
                       (uid,tpars,FStar_Pervasives_Native.None ,t),FStar_Pervasives_Native.None
                       )::[])
        ->
        let effect_prefix_doc =
          let uu____48533 = str "effect"  in
          let uu____48535 =
            let uu____48536 = p_uident uid  in
            FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____48536  in
          FStar_Pprint.op_Hat_Hat uu____48533 uu____48535  in
        let uu____48537 =
          let uu____48538 = p_typars tpars  in
          FStar_Pprint.surround (Prims.parse_int "2") (Prims.parse_int "1")
            effect_prefix_doc uu____48538 FStar_Pprint.equals
           in
        let uu____48541 = p_typ false false t  in
        op_Hat_Slash_Plus_Hat uu____48537 uu____48541
    | FStar_Parser_AST.Tycon (false ,tc,tcdefs) ->
        let s = if tc then str "class" else str "type"  in
        let uu____48572 =
          let uu____48573 = FStar_List.hd tcdefs  in
          p_fsdocTypeDeclPairs s uu____48573  in
        let uu____48586 =
          let uu____48587 = FStar_List.tl tcdefs  in
          FStar_All.pipe_left
            (FStar_Pprint.concat_map
               (fun x  ->
                  let uu____48625 =
                    let uu____48626 = str "and"  in
                    p_fsdocTypeDeclPairs uu____48626 x  in
                  FStar_Pprint.op_Hat_Hat break1 uu____48625)) uu____48587
           in
        FStar_Pprint.op_Hat_Hat uu____48572 uu____48586
    | FStar_Parser_AST.TopLevelLet (q,lbs) ->
        let let_doc =
          let uu____48643 = str "let"  in
          let uu____48645 = p_letqualifier q  in
          FStar_Pprint.op_Hat_Hat uu____48643 uu____48645  in
        let uu____48646 = str "and"  in
        separate_map_with_comments_kw let_doc uu____48646 p_letbinding lbs
          (fun uu____48656  ->
             match uu____48656 with
             | (p,t) ->
                 let uu____48663 =
                   FStar_Range.union_ranges p.FStar_Parser_AST.prange
                     t.FStar_Parser_AST.range
                    in
                 {
                   r = uu____48663;
                   has_qs = false;
                   has_attrs = false;
                   has_fsdoc = (FStar_Util.is_some d.FStar_Parser_AST.doc);
                   is_fsdoc = false
                 })
    | FStar_Parser_AST.Val (lid,t) ->
        let uu____48669 =
          let uu____48670 = str "val"  in
          let uu____48672 =
            let uu____48673 =
              let uu____48674 = p_lident lid  in
              let uu____48675 = sig_as_binders_if_possible t false  in
              FStar_Pprint.op_Hat_Hat uu____48674 uu____48675  in
            FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____48673  in
          FStar_Pprint.op_Hat_Hat uu____48670 uu____48672  in
        FStar_All.pipe_left FStar_Pprint.group uu____48669
    | FStar_Parser_AST.Assume (id1,t) ->
        let decl_keyword =
          let uu____48680 =
            let uu____48682 =
              FStar_Util.char_at id1.FStar_Ident.idText (Prims.parse_int "0")
               in
            FStar_All.pipe_right uu____48682 FStar_Util.is_upper  in
          if uu____48680
          then FStar_Pprint.empty
          else
            (let uu____48690 = str "val"  in
             FStar_Pprint.op_Hat_Hat uu____48690 FStar_Pprint.space)
           in
        let uu____48692 =
          let uu____48693 = p_ident id1  in
          let uu____48694 =
            let uu____48695 =
              let uu____48696 =
                let uu____48697 = p_typ false false t  in
                FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____48697  in
              FStar_Pprint.op_Hat_Hat FStar_Pprint.colon uu____48696  in
            FStar_Pprint.group uu____48695  in
          FStar_Pprint.op_Hat_Hat uu____48693 uu____48694  in
        FStar_Pprint.op_Hat_Hat decl_keyword uu____48692
    | FStar_Parser_AST.Exception (uid,t_opt) ->
        let uu____48706 = str "exception"  in
        let uu____48708 =
          let uu____48709 =
            let uu____48710 = p_uident uid  in
            let uu____48711 =
              FStar_Pprint.optional
                (fun t  ->
                   let uu____48715 =
                     let uu____48716 = str "of"  in
                     let uu____48718 = p_typ false false t  in
                     op_Hat_Slash_Plus_Hat uu____48716 uu____48718  in
                   FStar_Pprint.op_Hat_Hat break1 uu____48715) t_opt
               in
            FStar_Pprint.op_Hat_Hat uu____48710 uu____48711  in
          FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____48709  in
        FStar_Pprint.op_Hat_Hat uu____48706 uu____48708
    | FStar_Parser_AST.NewEffect ne ->
        let uu____48722 = str "new_effect"  in
        let uu____48724 =
          let uu____48725 = p_newEffect ne  in
          FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____48725  in
        FStar_Pprint.op_Hat_Hat uu____48722 uu____48724
    | FStar_Parser_AST.SubEffect se ->
        let uu____48727 = str "sub_effect"  in
        let uu____48729 =
          let uu____48730 = p_subEffect se  in
          FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____48730  in
        FStar_Pprint.op_Hat_Hat uu____48727 uu____48729
    | FStar_Parser_AST.Pragma p -> p_pragma p
    | FStar_Parser_AST.Fsdoc doc1 -> p_fsdoc doc1
    | FStar_Parser_AST.Main uu____48733 ->
        failwith "*Main declaration* : Is that really still in use ??"
    | FStar_Parser_AST.Tycon (true ,uu____48735,uu____48736) ->
        failwith
          "Effect abbreviation is expected to be defined by an abbreviation"
    | FStar_Parser_AST.Splice (ids,t) ->
        let uu____48764 = str "%splice"  in
        let uu____48766 =
          let uu____48767 =
            let uu____48768 = str ";"  in p_list p_uident uu____48768 ids  in
          let uu____48770 =
            let uu____48771 = p_term false false t  in
            FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____48771  in
          FStar_Pprint.op_Hat_Hat uu____48767 uu____48770  in
        FStar_Pprint.op_Hat_Hat uu____48764 uu____48766

and (p_pragma : FStar_Parser_AST.pragma -> FStar_Pprint.document) =
  fun uu___329_48774  ->
    match uu___329_48774 with
    | FStar_Parser_AST.SetOptions s ->
        let uu____48777 = str "#set-options"  in
        let uu____48779 =
          let uu____48780 =
            let uu____48781 = str s  in FStar_Pprint.dquotes uu____48781  in
          FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____48780  in
        FStar_Pprint.op_Hat_Hat uu____48777 uu____48779
    | FStar_Parser_AST.ResetOptions s_opt ->
        let uu____48786 = str "#reset-options"  in
        let uu____48788 =
          FStar_Pprint.optional
            (fun s  ->
               let uu____48794 =
                 let uu____48795 = str s  in FStar_Pprint.dquotes uu____48795
                  in
               FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____48794) s_opt
           in
        FStar_Pprint.op_Hat_Hat uu____48786 uu____48788
    | FStar_Parser_AST.PushOptions s_opt ->
        let uu____48800 = str "#push-options"  in
        let uu____48802 =
          FStar_Pprint.optional
            (fun s  ->
               let uu____48808 =
                 let uu____48809 = str s  in FStar_Pprint.dquotes uu____48809
                  in
               FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____48808) s_opt
           in
        FStar_Pprint.op_Hat_Hat uu____48800 uu____48802
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
    fun uu____48840  ->
      match uu____48840 with
      | (typedecl,fsdoc_opt) ->
          let uu____48853 = p_typeDecl (kw, fsdoc_opt) typedecl  in
          (match uu____48853 with
           | (comm,decl,body,pre) ->
               if comm = FStar_Pprint.empty
               then
                 let uu____48878 = pre body  in
                 FStar_Pprint.op_Hat_Hat decl uu____48878
               else
                 (let uu____48881 =
                    let uu____48882 =
                      let uu____48883 =
                        let uu____48884 = pre body  in
                        FStar_Pprint.op_Hat_Slash_Hat uu____48884 comm  in
                      FStar_Pprint.op_Hat_Hat decl uu____48883  in
                    let uu____48885 =
                      let uu____48886 =
                        let uu____48887 =
                          let uu____48888 =
                            let uu____48889 =
                              FStar_Pprint.op_Hat_Hat FStar_Pprint.hardline
                                body
                               in
                            FStar_Pprint.op_Hat_Hat comm uu____48889  in
                          FStar_Pprint.op_Hat_Hat FStar_Pprint.hardline
                            uu____48888
                           in
                        FStar_Pprint.nest (Prims.parse_int "2") uu____48887
                         in
                      FStar_Pprint.op_Hat_Hat decl uu____48886  in
                    FStar_Pprint.ifflat uu____48882 uu____48885  in
                  FStar_All.pipe_left FStar_Pprint.group uu____48881))

and (p_typeDecl :
  (FStar_Pprint.document * FStar_Parser_AST.fsdoc
    FStar_Pervasives_Native.option) ->
    FStar_Parser_AST.tycon ->
      (FStar_Pprint.document * FStar_Pprint.document * FStar_Pprint.document
        * (FStar_Pprint.document -> FStar_Pprint.document)))
  =
  fun pre  ->
    fun uu___330_48892  ->
      match uu___330_48892 with
      | FStar_Parser_AST.TyconAbstract (lid,bs,typ_opt) ->
          let uu____48921 = p_typeDeclPrefix pre false lid bs typ_opt  in
          (FStar_Pprint.empty, uu____48921, FStar_Pprint.empty,
            FStar_Pervasives.id)
      | FStar_Parser_AST.TyconAbbrev (lid,bs,typ_opt,t) ->
          let uu____48938 = p_typ_sep false false t  in
          (match uu____48938 with
           | (comm,doc1) ->
               let uu____48958 = p_typeDeclPrefix pre true lid bs typ_opt  in
               (comm, uu____48958, doc1, jump2))
      | FStar_Parser_AST.TyconRecord (lid,bs,typ_opt,record_field_decls) ->
          let p_recordFieldAndComments ps uu____49014 =
            match uu____49014 with
            | (lid1,t,doc_opt) ->
                let uu____49031 =
                  let uu____49036 =
                    FStar_Range.extend_to_end_of_line
                      t.FStar_Parser_AST.range
                     in
                  with_comment_sep (p_recordFieldDecl ps) (lid1, t, doc_opt)
                    uu____49036
                   in
                (match uu____49031 with
                 | (comm,field) ->
                     let sep =
                       if ps then FStar_Pprint.semi else FStar_Pprint.empty
                        in
                     inline_comment_or_above comm field sep)
             in
          let p_fields =
            let uu____49054 =
              separate_map_last FStar_Pprint.hardline
                p_recordFieldAndComments record_field_decls
               in
            braces_with_nesting uu____49054  in
          let uu____49063 = p_typeDeclPrefix pre true lid bs typ_opt  in
          (FStar_Pprint.empty, uu____49063, p_fields,
            ((fun d  -> FStar_Pprint.op_Hat_Hat FStar_Pprint.space d)))
      | FStar_Parser_AST.TyconVariant (lid,bs,typ_opt,ct_decls) ->
          let p_constructorBranchAndComments uu____49130 =
            match uu____49130 with
            | (uid,t_opt,doc_opt,use_of) ->
                let range =
                  let uu____49159 =
                    let uu____49160 =
                      FStar_Util.map_opt t_opt
                        (fun t  -> t.FStar_Parser_AST.range)
                       in
                    FStar_Util.dflt uid.FStar_Ident.idRange uu____49160  in
                  FStar_Range.extend_to_end_of_line uu____49159  in
                let uu____49165 =
                  with_comment_sep p_constructorBranch
                    (uid, t_opt, doc_opt, use_of) range
                   in
                (match uu____49165 with
                 | (comm,ctor) ->
                     inline_comment_or_above comm ctor FStar_Pprint.empty)
             in
          let datacon_doc =
            FStar_Pprint.separate_map FStar_Pprint.hardline
              p_constructorBranchAndComments ct_decls
             in
          let uu____49204 = p_typeDeclPrefix pre true lid bs typ_opt  in
          (FStar_Pprint.empty, uu____49204, datacon_doc, jump2)

and (p_typeDeclPrefix :
  (FStar_Pprint.document * FStar_Parser_AST.fsdoc
    FStar_Pervasives_Native.option) ->
    Prims.bool ->
      FStar_Ident.ident ->
        FStar_Parser_AST.binder Prims.list ->
          FStar_Parser_AST.knd FStar_Pervasives_Native.option ->
            FStar_Pprint.document)
  =
  fun uu____49209  ->
    fun eq1  ->
      fun lid  ->
        fun bs  ->
          fun typ_opt  ->
            match uu____49209 with
            | (kw,fsdoc_opt) ->
                let maybe_with_fsdoc cont =
                  let lid_doc = p_ident lid  in
                  let kw_lid =
                    let uu____49244 =
                      FStar_Pprint.op_Hat_Slash_Hat kw lid_doc  in
                    FStar_Pprint.group uu____49244  in
                  match fsdoc_opt with
                  | FStar_Pervasives_Native.None  -> cont kw_lid
                  | FStar_Pervasives_Native.Some fsdoc ->
                      let uu____49246 =
                        let uu____49249 =
                          let uu____49252 = p_fsdoc fsdoc  in
                          let uu____49253 =
                            let uu____49256 = cont lid_doc  in [uu____49256]
                             in
                          uu____49252 :: uu____49253  in
                        kw :: uu____49249  in
                      FStar_Pprint.separate FStar_Pprint.hardline uu____49246
                   in
                let typ =
                  let maybe_eq =
                    if eq1 then FStar_Pprint.equals else FStar_Pprint.empty
                     in
                  match typ_opt with
                  | FStar_Pervasives_Native.None  -> maybe_eq
                  | FStar_Pervasives_Native.Some t ->
                      let uu____49263 =
                        let uu____49264 =
                          let uu____49265 = p_typ false false t  in
                          FStar_Pprint.op_Hat_Slash_Hat uu____49265 maybe_eq
                           in
                        FStar_Pprint.op_Hat_Hat FStar_Pprint.space
                          uu____49264
                         in
                      FStar_Pprint.op_Hat_Hat FStar_Pprint.colon uu____49263
                   in
                if bs = []
                then maybe_with_fsdoc (fun n1  -> prefix2 n1 typ)
                else
                  (let binders = p_binders_list true bs  in
                   maybe_with_fsdoc
                     (fun n1  ->
                        let uu____49285 =
                          let uu____49286 = FStar_Pprint.flow break1 binders
                             in
                          prefix2 n1 uu____49286  in
                        prefix2 uu____49285 typ))

and (p_recordFieldDecl :
  Prims.bool ->
    (FStar_Ident.ident * FStar_Parser_AST.term * FStar_Parser_AST.fsdoc
      FStar_Pervasives_Native.option) -> FStar_Pprint.document)
  =
  fun ps  ->
    fun uu____49288  ->
      match uu____49288 with
      | (lid,t,doc_opt) ->
          let uu____49305 =
            let uu____49306 = FStar_Pprint.optional p_fsdoc doc_opt  in
            let uu____49307 =
              let uu____49308 = p_lident lid  in
              let uu____49309 =
                let uu____49310 = p_typ ps false t  in
                FStar_Pprint.op_Hat_Hat FStar_Pprint.colon uu____49310  in
              FStar_Pprint.op_Hat_Hat uu____49308 uu____49309  in
            FStar_Pprint.op_Hat_Hat uu____49306 uu____49307  in
          FStar_Pprint.group uu____49305

and (p_constructorBranch :
  (FStar_Ident.ident * FStar_Parser_AST.term FStar_Pervasives_Native.option *
    FStar_Parser_AST.fsdoc FStar_Pervasives_Native.option * Prims.bool) ->
    FStar_Pprint.document)
  =
  fun uu____49312  ->
    match uu____49312 with
    | (uid,t_opt,doc_opt,use_of) ->
        let sep = if use_of then str "of" else FStar_Pprint.colon  in
        let uid_doc =
          let uu____49346 =
            let uu____49347 =
              let uu____49348 = p_uident uid  in
              FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____49348  in
            FStar_Pprint.op_Hat_Hat FStar_Pprint.bar uu____49347  in
          FStar_Pprint.group uu____49346  in
        let uu____49349 = FStar_Pprint.optional p_fsdoc doc_opt  in
        let uu____49350 =
          default_or_map uid_doc
            (fun t  ->
               let uu____49354 =
                 let uu____49355 =
                   let uu____49356 =
                     let uu____49357 =
                       let uu____49358 = p_typ false false t  in
                       FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____49358
                        in
                     FStar_Pprint.op_Hat_Hat sep uu____49357  in
                   FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____49356  in
                 FStar_Pprint.op_Hat_Hat uid_doc uu____49355  in
               FStar_Pprint.group uu____49354) t_opt
           in
        FStar_Pprint.op_Hat_Hat uu____49349 uu____49350

and (p_letlhs :
  FStar_Pprint.document ->
    (FStar_Parser_AST.pattern * FStar_Parser_AST.term) ->
      Prims.bool -> FStar_Pprint.document)
  =
  fun kw  ->
    fun uu____49362  ->
      fun inner_let  ->
        match uu____49362 with
        | (pat,uu____49370) ->
            let uu____49371 =
              match pat.FStar_Parser_AST.pat with
              | FStar_Parser_AST.PatAscribed
                  (pat1,(t,FStar_Pervasives_Native.None )) ->
                  (pat1,
                    (FStar_Pervasives_Native.Some (t, FStar_Pprint.empty)))
              | FStar_Parser_AST.PatAscribed
                  (pat1,(t,FStar_Pervasives_Native.Some tac)) ->
                  let uu____49423 =
                    let uu____49430 =
                      let uu____49435 =
                        let uu____49436 =
                          let uu____49437 =
                            let uu____49438 = str "by"  in
                            let uu____49440 =
                              let uu____49441 = p_atomicTerm tac  in
                              FStar_Pprint.op_Hat_Hat FStar_Pprint.space
                                uu____49441
                               in
                            FStar_Pprint.op_Hat_Hat uu____49438 uu____49440
                             in
                          FStar_Pprint.op_Hat_Hat FStar_Pprint.space
                            uu____49437
                           in
                        FStar_Pprint.group uu____49436  in
                      (t, uu____49435)  in
                    FStar_Pervasives_Native.Some uu____49430  in
                  (pat1, uu____49423)
              | uu____49452 -> (pat, FStar_Pervasives_Native.None)  in
            (match uu____49371 with
             | (pat1,ascr) ->
                 (match pat1.FStar_Parser_AST.pat with
                  | FStar_Parser_AST.PatApp
                      ({
                         FStar_Parser_AST.pat = FStar_Parser_AST.PatVar
                           (lid,uu____49478);
                         FStar_Parser_AST.prange = uu____49479;_},pats)
                      ->
                      let ascr_doc =
                        match ascr with
                        | FStar_Pervasives_Native.Some (t,tac) ->
                            let uu____49496 =
                              sig_as_binders_if_possible t true  in
                            FStar_Pprint.op_Hat_Hat uu____49496 tac
                        | FStar_Pervasives_Native.None  -> FStar_Pprint.empty
                         in
                      let uu____49502 =
                        if inner_let
                        then
                          let uu____49516 = pats_as_binders_if_possible pats
                             in
                          match uu____49516 with
                          | (bs,style) ->
                              ((FStar_List.append bs [ascr_doc]), style)
                        else
                          (let uu____49539 = pats_as_binders_if_possible pats
                              in
                           match uu____49539 with
                           | (bs,style) ->
                               ((FStar_List.append bs [ascr_doc]), style))
                         in
                      (match uu____49502 with
                       | (terms,style) ->
                           let uu____49566 =
                             let uu____49567 =
                               let uu____49568 =
                                 let uu____49569 = p_lident lid  in
                                 let uu____49570 =
                                   format_sig style terms true true  in
                                 FStar_Pprint.op_Hat_Hat uu____49569
                                   uu____49570
                                  in
                               FStar_Pprint.op_Hat_Hat FStar_Pprint.space
                                 uu____49568
                                in
                             FStar_Pprint.op_Hat_Hat kw uu____49567  in
                           FStar_All.pipe_left FStar_Pprint.group uu____49566)
                  | uu____49573 ->
                      let ascr_doc =
                        match ascr with
                        | FStar_Pervasives_Native.Some (t,tac) ->
                            let uu____49581 =
                              let uu____49582 =
                                let uu____49583 =
                                  p_typ_top
                                    (Arrows
                                       ((Prims.parse_int "2"),
                                         (Prims.parse_int "2"))) false false
                                    t
                                   in
                                FStar_Pprint.op_Hat_Hat FStar_Pprint.colon
                                  uu____49583
                                 in
                              FStar_Pprint.group uu____49582  in
                            FStar_Pprint.op_Hat_Hat uu____49581 tac
                        | FStar_Pervasives_Native.None  -> FStar_Pprint.empty
                         in
                      let uu____49594 =
                        let uu____49595 =
                          let uu____49596 =
                            let uu____49597 = p_tuplePattern pat1  in
                            FStar_Pprint.op_Hat_Slash_Hat kw uu____49597  in
                          FStar_Pprint.group uu____49596  in
                        FStar_Pprint.op_Hat_Hat uu____49595 ascr_doc  in
                      FStar_Pprint.group uu____49594))

and (p_letbinding :
  FStar_Pprint.document ->
    (FStar_Parser_AST.pattern * FStar_Parser_AST.term) ->
      FStar_Pprint.document)
  =
  fun kw  ->
    fun uu____49599  ->
      match uu____49599 with
      | (pat,e) ->
          let doc_pat = p_letlhs kw (pat, e) false  in
          let uu____49608 = p_term_sep false false e  in
          (match uu____49608 with
           | (comm,doc_expr) ->
               let doc_expr1 =
                 inline_comment_or_above comm doc_expr FStar_Pprint.empty  in
               let uu____49618 =
                 let uu____49619 =
                   FStar_Pprint.op_Hat_Slash_Hat FStar_Pprint.equals
                     doc_expr1
                    in
                 FStar_Pprint.op_Hat_Slash_Hat doc_pat uu____49619  in
               let uu____49620 =
                 let uu____49621 =
                   let uu____49622 =
                     let uu____49623 =
                       let uu____49624 = jump2 doc_expr1  in
                       FStar_Pprint.op_Hat_Hat FStar_Pprint.equals
                         uu____49624
                        in
                     FStar_Pprint.group uu____49623  in
                   FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____49622  in
                 FStar_Pprint.op_Hat_Hat doc_pat uu____49621  in
               FStar_Pprint.ifflat uu____49618 uu____49620)

and (p_newEffect : FStar_Parser_AST.effect_decl -> FStar_Pprint.document) =
  fun uu___331_49625  ->
    match uu___331_49625 with
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
        let uu____49650 = p_uident uid  in
        let uu____49651 = p_binders true bs  in
        let uu____49653 =
          let uu____49654 = p_simpleTerm false false t  in
          prefix2 FStar_Pprint.equals uu____49654  in
        surround_maybe_empty (Prims.parse_int "2") (Prims.parse_int "1")
          uu____49650 uu____49651 uu____49653

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
          let uu____49669 =
            let uu____49670 =
              let uu____49671 =
                let uu____49672 = p_uident uid  in
                let uu____49673 = p_binders true bs  in
                let uu____49675 =
                  let uu____49676 = p_typ false false t  in
                  prefix2 FStar_Pprint.colon uu____49676  in
                surround_maybe_empty (Prims.parse_int "2")
                  (Prims.parse_int "1") uu____49672 uu____49673 uu____49675
                 in
              FStar_Pprint.group uu____49671  in
            let uu____49681 =
              let uu____49682 = str "with"  in
              let uu____49684 =
                let uu____49685 =
                  let uu____49686 =
                    let uu____49687 =
                      let uu____49688 =
                        let uu____49689 =
                          FStar_Pprint.op_Hat_Hat FStar_Pprint.semi
                            FStar_Pprint.space
                           in
                        FStar_Pprint.op_Hat_Hat FStar_Pprint.hardline
                          uu____49689
                         in
                      separate_map_last uu____49688 p_effectDecl eff_decls
                       in
                    FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____49687
                     in
                  FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____49686  in
                FStar_Pprint.op_Hat_Hat FStar_Pprint.hardline uu____49685  in
              FStar_Pprint.op_Hat_Hat uu____49682 uu____49684  in
            FStar_Pprint.op_Hat_Slash_Hat uu____49670 uu____49681  in
          braces_with_nesting uu____49669

and (p_effectDecl :
  Prims.bool -> FStar_Parser_AST.decl -> FStar_Pprint.document) =
  fun ps  ->
    fun d  ->
      match d.FStar_Parser_AST.d with
      | FStar_Parser_AST.Tycon
          (false
           ,uu____49693,(FStar_Parser_AST.TyconAbbrev
                         (lid,[],FStar_Pervasives_Native.None ,e),FStar_Pervasives_Native.None
                         )::[])
          ->
          let uu____49726 =
            let uu____49727 = p_lident lid  in
            let uu____49728 =
              FStar_Pprint.op_Hat_Hat FStar_Pprint.space FStar_Pprint.equals
               in
            FStar_Pprint.op_Hat_Hat uu____49727 uu____49728  in
          let uu____49729 = p_simpleTerm ps false e  in
          prefix2 uu____49726 uu____49729
      | uu____49731 ->
          let uu____49732 =
            let uu____49734 = FStar_Parser_AST.decl_to_string d  in
            FStar_Util.format1
              "Not a declaration of an effect member... or at least I hope so : %s"
              uu____49734
             in
          failwith uu____49732

and (p_subEffect : FStar_Parser_AST.lift -> FStar_Pprint.document) =
  fun lift  ->
    let lift_op_doc =
      let lifts =
        match lift.FStar_Parser_AST.lift_op with
        | FStar_Parser_AST.NonReifiableLift t -> [("lift_wp", t)]
        | FStar_Parser_AST.ReifiableLift (t1,t2) ->
            [("lift_wp", t1); ("lift", t2)]
        | FStar_Parser_AST.LiftForFree t -> [("lift", t)]  in
      let p_lift ps uu____49817 =
        match uu____49817 with
        | (kwd,t) ->
            let uu____49828 =
              let uu____49829 = str kwd  in
              let uu____49830 =
                FStar_Pprint.op_Hat_Hat FStar_Pprint.space
                  FStar_Pprint.equals
                 in
              FStar_Pprint.op_Hat_Hat uu____49829 uu____49830  in
            let uu____49831 = p_simpleTerm ps false t  in
            prefix2 uu____49828 uu____49831
         in
      separate_break_map_last FStar_Pprint.semi p_lift lifts  in
    let uu____49838 =
      let uu____49839 =
        let uu____49840 = p_quident lift.FStar_Parser_AST.msource  in
        let uu____49841 =
          let uu____49842 = str "~>"  in
          FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____49842  in
        FStar_Pprint.op_Hat_Hat uu____49840 uu____49841  in
      let uu____49844 = p_quident lift.FStar_Parser_AST.mdest  in
      prefix2 uu____49839 uu____49844  in
    let uu____49845 =
      let uu____49846 = braces_with_nesting lift_op_doc  in
      FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____49846  in
    FStar_Pprint.op_Hat_Hat uu____49838 uu____49845

and (p_qualifier : FStar_Parser_AST.qualifier -> FStar_Pprint.document) =
  fun uu___332_49847  ->
    match uu___332_49847 with
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
        let uu____49867 = p_qualifier q  in
        FStar_Pprint.op_Hat_Hat uu____49867 FStar_Pprint.hardline
    | uu____49868 ->
        let uu____49869 =
          let uu____49870 = FStar_List.map p_qualifier qs  in
          FStar_Pprint.flow break1 uu____49870  in
        FStar_Pprint.op_Hat_Hat uu____49869 FStar_Pprint.hardline

and (p_letqualifier :
  FStar_Parser_AST.let_qualifier -> FStar_Pprint.document) =
  fun uu___333_49873  ->
    match uu___333_49873 with
    | FStar_Parser_AST.Rec  ->
        let uu____49874 = str "rec"  in
        FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____49874
    | FStar_Parser_AST.NoLetQualifier  -> FStar_Pprint.empty

and (p_aqual : FStar_Parser_AST.arg_qualifier -> FStar_Pprint.document) =
  fun uu___334_49876  ->
    match uu___334_49876 with
    | FStar_Parser_AST.Implicit  -> str "#"
    | FStar_Parser_AST.Equality  -> str "$"
    | FStar_Parser_AST.Meta t ->
        let t1 =
          match t.FStar_Parser_AST.tm with
          | FStar_Parser_AST.Abs (uu____49881,e) -> e
          | uu____49887 ->
              FStar_Parser_AST.mk_term
                (FStar_Parser_AST.App
                   (t,
                     (FStar_Parser_AST.unit_const t.FStar_Parser_AST.range),
                     FStar_Parser_AST.Nothing)) t.FStar_Parser_AST.range
                FStar_Parser_AST.Expr
           in
        let uu____49888 = str "#["  in
        let uu____49890 =
          let uu____49891 = p_term false false t1  in
          let uu____49894 =
            let uu____49895 = str "]"  in
            FStar_Pprint.op_Hat_Hat uu____49895 break1  in
          FStar_Pprint.op_Hat_Hat uu____49891 uu____49894  in
        FStar_Pprint.op_Hat_Hat uu____49888 uu____49890

and (p_disjunctivePattern :
  FStar_Parser_AST.pattern -> FStar_Pprint.document) =
  fun p  ->
    match p.FStar_Parser_AST.pat with
    | FStar_Parser_AST.PatOr pats ->
        let uu____49901 =
          let uu____49902 =
            let uu____49903 =
              FStar_Pprint.op_Hat_Hat FStar_Pprint.bar FStar_Pprint.space  in
            FStar_Pprint.op_Hat_Hat break1 uu____49903  in
          FStar_Pprint.separate_map uu____49902 p_tuplePattern pats  in
        FStar_Pprint.group uu____49901
    | uu____49904 -> p_tuplePattern p

and (p_tuplePattern : FStar_Parser_AST.pattern -> FStar_Pprint.document) =
  fun p  ->
    match p.FStar_Parser_AST.pat with
    | FStar_Parser_AST.PatTuple (pats,false ) ->
        let uu____49913 =
          let uu____49914 = FStar_Pprint.op_Hat_Hat FStar_Pprint.comma break1
             in
          FStar_Pprint.separate_map uu____49914 p_constructorPattern pats  in
        FStar_Pprint.group uu____49913
    | uu____49915 -> p_constructorPattern p

and (p_constructorPattern :
  FStar_Parser_AST.pattern -> FStar_Pprint.document) =
  fun p  ->
    match p.FStar_Parser_AST.pat with
    | FStar_Parser_AST.PatApp
        ({ FStar_Parser_AST.pat = FStar_Parser_AST.PatName maybe_cons_lid;
           FStar_Parser_AST.prange = uu____49918;_},hd1::tl1::[])
        when
        FStar_Ident.lid_equals maybe_cons_lid FStar_Parser_Const.cons_lid ->
        let uu____49923 =
          FStar_Pprint.op_Hat_Hat FStar_Pprint.colon FStar_Pprint.colon  in
        let uu____49924 = p_constructorPattern hd1  in
        let uu____49925 = p_constructorPattern tl1  in
        infix0 uu____49923 uu____49924 uu____49925
    | FStar_Parser_AST.PatApp
        ({ FStar_Parser_AST.pat = FStar_Parser_AST.PatName uid;
           FStar_Parser_AST.prange = uu____49927;_},pats)
        ->
        let uu____49933 = p_quident uid  in
        let uu____49934 =
          FStar_Pprint.separate_map break1 p_atomicPattern pats  in
        prefix2 uu____49933 uu____49934
    | uu____49935 -> p_atomicPattern p

and (p_atomicPattern : FStar_Parser_AST.pattern -> FStar_Pprint.document) =
  fun p  ->
    match p.FStar_Parser_AST.pat with
    | FStar_Parser_AST.PatAscribed (pat,(t,FStar_Pervasives_Native.None )) ->
        (match ((pat.FStar_Parser_AST.pat), (t.FStar_Parser_AST.tm)) with
         | (FStar_Parser_AST.PatVar (lid,aqual),FStar_Parser_AST.Refine
            ({ FStar_Parser_AST.b = FStar_Parser_AST.Annotated (lid',t1);
               FStar_Parser_AST.brange = uu____49951;
               FStar_Parser_AST.blevel = uu____49952;
               FStar_Parser_AST.aqual = uu____49953;_},phi))
             when lid.FStar_Ident.idText = lid'.FStar_Ident.idText ->
             let uu____49962 =
               let uu____49963 = p_ident lid  in
               p_refinement aqual uu____49963 t1 phi  in
             soft_parens_with_nesting uu____49962
         | (FStar_Parser_AST.PatWild aqual,FStar_Parser_AST.Refine
            ({ FStar_Parser_AST.b = FStar_Parser_AST.NoName t1;
               FStar_Parser_AST.brange = uu____49966;
               FStar_Parser_AST.blevel = uu____49967;
               FStar_Parser_AST.aqual = uu____49968;_},phi))
             ->
             let uu____49974 =
               p_refinement aqual FStar_Pprint.underscore t1 phi  in
             soft_parens_with_nesting uu____49974
         | uu____49975 ->
             let uu____49980 =
               let uu____49981 = p_tuplePattern pat  in
               let uu____49982 =
                 let uu____49983 = p_tmEqNoRefinement t  in
                 FStar_Pprint.op_Hat_Slash_Hat FStar_Pprint.colon uu____49983
                  in
               FStar_Pprint.op_Hat_Hat uu____49981 uu____49982  in
             soft_parens_with_nesting uu____49980)
    | FStar_Parser_AST.PatList pats ->
        let uu____49987 =
          separate_break_map FStar_Pprint.semi p_tuplePattern pats  in
        FStar_Pprint.surround (Prims.parse_int "2") (Prims.parse_int "0")
          FStar_Pprint.lbracket uu____49987 FStar_Pprint.rbracket
    | FStar_Parser_AST.PatRecord pats ->
        let p_recordFieldPat uu____50006 =
          match uu____50006 with
          | (lid,pat) ->
              let uu____50013 = p_qlident lid  in
              let uu____50014 = p_tuplePattern pat  in
              infix2 FStar_Pprint.equals uu____50013 uu____50014
           in
        let uu____50015 =
          separate_break_map FStar_Pprint.semi p_recordFieldPat pats  in
        soft_braces_with_nesting uu____50015
    | FStar_Parser_AST.PatTuple (pats,true ) ->
        let uu____50027 =
          FStar_Pprint.op_Hat_Hat FStar_Pprint.lparen FStar_Pprint.bar  in
        let uu____50028 =
          separate_break_map FStar_Pprint.comma p_constructorPattern pats  in
        let uu____50029 =
          FStar_Pprint.op_Hat_Hat FStar_Pprint.bar FStar_Pprint.rparen  in
        FStar_Pprint.surround (Prims.parse_int "2") (Prims.parse_int "1")
          uu____50027 uu____50028 uu____50029
    | FStar_Parser_AST.PatTvar (tv,arg_qualifier_opt) -> p_tvar tv
    | FStar_Parser_AST.PatOp op ->
        let uu____50040 =
          let uu____50041 =
            let uu____50042 =
              let uu____50043 = FStar_Ident.text_of_id op  in str uu____50043
               in
            let uu____50045 =
              FStar_Pprint.op_Hat_Hat FStar_Pprint.space FStar_Pprint.rparen
               in
            FStar_Pprint.op_Hat_Hat uu____50042 uu____50045  in
          FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____50041  in
        FStar_Pprint.op_Hat_Hat FStar_Pprint.lparen uu____50040
    | FStar_Parser_AST.PatWild aqual ->
        let uu____50049 = FStar_Pprint.optional p_aqual aqual  in
        FStar_Pprint.op_Hat_Hat uu____50049 FStar_Pprint.underscore
    | FStar_Parser_AST.PatConst c -> p_constant c
    | FStar_Parser_AST.PatVar (lid,aqual) ->
        let uu____50057 = FStar_Pprint.optional p_aqual aqual  in
        let uu____50058 = p_lident lid  in
        FStar_Pprint.op_Hat_Hat uu____50057 uu____50058
    | FStar_Parser_AST.PatName uid -> p_quident uid
    | FStar_Parser_AST.PatOr uu____50060 -> failwith "Inner or pattern !"
    | FStar_Parser_AST.PatApp
        ({ FStar_Parser_AST.pat = FStar_Parser_AST.PatName uu____50064;
           FStar_Parser_AST.prange = uu____50065;_},uu____50066)
        ->
        let uu____50071 = p_tuplePattern p  in
        soft_parens_with_nesting uu____50071
    | FStar_Parser_AST.PatTuple (uu____50072,false ) ->
        let uu____50079 = p_tuplePattern p  in
        soft_parens_with_nesting uu____50079
    | uu____50080 ->
        let uu____50081 =
          let uu____50083 = FStar_Parser_AST.pat_to_string p  in
          FStar_Util.format1 "Invalid pattern %s" uu____50083  in
        failwith uu____50081

and (is_typ_tuple : FStar_Parser_AST.term -> Prims.bool) =
  fun e  ->
    match e.FStar_Parser_AST.tm with
    | FStar_Parser_AST.Op
        ({ FStar_Ident.idText = "*"; FStar_Ident.idRange = uu____50088;_},uu____50089)
        -> true
    | uu____50096 -> false

and (is_meta_qualifier :
  FStar_Parser_AST.arg_qualifier FStar_Pervasives_Native.option -> Prims.bool)
  =
  fun aq  ->
    match aq with
    | FStar_Pervasives_Native.Some (FStar_Parser_AST.Meta uu____50102) ->
        true
    | uu____50104 -> false

and (p_binder :
  Prims.bool -> FStar_Parser_AST.binder -> FStar_Pprint.document) =
  fun is_atomic  ->
    fun b  ->
      let uu____50111 = p_binder' is_atomic b  in
      match uu____50111 with
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
          let uu____50150 =
            let uu____50151 =
              FStar_Pprint.optional p_aqual b.FStar_Parser_AST.aqual  in
            let uu____50152 = p_lident lid  in
            FStar_Pprint.op_Hat_Hat uu____50151 uu____50152  in
          (uu____50150, FStar_Pervasives_Native.None, cat_with_colon)
      | FStar_Parser_AST.TVariable lid ->
          let uu____50158 = p_lident lid  in
          (uu____50158, FStar_Pervasives_Native.None, cat_with_colon)
      | FStar_Parser_AST.Annotated (lid,t) ->
          let uu____50165 =
            match t.FStar_Parser_AST.tm with
            | FStar_Parser_AST.Refine
                ({ FStar_Parser_AST.b = FStar_Parser_AST.Annotated (lid',t1);
                   FStar_Parser_AST.brange = uu____50176;
                   FStar_Parser_AST.blevel = uu____50177;
                   FStar_Parser_AST.aqual = uu____50178;_},phi)
                when lid.FStar_Ident.idText = lid'.FStar_Ident.idText ->
                let uu____50183 = p_lident lid  in
                p_refinement' b.FStar_Parser_AST.aqual uu____50183 t1 phi
            | uu____50184 ->
                let t' =
                  let uu____50186 = is_typ_tuple t  in
                  if uu____50186
                  then
                    let uu____50189 = p_tmFormula t  in
                    soft_parens_with_nesting uu____50189
                  else p_tmFormula t  in
                let uu____50192 =
                  let uu____50193 =
                    FStar_Pprint.optional p_aqual b.FStar_Parser_AST.aqual
                     in
                  let uu____50194 = p_lident lid  in
                  FStar_Pprint.op_Hat_Hat uu____50193 uu____50194  in
                (uu____50192, t')
             in
          (match uu____50165 with
           | (b',t') ->
               let catf =
                 let uu____50212 =
                   is_atomic || (is_meta_qualifier b.FStar_Parser_AST.aqual)
                    in
                 if uu____50212
                 then
                   fun x  ->
                     fun y  ->
                       let uu____50219 =
                         let uu____50220 =
                           let uu____50221 = cat_with_colon x y  in
                           FStar_Pprint.op_Hat_Hat uu____50221
                             FStar_Pprint.rparen
                            in
                         FStar_Pprint.op_Hat_Hat FStar_Pprint.lparen
                           uu____50220
                          in
                       FStar_Pprint.group uu____50219
                 else
                   (fun x  ->
                      fun y  ->
                        let uu____50226 = cat_with_colon x y  in
                        FStar_Pprint.group uu____50226)
                  in
               (b', (FStar_Pervasives_Native.Some t'), catf))
      | FStar_Parser_AST.TAnnotated uu____50235 ->
          failwith "Is this still used ?"
      | FStar_Parser_AST.NoName t ->
          (match t.FStar_Parser_AST.tm with
           | FStar_Parser_AST.Refine
               ({ FStar_Parser_AST.b = FStar_Parser_AST.NoName t1;
                  FStar_Parser_AST.brange = uu____50263;
                  FStar_Parser_AST.blevel = uu____50264;
                  FStar_Parser_AST.aqual = uu____50265;_},phi)
               ->
               let uu____50269 =
                 p_refinement' b.FStar_Parser_AST.aqual
                   FStar_Pprint.underscore t1 phi
                  in
               (match uu____50269 with
                | (b',t') ->
                    (b', (FStar_Pervasives_Native.Some t'), cat_with_colon))
           | uu____50290 ->
               if is_atomic
               then
                 let uu____50302 = p_atomicTerm t  in
                 (uu____50302, FStar_Pervasives_Native.None, cat_with_colon)
               else
                 (let uu____50309 = p_appTerm t  in
                  (uu____50309, FStar_Pervasives_Native.None, cat_with_colon)))

and (p_refinement :
  FStar_Parser_AST.arg_qualifier FStar_Pervasives_Native.option ->
    FStar_Pprint.document ->
      FStar_Parser_AST.term -> FStar_Parser_AST.term -> FStar_Pprint.document)
  =
  fun aqual_opt  ->
    fun binder  ->
      fun t  ->
        fun phi  ->
          let uu____50320 = p_refinement' aqual_opt binder t phi  in
          match uu____50320 with | (b,typ) -> cat_with_colon b typ

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
            | FStar_Parser_AST.Construct uu____50336 -> false
            | FStar_Parser_AST.App uu____50348 -> false
            | FStar_Parser_AST.Op uu____50356 -> false
            | uu____50364 -> true  in
          let uu____50366 = p_noSeqTerm false false phi  in
          match uu____50366 with
          | (comm,phi1) ->
              let phi2 =
                if comm = FStar_Pprint.empty
                then phi1
                else
                  (let uu____50383 =
                     FStar_Pprint.op_Hat_Hat FStar_Pprint.hardline phi1  in
                   FStar_Pprint.op_Hat_Hat comm uu____50383)
                 in
              let jump_break =
                if is_t_atomic
                then (Prims.parse_int "0")
                else (Prims.parse_int "1")  in
              let uu____50392 =
                let uu____50393 = FStar_Pprint.optional p_aqual aqual_opt  in
                FStar_Pprint.op_Hat_Hat uu____50393 binder  in
              let uu____50394 =
                let uu____50395 = p_appTerm t  in
                let uu____50396 =
                  let uu____50397 =
                    let uu____50398 =
                      let uu____50399 = soft_braces_with_nesting_tight phi2
                         in
                      let uu____50400 = soft_braces_with_nesting phi2  in
                      FStar_Pprint.ifflat uu____50399 uu____50400  in
                    FStar_Pprint.group uu____50398  in
                  FStar_Pprint.jump (Prims.parse_int "2") jump_break
                    uu____50397
                   in
                FStar_Pprint.op_Hat_Hat uu____50395 uu____50396  in
              (uu____50392, uu____50394)

and (p_binders_list :
  Prims.bool ->
    FStar_Parser_AST.binder Prims.list -> FStar_Pprint.document Prims.list)
  = fun is_atomic  -> fun bs  -> FStar_List.map (p_binder is_atomic) bs

and (p_binders :
  Prims.bool -> FStar_Parser_AST.binder Prims.list -> FStar_Pprint.document)
  =
  fun is_atomic  ->
    fun bs  ->
      let uu____50414 = p_binders_list is_atomic bs  in
      separate_or_flow break1 uu____50414

and (text_of_id_or_underscore : FStar_Ident.ident -> FStar_Pprint.document) =
  fun lid  ->
    let uu____50418 =
      (FStar_Util.starts_with lid.FStar_Ident.idText
         FStar_Ident.reserved_prefix)
        &&
        (let uu____50421 = FStar_Options.print_real_names ()  in
         Prims.op_Negation uu____50421)
       in
    if uu____50418
    then FStar_Pprint.underscore
    else (let uu____50426 = FStar_Ident.text_of_id lid  in str uu____50426)

and (text_of_lid_or_underscore : FStar_Ident.lident -> FStar_Pprint.document)
  =
  fun lid  ->
    let uu____50429 =
      (FStar_Util.starts_with (lid.FStar_Ident.ident).FStar_Ident.idText
         FStar_Ident.reserved_prefix)
        &&
        (let uu____50432 = FStar_Options.print_real_names ()  in
         Prims.op_Negation uu____50432)
       in
    if uu____50429
    then FStar_Pprint.underscore
    else (let uu____50437 = FStar_Ident.text_of_lid lid  in str uu____50437)

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
          let uu____50458 = FStar_Pprint.op_Hat_Hat doc1 sep  in
          FStar_Pprint.group uu____50458
        else
          (let uu____50461 =
             let uu____50462 =
               let uu____50463 =
                 let uu____50464 =
                   let uu____50465 = FStar_Pprint.op_Hat_Hat break1 comm  in
                   FStar_Pprint.op_Hat_Hat sep uu____50465  in
                 FStar_Pprint.op_Hat_Hat doc1 uu____50464  in
               FStar_Pprint.group uu____50463  in
             let uu____50466 =
               let uu____50467 =
                 let uu____50468 = FStar_Pprint.op_Hat_Hat doc1 sep  in
                 FStar_Pprint.op_Hat_Hat FStar_Pprint.hardline uu____50468
                  in
               FStar_Pprint.op_Hat_Hat comm uu____50467  in
             FStar_Pprint.ifflat uu____50462 uu____50466  in
           FStar_All.pipe_left FStar_Pprint.group uu____50461)

and (p_term :
  Prims.bool -> Prims.bool -> FStar_Parser_AST.term -> FStar_Pprint.document)
  =
  fun ps  ->
    fun pb  ->
      fun e  ->
        match e.FStar_Parser_AST.tm with
        | FStar_Parser_AST.Seq (e1,e2) ->
            let uu____50476 = p_noSeqTerm true false e1  in
            (match uu____50476 with
             | (comm,t1) ->
                 let uu____50485 =
                   inline_comment_or_above comm t1 FStar_Pprint.semi  in
                 let uu____50486 =
                   let uu____50487 = p_term ps pb e2  in
                   FStar_Pprint.op_Hat_Hat FStar_Pprint.hardline uu____50487
                    in
                 FStar_Pprint.op_Hat_Hat uu____50485 uu____50486)
        | FStar_Parser_AST.Bind (x,e1,e2) ->
            let uu____50491 =
              let uu____50492 =
                let uu____50493 =
                  let uu____50494 = p_lident x  in
                  let uu____50495 =
                    FStar_Pprint.op_Hat_Hat FStar_Pprint.space
                      FStar_Pprint.long_left_arrow
                     in
                  FStar_Pprint.op_Hat_Hat uu____50494 uu____50495  in
                let uu____50496 =
                  let uu____50497 = p_noSeqTermAndComment true false e1  in
                  let uu____50500 =
                    FStar_Pprint.op_Hat_Hat FStar_Pprint.space
                      FStar_Pprint.semi
                     in
                  FStar_Pprint.op_Hat_Hat uu____50497 uu____50500  in
                op_Hat_Slash_Plus_Hat uu____50493 uu____50496  in
              FStar_Pprint.group uu____50492  in
            let uu____50501 = p_term ps pb e2  in
            FStar_Pprint.op_Hat_Slash_Hat uu____50491 uu____50501
        | uu____50502 ->
            let uu____50503 = p_noSeqTermAndComment ps pb e  in
            FStar_Pprint.group uu____50503

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
            let uu____50515 = p_noSeqTerm true false e1  in
            (match uu____50515 with
             | (comm,t1) ->
                 let uu____50528 =
                   let uu____50529 =
                     let uu____50530 =
                       FStar_Pprint.op_Hat_Hat t1 FStar_Pprint.semi  in
                     FStar_Pprint.group uu____50530  in
                   let uu____50531 =
                     let uu____50532 = p_term ps pb e2  in
                     FStar_Pprint.op_Hat_Hat FStar_Pprint.hardline
                       uu____50532
                      in
                   FStar_Pprint.op_Hat_Hat uu____50529 uu____50531  in
                 (comm, uu____50528))
        | FStar_Parser_AST.Bind (x,e1,e2) ->
            let uu____50536 =
              let uu____50537 =
                let uu____50538 =
                  let uu____50539 =
                    let uu____50540 = p_lident x  in
                    let uu____50541 =
                      FStar_Pprint.op_Hat_Hat FStar_Pprint.space
                        FStar_Pprint.long_left_arrow
                       in
                    FStar_Pprint.op_Hat_Hat uu____50540 uu____50541  in
                  let uu____50542 =
                    let uu____50543 = p_noSeqTermAndComment true false e1  in
                    let uu____50546 =
                      FStar_Pprint.op_Hat_Hat FStar_Pprint.space
                        FStar_Pprint.semi
                       in
                    FStar_Pprint.op_Hat_Hat uu____50543 uu____50546  in
                  op_Hat_Slash_Plus_Hat uu____50539 uu____50542  in
                FStar_Pprint.group uu____50538  in
              let uu____50547 = p_term ps pb e2  in
              FStar_Pprint.op_Hat_Slash_Hat uu____50537 uu____50547  in
            (FStar_Pprint.empty, uu____50536)
        | uu____50548 -> p_noSeqTerm ps pb e

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
            let uu____50568 =
              let uu____50569 = p_tmIff e1  in
              let uu____50570 =
                let uu____50571 =
                  let uu____50572 = p_typ ps pb t  in
                  FStar_Pprint.op_Hat_Slash_Hat FStar_Pprint.colon
                    uu____50572
                   in
                FStar_Pprint.op_Hat_Hat FStar_Pprint.langle uu____50571  in
              FStar_Pprint.op_Hat_Slash_Hat uu____50569 uu____50570  in
            FStar_Pprint.group uu____50568
        | FStar_Parser_AST.Ascribed (e1,t,FStar_Pervasives_Native.Some tac)
            ->
            let uu____50578 =
              let uu____50579 = p_tmIff e1  in
              let uu____50580 =
                let uu____50581 =
                  let uu____50582 =
                    let uu____50583 = p_typ false false t  in
                    let uu____50586 =
                      let uu____50587 = str "by"  in
                      let uu____50589 = p_typ ps pb tac  in
                      FStar_Pprint.op_Hat_Slash_Hat uu____50587 uu____50589
                       in
                    FStar_Pprint.op_Hat_Slash_Hat uu____50583 uu____50586  in
                  FStar_Pprint.op_Hat_Slash_Hat FStar_Pprint.colon
                    uu____50582
                   in
                FStar_Pprint.op_Hat_Hat FStar_Pprint.langle uu____50581  in
              FStar_Pprint.op_Hat_Slash_Hat uu____50579 uu____50580  in
            FStar_Pprint.group uu____50578
        | FStar_Parser_AST.Op
            ({ FStar_Ident.idText = ".()<-";
               FStar_Ident.idRange = uu____50590;_},e1::e2::e3::[])
            ->
            let uu____50597 =
              let uu____50598 =
                let uu____50599 =
                  let uu____50600 = p_atomicTermNotQUident e1  in
                  let uu____50601 =
                    let uu____50602 =
                      let uu____50603 =
                        let uu____50604 = p_term false false e2  in
                        soft_parens_with_nesting uu____50604  in
                      let uu____50607 =
                        FStar_Pprint.op_Hat_Hat FStar_Pprint.space
                          FStar_Pprint.larrow
                         in
                      FStar_Pprint.op_Hat_Hat uu____50603 uu____50607  in
                    FStar_Pprint.op_Hat_Hat FStar_Pprint.dot uu____50602  in
                  FStar_Pprint.op_Hat_Hat uu____50600 uu____50601  in
                FStar_Pprint.group uu____50599  in
              let uu____50608 =
                let uu____50609 = p_noSeqTermAndComment ps pb e3  in
                jump2 uu____50609  in
              FStar_Pprint.op_Hat_Hat uu____50598 uu____50608  in
            FStar_Pprint.group uu____50597
        | FStar_Parser_AST.Op
            ({ FStar_Ident.idText = ".[]<-";
               FStar_Ident.idRange = uu____50610;_},e1::e2::e3::[])
            ->
            let uu____50617 =
              let uu____50618 =
                let uu____50619 =
                  let uu____50620 = p_atomicTermNotQUident e1  in
                  let uu____50621 =
                    let uu____50622 =
                      let uu____50623 =
                        let uu____50624 = p_term false false e2  in
                        soft_brackets_with_nesting uu____50624  in
                      let uu____50627 =
                        FStar_Pprint.op_Hat_Hat FStar_Pprint.space
                          FStar_Pprint.larrow
                         in
                      FStar_Pprint.op_Hat_Hat uu____50623 uu____50627  in
                    FStar_Pprint.op_Hat_Hat FStar_Pprint.dot uu____50622  in
                  FStar_Pprint.op_Hat_Hat uu____50620 uu____50621  in
                FStar_Pprint.group uu____50619  in
              let uu____50628 =
                let uu____50629 = p_noSeqTermAndComment ps pb e3  in
                jump2 uu____50629  in
              FStar_Pprint.op_Hat_Hat uu____50618 uu____50628  in
            FStar_Pprint.group uu____50617
        | FStar_Parser_AST.Requires (e1,wtf) ->
            let uu____50639 =
              let uu____50640 = str "requires"  in
              let uu____50642 = p_typ ps pb e1  in
              FStar_Pprint.op_Hat_Slash_Hat uu____50640 uu____50642  in
            FStar_Pprint.group uu____50639
        | FStar_Parser_AST.Ensures (e1,wtf) ->
            let uu____50652 =
              let uu____50653 = str "ensures"  in
              let uu____50655 = p_typ ps pb e1  in
              FStar_Pprint.op_Hat_Slash_Hat uu____50653 uu____50655  in
            FStar_Pprint.group uu____50652
        | FStar_Parser_AST.Attributes es ->
            let uu____50659 =
              let uu____50660 = str "attributes"  in
              let uu____50662 =
                FStar_Pprint.separate_map break1 p_atomicTerm es  in
              FStar_Pprint.op_Hat_Slash_Hat uu____50660 uu____50662  in
            FStar_Pprint.group uu____50659
        | FStar_Parser_AST.If (e1,e2,e3) ->
            if is_unit e3
            then
              let uu____50667 =
                let uu____50668 =
                  let uu____50669 = str "if"  in
                  let uu____50671 = p_noSeqTermAndComment false false e1  in
                  op_Hat_Slash_Plus_Hat uu____50669 uu____50671  in
                let uu____50674 =
                  let uu____50675 = str "then"  in
                  let uu____50677 = p_noSeqTermAndComment ps pb e2  in
                  op_Hat_Slash_Plus_Hat uu____50675 uu____50677  in
                FStar_Pprint.op_Hat_Slash_Hat uu____50668 uu____50674  in
              FStar_Pprint.group uu____50667
            else
              (let e2_doc =
                 match e2.FStar_Parser_AST.tm with
                 | FStar_Parser_AST.If (uu____50681,uu____50682,e31) when
                     is_unit e31 ->
                     let uu____50684 = p_noSeqTermAndComment false false e2
                        in
                     soft_parens_with_nesting uu____50684
                 | uu____50687 -> p_noSeqTermAndComment false false e2  in
               let uu____50690 =
                 let uu____50691 =
                   let uu____50692 = str "if"  in
                   let uu____50694 = p_noSeqTermAndComment false false e1  in
                   op_Hat_Slash_Plus_Hat uu____50692 uu____50694  in
                 let uu____50697 =
                   let uu____50698 =
                     let uu____50699 = str "then"  in
                     op_Hat_Slash_Plus_Hat uu____50699 e2_doc  in
                   let uu____50701 =
                     let uu____50702 = str "else"  in
                     let uu____50704 = p_noSeqTermAndComment ps pb e3  in
                     op_Hat_Slash_Plus_Hat uu____50702 uu____50704  in
                   FStar_Pprint.op_Hat_Slash_Hat uu____50698 uu____50701  in
                 FStar_Pprint.op_Hat_Slash_Hat uu____50691 uu____50697  in
               FStar_Pprint.group uu____50690)
        | FStar_Parser_AST.TryWith (e1,branches) ->
            let uu____50727 =
              let uu____50728 =
                let uu____50729 =
                  let uu____50730 = str "try"  in
                  let uu____50732 = p_noSeqTermAndComment false false e1  in
                  prefix2 uu____50730 uu____50732  in
                let uu____50735 =
                  let uu____50736 = str "with"  in
                  let uu____50738 =
                    separate_map_last FStar_Pprint.hardline p_patternBranch
                      branches
                     in
                  FStar_Pprint.op_Hat_Slash_Hat uu____50736 uu____50738  in
                FStar_Pprint.op_Hat_Slash_Hat uu____50729 uu____50735  in
              FStar_Pprint.group uu____50728  in
            let uu____50747 = paren_if (ps || pb)  in uu____50747 uu____50727
        | FStar_Parser_AST.Match (e1,branches) ->
            let uu____50774 =
              let uu____50775 =
                let uu____50776 =
                  let uu____50777 = str "match"  in
                  let uu____50779 = p_noSeqTermAndComment false false e1  in
                  let uu____50782 = str "with"  in
                  FStar_Pprint.surround (Prims.parse_int "2")
                    (Prims.parse_int "1") uu____50777 uu____50779 uu____50782
                   in
                let uu____50786 =
                  separate_map_last FStar_Pprint.hardline p_patternBranch
                    branches
                   in
                FStar_Pprint.op_Hat_Slash_Hat uu____50776 uu____50786  in
              FStar_Pprint.group uu____50775  in
            let uu____50795 = paren_if (ps || pb)  in uu____50795 uu____50774
        | FStar_Parser_AST.LetOpen (uid,e1) ->
            let uu____50802 =
              let uu____50803 =
                let uu____50804 =
                  let uu____50805 = str "let open"  in
                  let uu____50807 = p_quident uid  in
                  let uu____50808 = str "in"  in
                  FStar_Pprint.surround (Prims.parse_int "2")
                    (Prims.parse_int "1") uu____50805 uu____50807 uu____50808
                   in
                let uu____50812 = p_term false pb e1  in
                FStar_Pprint.op_Hat_Slash_Hat uu____50804 uu____50812  in
              FStar_Pprint.group uu____50803  in
            let uu____50814 = paren_if ps  in uu____50814 uu____50802
        | FStar_Parser_AST.Let (q,lbs,e1) ->
            let p_lb q1 uu____50879 is_last =
              match uu____50879 with
              | (a,(pat,e2)) ->
                  let attrs = p_attrs_opt a  in
                  let doc_let_or_and =
                    match q1 with
                    | FStar_Pervasives_Native.Some (FStar_Parser_AST.Rec ) ->
                        let uu____50913 =
                          let uu____50914 = str "let"  in
                          let uu____50916 = str "rec"  in
                          FStar_Pprint.op_Hat_Slash_Hat uu____50914
                            uu____50916
                           in
                        FStar_Pprint.group uu____50913
                    | FStar_Pervasives_Native.Some
                        (FStar_Parser_AST.NoLetQualifier ) -> str "let"
                    | uu____50919 -> str "and"  in
                  let doc_pat = p_letlhs doc_let_or_and (pat, e2) true  in
                  let uu____50925 = p_term_sep false false e2  in
                  (match uu____50925 with
                   | (comm,doc_expr) ->
                       let doc_expr1 =
                         inline_comment_or_above comm doc_expr
                           FStar_Pprint.empty
                          in
                       let uu____50935 =
                         if is_last
                         then
                           let uu____50937 =
                             FStar_Pprint.flow break1
                               [doc_pat; FStar_Pprint.equals]
                              in
                           let uu____50938 = str "in"  in
                           FStar_Pprint.surround (Prims.parse_int "2")
                             (Prims.parse_int "1") uu____50937 doc_expr1
                             uu____50938
                         else
                           (let uu____50944 =
                              FStar_Pprint.flow break1
                                [doc_pat; FStar_Pprint.equals; doc_expr1]
                               in
                            FStar_Pprint.hang (Prims.parse_int "2")
                              uu____50944)
                          in
                       FStar_Pprint.op_Hat_Hat attrs uu____50935)
               in
            let l = FStar_List.length lbs  in
            let lbs_docs =
              FStar_List.mapi
                (fun i  ->
                   fun lb  ->
                     if i = (Prims.parse_int "0")
                     then
                       let uu____50995 =
                         p_lb (FStar_Pervasives_Native.Some q) lb
                           (i = (l - (Prims.parse_int "1")))
                          in
                       FStar_Pprint.group uu____50995
                     else
                       (let uu____51006 =
                          p_lb FStar_Pervasives_Native.None lb
                            (i = (l - (Prims.parse_int "1")))
                           in
                        FStar_Pprint.group uu____51006)) lbs
               in
            let lbs_doc =
              let uu____51016 = FStar_Pprint.separate break1 lbs_docs  in
              FStar_Pprint.group uu____51016  in
            let uu____51017 =
              let uu____51018 =
                let uu____51019 =
                  let uu____51020 = p_term false pb e1  in
                  FStar_Pprint.op_Hat_Hat FStar_Pprint.hardline uu____51020
                   in
                FStar_Pprint.op_Hat_Hat lbs_doc uu____51019  in
              FStar_Pprint.group uu____51018  in
            let uu____51022 = paren_if ps  in uu____51022 uu____51017
        | FStar_Parser_AST.Abs
            ({ FStar_Parser_AST.pat = FStar_Parser_AST.PatVar (x,typ_opt);
               FStar_Parser_AST.prange = uu____51029;_}::[],{
                                                              FStar_Parser_AST.tm
                                                                =
                                                                FStar_Parser_AST.Match
                                                                (maybe_x,branches);
                                                              FStar_Parser_AST.range
                                                                = uu____51032;
                                                              FStar_Parser_AST.level
                                                                = uu____51033;_})
            when matches_var maybe_x x ->
            let uu____51060 =
              let uu____51061 =
                let uu____51062 = str "function"  in
                let uu____51064 =
                  separate_map_last FStar_Pprint.hardline p_patternBranch
                    branches
                   in
                FStar_Pprint.op_Hat_Slash_Hat uu____51062 uu____51064  in
              FStar_Pprint.group uu____51061  in
            let uu____51073 = paren_if (ps || pb)  in uu____51073 uu____51060
        | FStar_Parser_AST.Quote (e1,FStar_Parser_AST.Dynamic ) ->
            let uu____51079 =
              let uu____51080 = str "quote"  in
              let uu____51082 = p_noSeqTermAndComment ps pb e1  in
              FStar_Pprint.op_Hat_Slash_Hat uu____51080 uu____51082  in
            FStar_Pprint.group uu____51079
        | FStar_Parser_AST.Quote (e1,FStar_Parser_AST.Static ) ->
            let uu____51084 =
              let uu____51085 = str "`"  in
              let uu____51087 = p_noSeqTermAndComment ps pb e1  in
              FStar_Pprint.op_Hat_Hat uu____51085 uu____51087  in
            FStar_Pprint.group uu____51084
        | FStar_Parser_AST.VQuote e1 ->
            let uu____51089 =
              let uu____51090 = str "`%"  in
              let uu____51092 = p_noSeqTermAndComment ps pb e1  in
              FStar_Pprint.op_Hat_Hat uu____51090 uu____51092  in
            FStar_Pprint.group uu____51089
        | FStar_Parser_AST.Antiquote
            {
              FStar_Parser_AST.tm = FStar_Parser_AST.Quote
                (e1,FStar_Parser_AST.Dynamic );
              FStar_Parser_AST.range = uu____51094;
              FStar_Parser_AST.level = uu____51095;_}
            ->
            let uu____51096 =
              let uu____51097 = str "`@"  in
              let uu____51099 = p_noSeqTermAndComment ps pb e1  in
              FStar_Pprint.op_Hat_Hat uu____51097 uu____51099  in
            FStar_Pprint.group uu____51096
        | FStar_Parser_AST.Antiquote e1 ->
            let uu____51101 =
              let uu____51102 = str "`#"  in
              let uu____51104 = p_noSeqTermAndComment ps pb e1  in
              FStar_Pprint.op_Hat_Hat uu____51102 uu____51104  in
            FStar_Pprint.group uu____51101
        | FStar_Parser_AST.CalcProof (rel,init1,steps) ->
            let head1 =
              let uu____51113 = str "calc"  in
              let uu____51115 =
                let uu____51116 =
                  let uu____51117 = p_noSeqTermAndComment false false rel  in
                  let uu____51120 =
                    FStar_Pprint.op_Hat_Hat FStar_Pprint.space
                      FStar_Pprint.lbrace
                     in
                  FStar_Pprint.op_Hat_Hat uu____51117 uu____51120  in
                FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____51116  in
              FStar_Pprint.op_Hat_Hat uu____51113 uu____51115  in
            let bot = FStar_Pprint.rbrace  in
            let uu____51122 =
              FStar_Pprint.op_Hat_Hat FStar_Pprint.hardline bot  in
            let uu____51123 =
              let uu____51124 =
                let uu____51125 =
                  let uu____51126 = p_noSeqTermAndComment false false init1
                     in
                  let uu____51129 =
                    let uu____51130 = str ";"  in
                    let uu____51132 =
                      let uu____51133 =
                        separate_map_last FStar_Pprint.hardline p_calcStep
                          steps
                         in
                      FStar_Pprint.op_Hat_Hat FStar_Pprint.hardline
                        uu____51133
                       in
                    FStar_Pprint.op_Hat_Hat uu____51130 uu____51132  in
                  FStar_Pprint.op_Hat_Hat uu____51126 uu____51129  in
                FStar_Pprint.op_Hat_Hat FStar_Pprint.hardline uu____51125  in
              FStar_All.pipe_left (FStar_Pprint.nest (Prims.parse_int "2"))
                uu____51124
               in
            FStar_Pprint.enclose head1 uu____51122 uu____51123
        | uu____51135 -> p_typ ps pb e

and (p_calcStep :
  Prims.bool -> FStar_Parser_AST.calc_step -> FStar_Pprint.document) =
  fun uu____51136  ->
    fun uu____51137  ->
      match uu____51137 with
      | FStar_Parser_AST.CalcStep (rel,just,next) ->
          let uu____51142 =
            let uu____51143 = p_noSeqTermAndComment false false rel  in
            let uu____51146 =
              let uu____51147 =
                let uu____51148 =
                  let uu____51149 =
                    let uu____51150 = p_noSeqTermAndComment false false just
                       in
                    let uu____51153 =
                      let uu____51154 =
                        let uu____51155 =
                          let uu____51156 =
                            let uu____51157 =
                              p_noSeqTermAndComment false false next  in
                            let uu____51160 = str ";"  in
                            FStar_Pprint.op_Hat_Hat uu____51157 uu____51160
                             in
                          FStar_Pprint.op_Hat_Hat FStar_Pprint.hardline
                            uu____51156
                           in
                        FStar_Pprint.op_Hat_Hat FStar_Pprint.rbrace
                          uu____51155
                         in
                      FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____51154
                       in
                    FStar_Pprint.op_Hat_Hat uu____51150 uu____51153  in
                  FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____51149  in
                FStar_Pprint.op_Hat_Hat FStar_Pprint.lbrace uu____51148  in
              FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____51147  in
            FStar_Pprint.op_Hat_Hat uu____51143 uu____51146  in
          FStar_Pprint.group uu____51142

and (p_attrs_opt :
  FStar_Parser_AST.term Prims.list FStar_Pervasives_Native.option ->
    FStar_Pprint.document)
  =
  fun uu___335_51162  ->
    match uu___335_51162 with
    | FStar_Pervasives_Native.None  -> FStar_Pprint.empty
    | FStar_Pervasives_Native.Some terms ->
        let uu____51174 =
          let uu____51175 = str "[@"  in
          let uu____51177 =
            let uu____51178 =
              FStar_Pprint.separate_map break1 p_atomicTerm terms  in
            let uu____51179 = str "]"  in
            FStar_Pprint.op_Hat_Slash_Hat uu____51178 uu____51179  in
          FStar_Pprint.op_Hat_Slash_Hat uu____51175 uu____51177  in
        FStar_Pprint.group uu____51174

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
                 let uu____51216 =
                   let uu____51217 =
                     let uu____51218 = p_quantifier e  in
                     FStar_Pprint.op_Hat_Hat uu____51218 FStar_Pprint.space
                      in
                   FStar_Pprint.soft_surround (Prims.parse_int "2")
                     (Prims.parse_int "0") uu____51217 binders_doc
                     FStar_Pprint.dot
                    in
                 prefix2 uu____51216 term_doc
             | pats ->
                 let uu____51226 =
                   let uu____51227 =
                     let uu____51228 =
                       let uu____51229 =
                         let uu____51230 = p_quantifier e  in
                         FStar_Pprint.op_Hat_Hat uu____51230
                           FStar_Pprint.space
                          in
                       FStar_Pprint.soft_surround (Prims.parse_int "2")
                         (Prims.parse_int "0") uu____51229 binders_doc
                         FStar_Pprint.dot
                        in
                     let uu____51233 = p_trigger trigger  in
                     prefix2 uu____51228 uu____51233  in
                   FStar_Pprint.group uu____51227  in
                 prefix2 uu____51226 term_doc)
        | FStar_Parser_AST.QExists (bs,trigger,e1) ->
            let binders_doc = p_binders true bs  in
            let term_doc = p_noSeqTermAndComment ps pb e1  in
            (match trigger with
             | [] ->
                 let uu____51254 =
                   let uu____51255 =
                     let uu____51256 = p_quantifier e  in
                     FStar_Pprint.op_Hat_Hat uu____51256 FStar_Pprint.space
                      in
                   FStar_Pprint.soft_surround (Prims.parse_int "2")
                     (Prims.parse_int "0") uu____51255 binders_doc
                     FStar_Pprint.dot
                    in
                 prefix2 uu____51254 term_doc
             | pats ->
                 let uu____51264 =
                   let uu____51265 =
                     let uu____51266 =
                       let uu____51267 =
                         let uu____51268 = p_quantifier e  in
                         FStar_Pprint.op_Hat_Hat uu____51268
                           FStar_Pprint.space
                          in
                       FStar_Pprint.soft_surround (Prims.parse_int "2")
                         (Prims.parse_int "0") uu____51267 binders_doc
                         FStar_Pprint.dot
                        in
                     let uu____51271 = p_trigger trigger  in
                     prefix2 uu____51266 uu____51271  in
                   FStar_Pprint.group uu____51265  in
                 prefix2 uu____51264 term_doc)
        | uu____51272 -> p_simpleTerm ps pb e

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
      let uu____51293 = all_binders_annot t  in
      if uu____51293
      then
        let uu____51296 =
          p_typ_top
            (Binders ((Prims.parse_int "4"), (Prims.parse_int "0"), true))
            false false t
           in
        FStar_Pprint.op_Hat_Hat s uu____51296
      else
        (let uu____51307 =
           let uu____51308 =
             let uu____51309 =
               p_typ_top
                 (Arrows ((Prims.parse_int "2"), (Prims.parse_int "2")))
                 false false t
                in
             FStar_Pprint.op_Hat_Hat s uu____51309  in
           FStar_Pprint.op_Hat_Hat FStar_Pprint.colon uu____51308  in
         FStar_Pprint.group uu____51307)

and (collapse_pats :
  (FStar_Pprint.document * FStar_Pprint.document) Prims.list ->
    FStar_Pprint.document Prims.list)
  =
  fun pats  ->
    let fold_fun bs x =
      let uu____51368 = x  in
      match uu____51368 with
      | (b1,t1) ->
          (match bs with
           | [] -> [([b1], t1)]
           | hd1::tl1 ->
               let uu____51433 = hd1  in
               (match uu____51433 with
                | (b2s,t2) ->
                    if t1 = t2
                    then ((FStar_List.append b2s [b1]), t1) :: tl1
                    else ([b1], t1) :: hd1 :: tl1))
       in
    let p_collapsed_binder cb =
      let uu____51505 = cb  in
      match uu____51505 with
      | (bs,typ) ->
          (match bs with
           | [] -> failwith "Impossible"
           | b::[] -> cat_with_colon b typ
           | hd1::tl1 ->
               let uu____51524 =
                 FStar_List.fold_left
                   (fun x  ->
                      fun y  ->
                        let uu____51530 =
                          FStar_Pprint.op_Hat_Hat FStar_Pprint.space y  in
                        FStar_Pprint.op_Hat_Hat x uu____51530) hd1 tl1
                  in
               cat_with_colon uu____51524 typ)
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
                 FStar_Parser_AST.brange = uu____51609;
                 FStar_Parser_AST.blevel = uu____51610;
                 FStar_Parser_AST.aqual = uu____51611;_},phi))
               when lid.FStar_Ident.idText = lid'.FStar_Ident.idText ->
               let uu____51620 =
                 let uu____51625 = p_ident lid  in
                 p_refinement' aqual uu____51625 t1 phi  in
               FStar_Pervasives_Native.Some uu____51620
           | (FStar_Parser_AST.PatVar (lid,aqual),uu____51632) ->
               let uu____51637 =
                 let uu____51642 =
                   let uu____51643 = FStar_Pprint.optional p_aqual aqual  in
                   let uu____51644 = p_ident lid  in
                   FStar_Pprint.op_Hat_Hat uu____51643 uu____51644  in
                 let uu____51645 = p_tmEqNoRefinement t  in
                 (uu____51642, uu____51645)  in
               FStar_Pervasives_Native.Some uu____51637
           | uu____51650 -> FStar_Pervasives_Native.None)
      | uu____51659 -> FStar_Pervasives_Native.None  in
    let all_unbound p =
      match p.FStar_Parser_AST.pat with
      | FStar_Parser_AST.PatAscribed uu____51672 -> false
      | uu____51684 -> true  in
    let uu____51686 = map_if_all all_binders pats  in
    match uu____51686 with
    | FStar_Pervasives_Native.Some bs ->
        let uu____51718 = collapse_pats bs  in
        (uu____51718,
          (Binders ((Prims.parse_int "4"), (Prims.parse_int "0"), true)))
    | FStar_Pervasives_Native.None  ->
        let uu____51735 = FStar_List.map p_atomicPattern pats  in
        (uu____51735,
          (Binders ((Prims.parse_int "4"), (Prims.parse_int "0"), false)))

and (p_quantifier : FStar_Parser_AST.term -> FStar_Pprint.document) =
  fun e  ->
    match e.FStar_Parser_AST.tm with
    | FStar_Parser_AST.QForall uu____51747 -> str "forall"
    | FStar_Parser_AST.QExists uu____51761 -> str "exists"
    | uu____51775 ->
        failwith "Imposible : p_quantifier called on a non-quantifier term"

and (p_trigger :
  FStar_Parser_AST.term Prims.list Prims.list -> FStar_Pprint.document) =
  fun uu___336_51777  ->
    match uu___336_51777 with
    | [] -> FStar_Pprint.empty
    | pats ->
        let uu____51789 =
          let uu____51790 =
            let uu____51791 =
              let uu____51792 = str "pattern"  in
              let uu____51794 =
                let uu____51795 =
                  let uu____51796 = p_disjunctivePats pats  in
                  FStar_Pprint.jump (Prims.parse_int "2")
                    (Prims.parse_int "0") uu____51796
                   in
                FStar_Pprint.op_Hat_Hat uu____51795 FStar_Pprint.rbrace  in
              FStar_Pprint.op_Hat_Slash_Hat uu____51792 uu____51794  in
            FStar_Pprint.op_Hat_Hat FStar_Pprint.colon uu____51791  in
          FStar_Pprint.op_Hat_Hat FStar_Pprint.lbrace uu____51790  in
        FStar_Pprint.group uu____51789

and (p_disjunctivePats :
  FStar_Parser_AST.term Prims.list Prims.list -> FStar_Pprint.document) =
  fun pats  ->
    let uu____51804 = str "\\/"  in
    FStar_Pprint.separate_map uu____51804 p_conjunctivePats pats

and (p_conjunctivePats :
  FStar_Parser_AST.term Prims.list -> FStar_Pprint.document) =
  fun pats  ->
    let uu____51811 =
      let uu____51812 = FStar_Pprint.op_Hat_Hat FStar_Pprint.semi break1  in
      FStar_Pprint.separate_map uu____51812 p_appTerm pats  in
    FStar_Pprint.group uu____51811

and (p_simpleTerm :
  Prims.bool -> Prims.bool -> FStar_Parser_AST.term -> FStar_Pprint.document)
  =
  fun ps  ->
    fun pb  ->
      fun e  ->
        match e.FStar_Parser_AST.tm with
        | FStar_Parser_AST.Abs (pats,e1) ->
            let uu____51824 = p_term_sep false pb e1  in
            (match uu____51824 with
             | (comm,doc1) ->
                 let prefix1 =
                   let uu____51833 = str "fun"  in
                   let uu____51835 =
                     let uu____51836 =
                       FStar_Pprint.separate_map break1 p_atomicPattern pats
                        in
                     FStar_Pprint.op_Hat_Slash_Hat uu____51836
                       FStar_Pprint.rarrow
                      in
                   op_Hat_Slash_Plus_Hat uu____51833 uu____51835  in
                 let uu____51837 =
                   if comm <> FStar_Pprint.empty
                   then
                     let uu____51839 =
                       let uu____51840 =
                         let uu____51841 =
                           FStar_Pprint.op_Hat_Hat FStar_Pprint.hardline doc1
                            in
                         FStar_Pprint.op_Hat_Hat comm uu____51841  in
                       FStar_Pprint.op_Hat_Hat FStar_Pprint.hardline
                         uu____51840
                        in
                     FStar_Pprint.op_Hat_Hat prefix1 uu____51839
                   else
                     (let uu____51844 = op_Hat_Slash_Plus_Hat prefix1 doc1
                         in
                      FStar_Pprint.group uu____51844)
                    in
                 let uu____51845 = paren_if ps  in uu____51845 uu____51837)
        | uu____51850 -> p_tmIff e

and (p_maybeFocusArrow : Prims.bool -> FStar_Pprint.document) =
  fun b  -> if b then str "~>" else FStar_Pprint.rarrow

and (p_patternBranch :
  Prims.bool ->
    (FStar_Parser_AST.pattern * FStar_Parser_AST.term
      FStar_Pervasives_Native.option * FStar_Parser_AST.term) ->
      FStar_Pprint.document)
  =
  fun pb  ->
    fun uu____51858  ->
      match uu____51858 with
      | (pat,when_opt,e) ->
          let one_pattern_branch p =
            let branch =
              match when_opt with
              | FStar_Pervasives_Native.None  ->
                  let uu____51882 =
                    let uu____51883 =
                      let uu____51884 =
                        let uu____51885 = p_tuplePattern p  in
                        let uu____51886 =
                          FStar_Pprint.op_Hat_Hat FStar_Pprint.space
                            FStar_Pprint.rarrow
                           in
                        FStar_Pprint.op_Hat_Hat uu____51885 uu____51886  in
                      FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____51884
                       in
                    FStar_Pprint.op_Hat_Hat FStar_Pprint.bar uu____51883  in
                  FStar_Pprint.group uu____51882
              | FStar_Pervasives_Native.Some f ->
                  let uu____51888 =
                    let uu____51889 =
                      let uu____51890 =
                        let uu____51891 =
                          let uu____51892 =
                            let uu____51893 = p_tuplePattern p  in
                            let uu____51894 = str "when"  in
                            FStar_Pprint.op_Hat_Slash_Hat uu____51893
                              uu____51894
                             in
                          FStar_Pprint.group uu____51892  in
                        let uu____51896 =
                          let uu____51897 =
                            let uu____51900 = p_tmFormula f  in
                            [uu____51900; FStar_Pprint.rarrow]  in
                          FStar_Pprint.flow break1 uu____51897  in
                        FStar_Pprint.op_Hat_Slash_Hat uu____51891 uu____51896
                         in
                      FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____51890
                       in
                    FStar_Pprint.op_Hat_Hat FStar_Pprint.bar uu____51889  in
                  FStar_Pprint.hang (Prims.parse_int "2") uu____51888
               in
            let uu____51902 = p_term_sep false pb e  in
            match uu____51902 with
            | (comm,doc1) ->
                if pb
                then
                  (if comm = FStar_Pprint.empty
                   then
                     let uu____51912 = op_Hat_Slash_Plus_Hat branch doc1  in
                     FStar_Pprint.group uu____51912
                   else
                     (let uu____51915 =
                        let uu____51916 =
                          let uu____51917 =
                            let uu____51918 =
                              let uu____51919 =
                                FStar_Pprint.op_Hat_Hat break1 comm  in
                              FStar_Pprint.op_Hat_Hat doc1 uu____51919  in
                            op_Hat_Slash_Plus_Hat branch uu____51918  in
                          FStar_Pprint.group uu____51917  in
                        let uu____51920 =
                          let uu____51921 =
                            let uu____51922 =
                              inline_comment_or_above comm doc1
                                FStar_Pprint.empty
                               in
                            jump2 uu____51922  in
                          FStar_Pprint.op_Hat_Hat branch uu____51921  in
                        FStar_Pprint.ifflat uu____51916 uu____51920  in
                      FStar_Pprint.group uu____51915))
                else
                  if comm <> FStar_Pprint.empty
                  then
                    (let uu____51926 =
                       let uu____51927 =
                         FStar_Pprint.op_Hat_Hat FStar_Pprint.hardline doc1
                          in
                       FStar_Pprint.op_Hat_Hat comm uu____51927  in
                     op_Hat_Slash_Plus_Hat branch uu____51926)
                  else op_Hat_Slash_Plus_Hat branch doc1
             in
          (match pat.FStar_Parser_AST.pat with
           | FStar_Parser_AST.PatOr pats ->
               (match FStar_List.rev pats with
                | hd1::tl1 ->
                    let last_pat_branch = one_pattern_branch hd1  in
                    let uu____51938 =
                      let uu____51939 =
                        let uu____51940 =
                          let uu____51941 =
                            let uu____51942 =
                              let uu____51943 =
                                FStar_Pprint.op_Hat_Hat FStar_Pprint.bar
                                  FStar_Pprint.space
                                 in
                              FStar_Pprint.op_Hat_Hat break1 uu____51943  in
                            FStar_Pprint.separate_map uu____51942
                              p_tuplePattern (FStar_List.rev tl1)
                             in
                          FStar_Pprint.op_Hat_Slash_Hat uu____51941
                            last_pat_branch
                           in
                        FStar_Pprint.op_Hat_Hat FStar_Pprint.space
                          uu____51940
                         in
                      FStar_Pprint.op_Hat_Hat FStar_Pprint.bar uu____51939
                       in
                    FStar_Pprint.group uu____51938
                | [] ->
                    failwith "Impossible: disjunctive pattern can't be empty")
           | uu____51945 -> one_pattern_branch pat)

and (p_tmIff : FStar_Parser_AST.term -> FStar_Pprint.document) =
  fun e  ->
    match e.FStar_Parser_AST.tm with
    | FStar_Parser_AST.Op
        ({ FStar_Ident.idText = "<==>"; FStar_Ident.idRange = uu____51947;_},e1::e2::[])
        ->
        let uu____51953 = str "<==>"  in
        let uu____51955 = p_tmImplies e1  in
        let uu____51956 = p_tmIff e2  in
        infix0 uu____51953 uu____51955 uu____51956
    | uu____51957 -> p_tmImplies e

and (p_tmImplies : FStar_Parser_AST.term -> FStar_Pprint.document) =
  fun e  ->
    match e.FStar_Parser_AST.tm with
    | FStar_Parser_AST.Op
        ({ FStar_Ident.idText = "==>"; FStar_Ident.idRange = uu____51959;_},e1::e2::[])
        ->
        let uu____51965 = str "==>"  in
        let uu____51967 =
          p_tmArrow (Arrows ((Prims.parse_int "2"), (Prims.parse_int "2")))
            false p_tmFormula e1
           in
        let uu____51973 = p_tmImplies e2  in
        infix0 uu____51965 uu____51967 uu____51973
    | uu____51974 ->
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
          let uu____51988 =
            FStar_List.splitAt
              ((FStar_List.length terms) - (Prims.parse_int "1")) terms
             in
          match uu____51988 with
          | (terms',last1) ->
              let uu____52008 =
                match style with
                | Arrows (n1,ln) ->
                    let uu____52043 =
                      let uu____52044 =
                        FStar_Pprint.op_Hat_Hat FStar_Pprint.rarrow break1
                         in
                      FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____52044
                       in
                    let uu____52045 =
                      FStar_Pprint.op_Hat_Hat FStar_Pprint.rarrow
                        FStar_Pprint.space
                       in
                    (n1, ln, terms', uu____52043, uu____52045)
                | Binders (n1,ln,parens1) ->
                    let uu____52059 =
                      if parens1
                      then FStar_List.map soft_parens_with_nesting terms'
                      else terms'  in
                    let uu____52067 =
                      FStar_Pprint.op_Hat_Hat FStar_Pprint.colon
                        FStar_Pprint.space
                       in
                    (n1, ln, uu____52059, break1, uu____52067)
                 in
              (match uu____52008 with
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
                    | _52100 when _52100 = (Prims.parse_int "1") ->
                        FStar_List.hd terms
                    | uu____52101 ->
                        let uu____52102 =
                          let uu____52103 =
                            let uu____52104 =
                              let uu____52105 =
                                FStar_Pprint.separate sep terms'1  in
                              let uu____52106 =
                                let uu____52107 =
                                  FStar_Pprint.op_Hat_Hat last_op1 last2  in
                                FStar_Pprint.op_Hat_Hat one_line_space
                                  uu____52107
                                 in
                              FStar_Pprint.op_Hat_Hat uu____52105 uu____52106
                               in
                            FStar_Pprint.op_Hat_Hat fs uu____52104  in
                          let uu____52108 =
                            let uu____52109 =
                              let uu____52110 =
                                let uu____52111 =
                                  let uu____52112 =
                                    FStar_Pprint.separate sep terms'1  in
                                  FStar_Pprint.op_Hat_Hat fs uu____52112  in
                                let uu____52113 =
                                  let uu____52114 =
                                    let uu____52115 =
                                      let uu____52116 =
                                        FStar_Pprint.op_Hat_Hat sep
                                          single_line_arg_indent
                                         in
                                      let uu____52117 =
                                        FStar_List.map
                                          (fun x  ->
                                             let uu____52123 =
                                               FStar_Pprint.hang
                                                 (Prims.parse_int "2") x
                                                in
                                             FStar_Pprint.align uu____52123)
                                          terms'1
                                         in
                                      FStar_Pprint.separate uu____52116
                                        uu____52117
                                       in
                                    FStar_Pprint.op_Hat_Hat
                                      single_line_arg_indent uu____52115
                                     in
                                  jump2 uu____52114  in
                                FStar_Pprint.ifflat uu____52111 uu____52113
                                 in
                              FStar_Pprint.group uu____52110  in
                            let uu____52125 =
                              let uu____52126 =
                                let uu____52127 =
                                  FStar_Pprint.op_Hat_Hat last_op1 last2  in
                                FStar_Pprint.hang last_n uu____52127  in
                              FStar_Pprint.align uu____52126  in
                            FStar_Pprint.prefix n1 (Prims.parse_int "1")
                              uu____52109 uu____52125
                             in
                          FStar_Pprint.ifflat uu____52103 uu____52108  in
                        FStar_Pprint.group uu____52102))

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
            | Arrows uu____52141 -> p_tmArrow' p_Tm e
            | Binders uu____52148 -> collapse_binders p_Tm e  in
          format_sig style terms false flat_space

and (p_tmArrow' :
  (FStar_Parser_AST.term -> FStar_Pprint.document) ->
    FStar_Parser_AST.term -> FStar_Pprint.document Prims.list)
  =
  fun p_Tm  ->
    fun e  ->
      match e.FStar_Parser_AST.tm with
      | FStar_Parser_AST.Product (bs,tgt) ->
          let uu____52171 = FStar_List.map (fun b  -> p_binder false b) bs
             in
          let uu____52177 = p_tmArrow' p_Tm tgt  in
          FStar_List.append uu____52171 uu____52177
      | uu____52180 -> let uu____52181 = p_Tm e  in [uu____52181]

and (collapse_binders :
  (FStar_Parser_AST.term -> FStar_Pprint.document) ->
    FStar_Parser_AST.term -> FStar_Pprint.document Prims.list)
  =
  fun p_Tm  ->
    fun e  ->
      let rec accumulate_binders p_Tm1 e1 =
        match e1.FStar_Parser_AST.tm with
        | FStar_Parser_AST.Product (bs,tgt) ->
            let uu____52234 = FStar_List.map (fun b  -> p_binder' false b) bs
               in
            let uu____52260 = accumulate_binders p_Tm1 tgt  in
            FStar_List.append uu____52234 uu____52260
        | uu____52283 ->
            let uu____52284 =
              let uu____52295 = p_Tm1 e1  in
              (uu____52295, FStar_Pervasives_Native.None, cat_with_colon)  in
            [uu____52284]
         in
      let fold_fun bs x =
        let uu____52393 = x  in
        match uu____52393 with
        | (b1,t1,f1) ->
            (match bs with
             | [] -> [([b1], t1, f1)]
             | hd1::tl1 ->
                 let uu____52529 = hd1  in
                 (match uu____52529 with
                  | (b2s,t2,uu____52558) ->
                      (match (t1, t2) with
                       | (FStar_Pervasives_Native.Some
                          typ1,FStar_Pervasives_Native.Some typ2) ->
                           if typ1 = typ2
                           then ((FStar_List.append b2s [b1]), t1, f1) :: tl1
                           else ([b1], t1, f1) :: hd1 :: tl1
                       | uu____52668 -> ([b1], t1, f1) :: bs)))
         in
      let p_collapsed_binder cb =
        let uu____52729 = cb  in
        match uu____52729 with
        | (bs,t,f) ->
            (match t with
             | FStar_Pervasives_Native.None  ->
                 (match bs with
                  | b::[] -> b
                  | uu____52758 -> failwith "Impossible")
             | FStar_Pervasives_Native.Some typ ->
                 (match bs with
                  | [] -> failwith "Impossible"
                  | b::[] -> f b typ
                  | hd1::tl1 ->
                      let uu____52771 =
                        FStar_List.fold_left
                          (fun x  ->
                             fun y  ->
                               let uu____52777 =
                                 FStar_Pprint.op_Hat_Hat FStar_Pprint.space y
                                  in
                               FStar_Pprint.op_Hat_Hat x uu____52777) hd1 tl1
                         in
                      f uu____52771 typ))
         in
      let binders =
        let uu____52795 = accumulate_binders p_Tm e  in
        FStar_List.fold_left fold_fun [] uu____52795  in
      map_rev p_collapsed_binder binders

and (p_tmFormula : FStar_Parser_AST.term -> FStar_Pprint.document) =
  fun e  ->
    let conj =
      let uu____52858 =
        let uu____52859 = str "/\\"  in
        FStar_Pprint.op_Hat_Hat uu____52859 break1  in
      FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____52858  in
    let disj =
      let uu____52862 =
        let uu____52863 = str "\\/"  in
        FStar_Pprint.op_Hat_Hat uu____52863 break1  in
      FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____52862  in
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
        ({ FStar_Ident.idText = "\\/"; FStar_Ident.idRange = uu____52883;_},e1::e2::[])
        ->
        let uu____52889 = p_tmDisjunction e1  in
        let uu____52894 =
          let uu____52899 = p_tmConjunction e2  in [uu____52899]  in
        FStar_List.append uu____52889 uu____52894
    | uu____52908 -> let uu____52909 = p_tmConjunction e  in [uu____52909]

and (p_tmConjunction :
  FStar_Parser_AST.term -> FStar_Pprint.document Prims.list) =
  fun e  ->
    match e.FStar_Parser_AST.tm with
    | FStar_Parser_AST.Op
        ({ FStar_Ident.idText = "/\\"; FStar_Ident.idRange = uu____52919;_},e1::e2::[])
        ->
        let uu____52925 = p_tmConjunction e1  in
        let uu____52928 = let uu____52931 = p_tmTuple e2  in [uu____52931]
           in
        FStar_List.append uu____52925 uu____52928
    | uu____52932 -> let uu____52933 = p_tmTuple e  in [uu____52933]

and (p_tmTuple : FStar_Parser_AST.term -> FStar_Pprint.document) =
  fun e  -> with_comment p_tmTuple' e e.FStar_Parser_AST.range

and (p_tmTuple' : FStar_Parser_AST.term -> FStar_Pprint.document) =
  fun e  ->
    match e.FStar_Parser_AST.tm with
    | FStar_Parser_AST.Construct (lid,args) when
        (is_tuple_constructor lid) && (all_explicit args) ->
        let uu____52950 = FStar_Pprint.op_Hat_Hat FStar_Pprint.comma break1
           in
        FStar_Pprint.separate_map uu____52950
          (fun uu____52958  ->
             match uu____52958 with | (e1,uu____52964) -> p_tmEq e1) args
    | uu____52965 -> p_tmEq e

and (paren_if_gt :
  Prims.int -> Prims.int -> FStar_Pprint.document -> FStar_Pprint.document) =
  fun curr  ->
    fun mine  ->
      fun doc1  ->
        if mine <= curr
        then doc1
        else
          (let uu____52974 =
             let uu____52975 =
               FStar_Pprint.op_Hat_Hat doc1 FStar_Pprint.rparen  in
             FStar_Pprint.op_Hat_Hat FStar_Pprint.lparen uu____52975  in
           FStar_Pprint.group uu____52974)

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
               (let uu____52994 = FStar_Ident.text_of_id op  in
                uu____52994 = "="))
              ||
              (let uu____52999 = FStar_Ident.text_of_id op  in
               uu____52999 = "|>")
            ->
            let op1 = FStar_Ident.text_of_id op  in
            let uu____53005 = levels op1  in
            (match uu____53005 with
             | (left1,mine,right1) ->
                 let uu____53024 =
                   let uu____53025 = FStar_All.pipe_left str op1  in
                   let uu____53027 = p_tmEqWith' p_X left1 e1  in
                   let uu____53028 = p_tmEqWith' p_X right1 e2  in
                   infix0 uu____53025 uu____53027 uu____53028  in
                 paren_if_gt curr mine uu____53024)
        | FStar_Parser_AST.Op
            ({ FStar_Ident.idText = ":=";
               FStar_Ident.idRange = uu____53029;_},e1::e2::[])
            ->
            let uu____53035 =
              let uu____53036 = p_tmEqWith p_X e1  in
              let uu____53037 =
                let uu____53038 =
                  let uu____53039 =
                    let uu____53040 = p_tmEqWith p_X e2  in
                    op_Hat_Slash_Plus_Hat FStar_Pprint.equals uu____53040  in
                  FStar_Pprint.op_Hat_Hat FStar_Pprint.colon uu____53039  in
                FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____53038  in
              FStar_Pprint.op_Hat_Hat uu____53036 uu____53037  in
            FStar_Pprint.group uu____53035
        | FStar_Parser_AST.Op
            ({ FStar_Ident.idText = "-"; FStar_Ident.idRange = uu____53041;_},e1::[])
            ->
            let uu____53046 = levels "-"  in
            (match uu____53046 with
             | (left1,mine,right1) ->
                 let uu____53066 = p_tmEqWith' p_X mine e1  in
                 FStar_Pprint.op_Hat_Slash_Hat FStar_Pprint.minus uu____53066)
        | uu____53067 -> p_tmNoEqWith p_X e

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
              (lid,(e1,uu____53115)::(e2,uu____53117)::[]) when
              (FStar_Ident.lid_equals lid FStar_Parser_Const.cons_lid) &&
                (let uu____53137 = is_list e  in
                 Prims.op_Negation uu____53137)
              ->
              let op = "::"  in
              let uu____53142 = levels op  in
              (match uu____53142 with
               | (left1,mine,right1) ->
                   let uu____53161 =
                     let uu____53162 = str op  in
                     let uu____53163 = p_tmNoEqWith' false p_X left1 e1  in
                     let uu____53165 = p_tmNoEqWith' false p_X right1 e2  in
                     infix0 uu____53162 uu____53163 uu____53165  in
                   paren_if_gt curr mine uu____53161)
          | FStar_Parser_AST.Sum (binders,res) ->
              let op = "&"  in
              let uu____53184 = levels op  in
              (match uu____53184 with
               | (left1,mine,right1) ->
                   let p_dsumfst bt =
                     match bt with
                     | FStar_Util.Inl b ->
                         let uu____53218 = p_binder false b  in
                         let uu____53220 =
                           let uu____53221 =
                             let uu____53222 = str op  in
                             FStar_Pprint.op_Hat_Hat uu____53222 break1  in
                           FStar_Pprint.op_Hat_Hat FStar_Pprint.space
                             uu____53221
                            in
                         FStar_Pprint.op_Hat_Hat uu____53218 uu____53220
                     | FStar_Util.Inr t ->
                         let uu____53224 = p_tmNoEqWith' false p_X left1 t
                            in
                         let uu____53226 =
                           let uu____53227 =
                             let uu____53228 = str op  in
                             FStar_Pprint.op_Hat_Hat uu____53228 break1  in
                           FStar_Pprint.op_Hat_Hat FStar_Pprint.space
                             uu____53227
                            in
                         FStar_Pprint.op_Hat_Hat uu____53224 uu____53226
                      in
                   let uu____53229 =
                     let uu____53230 =
                       FStar_Pprint.concat_map p_dsumfst binders  in
                     let uu____53235 = p_tmNoEqWith' false p_X right1 res  in
                     FStar_Pprint.op_Hat_Hat uu____53230 uu____53235  in
                   paren_if_gt curr mine uu____53229)
          | FStar_Parser_AST.Op
              ({ FStar_Ident.idText = "*";
                 FStar_Ident.idRange = uu____53237;_},e1::e2::[])
              when FStar_ST.op_Bang unfold_tuples ->
              let op = "*"  in
              let uu____53267 = levels op  in
              (match uu____53267 with
               | (left1,mine,right1) ->
                   if inside_tuple
                   then
                     let uu____53287 = str op  in
                     let uu____53288 = p_tmNoEqWith' true p_X left1 e1  in
                     let uu____53290 = p_tmNoEqWith' true p_X right1 e2  in
                     infix0 uu____53287 uu____53288 uu____53290
                   else
                     (let uu____53294 =
                        let uu____53295 = str op  in
                        let uu____53296 = p_tmNoEqWith' true p_X left1 e1  in
                        let uu____53298 = p_tmNoEqWith' true p_X right1 e2
                           in
                        infix0 uu____53295 uu____53296 uu____53298  in
                      paren_if_gt curr mine uu____53294))
          | FStar_Parser_AST.Op (op,e1::e2::[]) when is_operatorInfix34 op ->
              let op1 = FStar_Ident.text_of_id op  in
              let uu____53307 = levels op1  in
              (match uu____53307 with
               | (left1,mine,right1) ->
                   let uu____53326 =
                     let uu____53327 = str op1  in
                     let uu____53328 = p_tmNoEqWith' false p_X left1 e1  in
                     let uu____53330 = p_tmNoEqWith' false p_X right1 e2  in
                     infix0 uu____53327 uu____53328 uu____53330  in
                   paren_if_gt curr mine uu____53326)
          | FStar_Parser_AST.Record (with_opt,record_fields) ->
              let uu____53350 =
                let uu____53351 =
                  default_or_map FStar_Pprint.empty p_with_clause with_opt
                   in
                let uu____53352 =
                  let uu____53353 =
                    FStar_Pprint.op_Hat_Hat FStar_Pprint.semi break1  in
                  separate_map_last uu____53353 p_simpleDef record_fields  in
                FStar_Pprint.op_Hat_Hat uu____53351 uu____53352  in
              braces_with_nesting uu____53350
          | FStar_Parser_AST.Op
              ({ FStar_Ident.idText = "~";
                 FStar_Ident.idRange = uu____53358;_},e1::[])
              ->
              let uu____53363 =
                let uu____53364 = str "~"  in
                let uu____53366 = p_atomicTerm e1  in
                FStar_Pprint.op_Hat_Hat uu____53364 uu____53366  in
              FStar_Pprint.group uu____53363
          | FStar_Parser_AST.Paren p when inside_tuple ->
              (match p.FStar_Parser_AST.tm with
               | FStar_Parser_AST.Op
                   ({ FStar_Ident.idText = "*";
                      FStar_Ident.idRange = uu____53368;_},e1::e2::[])
                   ->
                   let op = "*"  in
                   let uu____53377 = levels op  in
                   (match uu____53377 with
                    | (left1,mine,right1) ->
                        let uu____53396 =
                          let uu____53397 = str op  in
                          let uu____53398 = p_tmNoEqWith' true p_X left1 e1
                             in
                          let uu____53400 = p_tmNoEqWith' true p_X right1 e2
                             in
                          infix0 uu____53397 uu____53398 uu____53400  in
                        paren_if_gt curr mine uu____53396)
               | uu____53402 -> p_X e)
          | uu____53403 -> p_X e

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
        let uu____53410 =
          let uu____53411 = p_lident lid  in
          let uu____53412 =
            let uu____53413 = p_appTerm e1  in
            FStar_Pprint.op_Hat_Slash_Hat FStar_Pprint.colon uu____53413  in
          FStar_Pprint.op_Hat_Slash_Hat uu____53411 uu____53412  in
        FStar_Pprint.group uu____53410
    | FStar_Parser_AST.Refine (b,phi) -> p_refinedBinder b phi
    | uu____53416 -> p_appTerm e

and (p_with_clause : FStar_Parser_AST.term -> FStar_Pprint.document) =
  fun e  ->
    let uu____53418 = p_appTerm e  in
    let uu____53419 =
      let uu____53420 =
        let uu____53421 = str "with"  in
        FStar_Pprint.op_Hat_Hat uu____53421 break1  in
      FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____53420  in
    FStar_Pprint.op_Hat_Hat uu____53418 uu____53419

and (p_refinedBinder :
  FStar_Parser_AST.binder -> FStar_Parser_AST.term -> FStar_Pprint.document)
  =
  fun b  ->
    fun phi  ->
      match b.FStar_Parser_AST.b with
      | FStar_Parser_AST.Annotated (lid,t) ->
          let uu____53427 = p_lident lid  in
          p_refinement b.FStar_Parser_AST.aqual uu____53427 t phi
      | FStar_Parser_AST.TAnnotated uu____53428 ->
          failwith "Is this still used ?"
      | FStar_Parser_AST.Variable uu____53434 ->
          let uu____53435 =
            let uu____53437 = FStar_Parser_AST.binder_to_string b  in
            FStar_Util.format1
              "Imposible : a refined binder ought to be annotated %s"
              uu____53437
             in
          failwith uu____53435
      | FStar_Parser_AST.TVariable uu____53440 ->
          let uu____53441 =
            let uu____53443 = FStar_Parser_AST.binder_to_string b  in
            FStar_Util.format1
              "Imposible : a refined binder ought to be annotated %s"
              uu____53443
             in
          failwith uu____53441
      | FStar_Parser_AST.NoName uu____53446 ->
          let uu____53447 =
            let uu____53449 = FStar_Parser_AST.binder_to_string b  in
            FStar_Util.format1
              "Imposible : a refined binder ought to be annotated %s"
              uu____53449
             in
          failwith uu____53447

and (p_simpleDef :
  Prims.bool ->
    (FStar_Ident.lid * FStar_Parser_AST.term) -> FStar_Pprint.document)
  =
  fun ps  ->
    fun uu____53453  ->
      match uu____53453 with
      | (lid,e) ->
          let uu____53461 =
            let uu____53462 = p_qlident lid  in
            let uu____53463 =
              let uu____53464 = p_noSeqTermAndComment ps false e  in
              FStar_Pprint.op_Hat_Slash_Hat FStar_Pprint.equals uu____53464
               in
            FStar_Pprint.op_Hat_Slash_Hat uu____53462 uu____53463  in
          FStar_Pprint.group uu____53461

and (p_appTerm : FStar_Parser_AST.term -> FStar_Pprint.document) =
  fun e  ->
    match e.FStar_Parser_AST.tm with
    | FStar_Parser_AST.App uu____53467 when is_general_application e ->
        let uu____53474 = head_and_args e  in
        (match uu____53474 with
         | (head1,args) ->
             (match args with
              | e1::e2::[] when
                  (FStar_Pervasives_Native.snd e1) = FStar_Parser_AST.Infix
                  ->
                  let uu____53521 = p_argTerm e1  in
                  let uu____53522 =
                    let uu____53523 =
                      let uu____53524 =
                        let uu____53525 = str "`"  in
                        let uu____53527 =
                          let uu____53528 = p_indexingTerm head1  in
                          let uu____53529 = str "`"  in
                          FStar_Pprint.op_Hat_Hat uu____53528 uu____53529  in
                        FStar_Pprint.op_Hat_Hat uu____53525 uu____53527  in
                      FStar_Pprint.group uu____53524  in
                    let uu____53531 = p_argTerm e2  in
                    FStar_Pprint.op_Hat_Slash_Hat uu____53523 uu____53531  in
                  FStar_Pprint.op_Hat_Slash_Hat uu____53521 uu____53522
              | uu____53532 ->
                  let uu____53539 =
                    let uu____53550 =
                      FStar_ST.op_Bang should_print_fs_typ_app  in
                    if uu____53550
                    then
                      let uu____53584 =
                        FStar_Util.take
                          (fun uu____53608  ->
                             match uu____53608 with
                             | (uu____53614,aq) ->
                                 aq = FStar_Parser_AST.FsTypApp) args
                         in
                      match uu____53584 with
                      | (fs_typ_args,args1) ->
                          let uu____53652 =
                            let uu____53653 = p_indexingTerm head1  in
                            let uu____53654 =
                              let uu____53655 =
                                FStar_Pprint.op_Hat_Hat FStar_Pprint.comma
                                  break1
                                 in
                              soft_surround_map_or_flow (Prims.parse_int "2")
                                (Prims.parse_int "0") FStar_Pprint.empty
                                FStar_Pprint.langle uu____53655
                                FStar_Pprint.rangle p_fsTypArg fs_typ_args
                               in
                            FStar_Pprint.op_Hat_Hat uu____53653 uu____53654
                             in
                          (uu____53652, args1)
                    else
                      (let uu____53670 = p_indexingTerm head1  in
                       (uu____53670, args))
                     in
                  (match uu____53539 with
                   | (head_doc,args1) ->
                       let uu____53691 =
                         let uu____53692 =
                           FStar_Pprint.op_Hat_Hat head_doc
                             FStar_Pprint.space
                            in
                         soft_surround_map_or_flow (Prims.parse_int "2")
                           (Prims.parse_int "0") head_doc uu____53692 break1
                           FStar_Pprint.empty p_argTerm args1
                          in
                       FStar_Pprint.group uu____53691)))
    | FStar_Parser_AST.Construct (lid,args) when
        (is_general_construction e) &&
          (let uu____53714 = is_dtuple_constructor lid  in
           Prims.op_Negation uu____53714)
        ->
        (match args with
         | [] -> p_quident lid
         | arg::[] ->
             let uu____53733 =
               let uu____53734 = p_quident lid  in
               let uu____53735 = p_argTerm arg  in
               FStar_Pprint.op_Hat_Slash_Hat uu____53734 uu____53735  in
             FStar_Pprint.group uu____53733
         | hd1::tl1 ->
             let uu____53752 =
               let uu____53753 =
                 let uu____53754 =
                   let uu____53755 = p_quident lid  in
                   let uu____53756 = p_argTerm hd1  in
                   prefix2 uu____53755 uu____53756  in
                 FStar_Pprint.group uu____53754  in
               let uu____53757 =
                 let uu____53758 =
                   FStar_Pprint.separate_map break1 p_argTerm tl1  in
                 jump2 uu____53758  in
               FStar_Pprint.op_Hat_Hat uu____53753 uu____53757  in
             FStar_Pprint.group uu____53752)
    | uu____53763 -> p_indexingTerm e

and (p_argTerm :
  (FStar_Parser_AST.term * FStar_Parser_AST.imp) -> FStar_Pprint.document) =
  fun arg_imp  ->
    match arg_imp with
    | (u,FStar_Parser_AST.UnivApp ) -> p_universe u
    | (e,FStar_Parser_AST.FsTypApp ) ->
        (FStar_Errors.log_issue e.FStar_Parser_AST.range
           (FStar_Errors.Warning_UnexpectedFsTypApp,
             "Unexpected FsTypApp, output might not be formatted correctly.");
         (let uu____53774 = p_indexingTerm e  in
          FStar_Pprint.surround (Prims.parse_int "2") (Prims.parse_int "1")
            FStar_Pprint.langle uu____53774 FStar_Pprint.rangle))
    | (e,FStar_Parser_AST.Hash ) ->
        let uu____53778 = str "#"  in
        let uu____53780 = p_indexingTerm e  in
        FStar_Pprint.op_Hat_Hat uu____53778 uu____53780
    | (e,FStar_Parser_AST.HashBrace t) ->
        let uu____53783 = str "#["  in
        let uu____53785 =
          let uu____53786 = p_indexingTerm t  in
          let uu____53787 =
            let uu____53788 = str "]"  in
            let uu____53790 = p_indexingTerm e  in
            FStar_Pprint.op_Hat_Hat uu____53788 uu____53790  in
          FStar_Pprint.op_Hat_Hat uu____53786 uu____53787  in
        FStar_Pprint.op_Hat_Hat uu____53783 uu____53785
    | (e,FStar_Parser_AST.Infix ) -> p_indexingTerm e
    | (e,FStar_Parser_AST.Nothing ) -> p_indexingTerm e

and (p_fsTypArg :
  (FStar_Parser_AST.term * FStar_Parser_AST.imp) -> FStar_Pprint.document) =
  fun uu____53793  ->
    match uu____53793 with | (e,uu____53799) -> p_indexingTerm e

and (p_indexingTerm_aux :
  (FStar_Parser_AST.term -> FStar_Pprint.document) ->
    FStar_Parser_AST.term -> FStar_Pprint.document)
  =
  fun exit1  ->
    fun e  ->
      match e.FStar_Parser_AST.tm with
      | FStar_Parser_AST.Op
          ({ FStar_Ident.idText = ".()"; FStar_Ident.idRange = uu____53804;_},e1::e2::[])
          ->
          let uu____53810 =
            let uu____53811 = p_indexingTerm_aux p_atomicTermNotQUident e1
               in
            let uu____53812 =
              let uu____53813 =
                let uu____53814 = p_term false false e2  in
                soft_parens_with_nesting uu____53814  in
              FStar_Pprint.op_Hat_Hat FStar_Pprint.dot uu____53813  in
            FStar_Pprint.op_Hat_Hat uu____53811 uu____53812  in
          FStar_Pprint.group uu____53810
      | FStar_Parser_AST.Op
          ({ FStar_Ident.idText = ".[]"; FStar_Ident.idRange = uu____53817;_},e1::e2::[])
          ->
          let uu____53823 =
            let uu____53824 = p_indexingTerm_aux p_atomicTermNotQUident e1
               in
            let uu____53825 =
              let uu____53826 =
                let uu____53827 = p_term false false e2  in
                soft_brackets_with_nesting uu____53827  in
              FStar_Pprint.op_Hat_Hat FStar_Pprint.dot uu____53826  in
            FStar_Pprint.op_Hat_Hat uu____53824 uu____53825  in
          FStar_Pprint.group uu____53823
      | uu____53830 -> exit1 e

and (p_indexingTerm : FStar_Parser_AST.term -> FStar_Pprint.document) =
  fun e  -> p_indexingTerm_aux p_atomicTerm e

and (p_atomicTerm : FStar_Parser_AST.term -> FStar_Pprint.document) =
  fun e  ->
    match e.FStar_Parser_AST.tm with
    | FStar_Parser_AST.LetOpen (lid,e1) ->
        let uu____53835 = p_quident lid  in
        let uu____53836 =
          let uu____53837 =
            let uu____53838 = p_term false false e1  in
            soft_parens_with_nesting uu____53838  in
          FStar_Pprint.op_Hat_Hat FStar_Pprint.dot uu____53837  in
        FStar_Pprint.op_Hat_Hat uu____53835 uu____53836
    | FStar_Parser_AST.Name lid -> p_quident lid
    | FStar_Parser_AST.Op (op,e1::[]) when is_general_prefix_op op ->
        let uu____53846 =
          let uu____53847 = FStar_Ident.text_of_id op  in str uu____53847  in
        let uu____53849 = p_atomicTerm e1  in
        FStar_Pprint.op_Hat_Hat uu____53846 uu____53849
    | uu____53850 -> p_atomicTermNotQUident e

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
         | uu____53863 -> p_constant c)
    | FStar_Parser_AST.Name lid when
        FStar_Ident.lid_equals lid FStar_Parser_Const.true_lid -> str "True"
    | FStar_Parser_AST.Name lid when
        FStar_Ident.lid_equals lid FStar_Parser_Const.false_lid ->
        str "False"
    | FStar_Parser_AST.Op (op,e1::[]) when is_general_prefix_op op ->
        let uu____53872 =
          let uu____53873 = FStar_Ident.text_of_id op  in str uu____53873  in
        let uu____53875 = p_atomicTermNotQUident e1  in
        FStar_Pprint.op_Hat_Hat uu____53872 uu____53875
    | FStar_Parser_AST.Op (op,[]) ->
        let uu____53879 =
          let uu____53880 =
            let uu____53881 =
              let uu____53882 = FStar_Ident.text_of_id op  in str uu____53882
               in
            let uu____53884 =
              FStar_Pprint.op_Hat_Hat FStar_Pprint.space FStar_Pprint.rparen
               in
            FStar_Pprint.op_Hat_Hat uu____53881 uu____53884  in
          FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____53880  in
        FStar_Pprint.op_Hat_Hat FStar_Pprint.lparen uu____53879
    | FStar_Parser_AST.Construct (lid,args) when is_dtuple_constructor lid ->
        let uu____53899 = all_explicit args  in
        if uu____53899
        then
          let uu____53902 =
            FStar_Pprint.op_Hat_Hat FStar_Pprint.lparen FStar_Pprint.bar  in
          let uu____53903 =
            let uu____53904 =
              FStar_Pprint.op_Hat_Hat FStar_Pprint.comma break1  in
            let uu____53905 = FStar_List.map FStar_Pervasives_Native.fst args
               in
            FStar_Pprint.separate_map uu____53904 p_tmEq uu____53905  in
          let uu____53912 =
            FStar_Pprint.op_Hat_Hat FStar_Pprint.bar FStar_Pprint.rparen  in
          FStar_Pprint.surround (Prims.parse_int "2") (Prims.parse_int "1")
            uu____53902 uu____53903 uu____53912
        else
          (match args with
           | [] -> p_quident lid
           | arg::[] ->
               let uu____53934 =
                 let uu____53935 = p_quident lid  in
                 let uu____53936 = p_argTerm arg  in
                 FStar_Pprint.op_Hat_Slash_Hat uu____53935 uu____53936  in
               FStar_Pprint.group uu____53934
           | hd1::tl1 ->
               let uu____53953 =
                 let uu____53954 =
                   let uu____53955 =
                     let uu____53956 = p_quident lid  in
                     let uu____53957 = p_argTerm hd1  in
                     prefix2 uu____53956 uu____53957  in
                   FStar_Pprint.group uu____53955  in
                 let uu____53958 =
                   let uu____53959 =
                     FStar_Pprint.separate_map break1 p_argTerm tl1  in
                   jump2 uu____53959  in
                 FStar_Pprint.op_Hat_Hat uu____53954 uu____53958  in
               FStar_Pprint.group uu____53953)
    | FStar_Parser_AST.Project (e1,lid) ->
        let uu____53966 =
          let uu____53967 = p_atomicTermNotQUident e1  in
          let uu____53968 =
            let uu____53969 = p_qlident lid  in
            FStar_Pprint.op_Hat_Hat FStar_Pprint.dot uu____53969  in
          FStar_Pprint.prefix (Prims.parse_int "2") (Prims.parse_int "0")
            uu____53967 uu____53968
           in
        FStar_Pprint.group uu____53966
    | uu____53972 -> p_projectionLHS e

and (p_projectionLHS : FStar_Parser_AST.term -> FStar_Pprint.document) =
  fun e  ->
    match e.FStar_Parser_AST.tm with
    | FStar_Parser_AST.Var lid -> p_qlident lid
    | FStar_Parser_AST.Projector (constr_lid,field_lid) ->
        let uu____53977 = p_quident constr_lid  in
        let uu____53978 =
          let uu____53979 =
            let uu____53980 = p_lident field_lid  in
            FStar_Pprint.op_Hat_Hat FStar_Pprint.dot uu____53980  in
          FStar_Pprint.op_Hat_Hat FStar_Pprint.qmark uu____53979  in
        FStar_Pprint.op_Hat_Hat uu____53977 uu____53978
    | FStar_Parser_AST.Discrim constr_lid ->
        let uu____53982 = p_quident constr_lid  in
        FStar_Pprint.op_Hat_Hat uu____53982 FStar_Pprint.qmark
    | FStar_Parser_AST.Paren e1 ->
        let uu____53984 = p_term_sep false false e1  in
        (match uu____53984 with
         | (comm,t) ->
             let doc1 = soft_parens_with_nesting t  in
             if comm = FStar_Pprint.empty
             then doc1
             else
               (let uu____53997 =
                  FStar_Pprint.op_Hat_Hat FStar_Pprint.hardline doc1  in
                FStar_Pprint.op_Hat_Hat comm uu____53997))
    | uu____53998 when is_array e ->
        let es = extract_from_list e  in
        let uu____54002 =
          FStar_Pprint.op_Hat_Hat FStar_Pprint.lbracket FStar_Pprint.bar  in
        let uu____54003 =
          let uu____54004 = FStar_Pprint.op_Hat_Hat FStar_Pprint.semi break1
             in
          separate_map_or_flow_last uu____54004
            (fun ps  -> p_noSeqTermAndComment ps false) es
           in
        let uu____54009 =
          FStar_Pprint.op_Hat_Hat FStar_Pprint.bar FStar_Pprint.rbracket  in
        FStar_Pprint.surround (Prims.parse_int "2") (Prims.parse_int "0")
          uu____54002 uu____54003 uu____54009
    | uu____54012 when is_list e ->
        let uu____54013 =
          let uu____54014 = FStar_Pprint.op_Hat_Hat FStar_Pprint.semi break1
             in
          let uu____54015 = extract_from_list e  in
          separate_map_or_flow_last uu____54014
            (fun ps  -> p_noSeqTermAndComment ps false) uu____54015
           in
        FStar_Pprint.surround (Prims.parse_int "2") (Prims.parse_int "0")
          FStar_Pprint.lbracket uu____54013 FStar_Pprint.rbracket
    | uu____54024 when is_lex_list e ->
        let uu____54025 =
          FStar_Pprint.op_Hat_Hat FStar_Pprint.percent FStar_Pprint.lbracket
           in
        let uu____54026 =
          let uu____54027 = FStar_Pprint.op_Hat_Hat FStar_Pprint.semi break1
             in
          let uu____54028 = extract_from_list e  in
          separate_map_or_flow_last uu____54027
            (fun ps  -> p_noSeqTermAndComment ps false) uu____54028
           in
        FStar_Pprint.surround (Prims.parse_int "2") (Prims.parse_int "1")
          uu____54025 uu____54026 FStar_Pprint.rbracket
    | uu____54037 when is_ref_set e ->
        let es = extract_from_ref_set e  in
        let uu____54041 =
          FStar_Pprint.op_Hat_Hat FStar_Pprint.bang FStar_Pprint.lbrace  in
        let uu____54042 =
          let uu____54043 = FStar_Pprint.op_Hat_Hat FStar_Pprint.comma break1
             in
          separate_map_or_flow uu____54043 p_appTerm es  in
        FStar_Pprint.surround (Prims.parse_int "2") (Prims.parse_int "0")
          uu____54041 uu____54042 FStar_Pprint.rbrace
    | FStar_Parser_AST.Labeled (e1,s,b) ->
        let uu____54053 = str (Prims.op_Hat "(*" (Prims.op_Hat s "*)"))  in
        let uu____54056 = p_term false false e1  in
        FStar_Pprint.op_Hat_Slash_Hat uu____54053 uu____54056
    | FStar_Parser_AST.Op (op,args) when
        let uu____54065 = handleable_op op args  in
        Prims.op_Negation uu____54065 ->
        let uu____54067 =
          let uu____54069 =
            let uu____54071 = FStar_Ident.text_of_id op  in
            let uu____54073 =
              let uu____54075 =
                let uu____54077 =
                  FStar_Util.string_of_int (FStar_List.length args)  in
                Prims.op_Hat uu____54077
                  " arguments couldn't be handled by the pretty printer"
                 in
              Prims.op_Hat " with " uu____54075  in
            Prims.op_Hat uu____54071 uu____54073  in
          Prims.op_Hat "Operation " uu____54069  in
        failwith uu____54067
    | FStar_Parser_AST.Uvar id1 ->
        failwith "Unexpected universe variable out of universe context"
    | FStar_Parser_AST.Wild  ->
        let uu____54084 = p_term false false e  in
        soft_parens_with_nesting uu____54084
    | FStar_Parser_AST.Const uu____54087 ->
        let uu____54088 = p_term false false e  in
        soft_parens_with_nesting uu____54088
    | FStar_Parser_AST.Op uu____54091 ->
        let uu____54098 = p_term false false e  in
        soft_parens_with_nesting uu____54098
    | FStar_Parser_AST.Tvar uu____54101 ->
        let uu____54102 = p_term false false e  in
        soft_parens_with_nesting uu____54102
    | FStar_Parser_AST.Var uu____54105 ->
        let uu____54106 = p_term false false e  in
        soft_parens_with_nesting uu____54106
    | FStar_Parser_AST.Name uu____54109 ->
        let uu____54110 = p_term false false e  in
        soft_parens_with_nesting uu____54110
    | FStar_Parser_AST.Construct uu____54113 ->
        let uu____54124 = p_term false false e  in
        soft_parens_with_nesting uu____54124
    | FStar_Parser_AST.Abs uu____54127 ->
        let uu____54134 = p_term false false e  in
        soft_parens_with_nesting uu____54134
    | FStar_Parser_AST.App uu____54137 ->
        let uu____54144 = p_term false false e  in
        soft_parens_with_nesting uu____54144
    | FStar_Parser_AST.Let uu____54147 ->
        let uu____54168 = p_term false false e  in
        soft_parens_with_nesting uu____54168
    | FStar_Parser_AST.LetOpen uu____54171 ->
        let uu____54176 = p_term false false e  in
        soft_parens_with_nesting uu____54176
    | FStar_Parser_AST.Seq uu____54179 ->
        let uu____54184 = p_term false false e  in
        soft_parens_with_nesting uu____54184
    | FStar_Parser_AST.Bind uu____54187 ->
        let uu____54194 = p_term false false e  in
        soft_parens_with_nesting uu____54194
    | FStar_Parser_AST.If uu____54197 ->
        let uu____54204 = p_term false false e  in
        soft_parens_with_nesting uu____54204
    | FStar_Parser_AST.Match uu____54207 ->
        let uu____54222 = p_term false false e  in
        soft_parens_with_nesting uu____54222
    | FStar_Parser_AST.TryWith uu____54225 ->
        let uu____54240 = p_term false false e  in
        soft_parens_with_nesting uu____54240
    | FStar_Parser_AST.Ascribed uu____54243 ->
        let uu____54252 = p_term false false e  in
        soft_parens_with_nesting uu____54252
    | FStar_Parser_AST.Record uu____54255 ->
        let uu____54268 = p_term false false e  in
        soft_parens_with_nesting uu____54268
    | FStar_Parser_AST.Project uu____54271 ->
        let uu____54276 = p_term false false e  in
        soft_parens_with_nesting uu____54276
    | FStar_Parser_AST.Product uu____54279 ->
        let uu____54286 = p_term false false e  in
        soft_parens_with_nesting uu____54286
    | FStar_Parser_AST.Sum uu____54289 ->
        let uu____54300 = p_term false false e  in
        soft_parens_with_nesting uu____54300
    | FStar_Parser_AST.QForall uu____54303 ->
        let uu____54316 = p_term false false e  in
        soft_parens_with_nesting uu____54316
    | FStar_Parser_AST.QExists uu____54319 ->
        let uu____54332 = p_term false false e  in
        soft_parens_with_nesting uu____54332
    | FStar_Parser_AST.Refine uu____54335 ->
        let uu____54340 = p_term false false e  in
        soft_parens_with_nesting uu____54340
    | FStar_Parser_AST.NamedTyp uu____54343 ->
        let uu____54348 = p_term false false e  in
        soft_parens_with_nesting uu____54348
    | FStar_Parser_AST.Requires uu____54351 ->
        let uu____54359 = p_term false false e  in
        soft_parens_with_nesting uu____54359
    | FStar_Parser_AST.Ensures uu____54362 ->
        let uu____54370 = p_term false false e  in
        soft_parens_with_nesting uu____54370
    | FStar_Parser_AST.Attributes uu____54373 ->
        let uu____54376 = p_term false false e  in
        soft_parens_with_nesting uu____54376
    | FStar_Parser_AST.Quote uu____54379 ->
        let uu____54384 = p_term false false e  in
        soft_parens_with_nesting uu____54384
    | FStar_Parser_AST.VQuote uu____54387 ->
        let uu____54388 = p_term false false e  in
        soft_parens_with_nesting uu____54388
    | FStar_Parser_AST.Antiquote uu____54391 ->
        let uu____54392 = p_term false false e  in
        soft_parens_with_nesting uu____54392
    | FStar_Parser_AST.CalcProof uu____54395 ->
        let uu____54404 = p_term false false e  in
        soft_parens_with_nesting uu____54404

and (p_constant : FStar_Const.sconst -> FStar_Pprint.document) =
  fun uu___339_54407  ->
    match uu___339_54407 with
    | FStar_Const.Const_effect  -> str "Effect"
    | FStar_Const.Const_unit  -> str "()"
    | FStar_Const.Const_bool b -> FStar_Pprint.doc_of_bool b
    | FStar_Const.Const_real r -> str (Prims.op_Hat r "R")
    | FStar_Const.Const_float x -> str (FStar_Util.string_of_float x)
    | FStar_Const.Const_char x -> FStar_Pprint.doc_of_char x
    | FStar_Const.Const_string (s,uu____54419) ->
        let uu____54422 = str (FStar_String.escaped s)  in
        FStar_Pprint.dquotes uu____54422
    | FStar_Const.Const_bytearray (bytes,uu____54424) ->
        let uu____54429 =
          let uu____54430 = str (FStar_Util.string_of_bytes bytes)  in
          FStar_Pprint.dquotes uu____54430  in
        let uu____54431 = str "B"  in
        FStar_Pprint.op_Hat_Hat uu____54429 uu____54431
    | FStar_Const.Const_int (repr,sign_width_opt) ->
        let signedness uu___337_54454 =
          match uu___337_54454 with
          | FStar_Const.Unsigned  -> str "u"
          | FStar_Const.Signed  -> FStar_Pprint.empty  in
        let width uu___338_54461 =
          match uu___338_54461 with
          | FStar_Const.Int8  -> str "y"
          | FStar_Const.Int16  -> str "s"
          | FStar_Const.Int32  -> str "l"
          | FStar_Const.Int64  -> str "L"  in
        let ending =
          default_or_map FStar_Pprint.empty
            (fun uu____54476  ->
               match uu____54476 with
               | (s,w) ->
                   let uu____54483 = signedness s  in
                   let uu____54484 = width w  in
                   FStar_Pprint.op_Hat_Hat uu____54483 uu____54484)
            sign_width_opt
           in
        let uu____54485 = str repr  in
        FStar_Pprint.op_Hat_Hat uu____54485 ending
    | FStar_Const.Const_range_of  -> str "range_of"
    | FStar_Const.Const_set_range_of  -> str "set_range_of"
    | FStar_Const.Const_range r ->
        let uu____54489 = FStar_Range.string_of_range r  in str uu____54489
    | FStar_Const.Const_reify  -> str "reify"
    | FStar_Const.Const_reflect lid ->
        let uu____54493 = p_quident lid  in
        let uu____54494 =
          let uu____54495 =
            let uu____54496 = str "reflect"  in
            FStar_Pprint.op_Hat_Hat FStar_Pprint.dot uu____54496  in
          FStar_Pprint.op_Hat_Hat FStar_Pprint.qmark uu____54495  in
        FStar_Pprint.op_Hat_Hat uu____54493 uu____54494

and (p_universe : FStar_Parser_AST.term -> FStar_Pprint.document) =
  fun u  ->
    let uu____54499 = str "u#"  in
    let uu____54501 = p_atomicUniverse u  in
    FStar_Pprint.op_Hat_Hat uu____54499 uu____54501

and (p_universeFrom : FStar_Parser_AST.term -> FStar_Pprint.document) =
  fun u  ->
    match u.FStar_Parser_AST.tm with
    | FStar_Parser_AST.Op
        ({ FStar_Ident.idText = "+"; FStar_Ident.idRange = uu____54503;_},u1::u2::[])
        ->
        let uu____54509 =
          let uu____54510 = p_universeFrom u1  in
          let uu____54511 =
            let uu____54512 = p_universeFrom u2  in
            FStar_Pprint.op_Hat_Slash_Hat FStar_Pprint.plus uu____54512  in
          FStar_Pprint.op_Hat_Slash_Hat uu____54510 uu____54511  in
        FStar_Pprint.group uu____54509
    | FStar_Parser_AST.App uu____54513 ->
        let uu____54520 = head_and_args u  in
        (match uu____54520 with
         | (head1,args) ->
             (match head1.FStar_Parser_AST.tm with
              | FStar_Parser_AST.Var maybe_max_lid when
                  FStar_Ident.lid_equals maybe_max_lid
                    FStar_Parser_Const.max_lid
                  ->
                  let uu____54546 =
                    let uu____54547 = p_qlident FStar_Parser_Const.max_lid
                       in
                    let uu____54548 =
                      FStar_Pprint.separate_map FStar_Pprint.space
                        (fun uu____54556  ->
                           match uu____54556 with
                           | (u1,uu____54562) -> p_atomicUniverse u1) args
                       in
                    op_Hat_Slash_Plus_Hat uu____54547 uu____54548  in
                  FStar_Pprint.group uu____54546
              | uu____54563 ->
                  let uu____54564 =
                    let uu____54566 = FStar_Parser_AST.term_to_string u  in
                    FStar_Util.format1 "Invalid term in universe context %s"
                      uu____54566
                     in
                  failwith uu____54564))
    | uu____54569 -> p_atomicUniverse u

and (p_atomicUniverse : FStar_Parser_AST.term -> FStar_Pprint.document) =
  fun u  ->
    match u.FStar_Parser_AST.tm with
    | FStar_Parser_AST.Wild  -> FStar_Pprint.underscore
    | FStar_Parser_AST.Const (FStar_Const.Const_int (r,sw)) ->
        p_constant (FStar_Const.Const_int (r, sw))
    | FStar_Parser_AST.Uvar id1 ->
        let uu____54595 = FStar_Ident.text_of_id id1  in str uu____54595
    | FStar_Parser_AST.Paren u1 ->
        let uu____54598 = p_universeFrom u1  in
        soft_parens_with_nesting uu____54598
    | FStar_Parser_AST.Op
        ({ FStar_Ident.idText = "+"; FStar_Ident.idRange = uu____54599;_},uu____54600::uu____54601::[])
        ->
        let uu____54605 = p_universeFrom u  in
        soft_parens_with_nesting uu____54605
    | FStar_Parser_AST.App uu____54606 ->
        let uu____54613 = p_universeFrom u  in
        soft_parens_with_nesting uu____54613
    | uu____54614 ->
        let uu____54615 =
          let uu____54617 = FStar_Parser_AST.term_to_string u  in
          FStar_Util.format1 "Invalid term in universe context %s"
            uu____54617
           in
        failwith uu____54615

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
       | FStar_Parser_AST.Module (uu____54706,decls) ->
           let uu____54712 =
             FStar_All.pipe_right decls (FStar_List.map decl_to_document)  in
           FStar_All.pipe_right uu____54712
             (FStar_Pprint.separate FStar_Pprint.hardline)
       | FStar_Parser_AST.Interface (uu____54721,decls,uu____54723) ->
           let uu____54730 =
             FStar_All.pipe_right decls (FStar_List.map decl_to_document)  in
           FStar_All.pipe_right uu____54730
             (FStar_Pprint.separate FStar_Pprint.hardline)
        in
     FStar_ST.op_Colon_Equals should_print_fs_typ_app false; res)
  
let (comments_to_document :
  (Prims.string * FStar_Range.range) Prims.list -> FStar_Pprint.document) =
  fun comments  ->
    FStar_Pprint.separate_map FStar_Pprint.hardline
      (fun uu____54790  ->
         match uu____54790 with | (comment,range) -> str comment) comments
  
let (extract_decl_range : FStar_Parser_AST.decl -> decl_meta) =
  fun d  ->
    let has_qs =
      match ((d.FStar_Parser_AST.quals), (d.FStar_Parser_AST.d)) with
      | ((FStar_Parser_AST.Assumption )::[],FStar_Parser_AST.Assume
         (id1,uu____54812)) -> false
      | ([],uu____54816) -> false
      | uu____54820 -> true  in
    {
      r = (d.FStar_Parser_AST.drange);
      has_qs;
      has_attrs =
        (Prims.op_Negation (FStar_List.isEmpty d.FStar_Parser_AST.attrs));
      has_fsdoc = (FStar_Util.is_some d.FStar_Parser_AST.doc);
      is_fsdoc =
        (match d.FStar_Parser_AST.d with
         | FStar_Parser_AST.Fsdoc uu____54830 -> true
         | uu____54832 -> false)
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
        | FStar_Parser_AST.Module (uu____54875,decls) -> decls
        | FStar_Parser_AST.Interface (uu____54881,decls,uu____54883) -> decls
         in
      FStar_ST.op_Colon_Equals should_print_fs_typ_app false;
      (match decls with
       | [] -> (FStar_Pprint.empty, comments)
       | d::ds ->
           let uu____54935 =
             match ds with
             | {
                 FStar_Parser_AST.d = FStar_Parser_AST.Pragma
                   (FStar_Parser_AST.LightOff );
                 FStar_Parser_AST.drange = uu____54948;
                 FStar_Parser_AST.doc = uu____54949;
                 FStar_Parser_AST.quals = uu____54950;
                 FStar_Parser_AST.attrs = uu____54951;_}::uu____54952 ->
                 let d0 = FStar_List.hd ds  in
                 let uu____54958 =
                   let uu____54961 =
                     let uu____54964 = FStar_List.tl ds  in d :: uu____54964
                      in
                   d0 :: uu____54961  in
                 (uu____54958, (d0.FStar_Parser_AST.drange))
             | uu____54969 -> ((d :: ds), (d.FStar_Parser_AST.drange))  in
           (match uu____54935 with
            | (decls1,first_range) ->
                (FStar_ST.op_Colon_Equals comment_stack comments;
                 (let initial_comment =
                    let uu____55026 = FStar_Range.start_of_range first_range
                       in
                    place_comments_until_pos (Prims.parse_int "0")
                      (Prims.parse_int "1") uu____55026 dummy_meta
                      FStar_Pprint.empty false true
                     in
                  let doc1 =
                    separate_map_with_comments FStar_Pprint.empty
                      FStar_Pprint.empty p_decl decls1 extract_decl_range
                     in
                  let comments1 = FStar_ST.op_Bang comment_stack  in
                  FStar_ST.op_Colon_Equals comment_stack [];
                  FStar_ST.op_Colon_Equals should_print_fs_typ_app false;
                  (let uu____55135 =
                     FStar_Pprint.op_Hat_Hat initial_comment doc1  in
                   (uu____55135, comments1))))))
  