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
            let uu____43259 = let uu____43262 = f x  in uu____43262 :: acc
               in
            aux xs uu____43259
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
            let uu____43329 = f x  in
            (match uu____43329 with
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
          let uu____43385 = f x  in if uu____43385 then all f xs else false
  
let (all_explicit :
  (FStar_Parser_AST.term * FStar_Parser_AST.imp) Prims.list -> Prims.bool) =
  fun args  ->
    FStar_Util.for_all
      (fun uu___324_43418  ->
         match uu___324_43418 with
         | (uu____43424,FStar_Parser_AST.Nothing ) -> true
         | uu____43426 -> false) args
  
let (should_print_fs_typ_app : Prims.bool FStar_ST.ref) =
  FStar_Util.mk_ref false 
let (unfold_tuples : Prims.bool FStar_ST.ref) = FStar_Util.mk_ref true 
let with_fs_typ_app :
  'Auu____43477 'Auu____43478 .
    Prims.bool ->
      ('Auu____43477 -> 'Auu____43478) -> 'Auu____43477 -> 'Auu____43478
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
  'Auu____43588 'Auu____43589 .
    'Auu____43588 ->
      ('Auu____43589 -> 'Auu____43588) ->
        'Auu____43589 FStar_Pervasives_Native.option -> 'Auu____43588
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
  'Auu____43702 .
    FStar_Pprint.document ->
      ('Auu____43702 -> FStar_Pprint.document) ->
        'Auu____43702 Prims.list -> FStar_Pprint.document
  =
  fun sep  ->
    fun f  ->
      fun l  ->
        let uu____43727 =
          let uu____43728 =
            let uu____43729 = FStar_Pprint.op_Hat_Hat sep break1  in
            FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____43729  in
          FStar_Pprint.separate_map uu____43728 f l  in
        FStar_Pprint.group uu____43727
  
let precede_break_separate_map :
  'Auu____43741 .
    FStar_Pprint.document ->
      FStar_Pprint.document ->
        ('Auu____43741 -> FStar_Pprint.document) ->
          'Auu____43741 Prims.list -> FStar_Pprint.document
  =
  fun prec  ->
    fun sep  ->
      fun f  ->
        fun l  ->
          let uu____43771 =
            let uu____43772 = FStar_Pprint.op_Hat_Hat prec FStar_Pprint.space
               in
            let uu____43773 =
              let uu____43774 = FStar_List.hd l  in
              FStar_All.pipe_right uu____43774 f  in
            FStar_Pprint.precede uu____43772 uu____43773  in
          let uu____43775 =
            let uu____43776 = FStar_List.tl l  in
            FStar_Pprint.concat_map
              (fun x  ->
                 let uu____43782 =
                   let uu____43783 =
                     let uu____43784 = f x  in
                     FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____43784
                      in
                   FStar_Pprint.op_Hat_Hat sep uu____43783  in
                 FStar_Pprint.op_Hat_Hat break1 uu____43782) uu____43776
             in
          FStar_Pprint.op_Hat_Hat uu____43771 uu____43775
  
let concat_break_map :
  'Auu____43792 .
    ('Auu____43792 -> FStar_Pprint.document) ->
      'Auu____43792 Prims.list -> FStar_Pprint.document
  =
  fun f  ->
    fun l  ->
      let uu____43812 =
        FStar_Pprint.concat_map
          (fun x  ->
             let uu____43816 = f x  in
             FStar_Pprint.op_Hat_Hat uu____43816 break1) l
         in
      FStar_Pprint.group uu____43812
  
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
    let uu____43879 = str "begin"  in
    let uu____43881 = str "end"  in
    FStar_Pprint.soft_surround (Prims.parse_int "2") (Prims.parse_int "1")
      uu____43879 contents uu____43881
  
let separate_map_last :
  'Auu____43894 .
    FStar_Pprint.document ->
      (Prims.bool -> 'Auu____43894 -> FStar_Pprint.document) ->
        'Auu____43894 Prims.list -> FStar_Pprint.document
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
  'Auu____43952 .
    FStar_Pprint.document ->
      (Prims.bool -> 'Auu____43952 -> FStar_Pprint.document) ->
        'Auu____43952 Prims.list -> FStar_Pprint.document
  =
  fun sep  ->
    fun f  ->
      fun l  ->
        let uu____43984 =
          let uu____43985 =
            let uu____43986 = FStar_Pprint.op_Hat_Hat sep break1  in
            FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____43986  in
          separate_map_last uu____43985 f l  in
        FStar_Pprint.group uu____43984
  
let separate_map_or_flow :
  'Auu____43996 .
    FStar_Pprint.document ->
      ('Auu____43996 -> FStar_Pprint.document) ->
        'Auu____43996 Prims.list -> FStar_Pprint.document
  =
  fun sep  ->
    fun f  ->
      fun l  ->
        if (FStar_List.length l) < (Prims.parse_int "10")
        then FStar_Pprint.separate_map sep f l
        else FStar_Pprint.flow_map sep f l
  
let flow_map_last :
  'Auu____44034 .
    FStar_Pprint.document ->
      (Prims.bool -> 'Auu____44034 -> FStar_Pprint.document) ->
        'Auu____44034 Prims.list -> FStar_Pprint.document
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
  'Auu____44092 .
    FStar_Pprint.document ->
      (Prims.bool -> 'Auu____44092 -> FStar_Pprint.document) ->
        'Auu____44092 Prims.list -> FStar_Pprint.document
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
              let uu____44174 = FStar_Pprint.op_Hat_Slash_Hat doc1 doc3  in
              FStar_Pprint.group uu____44174
            else FStar_Pprint.surround n1 b doc1 doc2 doc3
  
let soft_surround_separate_map :
  'Auu____44196 .
    Prims.int ->
      Prims.int ->
        FStar_Pprint.document ->
          FStar_Pprint.document ->
            FStar_Pprint.document ->
              FStar_Pprint.document ->
                ('Auu____44196 -> FStar_Pprint.document) ->
                  'Auu____44196 Prims.list -> FStar_Pprint.document
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
                    (let uu____44255 = FStar_Pprint.separate_map sep f xs  in
                     FStar_Pprint.soft_surround n1 b opening uu____44255
                       closing)
  
let soft_surround_map_or_flow :
  'Auu____44275 .
    Prims.int ->
      Prims.int ->
        FStar_Pprint.document ->
          FStar_Pprint.document ->
            FStar_Pprint.document ->
              FStar_Pprint.document ->
                ('Auu____44275 -> FStar_Pprint.document) ->
                  'Auu____44275 Prims.list -> FStar_Pprint.document
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
                    (let uu____44334 = separate_map_or_flow sep f xs  in
                     FStar_Pprint.soft_surround n1 b opening uu____44334
                       closing)
  
let (doc_of_fsdoc :
  (Prims.string * (Prims.string * Prims.string) Prims.list) ->
    FStar_Pprint.document)
  =
  fun uu____44353  ->
    match uu____44353 with
    | (comment,keywords) ->
        let uu____44387 =
          let uu____44388 =
            let uu____44391 = str comment  in
            let uu____44392 =
              let uu____44395 =
                let uu____44398 =
                  FStar_Pprint.separate_map FStar_Pprint.comma
                    (fun uu____44409  ->
                       match uu____44409 with
                       | (k,v1) ->
                           let uu____44422 =
                             let uu____44425 = str k  in
                             let uu____44426 =
                               let uu____44429 =
                                 let uu____44432 = str v1  in [uu____44432]
                                  in
                               FStar_Pprint.rarrow :: uu____44429  in
                             uu____44425 :: uu____44426  in
                           FStar_Pprint.concat uu____44422) keywords
                   in
                [uu____44398]  in
              FStar_Pprint.space :: uu____44395  in
            uu____44391 :: uu____44392  in
          FStar_Pprint.concat uu____44388  in
        FStar_Pprint.group uu____44387
  
let (is_unit : FStar_Parser_AST.term -> Prims.bool) =
  fun e  ->
    match e.FStar_Parser_AST.tm with
    | FStar_Parser_AST.Const (FStar_Const.Const_unit ) -> true
    | uu____44442 -> false
  
let (matches_var : FStar_Parser_AST.term -> FStar_Ident.ident -> Prims.bool)
  =
  fun t  ->
    fun x  ->
      match t.FStar_Parser_AST.tm with
      | FStar_Parser_AST.Var y ->
          let uu____44458 = FStar_Ident.text_of_lid y  in
          x.FStar_Ident.idText = uu____44458
      | uu____44461 -> false
  
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
        | FStar_Parser_AST.Construct (lid,uu____44512::(e2,uu____44514)::[])
            -> (FStar_Ident.lid_equals lid cons_lid1) && (aux e2)
        | uu____44537 -> false  in
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
    | FStar_Parser_AST.Construct (uu____44561,[]) -> []
    | FStar_Parser_AST.Construct
        (uu____44572,(e1,FStar_Parser_AST.Nothing )::(e2,FStar_Parser_AST.Nothing
                                                      )::[])
        -> let uu____44593 = extract_from_list e2  in e1 :: uu____44593
    | uu____44596 ->
        let uu____44597 =
          let uu____44599 = FStar_Parser_AST.term_to_string e  in
          FStar_Util.format1 "Not a list %s" uu____44599  in
        failwith uu____44597
  
let (is_array : FStar_Parser_AST.term -> Prims.bool) =
  fun e  ->
    match e.FStar_Parser_AST.tm with
    | FStar_Parser_AST.App
        ({ FStar_Parser_AST.tm = FStar_Parser_AST.Var lid;
           FStar_Parser_AST.range = uu____44613;
           FStar_Parser_AST.level = uu____44614;_},l,FStar_Parser_AST.Nothing
         )
        ->
        (FStar_Ident.lid_equals lid FStar_Parser_Const.array_mk_array_lid) &&
          (is_list l)
    | uu____44616 -> false
  
let rec (is_ref_set : FStar_Parser_AST.term -> Prims.bool) =
  fun e  ->
    match e.FStar_Parser_AST.tm with
    | FStar_Parser_AST.Var maybe_empty_lid ->
        FStar_Ident.lid_equals maybe_empty_lid FStar_Parser_Const.set_empty
    | FStar_Parser_AST.App
        ({ FStar_Parser_AST.tm = FStar_Parser_AST.Var maybe_singleton_lid;
           FStar_Parser_AST.range = uu____44628;
           FStar_Parser_AST.level = uu____44629;_},{
                                                     FStar_Parser_AST.tm =
                                                       FStar_Parser_AST.App
                                                       ({
                                                          FStar_Parser_AST.tm
                                                            =
                                                            FStar_Parser_AST.Var
                                                            maybe_addr_of_lid;
                                                          FStar_Parser_AST.range
                                                            = uu____44631;
                                                          FStar_Parser_AST.level
                                                            = uu____44632;_},e1,FStar_Parser_AST.Nothing
                                                        );
                                                     FStar_Parser_AST.range =
                                                       uu____44634;
                                                     FStar_Parser_AST.level =
                                                       uu____44635;_},FStar_Parser_AST.Nothing
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
                FStar_Parser_AST.range = uu____44637;
                FStar_Parser_AST.level = uu____44638;_},e1,FStar_Parser_AST.Nothing
              );
           FStar_Parser_AST.range = uu____44640;
           FStar_Parser_AST.level = uu____44641;_},e2,FStar_Parser_AST.Nothing
         )
        ->
        ((FStar_Ident.lid_equals maybe_union_lid FStar_Parser_Const.set_union)
           && (is_ref_set e1))
          && (is_ref_set e2)
    | uu____44643 -> false
  
let rec (extract_from_ref_set :
  FStar_Parser_AST.term -> FStar_Parser_AST.term Prims.list) =
  fun e  ->
    match e.FStar_Parser_AST.tm with
    | FStar_Parser_AST.Var uu____44655 -> []
    | FStar_Parser_AST.App
        ({ FStar_Parser_AST.tm = FStar_Parser_AST.Var uu____44656;
           FStar_Parser_AST.range = uu____44657;
           FStar_Parser_AST.level = uu____44658;_},{
                                                     FStar_Parser_AST.tm =
                                                       FStar_Parser_AST.App
                                                       ({
                                                          FStar_Parser_AST.tm
                                                            =
                                                            FStar_Parser_AST.Var
                                                            uu____44659;
                                                          FStar_Parser_AST.range
                                                            = uu____44660;
                                                          FStar_Parser_AST.level
                                                            = uu____44661;_},e1,FStar_Parser_AST.Nothing
                                                        );
                                                     FStar_Parser_AST.range =
                                                       uu____44663;
                                                     FStar_Parser_AST.level =
                                                       uu____44664;_},FStar_Parser_AST.Nothing
         )
        -> [e1]
    | FStar_Parser_AST.App
        ({
           FStar_Parser_AST.tm = FStar_Parser_AST.App
             ({ FStar_Parser_AST.tm = FStar_Parser_AST.Var uu____44665;
                FStar_Parser_AST.range = uu____44666;
                FStar_Parser_AST.level = uu____44667;_},e1,FStar_Parser_AST.Nothing
              );
           FStar_Parser_AST.range = uu____44669;
           FStar_Parser_AST.level = uu____44670;_},e2,FStar_Parser_AST.Nothing
         )
        ->
        let uu____44672 = extract_from_ref_set e1  in
        let uu____44675 = extract_from_ref_set e2  in
        FStar_List.append uu____44672 uu____44675
    | uu____44678 ->
        let uu____44679 =
          let uu____44681 = FStar_Parser_AST.term_to_string e  in
          FStar_Util.format1 "Not a ref set %s" uu____44681  in
        failwith uu____44679
  
let (is_general_application : FStar_Parser_AST.term -> Prims.bool) =
  fun e  ->
    let uu____44693 = (is_array e) || (is_ref_set e)  in
    Prims.op_Negation uu____44693
  
let (is_general_construction : FStar_Parser_AST.term -> Prims.bool) =
  fun e  ->
    let uu____44702 = (is_list e) || (is_lex_list e)  in
    Prims.op_Negation uu____44702
  
let (is_general_prefix_op : FStar_Ident.ident -> Prims.bool) =
  fun op  ->
    let op_starting_char =
      let uu____44713 = FStar_Ident.text_of_id op  in
      FStar_Util.char_at uu____44713 (Prims.parse_int "0")  in
    ((op_starting_char = 33) || (op_starting_char = 63)) ||
      ((op_starting_char = 126) &&
         (let uu____44723 = FStar_Ident.text_of_id op  in uu____44723 <> "~"))
  
let (head_and_args :
  FStar_Parser_AST.term ->
    (FStar_Parser_AST.term * (FStar_Parser_AST.term * FStar_Parser_AST.imp)
      Prims.list))
  =
  fun e  ->
    let rec aux e1 acc =
      match e1.FStar_Parser_AST.tm with
      | FStar_Parser_AST.App (head1,arg,imp) -> aux head1 ((arg, imp) :: acc)
      | uu____44793 -> (e1, acc)  in
    aux e []
  
type associativity =
  | Left 
  | Right 
  | NonAssoc 
let (uu___is_Left : associativity -> Prims.bool) =
  fun projectee  ->
    match projectee with | Left  -> true | uu____44813 -> false
  
let (uu___is_Right : associativity -> Prims.bool) =
  fun projectee  ->
    match projectee with | Right  -> true | uu____44824 -> false
  
let (uu___is_NonAssoc : associativity -> Prims.bool) =
  fun projectee  ->
    match projectee with | NonAssoc  -> true | uu____44835 -> false
  
type token = (FStar_Char.char,Prims.string) FStar_Util.either
type associativity_level = (associativity * token Prims.list)
let (token_to_string :
  (FStar_BaseTypes.char,Prims.string) FStar_Util.either -> Prims.string) =
  fun uu___325_44861  ->
    match uu___325_44861 with
    | FStar_Util.Inl c -> Prims.op_Hat (FStar_Util.string_of_char c) ".*"
    | FStar_Util.Inr s -> s
  
let (matches_token :
  Prims.string ->
    (FStar_Char.char,Prims.string) FStar_Util.either -> Prims.bool)
  =
  fun s  ->
    fun uu___326_44896  ->
      match uu___326_44896 with
      | FStar_Util.Inl c ->
          let uu____44909 = FStar_String.get s (Prims.parse_int "0")  in
          uu____44909 = c
      | FStar_Util.Inr s' -> s = s'
  
let matches_level :
  'Auu____44925 .
    Prims.string ->
      ('Auu____44925 * (FStar_Char.char,Prims.string) FStar_Util.either
        Prims.list) -> Prims.bool
  =
  fun s  ->
    fun uu____44949  ->
      match uu____44949 with
      | (assoc_levels,tokens) ->
          let uu____44981 = FStar_List.tryFind (matches_token s) tokens  in
          uu____44981 <> FStar_Pervasives_Native.None
  
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
  let levels_from_associativity l uu___327_45153 =
    match uu___327_45153 with
    | Left  -> (l, l, (l - (Prims.parse_int "1")))
    | Right  -> ((l - (Prims.parse_int "1")), l, l)
    | NonAssoc  ->
        ((l - (Prims.parse_int "1")), l, (l - (Prims.parse_int "1")))
     in
  FStar_List.mapi
    (fun i  ->
       fun uu____45203  ->
         match uu____45203 with
         | (assoc1,tokens) -> ((levels_from_associativity i assoc1), tokens))
    level_associativity_spec
  
let (assign_levels :
  associativity_level Prims.list ->
    Prims.string -> (Prims.int * Prims.int * Prims.int))
  =
  fun token_associativity_spec  ->
    fun s  ->
      let uu____45278 = FStar_List.tryFind (matches_level s) level_table  in
      match uu____45278 with
      | FStar_Pervasives_Native.Some (assoc_levels,uu____45330) ->
          assoc_levels
      | uu____45368 -> failwith (Prims.op_Hat "Unrecognized operator " s)
  
let max_level :
  'Auu____45401 . ('Auu____45401 * token Prims.list) Prims.list -> Prims.int
  =
  fun l  ->
    let find_level_and_max n1 level =
      let uu____45450 =
        FStar_List.tryFind
          (fun uu____45486  ->
             match uu____45486 with
             | (uu____45503,tokens) ->
                 tokens = (FStar_Pervasives_Native.snd level)) level_table
         in
      match uu____45450 with
      | FStar_Pervasives_Native.Some
          ((uu____45532,l1,uu____45534),uu____45535) -> max n1 l1
      | FStar_Pervasives_Native.None  ->
          let uu____45585 =
            let uu____45587 =
              let uu____45589 =
                FStar_List.map token_to_string
                  (FStar_Pervasives_Native.snd level)
                 in
              FStar_String.concat "," uu____45589  in
            FStar_Util.format1 "Undefined associativity level %s" uu____45587
             in
          failwith uu____45585
       in
    FStar_List.fold_left find_level_and_max (Prims.parse_int "0") l
  
let (levels : Prims.string -> (Prims.int * Prims.int * Prims.int)) =
  fun op  ->
    let uu____45624 = assign_levels level_associativity_spec op  in
    match uu____45624 with
    | (left1,mine,right1) ->
        if op = "*"
        then ((left1 - (Prims.parse_int "1")), mine, right1)
        else (left1, mine, right1)
  
let (operatorInfix0ad12 : associativity_level Prims.list) =
  [opinfix0a; opinfix0b; opinfix0c; opinfix0d; opinfix1; opinfix2] 
let (is_operatorInfix0ad12 : FStar_Ident.ident -> Prims.bool) =
  fun op  ->
    let uu____45683 =
      let uu____45686 =
        let uu____45692 = FStar_Ident.text_of_id op  in
        FStar_All.pipe_left matches_level uu____45692  in
      FStar_List.tryFind uu____45686 operatorInfix0ad12  in
    uu____45683 <> FStar_Pervasives_Native.None
  
let (is_operatorInfix34 : FStar_Ident.ident -> Prims.bool) =
  let opinfix34 = [opinfix3; opinfix4]  in
  fun op  ->
    let uu____45759 =
      let uu____45774 =
        let uu____45792 = FStar_Ident.text_of_id op  in
        FStar_All.pipe_left matches_level uu____45792  in
      FStar_List.tryFind uu____45774 opinfix34  in
    uu____45759 <> FStar_Pervasives_Native.None
  
let (handleable_args_length : FStar_Ident.ident -> Prims.int) =
  fun op  ->
    let op_s = FStar_Ident.text_of_id op  in
    let uu____45858 =
      (is_general_prefix_op op) || (FStar_List.mem op_s ["-"; "~"])  in
    if uu____45858
    then (Prims.parse_int "1")
    else
      (let uu____45871 =
         ((is_operatorInfix0ad12 op) || (is_operatorInfix34 op)) ||
           (FStar_List.mem op_s
              ["<==>"; "==>"; "\\/"; "/\\"; "="; "|>"; ":="; ".()"; ".[]"])
          in
       if uu____45871
       then (Prims.parse_int "2")
       else
         if FStar_List.mem op_s [".()<-"; ".[]<-"]
         then (Prims.parse_int "3")
         else (Prims.parse_int "0"))
  
let handleable_op :
  'Auu____45917 . FStar_Ident.ident -> 'Auu____45917 Prims.list -> Prims.bool
  =
  fun op  ->
    fun args  ->
      match FStar_List.length args with
      | _45933 when _45933 = (Prims.parse_int "0") -> true
      | _45935 when _45935 = (Prims.parse_int "1") ->
          (is_general_prefix_op op) ||
            (let uu____45937 = FStar_Ident.text_of_id op  in
             FStar_List.mem uu____45937 ["-"; "~"])
      | _45945 when _45945 = (Prims.parse_int "2") ->
          ((is_operatorInfix0ad12 op) || (is_operatorInfix34 op)) ||
            (let uu____45947 = FStar_Ident.text_of_id op  in
             FStar_List.mem uu____45947
               ["<==>"; "==>"; "\\/"; "/\\"; "="; "|>"; ":="; ".()"; ".[]"])
      | _45969 when _45969 = (Prims.parse_int "3") ->
          let uu____45970 = FStar_Ident.text_of_id op  in
          FStar_List.mem uu____45970 [".()<-"; ".[]<-"]
      | uu____45978 -> false
  
type annotation_style =
  | Binders of (Prims.int * Prims.int * Prims.bool) 
  | Arrows of (Prims.int * Prims.int) 
let (uu___is_Binders : annotation_style -> Prims.bool) =
  fun projectee  ->
    match projectee with | Binders _0 -> true | uu____46024 -> false
  
let (__proj__Binders__item___0 :
  annotation_style -> (Prims.int * Prims.int * Prims.bool)) =
  fun projectee  -> match projectee with | Binders _0 -> _0 
let (uu___is_Arrows : annotation_style -> Prims.bool) =
  fun projectee  ->
    match projectee with | Arrows _0 -> true | uu____46077 -> false
  
let (__proj__Arrows__item___0 : annotation_style -> (Prims.int * Prims.int))
  = fun projectee  -> match projectee with | Arrows _0 -> _0 
let (all_binders_annot : FStar_Parser_AST.term -> Prims.bool) =
  fun e  ->
    let is_binder_annot b =
      match b.FStar_Parser_AST.b with
      | FStar_Parser_AST.Annotated uu____46120 -> true
      | uu____46126 -> false  in
    let rec all_binders e1 l =
      match e1.FStar_Parser_AST.tm with
      | FStar_Parser_AST.Product (bs,tgt) ->
          let uu____46159 = FStar_List.for_all is_binder_annot bs  in
          if uu____46159
          then all_binders tgt (l + (FStar_List.length bs))
          else (false, (Prims.parse_int "0"))
      | uu____46174 -> (true, (l + (Prims.parse_int "1")))  in
    let uu____46179 = all_binders e (Prims.parse_int "0")  in
    match uu____46179 with
    | (b,l) -> if b && (l > (Prims.parse_int "1")) then true else false
  
type catf =
  FStar_Pprint.document -> FStar_Pprint.document -> FStar_Pprint.document
let (cat_with_colon :
  FStar_Pprint.document -> FStar_Pprint.document -> FStar_Pprint.document) =
  fun x  ->
    fun y  ->
      let uu____46218 = FStar_Pprint.op_Hat_Slash_Hat FStar_Pprint.colon y
         in
      FStar_Pprint.op_Hat_Hat x uu____46218
  
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
  'Auu____46378 .
    ('Auu____46378 -> FStar_Pprint.document) ->
      'Auu____46378 -> FStar_Range.range -> FStar_Pprint.document
  =
  fun printer  ->
    fun tm  ->
      fun tmrange  ->
        let rec comments_before_pos acc print_pos lookahead_pos =
          let uu____46420 = FStar_ST.op_Bang comment_stack  in
          match uu____46420 with
          | [] -> (acc, false)
          | (c,crange)::cs ->
              let comment =
                let uu____46491 = str c  in
                FStar_Pprint.op_Hat_Hat uu____46491 FStar_Pprint.hardline  in
              let uu____46492 = FStar_Range.range_before_pos crange print_pos
                 in
              if uu____46492
              then
                (FStar_ST.op_Colon_Equals comment_stack cs;
                 (let uu____46534 = FStar_Pprint.op_Hat_Hat acc comment  in
                  comments_before_pos uu____46534 print_pos lookahead_pos))
              else
                (let uu____46537 =
                   FStar_Range.range_before_pos crange lookahead_pos  in
                 (acc, uu____46537))
           in
        let uu____46540 =
          let uu____46546 =
            let uu____46547 = FStar_Range.start_of_range tmrange  in
            FStar_Range.end_of_line uu____46547  in
          let uu____46548 = FStar_Range.end_of_range tmrange  in
          comments_before_pos FStar_Pprint.empty uu____46546 uu____46548  in
        match uu____46540 with
        | (comments,has_lookahead) ->
            let printed_e = printer tm  in
            let comments1 =
              if has_lookahead
              then
                let pos = FStar_Range.end_of_range tmrange  in
                let uu____46557 = comments_before_pos comments pos pos  in
                FStar_Pervasives_Native.fst uu____46557
              else comments  in
            if comments1 = FStar_Pprint.empty
            then printed_e
            else
              (let uu____46569 = FStar_Pprint.op_Hat_Hat comments1 printed_e
                  in
               FStar_Pprint.group uu____46569)
  
let with_comment_sep :
  'Auu____46581 'Auu____46582 .
    ('Auu____46581 -> 'Auu____46582) ->
      'Auu____46581 ->
        FStar_Range.range -> (FStar_Pprint.document * 'Auu____46582)
  =
  fun printer  ->
    fun tm  ->
      fun tmrange  ->
        let rec comments_before_pos acc print_pos lookahead_pos =
          let uu____46628 = FStar_ST.op_Bang comment_stack  in
          match uu____46628 with
          | [] -> (acc, false)
          | (c,crange)::cs ->
              let comment = str c  in
              let uu____46699 = FStar_Range.range_before_pos crange print_pos
                 in
              if uu____46699
              then
                (FStar_ST.op_Colon_Equals comment_stack cs;
                 (let uu____46741 =
                    if acc = FStar_Pprint.empty
                    then comment
                    else
                      (let uu____46745 =
                         FStar_Pprint.op_Hat_Hat FStar_Pprint.hardline
                           comment
                          in
                       FStar_Pprint.op_Hat_Hat acc uu____46745)
                     in
                  comments_before_pos uu____46741 print_pos lookahead_pos))
              else
                (let uu____46748 =
                   FStar_Range.range_before_pos crange lookahead_pos  in
                 (acc, uu____46748))
           in
        let uu____46751 =
          let uu____46757 =
            let uu____46758 = FStar_Range.start_of_range tmrange  in
            FStar_Range.end_of_line uu____46758  in
          let uu____46759 = FStar_Range.end_of_range tmrange  in
          comments_before_pos FStar_Pprint.empty uu____46757 uu____46759  in
        match uu____46751 with
        | (comments,has_lookahead) ->
            let printed_e = printer tm  in
            let comments1 =
              if has_lookahead
              then
                let pos = FStar_Range.end_of_range tmrange  in
                let uu____46772 = comments_before_pos comments pos pos  in
                FStar_Pervasives_Native.fst uu____46772
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
                let uu____46825 = FStar_ST.op_Bang comment_stack  in
                match uu____46825 with
                | (comment,crange)::cs when
                    FStar_Range.range_before_pos crange pos ->
                    (FStar_ST.op_Colon_Equals comment_stack cs;
                     (let lnum =
                        let uu____46919 =
                          let uu____46921 =
                            let uu____46923 =
                              FStar_Range.start_of_range crange  in
                            FStar_Range.line_of_pos uu____46923  in
                          uu____46921 - lbegin  in
                        max k uu____46919  in
                      let lnum1 = min (Prims.parse_int "2") lnum  in
                      let doc2 =
                        let uu____46928 =
                          let uu____46929 =
                            FStar_Pprint.repeat lnum1 FStar_Pprint.hardline
                             in
                          let uu____46930 = str comment  in
                          FStar_Pprint.op_Hat_Hat uu____46929 uu____46930  in
                        FStar_Pprint.op_Hat_Hat doc1 uu____46928  in
                      let uu____46931 =
                        let uu____46933 = FStar_Range.end_of_range crange  in
                        FStar_Range.line_of_pos uu____46933  in
                      place_comments_until_pos (Prims.parse_int "1")
                        uu____46931 pos meta_decl doc2 true init1))
                | uu____46936 ->
                    if doc1 = FStar_Pprint.empty
                    then FStar_Pprint.empty
                    else
                      (let lnum =
                         let uu____46949 = FStar_Range.line_of_pos pos  in
                         uu____46949 - lbegin  in
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
                       let uu____46991 =
                         FStar_Pprint.repeat lnum7 FStar_Pprint.hardline  in
                       FStar_Pprint.op_Hat_Hat doc1 uu____46991)
  
let separate_map_with_comments :
  'Auu____47005 .
    FStar_Pprint.document ->
      FStar_Pprint.document ->
        ('Auu____47005 -> FStar_Pprint.document) ->
          'Auu____47005 Prims.list ->
            ('Auu____47005 -> decl_meta) -> FStar_Pprint.document
  =
  fun prefix1  ->
    fun sep  ->
      fun f  ->
        fun xs  ->
          fun extract_meta  ->
            let fold_fun uu____47064 x =
              match uu____47064 with
              | (last_line,doc1) ->
                  let meta_decl = extract_meta x  in
                  let r = meta_decl.r  in
                  let doc2 =
                    let uu____47083 = FStar_Range.start_of_range r  in
                    place_comments_until_pos (Prims.parse_int "1") last_line
                      uu____47083 meta_decl doc1 false false
                     in
                  let uu____47087 =
                    let uu____47089 = FStar_Range.end_of_range r  in
                    FStar_Range.line_of_pos uu____47089  in
                  let uu____47090 =
                    let uu____47091 =
                      let uu____47092 = f x  in
                      FStar_Pprint.op_Hat_Hat sep uu____47092  in
                    FStar_Pprint.op_Hat_Hat doc2 uu____47091  in
                  (uu____47087, uu____47090)
               in
            let uu____47094 =
              let uu____47101 = FStar_List.hd xs  in
              let uu____47102 = FStar_List.tl xs  in
              (uu____47101, uu____47102)  in
            match uu____47094 with
            | (x,xs1) ->
                let init1 =
                  let meta_decl = extract_meta x  in
                  let uu____47120 =
                    let uu____47122 = FStar_Range.end_of_range meta_decl.r
                       in
                    FStar_Range.line_of_pos uu____47122  in
                  let uu____47123 =
                    let uu____47124 = f x  in
                    FStar_Pprint.op_Hat_Hat prefix1 uu____47124  in
                  (uu____47120, uu____47123)  in
                let uu____47126 = FStar_List.fold_left fold_fun init1 xs1  in
                FStar_Pervasives_Native.snd uu____47126
  
let separate_map_with_comments_kw :
  'Auu____47153 'Auu____47154 .
    'Auu____47153 ->
      'Auu____47153 ->
        ('Auu____47153 -> 'Auu____47154 -> FStar_Pprint.document) ->
          'Auu____47154 Prims.list ->
            ('Auu____47154 -> decl_meta) -> FStar_Pprint.document
  =
  fun prefix1  ->
    fun sep  ->
      fun f  ->
        fun xs  ->
          fun extract_meta  ->
            let fold_fun uu____47218 x =
              match uu____47218 with
              | (last_line,doc1) ->
                  let meta_decl = extract_meta x  in
                  let r = meta_decl.r  in
                  let doc2 =
                    let uu____47237 = FStar_Range.start_of_range r  in
                    place_comments_until_pos (Prims.parse_int "1") last_line
                      uu____47237 meta_decl doc1 false false
                     in
                  let uu____47241 =
                    let uu____47243 = FStar_Range.end_of_range r  in
                    FStar_Range.line_of_pos uu____47243  in
                  let uu____47244 =
                    let uu____47245 = f sep x  in
                    FStar_Pprint.op_Hat_Hat doc2 uu____47245  in
                  (uu____47241, uu____47244)
               in
            let uu____47247 =
              let uu____47254 = FStar_List.hd xs  in
              let uu____47255 = FStar_List.tl xs  in
              (uu____47254, uu____47255)  in
            match uu____47247 with
            | (x,xs1) ->
                let init1 =
                  let meta_decl = extract_meta x  in
                  let uu____47273 =
                    let uu____47275 = FStar_Range.end_of_range meta_decl.r
                       in
                    FStar_Range.line_of_pos uu____47275  in
                  let uu____47276 = f prefix1 x  in
                  (uu____47273, uu____47276)  in
                let uu____47278 = FStar_List.fold_left fold_fun init1 xs1  in
                FStar_Pervasives_Native.snd uu____47278
  
let rec (p_decl : FStar_Parser_AST.decl -> FStar_Pprint.document) =
  fun d  ->
    let qualifiers =
      match ((d.FStar_Parser_AST.quals), (d.FStar_Parser_AST.d)) with
      | ((FStar_Parser_AST.Assumption )::[],FStar_Parser_AST.Assume
         (id1,uu____48264)) ->
          let uu____48267 =
            let uu____48269 =
              FStar_Util.char_at id1.FStar_Ident.idText (Prims.parse_int "0")
               in
            FStar_All.pipe_right uu____48269 FStar_Util.is_upper  in
          if uu____48267
          then
            let uu____48275 = p_qualifier FStar_Parser_AST.Assumption  in
            FStar_Pprint.op_Hat_Hat uu____48275 FStar_Pprint.space
          else p_qualifiers d.FStar_Parser_AST.quals
      | uu____48278 -> p_qualifiers d.FStar_Parser_AST.quals  in
    let uu____48285 =
      FStar_Pprint.optional (fun d1  -> p_fsdoc d1) d.FStar_Parser_AST.doc
       in
    let uu____48288 =
      let uu____48289 = p_attributes d.FStar_Parser_AST.attrs  in
      let uu____48290 =
        let uu____48291 = p_rawDecl d  in
        FStar_Pprint.op_Hat_Hat qualifiers uu____48291  in
      FStar_Pprint.op_Hat_Hat uu____48289 uu____48290  in
    FStar_Pprint.op_Hat_Hat uu____48285 uu____48288

and (p_attributes : FStar_Parser_AST.attributes_ -> FStar_Pprint.document) =
  fun attrs  ->
    match attrs with
    | [] -> FStar_Pprint.empty
    | uu____48293 ->
        let uu____48294 =
          let uu____48295 = str "@ "  in
          let uu____48297 =
            let uu____48298 =
              let uu____48299 =
                let uu____48300 =
                  let uu____48301 = FStar_List.map p_atomicTerm attrs  in
                  FStar_Pprint.flow break1 uu____48301  in
                FStar_Pprint.op_Hat_Hat uu____48300 FStar_Pprint.rbracket  in
              FStar_Pprint.align uu____48299  in
            FStar_Pprint.op_Hat_Hat uu____48298 FStar_Pprint.hardline  in
          FStar_Pprint.op_Hat_Hat uu____48295 uu____48297  in
        FStar_Pprint.op_Hat_Hat FStar_Pprint.lbracket uu____48294

and (p_fsdoc : FStar_Parser_AST.fsdoc -> FStar_Pprint.document) =
  fun uu____48304  ->
    match uu____48304 with
    | (doc1,kwd_args) ->
        let kwd_args_doc =
          match kwd_args with
          | [] -> FStar_Pprint.empty
          | kwd_args1 ->
              let process_kwd_arg uu____48352 =
                match uu____48352 with
                | (kwd,arg) ->
                    let uu____48365 = str "@"  in
                    let uu____48367 =
                      let uu____48368 = str kwd  in
                      let uu____48369 =
                        let uu____48370 = str arg  in
                        FStar_Pprint.op_Hat_Hat FStar_Pprint.space
                          uu____48370
                         in
                      FStar_Pprint.op_Hat_Hat uu____48368 uu____48369  in
                    FStar_Pprint.op_Hat_Hat uu____48365 uu____48367
                 in
              let uu____48371 =
                FStar_Pprint.separate_map FStar_Pprint.hardline
                  process_kwd_arg kwd_args1
                 in
              FStar_Pprint.op_Hat_Hat uu____48371 FStar_Pprint.hardline
           in
        let uu____48378 =
          let uu____48379 =
            let uu____48380 =
              let uu____48381 = str doc1  in
              let uu____48382 =
                let uu____48383 =
                  let uu____48384 =
                    FStar_Pprint.op_Hat_Hat FStar_Pprint.rparen
                      FStar_Pprint.hardline
                     in
                  FStar_Pprint.op_Hat_Hat FStar_Pprint.star uu____48384  in
                FStar_Pprint.op_Hat_Hat kwd_args_doc uu____48383  in
              FStar_Pprint.op_Hat_Hat uu____48381 uu____48382  in
            FStar_Pprint.op_Hat_Hat FStar_Pprint.star uu____48380  in
          FStar_Pprint.op_Hat_Hat FStar_Pprint.star uu____48379  in
        FStar_Pprint.op_Hat_Hat FStar_Pprint.lparen uu____48378

and (p_justSig : FStar_Parser_AST.decl -> FStar_Pprint.document) =
  fun d  ->
    match d.FStar_Parser_AST.d with
    | FStar_Parser_AST.Val (lid,t) ->
        let uu____48388 =
          let uu____48389 = str "val"  in
          let uu____48391 =
            let uu____48392 =
              let uu____48393 = p_lident lid  in
              let uu____48394 =
                FStar_Pprint.op_Hat_Hat FStar_Pprint.space FStar_Pprint.colon
                 in
              FStar_Pprint.op_Hat_Hat uu____48393 uu____48394  in
            FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____48392  in
          FStar_Pprint.op_Hat_Hat uu____48389 uu____48391  in
        let uu____48395 = p_typ false false t  in
        FStar_Pprint.op_Hat_Hat uu____48388 uu____48395
    | FStar_Parser_AST.TopLevelLet (uu____48398,lbs) ->
        FStar_Pprint.separate_map FStar_Pprint.hardline
          (fun lb  ->
             let uu____48423 =
               let uu____48424 = str "let"  in p_letlhs uu____48424 lb false
                in
             FStar_Pprint.group uu____48423) lbs
    | uu____48427 -> FStar_Pprint.empty

and (p_list :
  (FStar_Ident.ident -> FStar_Pprint.document) ->
    FStar_Pprint.document ->
      FStar_Ident.ident Prims.list -> FStar_Pprint.document)
  =
  fun f  ->
    fun sep  ->
      fun l  ->
        let rec p_list' uu___328_48442 =
          match uu___328_48442 with
          | [] -> FStar_Pprint.empty
          | x::[] -> f x
          | x::xs ->
              let uu____48450 = f x  in
              let uu____48451 =
                let uu____48452 = p_list' xs  in
                FStar_Pprint.op_Hat_Hat sep uu____48452  in
              FStar_Pprint.op_Hat_Hat uu____48450 uu____48451
           in
        let uu____48453 = str "["  in
        let uu____48455 =
          let uu____48456 = p_list' l  in
          let uu____48457 = str "]"  in
          FStar_Pprint.op_Hat_Hat uu____48456 uu____48457  in
        FStar_Pprint.op_Hat_Hat uu____48453 uu____48455

and (p_rawDecl : FStar_Parser_AST.decl -> FStar_Pprint.document) =
  fun d  ->
    match d.FStar_Parser_AST.d with
    | FStar_Parser_AST.Open uid ->
        let uu____48461 =
          let uu____48462 = str "open"  in
          let uu____48464 = p_quident uid  in
          FStar_Pprint.op_Hat_Slash_Hat uu____48462 uu____48464  in
        FStar_Pprint.group uu____48461
    | FStar_Parser_AST.Include uid ->
        let uu____48466 =
          let uu____48467 = str "include"  in
          let uu____48469 = p_quident uid  in
          FStar_Pprint.op_Hat_Slash_Hat uu____48467 uu____48469  in
        FStar_Pprint.group uu____48466
    | FStar_Parser_AST.Friend uid ->
        let uu____48471 =
          let uu____48472 = str "friend"  in
          let uu____48474 = p_quident uid  in
          FStar_Pprint.op_Hat_Slash_Hat uu____48472 uu____48474  in
        FStar_Pprint.group uu____48471
    | FStar_Parser_AST.ModuleAbbrev (uid1,uid2) ->
        let uu____48477 =
          let uu____48478 = str "module"  in
          let uu____48480 =
            let uu____48481 =
              let uu____48482 = p_uident uid1  in
              let uu____48483 =
                FStar_Pprint.op_Hat_Hat FStar_Pprint.space
                  FStar_Pprint.equals
                 in
              FStar_Pprint.op_Hat_Hat uu____48482 uu____48483  in
            FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____48481  in
          FStar_Pprint.op_Hat_Hat uu____48478 uu____48480  in
        let uu____48484 = p_quident uid2  in
        op_Hat_Slash_Plus_Hat uu____48477 uu____48484
    | FStar_Parser_AST.TopLevelModule uid ->
        let uu____48486 =
          let uu____48487 = str "module"  in
          let uu____48489 =
            let uu____48490 = p_quident uid  in
            FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____48490  in
          FStar_Pprint.op_Hat_Hat uu____48487 uu____48489  in
        FStar_Pprint.group uu____48486
    | FStar_Parser_AST.Tycon
        (true
         ,uu____48491,(FStar_Parser_AST.TyconAbbrev
                       (uid,tpars,FStar_Pervasives_Native.None ,t),FStar_Pervasives_Native.None
                       )::[])
        ->
        let effect_prefix_doc =
          let uu____48528 = str "effect"  in
          let uu____48530 =
            let uu____48531 = p_uident uid  in
            FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____48531  in
          FStar_Pprint.op_Hat_Hat uu____48528 uu____48530  in
        let uu____48532 =
          let uu____48533 = p_typars tpars  in
          FStar_Pprint.surround (Prims.parse_int "2") (Prims.parse_int "1")
            effect_prefix_doc uu____48533 FStar_Pprint.equals
           in
        let uu____48536 = p_typ false false t  in
        op_Hat_Slash_Plus_Hat uu____48532 uu____48536
    | FStar_Parser_AST.Tycon (false ,tc,tcdefs) ->
        let s = if tc then str "class" else str "type"  in
        let uu____48567 =
          let uu____48568 = FStar_List.hd tcdefs  in
          p_fsdocTypeDeclPairs s uu____48568  in
        let uu____48581 =
          let uu____48582 = FStar_List.tl tcdefs  in
          FStar_All.pipe_left
            (FStar_Pprint.concat_map
               (fun x  ->
                  let uu____48620 =
                    let uu____48621 = str "and"  in
                    p_fsdocTypeDeclPairs uu____48621 x  in
                  FStar_Pprint.op_Hat_Hat break1 uu____48620)) uu____48582
           in
        FStar_Pprint.op_Hat_Hat uu____48567 uu____48581
    | FStar_Parser_AST.TopLevelLet (q,lbs) ->
        let let_doc =
          let uu____48638 = str "let"  in
          let uu____48640 = p_letqualifier q  in
          FStar_Pprint.op_Hat_Hat uu____48638 uu____48640  in
        let uu____48641 = str "and"  in
        separate_map_with_comments_kw let_doc uu____48641 p_letbinding lbs
          (fun uu____48651  ->
             match uu____48651 with
             | (p,t) ->
                 let uu____48658 =
                   FStar_Range.union_ranges p.FStar_Parser_AST.prange
                     t.FStar_Parser_AST.range
                    in
                 {
                   r = uu____48658;
                   has_qs = false;
                   has_attrs = false;
                   has_fsdoc = (FStar_Util.is_some d.FStar_Parser_AST.doc);
                   is_fsdoc = false
                 })
    | FStar_Parser_AST.Val (lid,t) ->
        let uu____48664 =
          let uu____48665 = str "val"  in
          let uu____48667 =
            let uu____48668 =
              let uu____48669 = p_lident lid  in
              let uu____48670 = sig_as_binders_if_possible t false  in
              FStar_Pprint.op_Hat_Hat uu____48669 uu____48670  in
            FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____48668  in
          FStar_Pprint.op_Hat_Hat uu____48665 uu____48667  in
        FStar_All.pipe_left FStar_Pprint.group uu____48664
    | FStar_Parser_AST.Assume (id1,t) ->
        let decl_keyword =
          let uu____48675 =
            let uu____48677 =
              FStar_Util.char_at id1.FStar_Ident.idText (Prims.parse_int "0")
               in
            FStar_All.pipe_right uu____48677 FStar_Util.is_upper  in
          if uu____48675
          then FStar_Pprint.empty
          else
            (let uu____48685 = str "val"  in
             FStar_Pprint.op_Hat_Hat uu____48685 FStar_Pprint.space)
           in
        let uu____48687 =
          let uu____48688 = p_ident id1  in
          let uu____48689 =
            let uu____48690 =
              let uu____48691 =
                let uu____48692 = p_typ false false t  in
                FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____48692  in
              FStar_Pprint.op_Hat_Hat FStar_Pprint.colon uu____48691  in
            FStar_Pprint.group uu____48690  in
          FStar_Pprint.op_Hat_Hat uu____48688 uu____48689  in
        FStar_Pprint.op_Hat_Hat decl_keyword uu____48687
    | FStar_Parser_AST.Exception (uid,t_opt) ->
        let uu____48701 = str "exception"  in
        let uu____48703 =
          let uu____48704 =
            let uu____48705 = p_uident uid  in
            let uu____48706 =
              FStar_Pprint.optional
                (fun t  ->
                   let uu____48710 =
                     let uu____48711 = str "of"  in
                     let uu____48713 = p_typ false false t  in
                     op_Hat_Slash_Plus_Hat uu____48711 uu____48713  in
                   FStar_Pprint.op_Hat_Hat break1 uu____48710) t_opt
               in
            FStar_Pprint.op_Hat_Hat uu____48705 uu____48706  in
          FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____48704  in
        FStar_Pprint.op_Hat_Hat uu____48701 uu____48703
    | FStar_Parser_AST.NewEffect ne ->
        let uu____48717 = str "new_effect"  in
        let uu____48719 =
          let uu____48720 = p_newEffect ne  in
          FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____48720  in
        FStar_Pprint.op_Hat_Hat uu____48717 uu____48719
    | FStar_Parser_AST.SubEffect se ->
        let uu____48722 = str "sub_effect"  in
        let uu____48724 =
          let uu____48725 = p_subEffect se  in
          FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____48725  in
        FStar_Pprint.op_Hat_Hat uu____48722 uu____48724
    | FStar_Parser_AST.Pragma p -> p_pragma p
    | FStar_Parser_AST.Fsdoc doc1 -> p_fsdoc doc1
    | FStar_Parser_AST.Main uu____48728 ->
        failwith "*Main declaration* : Is that really still in use ??"
    | FStar_Parser_AST.Tycon (true ,uu____48730,uu____48731) ->
        failwith
          "Effect abbreviation is expected to be defined by an abbreviation"
    | FStar_Parser_AST.Splice (ids,t) ->
        let uu____48759 = str "%splice"  in
        let uu____48761 =
          let uu____48762 =
            let uu____48763 = str ";"  in p_list p_uident uu____48763 ids  in
          let uu____48765 =
            let uu____48766 = p_term false false t  in
            FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____48766  in
          FStar_Pprint.op_Hat_Hat uu____48762 uu____48765  in
        FStar_Pprint.op_Hat_Hat uu____48759 uu____48761

and (p_pragma : FStar_Parser_AST.pragma -> FStar_Pprint.document) =
  fun uu___329_48769  ->
    match uu___329_48769 with
    | FStar_Parser_AST.SetOptions s ->
        let uu____48772 = str "#set-options"  in
        let uu____48774 =
          let uu____48775 =
            let uu____48776 = str s  in FStar_Pprint.dquotes uu____48776  in
          FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____48775  in
        FStar_Pprint.op_Hat_Hat uu____48772 uu____48774
    | FStar_Parser_AST.ResetOptions s_opt ->
        let uu____48781 = str "#reset-options"  in
        let uu____48783 =
          FStar_Pprint.optional
            (fun s  ->
               let uu____48789 =
                 let uu____48790 = str s  in FStar_Pprint.dquotes uu____48790
                  in
               FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____48789) s_opt
           in
        FStar_Pprint.op_Hat_Hat uu____48781 uu____48783
    | FStar_Parser_AST.PushOptions s_opt ->
        let uu____48795 = str "#push-options"  in
        let uu____48797 =
          FStar_Pprint.optional
            (fun s  ->
               let uu____48803 =
                 let uu____48804 = str s  in FStar_Pprint.dquotes uu____48804
                  in
               FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____48803) s_opt
           in
        FStar_Pprint.op_Hat_Hat uu____48795 uu____48797
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
    fun uu____48835  ->
      match uu____48835 with
      | (typedecl,fsdoc_opt) ->
          let uu____48848 = p_typeDecl (kw, fsdoc_opt) typedecl  in
          (match uu____48848 with
           | (comm,decl,body,pre) ->
               if comm = FStar_Pprint.empty
               then
                 let uu____48873 = pre body  in
                 FStar_Pprint.op_Hat_Hat decl uu____48873
               else
                 (let uu____48876 =
                    let uu____48877 =
                      let uu____48878 =
                        let uu____48879 = pre body  in
                        FStar_Pprint.op_Hat_Slash_Hat uu____48879 comm  in
                      FStar_Pprint.op_Hat_Hat decl uu____48878  in
                    let uu____48880 =
                      let uu____48881 =
                        let uu____48882 =
                          let uu____48883 =
                            let uu____48884 =
                              FStar_Pprint.op_Hat_Hat FStar_Pprint.hardline
                                body
                               in
                            FStar_Pprint.op_Hat_Hat comm uu____48884  in
                          FStar_Pprint.op_Hat_Hat FStar_Pprint.hardline
                            uu____48883
                           in
                        FStar_Pprint.nest (Prims.parse_int "2") uu____48882
                         in
                      FStar_Pprint.op_Hat_Hat decl uu____48881  in
                    FStar_Pprint.ifflat uu____48877 uu____48880  in
                  FStar_All.pipe_left FStar_Pprint.group uu____48876))

and (p_typeDecl :
  (FStar_Pprint.document * FStar_Parser_AST.fsdoc
    FStar_Pervasives_Native.option) ->
    FStar_Parser_AST.tycon ->
      (FStar_Pprint.document * FStar_Pprint.document * FStar_Pprint.document
        * (FStar_Pprint.document -> FStar_Pprint.document)))
  =
  fun pre  ->
    fun uu___330_48887  ->
      match uu___330_48887 with
      | FStar_Parser_AST.TyconAbstract (lid,bs,typ_opt) ->
          let uu____48916 = p_typeDeclPrefix pre false lid bs typ_opt  in
          (FStar_Pprint.empty, uu____48916, FStar_Pprint.empty,
            FStar_Pervasives.id)
      | FStar_Parser_AST.TyconAbbrev (lid,bs,typ_opt,t) ->
          let uu____48933 = p_typ_sep false false t  in
          (match uu____48933 with
           | (comm,doc1) ->
               let uu____48953 = p_typeDeclPrefix pre true lid bs typ_opt  in
               (comm, uu____48953, doc1, jump2))
      | FStar_Parser_AST.TyconRecord (lid,bs,typ_opt,record_field_decls) ->
          let p_recordFieldAndComments ps uu____49009 =
            match uu____49009 with
            | (lid1,t,doc_opt) ->
                let uu____49026 =
                  let uu____49031 =
                    FStar_Range.extend_to_end_of_line
                      t.FStar_Parser_AST.range
                     in
                  with_comment_sep (p_recordFieldDecl ps) (lid1, t, doc_opt)
                    uu____49031
                   in
                (match uu____49026 with
                 | (comm,field) ->
                     let sep =
                       if ps then FStar_Pprint.semi else FStar_Pprint.empty
                        in
                     inline_comment_or_above comm field sep)
             in
          let p_fields =
            let uu____49049 =
              separate_map_last FStar_Pprint.hardline
                p_recordFieldAndComments record_field_decls
               in
            braces_with_nesting uu____49049  in
          let uu____49058 = p_typeDeclPrefix pre true lid bs typ_opt  in
          (FStar_Pprint.empty, uu____49058, p_fields,
            ((fun d  -> FStar_Pprint.op_Hat_Hat FStar_Pprint.space d)))
      | FStar_Parser_AST.TyconVariant (lid,bs,typ_opt,ct_decls) ->
          let p_constructorBranchAndComments uu____49125 =
            match uu____49125 with
            | (uid,t_opt,doc_opt,use_of) ->
                let range =
                  let uu____49154 =
                    let uu____49155 =
                      FStar_Util.map_opt t_opt
                        (fun t  -> t.FStar_Parser_AST.range)
                       in
                    FStar_Util.dflt uid.FStar_Ident.idRange uu____49155  in
                  FStar_Range.extend_to_end_of_line uu____49154  in
                let uu____49160 =
                  with_comment_sep p_constructorBranch
                    (uid, t_opt, doc_opt, use_of) range
                   in
                (match uu____49160 with
                 | (comm,ctor) ->
                     inline_comment_or_above comm ctor FStar_Pprint.empty)
             in
          let datacon_doc =
            FStar_Pprint.separate_map FStar_Pprint.hardline
              p_constructorBranchAndComments ct_decls
             in
          let uu____49199 = p_typeDeclPrefix pre true lid bs typ_opt  in
          (FStar_Pprint.empty, uu____49199, datacon_doc, jump2)

and (p_typeDeclPrefix :
  (FStar_Pprint.document * FStar_Parser_AST.fsdoc
    FStar_Pervasives_Native.option) ->
    Prims.bool ->
      FStar_Ident.ident ->
        FStar_Parser_AST.binder Prims.list ->
          FStar_Parser_AST.knd FStar_Pervasives_Native.option ->
            FStar_Pprint.document)
  =
  fun uu____49204  ->
    fun eq1  ->
      fun lid  ->
        fun bs  ->
          fun typ_opt  ->
            match uu____49204 with
            | (kw,fsdoc_opt) ->
                let maybe_with_fsdoc cont =
                  let lid_doc = p_ident lid  in
                  let kw_lid =
                    let uu____49239 =
                      FStar_Pprint.op_Hat_Slash_Hat kw lid_doc  in
                    FStar_Pprint.group uu____49239  in
                  match fsdoc_opt with
                  | FStar_Pervasives_Native.None  -> cont kw_lid
                  | FStar_Pervasives_Native.Some fsdoc ->
                      let uu____49241 =
                        let uu____49244 =
                          let uu____49247 = p_fsdoc fsdoc  in
                          let uu____49248 =
                            let uu____49251 = cont lid_doc  in [uu____49251]
                             in
                          uu____49247 :: uu____49248  in
                        kw :: uu____49244  in
                      FStar_Pprint.separate FStar_Pprint.hardline uu____49241
                   in
                let typ =
                  let maybe_eq =
                    if eq1 then FStar_Pprint.equals else FStar_Pprint.empty
                     in
                  match typ_opt with
                  | FStar_Pervasives_Native.None  -> maybe_eq
                  | FStar_Pervasives_Native.Some t ->
                      let uu____49258 =
                        let uu____49259 =
                          let uu____49260 = p_typ false false t  in
                          FStar_Pprint.op_Hat_Slash_Hat uu____49260 maybe_eq
                           in
                        FStar_Pprint.op_Hat_Hat FStar_Pprint.space
                          uu____49259
                         in
                      FStar_Pprint.op_Hat_Hat FStar_Pprint.colon uu____49258
                   in
                if bs = []
                then maybe_with_fsdoc (fun n1  -> prefix2 n1 typ)
                else
                  (let binders = p_binders_list true bs  in
                   maybe_with_fsdoc
                     (fun n1  ->
                        let uu____49280 =
                          let uu____49281 = FStar_Pprint.flow break1 binders
                             in
                          prefix2 n1 uu____49281  in
                        prefix2 uu____49280 typ))

and (p_recordFieldDecl :
  Prims.bool ->
    (FStar_Ident.ident * FStar_Parser_AST.term * FStar_Parser_AST.fsdoc
      FStar_Pervasives_Native.option) -> FStar_Pprint.document)
  =
  fun ps  ->
    fun uu____49283  ->
      match uu____49283 with
      | (lid,t,doc_opt) ->
          let uu____49300 =
            let uu____49301 = FStar_Pprint.optional p_fsdoc doc_opt  in
            let uu____49302 =
              let uu____49303 = p_lident lid  in
              let uu____49304 =
                let uu____49305 = p_typ ps false t  in
                FStar_Pprint.op_Hat_Hat FStar_Pprint.colon uu____49305  in
              FStar_Pprint.op_Hat_Hat uu____49303 uu____49304  in
            FStar_Pprint.op_Hat_Hat uu____49301 uu____49302  in
          FStar_Pprint.group uu____49300

and (p_constructorBranch :
  (FStar_Ident.ident * FStar_Parser_AST.term FStar_Pervasives_Native.option *
    FStar_Parser_AST.fsdoc FStar_Pervasives_Native.option * Prims.bool) ->
    FStar_Pprint.document)
  =
  fun uu____49307  ->
    match uu____49307 with
    | (uid,t_opt,doc_opt,use_of) ->
        let sep = if use_of then str "of" else FStar_Pprint.colon  in
        let uid_doc =
          let uu____49341 =
            let uu____49342 =
              let uu____49343 = p_uident uid  in
              FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____49343  in
            FStar_Pprint.op_Hat_Hat FStar_Pprint.bar uu____49342  in
          FStar_Pprint.group uu____49341  in
        let uu____49344 = FStar_Pprint.optional p_fsdoc doc_opt  in
        let uu____49345 =
          default_or_map uid_doc
            (fun t  ->
               let uu____49349 =
                 let uu____49350 =
                   let uu____49351 =
                     let uu____49352 =
                       let uu____49353 = p_typ false false t  in
                       FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____49353
                        in
                     FStar_Pprint.op_Hat_Hat sep uu____49352  in
                   FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____49351  in
                 FStar_Pprint.op_Hat_Hat uid_doc uu____49350  in
               FStar_Pprint.group uu____49349) t_opt
           in
        FStar_Pprint.op_Hat_Hat uu____49344 uu____49345

and (p_letlhs :
  FStar_Pprint.document ->
    (FStar_Parser_AST.pattern * FStar_Parser_AST.term) ->
      Prims.bool -> FStar_Pprint.document)
  =
  fun kw  ->
    fun uu____49357  ->
      fun inner_let  ->
        match uu____49357 with
        | (pat,uu____49365) ->
            let uu____49366 =
              match pat.FStar_Parser_AST.pat with
              | FStar_Parser_AST.PatAscribed
                  (pat1,(t,FStar_Pervasives_Native.None )) ->
                  (pat1,
                    (FStar_Pervasives_Native.Some (t, FStar_Pprint.empty)))
              | FStar_Parser_AST.PatAscribed
                  (pat1,(t,FStar_Pervasives_Native.Some tac)) ->
                  let uu____49418 =
                    let uu____49425 =
                      let uu____49430 =
                        let uu____49431 =
                          let uu____49432 =
                            let uu____49433 = str "by"  in
                            let uu____49435 =
                              let uu____49436 = p_atomicTerm tac  in
                              FStar_Pprint.op_Hat_Hat FStar_Pprint.space
                                uu____49436
                               in
                            FStar_Pprint.op_Hat_Hat uu____49433 uu____49435
                             in
                          FStar_Pprint.op_Hat_Hat FStar_Pprint.space
                            uu____49432
                           in
                        FStar_Pprint.group uu____49431  in
                      (t, uu____49430)  in
                    FStar_Pervasives_Native.Some uu____49425  in
                  (pat1, uu____49418)
              | uu____49447 -> (pat, FStar_Pervasives_Native.None)  in
            (match uu____49366 with
             | (pat1,ascr) ->
                 (match pat1.FStar_Parser_AST.pat with
                  | FStar_Parser_AST.PatApp
                      ({
                         FStar_Parser_AST.pat = FStar_Parser_AST.PatVar
                           (lid,uu____49473);
                         FStar_Parser_AST.prange = uu____49474;_},pats)
                      ->
                      let ascr_doc =
                        match ascr with
                        | FStar_Pervasives_Native.Some (t,tac) ->
                            let uu____49491 =
                              sig_as_binders_if_possible t true  in
                            FStar_Pprint.op_Hat_Hat uu____49491 tac
                        | FStar_Pervasives_Native.None  -> FStar_Pprint.empty
                         in
                      let uu____49497 =
                        if inner_let
                        then
                          let uu____49511 = pats_as_binders_if_possible pats
                             in
                          match uu____49511 with
                          | (bs,style) ->
                              ((FStar_List.append bs [ascr_doc]), style)
                        else
                          (let uu____49534 = pats_as_binders_if_possible pats
                              in
                           match uu____49534 with
                           | (bs,style) ->
                               ((FStar_List.append bs [ascr_doc]), style))
                         in
                      (match uu____49497 with
                       | (terms,style) ->
                           let uu____49561 =
                             let uu____49562 =
                               let uu____49563 =
                                 let uu____49564 = p_lident lid  in
                                 let uu____49565 =
                                   format_sig style terms true true  in
                                 FStar_Pprint.op_Hat_Hat uu____49564
                                   uu____49565
                                  in
                               FStar_Pprint.op_Hat_Hat FStar_Pprint.space
                                 uu____49563
                                in
                             FStar_Pprint.op_Hat_Hat kw uu____49562  in
                           FStar_All.pipe_left FStar_Pprint.group uu____49561)
                  | uu____49568 ->
                      let ascr_doc =
                        match ascr with
                        | FStar_Pervasives_Native.Some (t,tac) ->
                            let uu____49576 =
                              let uu____49577 =
                                let uu____49578 =
                                  p_typ_top
                                    (Arrows
                                       ((Prims.parse_int "2"),
                                         (Prims.parse_int "2"))) false false
                                    t
                                   in
                                FStar_Pprint.op_Hat_Hat FStar_Pprint.colon
                                  uu____49578
                                 in
                              FStar_Pprint.group uu____49577  in
                            FStar_Pprint.op_Hat_Hat uu____49576 tac
                        | FStar_Pervasives_Native.None  -> FStar_Pprint.empty
                         in
                      let uu____49589 =
                        let uu____49590 =
                          let uu____49591 =
                            let uu____49592 = p_tuplePattern pat1  in
                            FStar_Pprint.op_Hat_Slash_Hat kw uu____49592  in
                          FStar_Pprint.group uu____49591  in
                        FStar_Pprint.op_Hat_Hat uu____49590 ascr_doc  in
                      FStar_Pprint.group uu____49589))

and (p_letbinding :
  FStar_Pprint.document ->
    (FStar_Parser_AST.pattern * FStar_Parser_AST.term) ->
      FStar_Pprint.document)
  =
  fun kw  ->
    fun uu____49594  ->
      match uu____49594 with
      | (pat,e) ->
          let doc_pat = p_letlhs kw (pat, e) false  in
          let uu____49603 = p_term_sep false false e  in
          (match uu____49603 with
           | (comm,doc_expr) ->
               let doc_expr1 =
                 inline_comment_or_above comm doc_expr FStar_Pprint.empty  in
               let uu____49613 =
                 let uu____49614 =
                   FStar_Pprint.op_Hat_Slash_Hat FStar_Pprint.equals
                     doc_expr1
                    in
                 FStar_Pprint.op_Hat_Slash_Hat doc_pat uu____49614  in
               let uu____49615 =
                 let uu____49616 =
                   let uu____49617 =
                     let uu____49618 =
                       let uu____49619 = jump2 doc_expr1  in
                       FStar_Pprint.op_Hat_Hat FStar_Pprint.equals
                         uu____49619
                        in
                     FStar_Pprint.group uu____49618  in
                   FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____49617  in
                 FStar_Pprint.op_Hat_Hat doc_pat uu____49616  in
               FStar_Pprint.ifflat uu____49613 uu____49615)

and (p_newEffect : FStar_Parser_AST.effect_decl -> FStar_Pprint.document) =
  fun uu___331_49620  ->
    match uu___331_49620 with
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
        let uu____49645 = p_uident uid  in
        let uu____49646 = p_binders true bs  in
        let uu____49648 =
          let uu____49649 = p_simpleTerm false false t  in
          prefix2 FStar_Pprint.equals uu____49649  in
        surround_maybe_empty (Prims.parse_int "2") (Prims.parse_int "1")
          uu____49645 uu____49646 uu____49648

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
          let uu____49664 =
            let uu____49665 =
              let uu____49666 =
                let uu____49667 = p_uident uid  in
                let uu____49668 = p_binders true bs  in
                let uu____49670 =
                  let uu____49671 = p_typ false false t  in
                  prefix2 FStar_Pprint.colon uu____49671  in
                surround_maybe_empty (Prims.parse_int "2")
                  (Prims.parse_int "1") uu____49667 uu____49668 uu____49670
                 in
              FStar_Pprint.group uu____49666  in
            let uu____49676 =
              let uu____49677 = str "with"  in
              let uu____49679 =
                let uu____49680 =
                  let uu____49681 =
                    let uu____49682 =
                      let uu____49683 =
                        let uu____49684 =
                          FStar_Pprint.op_Hat_Hat FStar_Pprint.semi
                            FStar_Pprint.space
                           in
                        FStar_Pprint.op_Hat_Hat FStar_Pprint.hardline
                          uu____49684
                         in
                      separate_map_last uu____49683 p_effectDecl eff_decls
                       in
                    FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____49682
                     in
                  FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____49681  in
                FStar_Pprint.op_Hat_Hat FStar_Pprint.hardline uu____49680  in
              FStar_Pprint.op_Hat_Hat uu____49677 uu____49679  in
            FStar_Pprint.op_Hat_Slash_Hat uu____49665 uu____49676  in
          braces_with_nesting uu____49664

and (p_effectDecl :
  Prims.bool -> FStar_Parser_AST.decl -> FStar_Pprint.document) =
  fun ps  ->
    fun d  ->
      match d.FStar_Parser_AST.d with
      | FStar_Parser_AST.Tycon
          (false
           ,uu____49688,(FStar_Parser_AST.TyconAbbrev
                         (lid,[],FStar_Pervasives_Native.None ,e),FStar_Pervasives_Native.None
                         )::[])
          ->
          let uu____49721 =
            let uu____49722 = p_lident lid  in
            let uu____49723 =
              FStar_Pprint.op_Hat_Hat FStar_Pprint.space FStar_Pprint.equals
               in
            FStar_Pprint.op_Hat_Hat uu____49722 uu____49723  in
          let uu____49724 = p_simpleTerm ps false e  in
          prefix2 uu____49721 uu____49724
      | uu____49726 ->
          let uu____49727 =
            let uu____49729 = FStar_Parser_AST.decl_to_string d  in
            FStar_Util.format1
              "Not a declaration of an effect member... or at least I hope so : %s"
              uu____49729
             in
          failwith uu____49727

and (p_subEffect : FStar_Parser_AST.lift -> FStar_Pprint.document) =
  fun lift  ->
    let lift_op_doc =
      let lifts =
        match lift.FStar_Parser_AST.lift_op with
        | FStar_Parser_AST.NonReifiableLift t -> [("lift_wp", t)]
        | FStar_Parser_AST.ReifiableLift (t1,t2) ->
            [("lift_wp", t1); ("lift", t2)]
        | FStar_Parser_AST.LiftForFree t -> [("lift", t)]  in
      let p_lift ps uu____49812 =
        match uu____49812 with
        | (kwd,t) ->
            let uu____49823 =
              let uu____49824 = str kwd  in
              let uu____49825 =
                FStar_Pprint.op_Hat_Hat FStar_Pprint.space
                  FStar_Pprint.equals
                 in
              FStar_Pprint.op_Hat_Hat uu____49824 uu____49825  in
            let uu____49826 = p_simpleTerm ps false t  in
            prefix2 uu____49823 uu____49826
         in
      separate_break_map_last FStar_Pprint.semi p_lift lifts  in
    let uu____49833 =
      let uu____49834 =
        let uu____49835 = p_quident lift.FStar_Parser_AST.msource  in
        let uu____49836 =
          let uu____49837 = str "~>"  in
          FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____49837  in
        FStar_Pprint.op_Hat_Hat uu____49835 uu____49836  in
      let uu____49839 = p_quident lift.FStar_Parser_AST.mdest  in
      prefix2 uu____49834 uu____49839  in
    let uu____49840 =
      let uu____49841 = braces_with_nesting lift_op_doc  in
      FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____49841  in
    FStar_Pprint.op_Hat_Hat uu____49833 uu____49840

and (p_qualifier : FStar_Parser_AST.qualifier -> FStar_Pprint.document) =
  fun uu___332_49842  ->
    match uu___332_49842 with
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
        let uu____49862 = p_qualifier q  in
        FStar_Pprint.op_Hat_Hat uu____49862 FStar_Pprint.hardline
    | uu____49863 ->
        let uu____49864 =
          let uu____49865 = FStar_List.map p_qualifier qs  in
          FStar_Pprint.flow break1 uu____49865  in
        FStar_Pprint.op_Hat_Hat uu____49864 FStar_Pprint.hardline

and (p_letqualifier :
  FStar_Parser_AST.let_qualifier -> FStar_Pprint.document) =
  fun uu___333_49868  ->
    match uu___333_49868 with
    | FStar_Parser_AST.Rec  ->
        let uu____49869 = str "rec"  in
        FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____49869
    | FStar_Parser_AST.NoLetQualifier  -> FStar_Pprint.empty

and (p_aqual : FStar_Parser_AST.arg_qualifier -> FStar_Pprint.document) =
  fun uu___334_49871  ->
    match uu___334_49871 with
    | FStar_Parser_AST.Implicit  -> str "#"
    | FStar_Parser_AST.Equality  -> str "$"
    | FStar_Parser_AST.Meta t ->
        let t1 =
          match t.FStar_Parser_AST.tm with
          | FStar_Parser_AST.Abs (uu____49876,e) -> e
          | uu____49882 ->
              FStar_Parser_AST.mk_term
                (FStar_Parser_AST.App
                   (t,
                     (FStar_Parser_AST.unit_const t.FStar_Parser_AST.range),
                     FStar_Parser_AST.Nothing)) t.FStar_Parser_AST.range
                FStar_Parser_AST.Expr
           in
        let uu____49883 = str "#["  in
        let uu____49885 =
          let uu____49886 = p_term false false t1  in
          let uu____49889 =
            let uu____49890 = str "]"  in
            FStar_Pprint.op_Hat_Hat uu____49890 break1  in
          FStar_Pprint.op_Hat_Hat uu____49886 uu____49889  in
        FStar_Pprint.op_Hat_Hat uu____49883 uu____49885

and (p_disjunctivePattern :
  FStar_Parser_AST.pattern -> FStar_Pprint.document) =
  fun p  ->
    match p.FStar_Parser_AST.pat with
    | FStar_Parser_AST.PatOr pats ->
        let uu____49896 =
          let uu____49897 =
            let uu____49898 =
              FStar_Pprint.op_Hat_Hat FStar_Pprint.bar FStar_Pprint.space  in
            FStar_Pprint.op_Hat_Hat break1 uu____49898  in
          FStar_Pprint.separate_map uu____49897 p_tuplePattern pats  in
        FStar_Pprint.group uu____49896
    | uu____49899 -> p_tuplePattern p

and (p_tuplePattern : FStar_Parser_AST.pattern -> FStar_Pprint.document) =
  fun p  ->
    match p.FStar_Parser_AST.pat with
    | FStar_Parser_AST.PatTuple (pats,false ) ->
        let uu____49908 =
          let uu____49909 = FStar_Pprint.op_Hat_Hat FStar_Pprint.comma break1
             in
          FStar_Pprint.separate_map uu____49909 p_constructorPattern pats  in
        FStar_Pprint.group uu____49908
    | uu____49910 -> p_constructorPattern p

and (p_constructorPattern :
  FStar_Parser_AST.pattern -> FStar_Pprint.document) =
  fun p  ->
    match p.FStar_Parser_AST.pat with
    | FStar_Parser_AST.PatApp
        ({ FStar_Parser_AST.pat = FStar_Parser_AST.PatName maybe_cons_lid;
           FStar_Parser_AST.prange = uu____49913;_},hd1::tl1::[])
        when
        FStar_Ident.lid_equals maybe_cons_lid FStar_Parser_Const.cons_lid ->
        let uu____49918 =
          FStar_Pprint.op_Hat_Hat FStar_Pprint.colon FStar_Pprint.colon  in
        let uu____49919 = p_constructorPattern hd1  in
        let uu____49920 = p_constructorPattern tl1  in
        infix0 uu____49918 uu____49919 uu____49920
    | FStar_Parser_AST.PatApp
        ({ FStar_Parser_AST.pat = FStar_Parser_AST.PatName uid;
           FStar_Parser_AST.prange = uu____49922;_},pats)
        ->
        let uu____49928 = p_quident uid  in
        let uu____49929 =
          FStar_Pprint.separate_map break1 p_atomicPattern pats  in
        prefix2 uu____49928 uu____49929
    | uu____49930 -> p_atomicPattern p

and (p_atomicPattern : FStar_Parser_AST.pattern -> FStar_Pprint.document) =
  fun p  ->
    match p.FStar_Parser_AST.pat with
    | FStar_Parser_AST.PatAscribed (pat,(t,FStar_Pervasives_Native.None )) ->
        (match ((pat.FStar_Parser_AST.pat), (t.FStar_Parser_AST.tm)) with
         | (FStar_Parser_AST.PatVar (lid,aqual),FStar_Parser_AST.Refine
            ({ FStar_Parser_AST.b = FStar_Parser_AST.Annotated (lid',t1);
               FStar_Parser_AST.brange = uu____49946;
               FStar_Parser_AST.blevel = uu____49947;
               FStar_Parser_AST.aqual = uu____49948;_},phi))
             when lid.FStar_Ident.idText = lid'.FStar_Ident.idText ->
             let uu____49957 =
               let uu____49958 = p_ident lid  in
               p_refinement aqual uu____49958 t1 phi  in
             soft_parens_with_nesting uu____49957
         | (FStar_Parser_AST.PatWild aqual,FStar_Parser_AST.Refine
            ({ FStar_Parser_AST.b = FStar_Parser_AST.NoName t1;
               FStar_Parser_AST.brange = uu____49961;
               FStar_Parser_AST.blevel = uu____49962;
               FStar_Parser_AST.aqual = uu____49963;_},phi))
             ->
             let uu____49969 =
               p_refinement aqual FStar_Pprint.underscore t1 phi  in
             soft_parens_with_nesting uu____49969
         | uu____49970 ->
             let uu____49975 =
               let uu____49976 = p_tuplePattern pat  in
               let uu____49977 =
                 let uu____49978 = p_tmEqNoRefinement t  in
                 FStar_Pprint.op_Hat_Slash_Hat FStar_Pprint.colon uu____49978
                  in
               FStar_Pprint.op_Hat_Hat uu____49976 uu____49977  in
             soft_parens_with_nesting uu____49975)
    | FStar_Parser_AST.PatList pats ->
        let uu____49982 =
          separate_break_map FStar_Pprint.semi p_tuplePattern pats  in
        FStar_Pprint.surround (Prims.parse_int "2") (Prims.parse_int "0")
          FStar_Pprint.lbracket uu____49982 FStar_Pprint.rbracket
    | FStar_Parser_AST.PatRecord pats ->
        let p_recordFieldPat uu____50001 =
          match uu____50001 with
          | (lid,pat) ->
              let uu____50008 = p_qlident lid  in
              let uu____50009 = p_tuplePattern pat  in
              infix2 FStar_Pprint.equals uu____50008 uu____50009
           in
        let uu____50010 =
          separate_break_map FStar_Pprint.semi p_recordFieldPat pats  in
        soft_braces_with_nesting uu____50010
    | FStar_Parser_AST.PatTuple (pats,true ) ->
        let uu____50022 =
          FStar_Pprint.op_Hat_Hat FStar_Pprint.lparen FStar_Pprint.bar  in
        let uu____50023 =
          separate_break_map FStar_Pprint.comma p_constructorPattern pats  in
        let uu____50024 =
          FStar_Pprint.op_Hat_Hat FStar_Pprint.bar FStar_Pprint.rparen  in
        FStar_Pprint.surround (Prims.parse_int "2") (Prims.parse_int "1")
          uu____50022 uu____50023 uu____50024
    | FStar_Parser_AST.PatTvar (tv,arg_qualifier_opt) -> p_tvar tv
    | FStar_Parser_AST.PatOp op ->
        let uu____50035 =
          let uu____50036 =
            let uu____50037 =
              let uu____50038 = FStar_Ident.text_of_id op  in str uu____50038
               in
            let uu____50040 =
              FStar_Pprint.op_Hat_Hat FStar_Pprint.space FStar_Pprint.rparen
               in
            FStar_Pprint.op_Hat_Hat uu____50037 uu____50040  in
          FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____50036  in
        FStar_Pprint.op_Hat_Hat FStar_Pprint.lparen uu____50035
    | FStar_Parser_AST.PatWild aqual ->
        let uu____50044 = FStar_Pprint.optional p_aqual aqual  in
        FStar_Pprint.op_Hat_Hat uu____50044 FStar_Pprint.underscore
    | FStar_Parser_AST.PatConst c -> p_constant c
    | FStar_Parser_AST.PatVar (lid,aqual) ->
        let uu____50052 = FStar_Pprint.optional p_aqual aqual  in
        let uu____50053 = p_lident lid  in
        FStar_Pprint.op_Hat_Hat uu____50052 uu____50053
    | FStar_Parser_AST.PatName uid -> p_quident uid
    | FStar_Parser_AST.PatOr uu____50055 -> failwith "Inner or pattern !"
    | FStar_Parser_AST.PatApp
        ({ FStar_Parser_AST.pat = FStar_Parser_AST.PatName uu____50059;
           FStar_Parser_AST.prange = uu____50060;_},uu____50061)
        ->
        let uu____50066 = p_tuplePattern p  in
        soft_parens_with_nesting uu____50066
    | FStar_Parser_AST.PatTuple (uu____50067,false ) ->
        let uu____50074 = p_tuplePattern p  in
        soft_parens_with_nesting uu____50074
    | uu____50075 ->
        let uu____50076 =
          let uu____50078 = FStar_Parser_AST.pat_to_string p  in
          FStar_Util.format1 "Invalid pattern %s" uu____50078  in
        failwith uu____50076

and (is_typ_tuple : FStar_Parser_AST.term -> Prims.bool) =
  fun e  ->
    match e.FStar_Parser_AST.tm with
    | FStar_Parser_AST.Op
        ({ FStar_Ident.idText = "*"; FStar_Ident.idRange = uu____50083;_},uu____50084)
        -> true
    | uu____50091 -> false

and (is_meta_qualifier :
  FStar_Parser_AST.arg_qualifier FStar_Pervasives_Native.option -> Prims.bool)
  =
  fun aq  ->
    match aq with
    | FStar_Pervasives_Native.Some (FStar_Parser_AST.Meta uu____50097) ->
        true
    | uu____50099 -> false

and (p_binder :
  Prims.bool -> FStar_Parser_AST.binder -> FStar_Pprint.document) =
  fun is_atomic  ->
    fun b  ->
      let uu____50106 = p_binder' is_atomic b  in
      match uu____50106 with
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
          let uu____50145 =
            let uu____50146 =
              FStar_Pprint.optional p_aqual b.FStar_Parser_AST.aqual  in
            let uu____50147 = p_lident lid  in
            FStar_Pprint.op_Hat_Hat uu____50146 uu____50147  in
          (uu____50145, FStar_Pervasives_Native.None, cat_with_colon)
      | FStar_Parser_AST.TVariable lid ->
          let uu____50153 = p_lident lid  in
          (uu____50153, FStar_Pervasives_Native.None, cat_with_colon)
      | FStar_Parser_AST.Annotated (lid,t) ->
          let uu____50160 =
            match t.FStar_Parser_AST.tm with
            | FStar_Parser_AST.Refine
                ({ FStar_Parser_AST.b = FStar_Parser_AST.Annotated (lid',t1);
                   FStar_Parser_AST.brange = uu____50171;
                   FStar_Parser_AST.blevel = uu____50172;
                   FStar_Parser_AST.aqual = uu____50173;_},phi)
                when lid.FStar_Ident.idText = lid'.FStar_Ident.idText ->
                let uu____50178 = p_lident lid  in
                p_refinement' b.FStar_Parser_AST.aqual uu____50178 t1 phi
            | uu____50179 ->
                let t' =
                  let uu____50181 = is_typ_tuple t  in
                  if uu____50181
                  then
                    let uu____50184 = p_tmFormula t  in
                    soft_parens_with_nesting uu____50184
                  else p_tmFormula t  in
                let uu____50187 =
                  let uu____50188 =
                    FStar_Pprint.optional p_aqual b.FStar_Parser_AST.aqual
                     in
                  let uu____50189 = p_lident lid  in
                  FStar_Pprint.op_Hat_Hat uu____50188 uu____50189  in
                (uu____50187, t')
             in
          (match uu____50160 with
           | (b',t') ->
               let catf =
                 let uu____50207 =
                   is_atomic || (is_meta_qualifier b.FStar_Parser_AST.aqual)
                    in
                 if uu____50207
                 then
                   fun x  ->
                     fun y  ->
                       let uu____50214 =
                         let uu____50215 =
                           let uu____50216 = cat_with_colon x y  in
                           FStar_Pprint.op_Hat_Hat uu____50216
                             FStar_Pprint.rparen
                            in
                         FStar_Pprint.op_Hat_Hat FStar_Pprint.lparen
                           uu____50215
                          in
                       FStar_Pprint.group uu____50214
                 else
                   (fun x  ->
                      fun y  ->
                        let uu____50221 = cat_with_colon x y  in
                        FStar_Pprint.group uu____50221)
                  in
               (b', (FStar_Pervasives_Native.Some t'), catf))
      | FStar_Parser_AST.TAnnotated uu____50230 ->
          failwith "Is this still used ?"
      | FStar_Parser_AST.NoName t ->
          (match t.FStar_Parser_AST.tm with
           | FStar_Parser_AST.Refine
               ({ FStar_Parser_AST.b = FStar_Parser_AST.NoName t1;
                  FStar_Parser_AST.brange = uu____50258;
                  FStar_Parser_AST.blevel = uu____50259;
                  FStar_Parser_AST.aqual = uu____50260;_},phi)
               ->
               let uu____50264 =
                 p_refinement' b.FStar_Parser_AST.aqual
                   FStar_Pprint.underscore t1 phi
                  in
               (match uu____50264 with
                | (b',t') ->
                    (b', (FStar_Pervasives_Native.Some t'), cat_with_colon))
           | uu____50285 ->
               if is_atomic
               then
                 let uu____50297 = p_atomicTerm t  in
                 (uu____50297, FStar_Pervasives_Native.None, cat_with_colon)
               else
                 (let uu____50304 = p_appTerm t  in
                  (uu____50304, FStar_Pervasives_Native.None, cat_with_colon)))

and (p_refinement :
  FStar_Parser_AST.arg_qualifier FStar_Pervasives_Native.option ->
    FStar_Pprint.document ->
      FStar_Parser_AST.term -> FStar_Parser_AST.term -> FStar_Pprint.document)
  =
  fun aqual_opt  ->
    fun binder  ->
      fun t  ->
        fun phi  ->
          let uu____50315 = p_refinement' aqual_opt binder t phi  in
          match uu____50315 with | (b,typ) -> cat_with_colon b typ

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
            | FStar_Parser_AST.Construct uu____50331 -> false
            | FStar_Parser_AST.App uu____50343 -> false
            | FStar_Parser_AST.Op uu____50351 -> false
            | uu____50359 -> true  in
          let uu____50361 = p_noSeqTerm false false phi  in
          match uu____50361 with
          | (comm,phi1) ->
              let phi2 =
                if comm = FStar_Pprint.empty
                then phi1
                else
                  (let uu____50378 =
                     FStar_Pprint.op_Hat_Hat FStar_Pprint.hardline phi1  in
                   FStar_Pprint.op_Hat_Hat comm uu____50378)
                 in
              let jump_break =
                if is_t_atomic
                then (Prims.parse_int "0")
                else (Prims.parse_int "1")  in
              let uu____50387 =
                let uu____50388 = FStar_Pprint.optional p_aqual aqual_opt  in
                FStar_Pprint.op_Hat_Hat uu____50388 binder  in
              let uu____50389 =
                let uu____50390 = p_appTerm t  in
                let uu____50391 =
                  let uu____50392 =
                    let uu____50393 =
                      let uu____50394 = soft_braces_with_nesting_tight phi2
                         in
                      let uu____50395 = soft_braces_with_nesting phi2  in
                      FStar_Pprint.ifflat uu____50394 uu____50395  in
                    FStar_Pprint.group uu____50393  in
                  FStar_Pprint.jump (Prims.parse_int "2") jump_break
                    uu____50392
                   in
                FStar_Pprint.op_Hat_Hat uu____50390 uu____50391  in
              (uu____50387, uu____50389)

and (p_binders_list :
  Prims.bool ->
    FStar_Parser_AST.binder Prims.list -> FStar_Pprint.document Prims.list)
  = fun is_atomic  -> fun bs  -> FStar_List.map (p_binder is_atomic) bs

and (p_binders :
  Prims.bool -> FStar_Parser_AST.binder Prims.list -> FStar_Pprint.document)
  =
  fun is_atomic  ->
    fun bs  ->
      let uu____50409 = p_binders_list is_atomic bs  in
      separate_or_flow break1 uu____50409

and (text_of_id_or_underscore : FStar_Ident.ident -> FStar_Pprint.document) =
  fun lid  ->
    let uu____50413 =
      (FStar_Util.starts_with lid.FStar_Ident.idText
         FStar_Ident.reserved_prefix)
        &&
        (let uu____50416 = FStar_Options.print_real_names ()  in
         Prims.op_Negation uu____50416)
       in
    if uu____50413
    then FStar_Pprint.underscore
    else (let uu____50421 = FStar_Ident.text_of_id lid  in str uu____50421)

and (text_of_lid_or_underscore : FStar_Ident.lident -> FStar_Pprint.document)
  =
  fun lid  ->
    let uu____50424 =
      (FStar_Util.starts_with (lid.FStar_Ident.ident).FStar_Ident.idText
         FStar_Ident.reserved_prefix)
        &&
        (let uu____50427 = FStar_Options.print_real_names ()  in
         Prims.op_Negation uu____50427)
       in
    if uu____50424
    then FStar_Pprint.underscore
    else (let uu____50432 = FStar_Ident.text_of_lid lid  in str uu____50432)

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
          let uu____50453 = FStar_Pprint.op_Hat_Hat doc1 sep  in
          FStar_Pprint.group uu____50453
        else
          (let uu____50456 =
             let uu____50457 =
               let uu____50458 =
                 let uu____50459 =
                   let uu____50460 = FStar_Pprint.op_Hat_Hat break1 comm  in
                   FStar_Pprint.op_Hat_Hat sep uu____50460  in
                 FStar_Pprint.op_Hat_Hat doc1 uu____50459  in
               FStar_Pprint.group uu____50458  in
             let uu____50461 =
               let uu____50462 =
                 let uu____50463 = FStar_Pprint.op_Hat_Hat doc1 sep  in
                 FStar_Pprint.op_Hat_Hat FStar_Pprint.hardline uu____50463
                  in
               FStar_Pprint.op_Hat_Hat comm uu____50462  in
             FStar_Pprint.ifflat uu____50457 uu____50461  in
           FStar_All.pipe_left FStar_Pprint.group uu____50456)

and (p_term :
  Prims.bool -> Prims.bool -> FStar_Parser_AST.term -> FStar_Pprint.document)
  =
  fun ps  ->
    fun pb  ->
      fun e  ->
        match e.FStar_Parser_AST.tm with
        | FStar_Parser_AST.Seq (e1,e2) ->
            let uu____50471 = p_noSeqTerm true false e1  in
            (match uu____50471 with
             | (comm,t1) ->
                 let uu____50480 =
                   inline_comment_or_above comm t1 FStar_Pprint.semi  in
                 let uu____50481 =
                   let uu____50482 = p_term ps pb e2  in
                   FStar_Pprint.op_Hat_Hat FStar_Pprint.hardline uu____50482
                    in
                 FStar_Pprint.op_Hat_Hat uu____50480 uu____50481)
        | FStar_Parser_AST.Bind (x,e1,e2) ->
            let uu____50486 =
              let uu____50487 =
                let uu____50488 =
                  let uu____50489 = p_lident x  in
                  let uu____50490 =
                    FStar_Pprint.op_Hat_Hat FStar_Pprint.space
                      FStar_Pprint.long_left_arrow
                     in
                  FStar_Pprint.op_Hat_Hat uu____50489 uu____50490  in
                let uu____50491 =
                  let uu____50492 = p_noSeqTermAndComment true false e1  in
                  let uu____50495 =
                    FStar_Pprint.op_Hat_Hat FStar_Pprint.space
                      FStar_Pprint.semi
                     in
                  FStar_Pprint.op_Hat_Hat uu____50492 uu____50495  in
                op_Hat_Slash_Plus_Hat uu____50488 uu____50491  in
              FStar_Pprint.group uu____50487  in
            let uu____50496 = p_term ps pb e2  in
            FStar_Pprint.op_Hat_Slash_Hat uu____50486 uu____50496
        | uu____50497 ->
            let uu____50498 = p_noSeqTermAndComment ps pb e  in
            FStar_Pprint.group uu____50498

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
            let uu____50510 = p_noSeqTerm true false e1  in
            (match uu____50510 with
             | (comm,t1) ->
                 let uu____50523 =
                   let uu____50524 =
                     let uu____50525 =
                       FStar_Pprint.op_Hat_Hat t1 FStar_Pprint.semi  in
                     FStar_Pprint.group uu____50525  in
                   let uu____50526 =
                     let uu____50527 = p_term ps pb e2  in
                     FStar_Pprint.op_Hat_Hat FStar_Pprint.hardline
                       uu____50527
                      in
                   FStar_Pprint.op_Hat_Hat uu____50524 uu____50526  in
                 (comm, uu____50523))
        | FStar_Parser_AST.Bind (x,e1,e2) ->
            let uu____50531 =
              let uu____50532 =
                let uu____50533 =
                  let uu____50534 =
                    let uu____50535 = p_lident x  in
                    let uu____50536 =
                      FStar_Pprint.op_Hat_Hat FStar_Pprint.space
                        FStar_Pprint.long_left_arrow
                       in
                    FStar_Pprint.op_Hat_Hat uu____50535 uu____50536  in
                  let uu____50537 =
                    let uu____50538 = p_noSeqTermAndComment true false e1  in
                    let uu____50541 =
                      FStar_Pprint.op_Hat_Hat FStar_Pprint.space
                        FStar_Pprint.semi
                       in
                    FStar_Pprint.op_Hat_Hat uu____50538 uu____50541  in
                  op_Hat_Slash_Plus_Hat uu____50534 uu____50537  in
                FStar_Pprint.group uu____50533  in
              let uu____50542 = p_term ps pb e2  in
              FStar_Pprint.op_Hat_Slash_Hat uu____50532 uu____50542  in
            (FStar_Pprint.empty, uu____50531)
        | uu____50543 -> p_noSeqTerm ps pb e

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
            let uu____50563 =
              let uu____50564 = p_tmIff e1  in
              let uu____50565 =
                let uu____50566 =
                  let uu____50567 = p_typ ps pb t  in
                  FStar_Pprint.op_Hat_Slash_Hat FStar_Pprint.colon
                    uu____50567
                   in
                FStar_Pprint.op_Hat_Hat FStar_Pprint.langle uu____50566  in
              FStar_Pprint.op_Hat_Slash_Hat uu____50564 uu____50565  in
            FStar_Pprint.group uu____50563
        | FStar_Parser_AST.Ascribed (e1,t,FStar_Pervasives_Native.Some tac)
            ->
            let uu____50573 =
              let uu____50574 = p_tmIff e1  in
              let uu____50575 =
                let uu____50576 =
                  let uu____50577 =
                    let uu____50578 = p_typ false false t  in
                    let uu____50581 =
                      let uu____50582 = str "by"  in
                      let uu____50584 = p_typ ps pb tac  in
                      FStar_Pprint.op_Hat_Slash_Hat uu____50582 uu____50584
                       in
                    FStar_Pprint.op_Hat_Slash_Hat uu____50578 uu____50581  in
                  FStar_Pprint.op_Hat_Slash_Hat FStar_Pprint.colon
                    uu____50577
                   in
                FStar_Pprint.op_Hat_Hat FStar_Pprint.langle uu____50576  in
              FStar_Pprint.op_Hat_Slash_Hat uu____50574 uu____50575  in
            FStar_Pprint.group uu____50573
        | FStar_Parser_AST.Op
            ({ FStar_Ident.idText = ".()<-";
               FStar_Ident.idRange = uu____50585;_},e1::e2::e3::[])
            ->
            let uu____50592 =
              let uu____50593 =
                let uu____50594 =
                  let uu____50595 = p_atomicTermNotQUident e1  in
                  let uu____50596 =
                    let uu____50597 =
                      let uu____50598 =
                        let uu____50599 = p_term false false e2  in
                        soft_parens_with_nesting uu____50599  in
                      let uu____50602 =
                        FStar_Pprint.op_Hat_Hat FStar_Pprint.space
                          FStar_Pprint.larrow
                         in
                      FStar_Pprint.op_Hat_Hat uu____50598 uu____50602  in
                    FStar_Pprint.op_Hat_Hat FStar_Pprint.dot uu____50597  in
                  FStar_Pprint.op_Hat_Hat uu____50595 uu____50596  in
                FStar_Pprint.group uu____50594  in
              let uu____50603 =
                let uu____50604 = p_noSeqTermAndComment ps pb e3  in
                jump2 uu____50604  in
              FStar_Pprint.op_Hat_Hat uu____50593 uu____50603  in
            FStar_Pprint.group uu____50592
        | FStar_Parser_AST.Op
            ({ FStar_Ident.idText = ".[]<-";
               FStar_Ident.idRange = uu____50605;_},e1::e2::e3::[])
            ->
            let uu____50612 =
              let uu____50613 =
                let uu____50614 =
                  let uu____50615 = p_atomicTermNotQUident e1  in
                  let uu____50616 =
                    let uu____50617 =
                      let uu____50618 =
                        let uu____50619 = p_term false false e2  in
                        soft_brackets_with_nesting uu____50619  in
                      let uu____50622 =
                        FStar_Pprint.op_Hat_Hat FStar_Pprint.space
                          FStar_Pprint.larrow
                         in
                      FStar_Pprint.op_Hat_Hat uu____50618 uu____50622  in
                    FStar_Pprint.op_Hat_Hat FStar_Pprint.dot uu____50617  in
                  FStar_Pprint.op_Hat_Hat uu____50615 uu____50616  in
                FStar_Pprint.group uu____50614  in
              let uu____50623 =
                let uu____50624 = p_noSeqTermAndComment ps pb e3  in
                jump2 uu____50624  in
              FStar_Pprint.op_Hat_Hat uu____50613 uu____50623  in
            FStar_Pprint.group uu____50612
        | FStar_Parser_AST.Requires (e1,wtf) ->
            let uu____50634 =
              let uu____50635 = str "requires"  in
              let uu____50637 = p_typ ps pb e1  in
              FStar_Pprint.op_Hat_Slash_Hat uu____50635 uu____50637  in
            FStar_Pprint.group uu____50634
        | FStar_Parser_AST.Ensures (e1,wtf) ->
            let uu____50647 =
              let uu____50648 = str "ensures"  in
              let uu____50650 = p_typ ps pb e1  in
              FStar_Pprint.op_Hat_Slash_Hat uu____50648 uu____50650  in
            FStar_Pprint.group uu____50647
        | FStar_Parser_AST.Attributes es ->
            let uu____50654 =
              let uu____50655 = str "attributes"  in
              let uu____50657 =
                FStar_Pprint.separate_map break1 p_atomicTerm es  in
              FStar_Pprint.op_Hat_Slash_Hat uu____50655 uu____50657  in
            FStar_Pprint.group uu____50654
        | FStar_Parser_AST.If (e1,e2,e3) ->
            if is_unit e3
            then
              let uu____50662 =
                let uu____50663 =
                  let uu____50664 = str "if"  in
                  let uu____50666 = p_noSeqTermAndComment false false e1  in
                  op_Hat_Slash_Plus_Hat uu____50664 uu____50666  in
                let uu____50669 =
                  let uu____50670 = str "then"  in
                  let uu____50672 = p_noSeqTermAndComment ps pb e2  in
                  op_Hat_Slash_Plus_Hat uu____50670 uu____50672  in
                FStar_Pprint.op_Hat_Slash_Hat uu____50663 uu____50669  in
              FStar_Pprint.group uu____50662
            else
              (let e2_doc =
                 match e2.FStar_Parser_AST.tm with
                 | FStar_Parser_AST.If (uu____50676,uu____50677,e31) when
                     is_unit e31 ->
                     let uu____50679 = p_noSeqTermAndComment false false e2
                        in
                     soft_parens_with_nesting uu____50679
                 | uu____50682 -> p_noSeqTermAndComment false false e2  in
               let uu____50685 =
                 let uu____50686 =
                   let uu____50687 = str "if"  in
                   let uu____50689 = p_noSeqTermAndComment false false e1  in
                   op_Hat_Slash_Plus_Hat uu____50687 uu____50689  in
                 let uu____50692 =
                   let uu____50693 =
                     let uu____50694 = str "then"  in
                     op_Hat_Slash_Plus_Hat uu____50694 e2_doc  in
                   let uu____50696 =
                     let uu____50697 = str "else"  in
                     let uu____50699 = p_noSeqTermAndComment ps pb e3  in
                     op_Hat_Slash_Plus_Hat uu____50697 uu____50699  in
                   FStar_Pprint.op_Hat_Slash_Hat uu____50693 uu____50696  in
                 FStar_Pprint.op_Hat_Slash_Hat uu____50686 uu____50692  in
               FStar_Pprint.group uu____50685)
        | FStar_Parser_AST.TryWith (e1,branches) ->
            let uu____50722 =
              let uu____50723 =
                let uu____50724 =
                  let uu____50725 = str "try"  in
                  let uu____50727 = p_noSeqTermAndComment false false e1  in
                  prefix2 uu____50725 uu____50727  in
                let uu____50730 =
                  let uu____50731 = str "with"  in
                  let uu____50733 =
                    separate_map_last FStar_Pprint.hardline p_patternBranch
                      branches
                     in
                  FStar_Pprint.op_Hat_Slash_Hat uu____50731 uu____50733  in
                FStar_Pprint.op_Hat_Slash_Hat uu____50724 uu____50730  in
              FStar_Pprint.group uu____50723  in
            let uu____50742 = paren_if (ps || pb)  in uu____50742 uu____50722
        | FStar_Parser_AST.Match (e1,branches) ->
            let uu____50769 =
              let uu____50770 =
                let uu____50771 =
                  let uu____50772 = str "match"  in
                  let uu____50774 = p_noSeqTermAndComment false false e1  in
                  let uu____50777 = str "with"  in
                  FStar_Pprint.surround (Prims.parse_int "2")
                    (Prims.parse_int "1") uu____50772 uu____50774 uu____50777
                   in
                let uu____50781 =
                  separate_map_last FStar_Pprint.hardline p_patternBranch
                    branches
                   in
                FStar_Pprint.op_Hat_Slash_Hat uu____50771 uu____50781  in
              FStar_Pprint.group uu____50770  in
            let uu____50790 = paren_if (ps || pb)  in uu____50790 uu____50769
        | FStar_Parser_AST.LetOpen (uid,e1) ->
            let uu____50797 =
              let uu____50798 =
                let uu____50799 =
                  let uu____50800 = str "let open"  in
                  let uu____50802 = p_quident uid  in
                  let uu____50803 = str "in"  in
                  FStar_Pprint.surround (Prims.parse_int "2")
                    (Prims.parse_int "1") uu____50800 uu____50802 uu____50803
                   in
                let uu____50807 = p_term false pb e1  in
                FStar_Pprint.op_Hat_Slash_Hat uu____50799 uu____50807  in
              FStar_Pprint.group uu____50798  in
            let uu____50809 = paren_if ps  in uu____50809 uu____50797
        | FStar_Parser_AST.Let (q,lbs,e1) ->
            let p_lb q1 uu____50874 is_last =
              match uu____50874 with
              | (a,(pat,e2)) ->
                  let attrs = p_attrs_opt a  in
                  let doc_let_or_and =
                    match q1 with
                    | FStar_Pervasives_Native.Some (FStar_Parser_AST.Rec ) ->
                        let uu____50908 =
                          let uu____50909 = str "let"  in
                          let uu____50911 = str "rec"  in
                          FStar_Pprint.op_Hat_Slash_Hat uu____50909
                            uu____50911
                           in
                        FStar_Pprint.group uu____50908
                    | FStar_Pervasives_Native.Some
                        (FStar_Parser_AST.NoLetQualifier ) -> str "let"
                    | uu____50914 -> str "and"  in
                  let doc_pat = p_letlhs doc_let_or_and (pat, e2) true  in
                  let uu____50920 = p_term_sep false false e2  in
                  (match uu____50920 with
                   | (comm,doc_expr) ->
                       let doc_expr1 =
                         inline_comment_or_above comm doc_expr
                           FStar_Pprint.empty
                          in
                       let uu____50930 =
                         if is_last
                         then
                           let uu____50932 =
                             FStar_Pprint.flow break1
                               [doc_pat; FStar_Pprint.equals]
                              in
                           let uu____50933 = str "in"  in
                           FStar_Pprint.surround (Prims.parse_int "2")
                             (Prims.parse_int "1") uu____50932 doc_expr1
                             uu____50933
                         else
                           (let uu____50939 =
                              FStar_Pprint.flow break1
                                [doc_pat; FStar_Pprint.equals; doc_expr1]
                               in
                            FStar_Pprint.hang (Prims.parse_int "2")
                              uu____50939)
                          in
                       FStar_Pprint.op_Hat_Hat attrs uu____50930)
               in
            let l = FStar_List.length lbs  in
            let lbs_docs =
              FStar_List.mapi
                (fun i  ->
                   fun lb  ->
                     if i = (Prims.parse_int "0")
                     then
                       let uu____50990 =
                         p_lb (FStar_Pervasives_Native.Some q) lb
                           (i = (l - (Prims.parse_int "1")))
                          in
                       FStar_Pprint.group uu____50990
                     else
                       (let uu____51001 =
                          p_lb FStar_Pervasives_Native.None lb
                            (i = (l - (Prims.parse_int "1")))
                           in
                        FStar_Pprint.group uu____51001)) lbs
               in
            let lbs_doc =
              let uu____51011 = FStar_Pprint.separate break1 lbs_docs  in
              FStar_Pprint.group uu____51011  in
            let uu____51012 =
              let uu____51013 =
                let uu____51014 =
                  let uu____51015 = p_term false pb e1  in
                  FStar_Pprint.op_Hat_Hat FStar_Pprint.hardline uu____51015
                   in
                FStar_Pprint.op_Hat_Hat lbs_doc uu____51014  in
              FStar_Pprint.group uu____51013  in
            let uu____51017 = paren_if ps  in uu____51017 uu____51012
        | FStar_Parser_AST.Abs
            ({ FStar_Parser_AST.pat = FStar_Parser_AST.PatVar (x,typ_opt);
               FStar_Parser_AST.prange = uu____51024;_}::[],{
                                                              FStar_Parser_AST.tm
                                                                =
                                                                FStar_Parser_AST.Match
                                                                (maybe_x,branches);
                                                              FStar_Parser_AST.range
                                                                = uu____51027;
                                                              FStar_Parser_AST.level
                                                                = uu____51028;_})
            when matches_var maybe_x x ->
            let uu____51055 =
              let uu____51056 =
                let uu____51057 = str "function"  in
                let uu____51059 =
                  separate_map_last FStar_Pprint.hardline p_patternBranch
                    branches
                   in
                FStar_Pprint.op_Hat_Slash_Hat uu____51057 uu____51059  in
              FStar_Pprint.group uu____51056  in
            let uu____51068 = paren_if (ps || pb)  in uu____51068 uu____51055
        | FStar_Parser_AST.Quote (e1,FStar_Parser_AST.Dynamic ) ->
            let uu____51074 =
              let uu____51075 = str "quote"  in
              let uu____51077 = p_noSeqTermAndComment ps pb e1  in
              FStar_Pprint.op_Hat_Slash_Hat uu____51075 uu____51077  in
            FStar_Pprint.group uu____51074
        | FStar_Parser_AST.Quote (e1,FStar_Parser_AST.Static ) ->
            let uu____51079 =
              let uu____51080 = str "`"  in
              let uu____51082 = p_noSeqTermAndComment ps pb e1  in
              FStar_Pprint.op_Hat_Hat uu____51080 uu____51082  in
            FStar_Pprint.group uu____51079
        | FStar_Parser_AST.VQuote e1 ->
            let uu____51084 =
              let uu____51085 = str "`%"  in
              let uu____51087 = p_noSeqTermAndComment ps pb e1  in
              FStar_Pprint.op_Hat_Hat uu____51085 uu____51087  in
            FStar_Pprint.group uu____51084
        | FStar_Parser_AST.Antiquote
            {
              FStar_Parser_AST.tm = FStar_Parser_AST.Quote
                (e1,FStar_Parser_AST.Dynamic );
              FStar_Parser_AST.range = uu____51089;
              FStar_Parser_AST.level = uu____51090;_}
            ->
            let uu____51091 =
              let uu____51092 = str "`@"  in
              let uu____51094 = p_noSeqTermAndComment ps pb e1  in
              FStar_Pprint.op_Hat_Hat uu____51092 uu____51094  in
            FStar_Pprint.group uu____51091
        | FStar_Parser_AST.Antiquote e1 ->
            let uu____51096 =
              let uu____51097 = str "`#"  in
              let uu____51099 = p_noSeqTermAndComment ps pb e1  in
              FStar_Pprint.op_Hat_Hat uu____51097 uu____51099  in
            FStar_Pprint.group uu____51096
        | FStar_Parser_AST.CalcProof (rel,init1,steps) ->
            let head1 =
              let uu____51108 = str "calc"  in
              let uu____51110 =
                let uu____51111 =
                  let uu____51112 = p_noSeqTermAndComment false false rel  in
                  let uu____51115 =
                    FStar_Pprint.op_Hat_Hat FStar_Pprint.space
                      FStar_Pprint.lbrace
                     in
                  FStar_Pprint.op_Hat_Hat uu____51112 uu____51115  in
                FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____51111  in
              FStar_Pprint.op_Hat_Hat uu____51108 uu____51110  in
            let bot = FStar_Pprint.rbrace  in
            let uu____51117 =
              FStar_Pprint.op_Hat_Hat FStar_Pprint.hardline bot  in
            let uu____51118 =
              let uu____51119 =
                let uu____51120 =
                  let uu____51121 = p_noSeqTermAndComment false false init1
                     in
                  let uu____51124 =
                    let uu____51125 = str ";"  in
                    let uu____51127 =
                      let uu____51128 =
                        separate_map_last FStar_Pprint.hardline p_calcStep
                          steps
                         in
                      FStar_Pprint.op_Hat_Hat FStar_Pprint.hardline
                        uu____51128
                       in
                    FStar_Pprint.op_Hat_Hat uu____51125 uu____51127  in
                  FStar_Pprint.op_Hat_Hat uu____51121 uu____51124  in
                FStar_Pprint.op_Hat_Hat FStar_Pprint.hardline uu____51120  in
              FStar_All.pipe_left (FStar_Pprint.nest (Prims.parse_int "2"))
                uu____51119
               in
            FStar_Pprint.enclose head1 uu____51117 uu____51118
        | uu____51130 -> p_typ ps pb e

and (p_calcStep :
  Prims.bool -> FStar_Parser_AST.calc_step -> FStar_Pprint.document) =
  fun uu____51131  ->
    fun uu____51132  ->
      match uu____51132 with
      | FStar_Parser_AST.CalcStep (rel,just,next) ->
          let uu____51137 =
            let uu____51138 = p_noSeqTermAndComment false false rel  in
            let uu____51141 =
              let uu____51142 =
                let uu____51143 =
                  let uu____51144 =
                    let uu____51145 = p_noSeqTermAndComment false false just
                       in
                    let uu____51148 =
                      let uu____51149 =
                        let uu____51150 =
                          let uu____51151 =
                            let uu____51152 =
                              p_noSeqTermAndComment false false next  in
                            let uu____51155 = str ";"  in
                            FStar_Pprint.op_Hat_Hat uu____51152 uu____51155
                             in
                          FStar_Pprint.op_Hat_Hat FStar_Pprint.hardline
                            uu____51151
                           in
                        FStar_Pprint.op_Hat_Hat FStar_Pprint.rbrace
                          uu____51150
                         in
                      FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____51149
                       in
                    FStar_Pprint.op_Hat_Hat uu____51145 uu____51148  in
                  FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____51144  in
                FStar_Pprint.op_Hat_Hat FStar_Pprint.lbrace uu____51143  in
              FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____51142  in
            FStar_Pprint.op_Hat_Hat uu____51138 uu____51141  in
          FStar_Pprint.group uu____51137

and (p_attrs_opt :
  FStar_Parser_AST.term Prims.list FStar_Pervasives_Native.option ->
    FStar_Pprint.document)
  =
  fun uu___335_51157  ->
    match uu___335_51157 with
    | FStar_Pervasives_Native.None  -> FStar_Pprint.empty
    | FStar_Pervasives_Native.Some terms ->
        let uu____51169 =
          let uu____51170 = str "[@"  in
          let uu____51172 =
            let uu____51173 =
              FStar_Pprint.separate_map break1 p_atomicTerm terms  in
            let uu____51174 = str "]"  in
            FStar_Pprint.op_Hat_Slash_Hat uu____51173 uu____51174  in
          FStar_Pprint.op_Hat_Slash_Hat uu____51170 uu____51172  in
        FStar_Pprint.group uu____51169

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
                 let uu____51211 =
                   let uu____51212 =
                     let uu____51213 = p_quantifier e  in
                     FStar_Pprint.op_Hat_Hat uu____51213 FStar_Pprint.space
                      in
                   FStar_Pprint.soft_surround (Prims.parse_int "2")
                     (Prims.parse_int "0") uu____51212 binders_doc
                     FStar_Pprint.dot
                    in
                 prefix2 uu____51211 term_doc
             | pats ->
                 let uu____51221 =
                   let uu____51222 =
                     let uu____51223 =
                       let uu____51224 =
                         let uu____51225 = p_quantifier e  in
                         FStar_Pprint.op_Hat_Hat uu____51225
                           FStar_Pprint.space
                          in
                       FStar_Pprint.soft_surround (Prims.parse_int "2")
                         (Prims.parse_int "0") uu____51224 binders_doc
                         FStar_Pprint.dot
                        in
                     let uu____51228 = p_trigger trigger  in
                     prefix2 uu____51223 uu____51228  in
                   FStar_Pprint.group uu____51222  in
                 prefix2 uu____51221 term_doc)
        | FStar_Parser_AST.QExists (bs,trigger,e1) ->
            let binders_doc = p_binders true bs  in
            let term_doc = p_noSeqTermAndComment ps pb e1  in
            (match trigger with
             | [] ->
                 let uu____51249 =
                   let uu____51250 =
                     let uu____51251 = p_quantifier e  in
                     FStar_Pprint.op_Hat_Hat uu____51251 FStar_Pprint.space
                      in
                   FStar_Pprint.soft_surround (Prims.parse_int "2")
                     (Prims.parse_int "0") uu____51250 binders_doc
                     FStar_Pprint.dot
                    in
                 prefix2 uu____51249 term_doc
             | pats ->
                 let uu____51259 =
                   let uu____51260 =
                     let uu____51261 =
                       let uu____51262 =
                         let uu____51263 = p_quantifier e  in
                         FStar_Pprint.op_Hat_Hat uu____51263
                           FStar_Pprint.space
                          in
                       FStar_Pprint.soft_surround (Prims.parse_int "2")
                         (Prims.parse_int "0") uu____51262 binders_doc
                         FStar_Pprint.dot
                        in
                     let uu____51266 = p_trigger trigger  in
                     prefix2 uu____51261 uu____51266  in
                   FStar_Pprint.group uu____51260  in
                 prefix2 uu____51259 term_doc)
        | uu____51267 -> p_simpleTerm ps pb e

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
      let uu____51288 = all_binders_annot t  in
      if uu____51288
      then
        let uu____51291 =
          p_typ_top
            (Binders ((Prims.parse_int "4"), (Prims.parse_int "0"), true))
            false false t
           in
        FStar_Pprint.op_Hat_Hat s uu____51291
      else
        (let uu____51302 =
           let uu____51303 =
             let uu____51304 =
               p_typ_top
                 (Arrows ((Prims.parse_int "2"), (Prims.parse_int "2")))
                 false false t
                in
             FStar_Pprint.op_Hat_Hat s uu____51304  in
           FStar_Pprint.op_Hat_Hat FStar_Pprint.colon uu____51303  in
         FStar_Pprint.group uu____51302)

and (collapse_pats :
  (FStar_Pprint.document * FStar_Pprint.document) Prims.list ->
    FStar_Pprint.document Prims.list)
  =
  fun pats  ->
    let fold_fun bs x =
      let uu____51363 = x  in
      match uu____51363 with
      | (b1,t1) ->
          (match bs with
           | [] -> [([b1], t1)]
           | hd1::tl1 ->
               let uu____51428 = hd1  in
               (match uu____51428 with
                | (b2s,t2) ->
                    if t1 = t2
                    then ((FStar_List.append b2s [b1]), t1) :: tl1
                    else ([b1], t1) :: hd1 :: tl1))
       in
    let p_collapsed_binder cb =
      let uu____51500 = cb  in
      match uu____51500 with
      | (bs,typ) ->
          (match bs with
           | [] -> failwith "Impossible"
           | b::[] -> cat_with_colon b typ
           | hd1::tl1 ->
               let uu____51519 =
                 FStar_List.fold_left
                   (fun x  ->
                      fun y  ->
                        let uu____51525 =
                          FStar_Pprint.op_Hat_Hat FStar_Pprint.space y  in
                        FStar_Pprint.op_Hat_Hat x uu____51525) hd1 tl1
                  in
               cat_with_colon uu____51519 typ)
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
                 FStar_Parser_AST.brange = uu____51604;
                 FStar_Parser_AST.blevel = uu____51605;
                 FStar_Parser_AST.aqual = uu____51606;_},phi))
               when lid.FStar_Ident.idText = lid'.FStar_Ident.idText ->
               let uu____51615 =
                 let uu____51620 = p_ident lid  in
                 p_refinement' aqual uu____51620 t1 phi  in
               FStar_Pervasives_Native.Some uu____51615
           | (FStar_Parser_AST.PatVar (lid,aqual),uu____51627) ->
               let uu____51632 =
                 let uu____51637 =
                   let uu____51638 = FStar_Pprint.optional p_aqual aqual  in
                   let uu____51639 = p_ident lid  in
                   FStar_Pprint.op_Hat_Hat uu____51638 uu____51639  in
                 let uu____51640 = p_tmEqNoRefinement t  in
                 (uu____51637, uu____51640)  in
               FStar_Pervasives_Native.Some uu____51632
           | uu____51645 -> FStar_Pervasives_Native.None)
      | uu____51654 -> FStar_Pervasives_Native.None  in
    let all_unbound p =
      match p.FStar_Parser_AST.pat with
      | FStar_Parser_AST.PatAscribed uu____51667 -> false
      | uu____51679 -> true  in
    let uu____51681 = map_if_all all_binders pats  in
    match uu____51681 with
    | FStar_Pervasives_Native.Some bs ->
        let uu____51713 = collapse_pats bs  in
        (uu____51713,
          (Binders ((Prims.parse_int "4"), (Prims.parse_int "0"), true)))
    | FStar_Pervasives_Native.None  ->
        let uu____51730 = FStar_List.map p_atomicPattern pats  in
        (uu____51730,
          (Binders ((Prims.parse_int "4"), (Prims.parse_int "0"), false)))

and (p_quantifier : FStar_Parser_AST.term -> FStar_Pprint.document) =
  fun e  ->
    match e.FStar_Parser_AST.tm with
    | FStar_Parser_AST.QForall uu____51742 -> str "forall"
    | FStar_Parser_AST.QExists uu____51756 -> str "exists"
    | uu____51770 ->
        failwith "Imposible : p_quantifier called on a non-quantifier term"

and (p_trigger :
  FStar_Parser_AST.term Prims.list Prims.list -> FStar_Pprint.document) =
  fun uu___336_51772  ->
    match uu___336_51772 with
    | [] -> FStar_Pprint.empty
    | pats ->
        let uu____51784 =
          let uu____51785 =
            let uu____51786 =
              let uu____51787 = str "pattern"  in
              let uu____51789 =
                let uu____51790 =
                  let uu____51791 = p_disjunctivePats pats  in
                  FStar_Pprint.jump (Prims.parse_int "2")
                    (Prims.parse_int "0") uu____51791
                   in
                FStar_Pprint.op_Hat_Hat uu____51790 FStar_Pprint.rbrace  in
              FStar_Pprint.op_Hat_Slash_Hat uu____51787 uu____51789  in
            FStar_Pprint.op_Hat_Hat FStar_Pprint.colon uu____51786  in
          FStar_Pprint.op_Hat_Hat FStar_Pprint.lbrace uu____51785  in
        FStar_Pprint.group uu____51784

and (p_disjunctivePats :
  FStar_Parser_AST.term Prims.list Prims.list -> FStar_Pprint.document) =
  fun pats  ->
    let uu____51799 = str "\\/"  in
    FStar_Pprint.separate_map uu____51799 p_conjunctivePats pats

and (p_conjunctivePats :
  FStar_Parser_AST.term Prims.list -> FStar_Pprint.document) =
  fun pats  ->
    let uu____51806 =
      let uu____51807 = FStar_Pprint.op_Hat_Hat FStar_Pprint.semi break1  in
      FStar_Pprint.separate_map uu____51807 p_appTerm pats  in
    FStar_Pprint.group uu____51806

and (p_simpleTerm :
  Prims.bool -> Prims.bool -> FStar_Parser_AST.term -> FStar_Pprint.document)
  =
  fun ps  ->
    fun pb  ->
      fun e  ->
        match e.FStar_Parser_AST.tm with
        | FStar_Parser_AST.Abs (pats,e1) ->
            let uu____51819 = p_term_sep false pb e1  in
            (match uu____51819 with
             | (comm,doc1) ->
                 let prefix1 =
                   let uu____51828 = str "fun"  in
                   let uu____51830 =
                     let uu____51831 =
                       FStar_Pprint.separate_map break1 p_atomicPattern pats
                        in
                     FStar_Pprint.op_Hat_Slash_Hat uu____51831
                       FStar_Pprint.rarrow
                      in
                   op_Hat_Slash_Plus_Hat uu____51828 uu____51830  in
                 let uu____51832 =
                   if comm <> FStar_Pprint.empty
                   then
                     let uu____51834 =
                       let uu____51835 =
                         let uu____51836 =
                           FStar_Pprint.op_Hat_Hat FStar_Pprint.hardline doc1
                            in
                         FStar_Pprint.op_Hat_Hat comm uu____51836  in
                       FStar_Pprint.op_Hat_Hat FStar_Pprint.hardline
                         uu____51835
                        in
                     FStar_Pprint.op_Hat_Hat prefix1 uu____51834
                   else
                     (let uu____51839 = op_Hat_Slash_Plus_Hat prefix1 doc1
                         in
                      FStar_Pprint.group uu____51839)
                    in
                 let uu____51840 = paren_if ps  in uu____51840 uu____51832)
        | uu____51845 -> p_tmIff e

and (p_maybeFocusArrow : Prims.bool -> FStar_Pprint.document) =
  fun b  -> if b then str "~>" else FStar_Pprint.rarrow

and (p_patternBranch :
  Prims.bool ->
    (FStar_Parser_AST.pattern * FStar_Parser_AST.term
      FStar_Pervasives_Native.option * FStar_Parser_AST.term) ->
      FStar_Pprint.document)
  =
  fun pb  ->
    fun uu____51853  ->
      match uu____51853 with
      | (pat,when_opt,e) ->
          let one_pattern_branch p =
            let branch =
              match when_opt with
              | FStar_Pervasives_Native.None  ->
                  let uu____51877 =
                    let uu____51878 =
                      let uu____51879 =
                        let uu____51880 = p_tuplePattern p  in
                        let uu____51881 =
                          FStar_Pprint.op_Hat_Hat FStar_Pprint.space
                            FStar_Pprint.rarrow
                           in
                        FStar_Pprint.op_Hat_Hat uu____51880 uu____51881  in
                      FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____51879
                       in
                    FStar_Pprint.op_Hat_Hat FStar_Pprint.bar uu____51878  in
                  FStar_Pprint.group uu____51877
              | FStar_Pervasives_Native.Some f ->
                  let uu____51883 =
                    let uu____51884 =
                      let uu____51885 =
                        let uu____51886 =
                          let uu____51887 =
                            let uu____51888 = p_tuplePattern p  in
                            let uu____51889 = str "when"  in
                            FStar_Pprint.op_Hat_Slash_Hat uu____51888
                              uu____51889
                             in
                          FStar_Pprint.group uu____51887  in
                        let uu____51891 =
                          let uu____51892 =
                            let uu____51895 = p_tmFormula f  in
                            [uu____51895; FStar_Pprint.rarrow]  in
                          FStar_Pprint.flow break1 uu____51892  in
                        FStar_Pprint.op_Hat_Slash_Hat uu____51886 uu____51891
                         in
                      FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____51885
                       in
                    FStar_Pprint.op_Hat_Hat FStar_Pprint.bar uu____51884  in
                  FStar_Pprint.hang (Prims.parse_int "2") uu____51883
               in
            let uu____51897 = p_term_sep false pb e  in
            match uu____51897 with
            | (comm,doc1) ->
                if pb
                then
                  (if comm = FStar_Pprint.empty
                   then
                     let uu____51907 = op_Hat_Slash_Plus_Hat branch doc1  in
                     FStar_Pprint.group uu____51907
                   else
                     (let uu____51910 =
                        let uu____51911 =
                          let uu____51912 =
                            let uu____51913 =
                              let uu____51914 =
                                FStar_Pprint.op_Hat_Hat break1 comm  in
                              FStar_Pprint.op_Hat_Hat doc1 uu____51914  in
                            op_Hat_Slash_Plus_Hat branch uu____51913  in
                          FStar_Pprint.group uu____51912  in
                        let uu____51915 =
                          let uu____51916 =
                            let uu____51917 =
                              inline_comment_or_above comm doc1
                                FStar_Pprint.empty
                               in
                            jump2 uu____51917  in
                          FStar_Pprint.op_Hat_Hat branch uu____51916  in
                        FStar_Pprint.ifflat uu____51911 uu____51915  in
                      FStar_Pprint.group uu____51910))
                else
                  if comm <> FStar_Pprint.empty
                  then
                    (let uu____51921 =
                       let uu____51922 =
                         FStar_Pprint.op_Hat_Hat FStar_Pprint.hardline doc1
                          in
                       FStar_Pprint.op_Hat_Hat comm uu____51922  in
                     op_Hat_Slash_Plus_Hat branch uu____51921)
                  else op_Hat_Slash_Plus_Hat branch doc1
             in
          (match pat.FStar_Parser_AST.pat with
           | FStar_Parser_AST.PatOr pats ->
               (match FStar_List.rev pats with
                | hd1::tl1 ->
                    let last_pat_branch = one_pattern_branch hd1  in
                    let uu____51933 =
                      let uu____51934 =
                        let uu____51935 =
                          let uu____51936 =
                            let uu____51937 =
                              let uu____51938 =
                                FStar_Pprint.op_Hat_Hat FStar_Pprint.bar
                                  FStar_Pprint.space
                                 in
                              FStar_Pprint.op_Hat_Hat break1 uu____51938  in
                            FStar_Pprint.separate_map uu____51937
                              p_tuplePattern (FStar_List.rev tl1)
                             in
                          FStar_Pprint.op_Hat_Slash_Hat uu____51936
                            last_pat_branch
                           in
                        FStar_Pprint.op_Hat_Hat FStar_Pprint.space
                          uu____51935
                         in
                      FStar_Pprint.op_Hat_Hat FStar_Pprint.bar uu____51934
                       in
                    FStar_Pprint.group uu____51933
                | [] ->
                    failwith "Impossible: disjunctive pattern can't be empty")
           | uu____51940 -> one_pattern_branch pat)

and (p_tmIff : FStar_Parser_AST.term -> FStar_Pprint.document) =
  fun e  ->
    match e.FStar_Parser_AST.tm with
    | FStar_Parser_AST.Op
        ({ FStar_Ident.idText = "<==>"; FStar_Ident.idRange = uu____51942;_},e1::e2::[])
        ->
        let uu____51948 = str "<==>"  in
        let uu____51950 = p_tmImplies e1  in
        let uu____51951 = p_tmIff e2  in
        infix0 uu____51948 uu____51950 uu____51951
    | uu____51952 -> p_tmImplies e

and (p_tmImplies : FStar_Parser_AST.term -> FStar_Pprint.document) =
  fun e  ->
    match e.FStar_Parser_AST.tm with
    | FStar_Parser_AST.Op
        ({ FStar_Ident.idText = "==>"; FStar_Ident.idRange = uu____51954;_},e1::e2::[])
        ->
        let uu____51960 = str "==>"  in
        let uu____51962 =
          p_tmArrow (Arrows ((Prims.parse_int "2"), (Prims.parse_int "2")))
            false p_tmFormula e1
           in
        let uu____51968 = p_tmImplies e2  in
        infix0 uu____51960 uu____51962 uu____51968
    | uu____51969 ->
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
          let uu____51983 =
            FStar_List.splitAt
              ((FStar_List.length terms) - (Prims.parse_int "1")) terms
             in
          match uu____51983 with
          | (terms',last1) ->
              let uu____52003 =
                match style with
                | Arrows (n1,ln) ->
                    let uu____52038 =
                      let uu____52039 =
                        FStar_Pprint.op_Hat_Hat FStar_Pprint.rarrow break1
                         in
                      FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____52039
                       in
                    let uu____52040 =
                      FStar_Pprint.op_Hat_Hat FStar_Pprint.rarrow
                        FStar_Pprint.space
                       in
                    (n1, ln, terms', uu____52038, uu____52040)
                | Binders (n1,ln,parens1) ->
                    let uu____52054 =
                      if parens1
                      then FStar_List.map soft_parens_with_nesting terms'
                      else terms'  in
                    let uu____52062 =
                      FStar_Pprint.op_Hat_Hat FStar_Pprint.colon
                        FStar_Pprint.space
                       in
                    (n1, ln, uu____52054, break1, uu____52062)
                 in
              (match uu____52003 with
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
                    | _52095 when _52095 = (Prims.parse_int "1") ->
                        FStar_List.hd terms
                    | uu____52096 ->
                        let uu____52097 =
                          let uu____52098 =
                            let uu____52099 =
                              let uu____52100 =
                                FStar_Pprint.separate sep terms'1  in
                              let uu____52101 =
                                let uu____52102 =
                                  FStar_Pprint.op_Hat_Hat last_op1 last2  in
                                FStar_Pprint.op_Hat_Hat one_line_space
                                  uu____52102
                                 in
                              FStar_Pprint.op_Hat_Hat uu____52100 uu____52101
                               in
                            FStar_Pprint.op_Hat_Hat fs uu____52099  in
                          let uu____52103 =
                            let uu____52104 =
                              let uu____52105 =
                                let uu____52106 =
                                  let uu____52107 =
                                    FStar_Pprint.separate sep terms'1  in
                                  FStar_Pprint.op_Hat_Hat fs uu____52107  in
                                let uu____52108 =
                                  let uu____52109 =
                                    let uu____52110 =
                                      let uu____52111 =
                                        FStar_Pprint.op_Hat_Hat sep
                                          single_line_arg_indent
                                         in
                                      let uu____52112 =
                                        FStar_List.map
                                          (fun x  ->
                                             let uu____52118 =
                                               FStar_Pprint.hang
                                                 (Prims.parse_int "2") x
                                                in
                                             FStar_Pprint.align uu____52118)
                                          terms'1
                                         in
                                      FStar_Pprint.separate uu____52111
                                        uu____52112
                                       in
                                    FStar_Pprint.op_Hat_Hat
                                      single_line_arg_indent uu____52110
                                     in
                                  jump2 uu____52109  in
                                FStar_Pprint.ifflat uu____52106 uu____52108
                                 in
                              FStar_Pprint.group uu____52105  in
                            let uu____52120 =
                              let uu____52121 =
                                let uu____52122 =
                                  FStar_Pprint.op_Hat_Hat last_op1 last2  in
                                FStar_Pprint.hang last_n uu____52122  in
                              FStar_Pprint.align uu____52121  in
                            FStar_Pprint.prefix n1 (Prims.parse_int "1")
                              uu____52104 uu____52120
                             in
                          FStar_Pprint.ifflat uu____52098 uu____52103  in
                        FStar_Pprint.group uu____52097))

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
            | Arrows uu____52136 -> p_tmArrow' p_Tm e
            | Binders uu____52143 -> collapse_binders p_Tm e  in
          format_sig style terms false flat_space

and (p_tmArrow' :
  (FStar_Parser_AST.term -> FStar_Pprint.document) ->
    FStar_Parser_AST.term -> FStar_Pprint.document Prims.list)
  =
  fun p_Tm  ->
    fun e  ->
      match e.FStar_Parser_AST.tm with
      | FStar_Parser_AST.Product (bs,tgt) ->
          let uu____52166 = FStar_List.map (fun b  -> p_binder false b) bs
             in
          let uu____52172 = p_tmArrow' p_Tm tgt  in
          FStar_List.append uu____52166 uu____52172
      | uu____52175 -> let uu____52176 = p_Tm e  in [uu____52176]

and (collapse_binders :
  (FStar_Parser_AST.term -> FStar_Pprint.document) ->
    FStar_Parser_AST.term -> FStar_Pprint.document Prims.list)
  =
  fun p_Tm  ->
    fun e  ->
      let rec accumulate_binders p_Tm1 e1 =
        match e1.FStar_Parser_AST.tm with
        | FStar_Parser_AST.Product (bs,tgt) ->
            let uu____52229 = FStar_List.map (fun b  -> p_binder' false b) bs
               in
            let uu____52255 = accumulate_binders p_Tm1 tgt  in
            FStar_List.append uu____52229 uu____52255
        | uu____52278 ->
            let uu____52279 =
              let uu____52290 = p_Tm1 e1  in
              (uu____52290, FStar_Pervasives_Native.None, cat_with_colon)  in
            [uu____52279]
         in
      let fold_fun bs x =
        let uu____52388 = x  in
        match uu____52388 with
        | (b1,t1,f1) ->
            (match bs with
             | [] -> [([b1], t1, f1)]
             | hd1::tl1 ->
                 let uu____52524 = hd1  in
                 (match uu____52524 with
                  | (b2s,t2,uu____52553) ->
                      (match (t1, t2) with
                       | (FStar_Pervasives_Native.Some
                          typ1,FStar_Pervasives_Native.Some typ2) ->
                           if typ1 = typ2
                           then ((FStar_List.append b2s [b1]), t1, f1) :: tl1
                           else ([b1], t1, f1) :: hd1 :: tl1
                       | uu____52663 -> ([b1], t1, f1) :: bs)))
         in
      let p_collapsed_binder cb =
        let uu____52724 = cb  in
        match uu____52724 with
        | (bs,t,f) ->
            (match t with
             | FStar_Pervasives_Native.None  ->
                 (match bs with
                  | b::[] -> b
                  | uu____52753 -> failwith "Impossible")
             | FStar_Pervasives_Native.Some typ ->
                 (match bs with
                  | [] -> failwith "Impossible"
                  | b::[] -> f b typ
                  | hd1::tl1 ->
                      let uu____52766 =
                        FStar_List.fold_left
                          (fun x  ->
                             fun y  ->
                               let uu____52772 =
                                 FStar_Pprint.op_Hat_Hat FStar_Pprint.space y
                                  in
                               FStar_Pprint.op_Hat_Hat x uu____52772) hd1 tl1
                         in
                      f uu____52766 typ))
         in
      let binders =
        let uu____52790 = accumulate_binders p_Tm e  in
        FStar_List.fold_left fold_fun [] uu____52790  in
      map_rev p_collapsed_binder binders

and (p_tmFormula : FStar_Parser_AST.term -> FStar_Pprint.document) =
  fun e  ->
    let conj =
      let uu____52853 =
        let uu____52854 = str "/\\"  in
        FStar_Pprint.op_Hat_Hat uu____52854 break1  in
      FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____52853  in
    let disj =
      let uu____52857 =
        let uu____52858 = str "\\/"  in
        FStar_Pprint.op_Hat_Hat uu____52858 break1  in
      FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____52857  in
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
        ({ FStar_Ident.idText = "\\/"; FStar_Ident.idRange = uu____52878;_},e1::e2::[])
        ->
        let uu____52884 = p_tmDisjunction e1  in
        let uu____52889 =
          let uu____52894 = p_tmConjunction e2  in [uu____52894]  in
        FStar_List.append uu____52884 uu____52889
    | uu____52903 -> let uu____52904 = p_tmConjunction e  in [uu____52904]

and (p_tmConjunction :
  FStar_Parser_AST.term -> FStar_Pprint.document Prims.list) =
  fun e  ->
    match e.FStar_Parser_AST.tm with
    | FStar_Parser_AST.Op
        ({ FStar_Ident.idText = "/\\"; FStar_Ident.idRange = uu____52914;_},e1::e2::[])
        ->
        let uu____52920 = p_tmConjunction e1  in
        let uu____52923 = let uu____52926 = p_tmTuple e2  in [uu____52926]
           in
        FStar_List.append uu____52920 uu____52923
    | uu____52927 -> let uu____52928 = p_tmTuple e  in [uu____52928]

and (p_tmTuple : FStar_Parser_AST.term -> FStar_Pprint.document) =
  fun e  -> with_comment p_tmTuple' e e.FStar_Parser_AST.range

and (p_tmTuple' : FStar_Parser_AST.term -> FStar_Pprint.document) =
  fun e  ->
    match e.FStar_Parser_AST.tm with
    | FStar_Parser_AST.Construct (lid,args) when
        (is_tuple_constructor lid) && (all_explicit args) ->
        let uu____52945 = FStar_Pprint.op_Hat_Hat FStar_Pprint.comma break1
           in
        FStar_Pprint.separate_map uu____52945
          (fun uu____52953  ->
             match uu____52953 with | (e1,uu____52959) -> p_tmEq e1) args
    | uu____52960 -> p_tmEq e

and (paren_if_gt :
  Prims.int -> Prims.int -> FStar_Pprint.document -> FStar_Pprint.document) =
  fun curr  ->
    fun mine  ->
      fun doc1  ->
        if mine <= curr
        then doc1
        else
          (let uu____52969 =
             let uu____52970 =
               FStar_Pprint.op_Hat_Hat doc1 FStar_Pprint.rparen  in
             FStar_Pprint.op_Hat_Hat FStar_Pprint.lparen uu____52970  in
           FStar_Pprint.group uu____52969)

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
               (let uu____52989 = FStar_Ident.text_of_id op  in
                uu____52989 = "="))
              ||
              (let uu____52994 = FStar_Ident.text_of_id op  in
               uu____52994 = "|>")
            ->
            let op1 = FStar_Ident.text_of_id op  in
            let uu____53000 = levels op1  in
            (match uu____53000 with
             | (left1,mine,right1) ->
                 let uu____53019 =
                   let uu____53020 = FStar_All.pipe_left str op1  in
                   let uu____53022 = p_tmEqWith' p_X left1 e1  in
                   let uu____53023 = p_tmEqWith' p_X right1 e2  in
                   infix0 uu____53020 uu____53022 uu____53023  in
                 paren_if_gt curr mine uu____53019)
        | FStar_Parser_AST.Op
            ({ FStar_Ident.idText = ":=";
               FStar_Ident.idRange = uu____53024;_},e1::e2::[])
            ->
            let uu____53030 =
              let uu____53031 = p_tmEqWith p_X e1  in
              let uu____53032 =
                let uu____53033 =
                  let uu____53034 =
                    let uu____53035 = p_tmEqWith p_X e2  in
                    op_Hat_Slash_Plus_Hat FStar_Pprint.equals uu____53035  in
                  FStar_Pprint.op_Hat_Hat FStar_Pprint.colon uu____53034  in
                FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____53033  in
              FStar_Pprint.op_Hat_Hat uu____53031 uu____53032  in
            FStar_Pprint.group uu____53030
        | FStar_Parser_AST.Op
            ({ FStar_Ident.idText = "-"; FStar_Ident.idRange = uu____53036;_},e1::[])
            ->
            let uu____53041 = levels "-"  in
            (match uu____53041 with
             | (left1,mine,right1) ->
                 let uu____53061 = p_tmEqWith' p_X mine e1  in
                 FStar_Pprint.op_Hat_Slash_Hat FStar_Pprint.minus uu____53061)
        | uu____53062 -> p_tmNoEqWith p_X e

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
              (lid,(e1,uu____53110)::(e2,uu____53112)::[]) when
              (FStar_Ident.lid_equals lid FStar_Parser_Const.cons_lid) &&
                (let uu____53132 = is_list e  in
                 Prims.op_Negation uu____53132)
              ->
              let op = "::"  in
              let uu____53137 = levels op  in
              (match uu____53137 with
               | (left1,mine,right1) ->
                   let uu____53156 =
                     let uu____53157 = str op  in
                     let uu____53158 = p_tmNoEqWith' false p_X left1 e1  in
                     let uu____53160 = p_tmNoEqWith' false p_X right1 e2  in
                     infix0 uu____53157 uu____53158 uu____53160  in
                   paren_if_gt curr mine uu____53156)
          | FStar_Parser_AST.Sum (binders,res) ->
              let op = "&"  in
              let uu____53179 = levels op  in
              (match uu____53179 with
               | (left1,mine,right1) ->
                   let p_dsumfst bt =
                     match bt with
                     | FStar_Util.Inl b ->
                         let uu____53213 = p_binder false b  in
                         let uu____53215 =
                           let uu____53216 =
                             let uu____53217 = str op  in
                             FStar_Pprint.op_Hat_Hat uu____53217 break1  in
                           FStar_Pprint.op_Hat_Hat FStar_Pprint.space
                             uu____53216
                            in
                         FStar_Pprint.op_Hat_Hat uu____53213 uu____53215
                     | FStar_Util.Inr t ->
                         let uu____53219 = p_tmNoEqWith' false p_X left1 t
                            in
                         let uu____53221 =
                           let uu____53222 =
                             let uu____53223 = str op  in
                             FStar_Pprint.op_Hat_Hat uu____53223 break1  in
                           FStar_Pprint.op_Hat_Hat FStar_Pprint.space
                             uu____53222
                            in
                         FStar_Pprint.op_Hat_Hat uu____53219 uu____53221
                      in
                   let uu____53224 =
                     let uu____53225 =
                       FStar_Pprint.concat_map p_dsumfst binders  in
                     let uu____53230 = p_tmNoEqWith' false p_X right1 res  in
                     FStar_Pprint.op_Hat_Hat uu____53225 uu____53230  in
                   paren_if_gt curr mine uu____53224)
          | FStar_Parser_AST.Op
              ({ FStar_Ident.idText = "*";
                 FStar_Ident.idRange = uu____53232;_},e1::e2::[])
              when FStar_ST.op_Bang unfold_tuples ->
              let op = "*"  in
              let uu____53262 = levels op  in
              (match uu____53262 with
               | (left1,mine,right1) ->
                   if inside_tuple
                   then
                     let uu____53282 = str op  in
                     let uu____53283 = p_tmNoEqWith' true p_X left1 e1  in
                     let uu____53285 = p_tmNoEqWith' true p_X right1 e2  in
                     infix0 uu____53282 uu____53283 uu____53285
                   else
                     (let uu____53289 =
                        let uu____53290 = str op  in
                        let uu____53291 = p_tmNoEqWith' true p_X left1 e1  in
                        let uu____53293 = p_tmNoEqWith' true p_X right1 e2
                           in
                        infix0 uu____53290 uu____53291 uu____53293  in
                      paren_if_gt curr mine uu____53289))
          | FStar_Parser_AST.Op (op,e1::e2::[]) when is_operatorInfix34 op ->
              let op1 = FStar_Ident.text_of_id op  in
              let uu____53302 = levels op1  in
              (match uu____53302 with
               | (left1,mine,right1) ->
                   let uu____53321 =
                     let uu____53322 = str op1  in
                     let uu____53323 = p_tmNoEqWith' false p_X left1 e1  in
                     let uu____53325 = p_tmNoEqWith' false p_X right1 e2  in
                     infix0 uu____53322 uu____53323 uu____53325  in
                   paren_if_gt curr mine uu____53321)
          | FStar_Parser_AST.Record (with_opt,record_fields) ->
              let uu____53345 =
                let uu____53346 =
                  default_or_map FStar_Pprint.empty p_with_clause with_opt
                   in
                let uu____53347 =
                  let uu____53348 =
                    FStar_Pprint.op_Hat_Hat FStar_Pprint.semi break1  in
                  separate_map_last uu____53348 p_simpleDef record_fields  in
                FStar_Pprint.op_Hat_Hat uu____53346 uu____53347  in
              braces_with_nesting uu____53345
          | FStar_Parser_AST.Op
              ({ FStar_Ident.idText = "~";
                 FStar_Ident.idRange = uu____53353;_},e1::[])
              ->
              let uu____53358 =
                let uu____53359 = str "~"  in
                let uu____53361 = p_atomicTerm e1  in
                FStar_Pprint.op_Hat_Hat uu____53359 uu____53361  in
              FStar_Pprint.group uu____53358
          | FStar_Parser_AST.Paren p when inside_tuple ->
              (match p.FStar_Parser_AST.tm with
               | FStar_Parser_AST.Op
                   ({ FStar_Ident.idText = "*";
                      FStar_Ident.idRange = uu____53363;_},e1::e2::[])
                   ->
                   let op = "*"  in
                   let uu____53372 = levels op  in
                   (match uu____53372 with
                    | (left1,mine,right1) ->
                        let uu____53391 =
                          let uu____53392 = str op  in
                          let uu____53393 = p_tmNoEqWith' true p_X left1 e1
                             in
                          let uu____53395 = p_tmNoEqWith' true p_X right1 e2
                             in
                          infix0 uu____53392 uu____53393 uu____53395  in
                        paren_if_gt curr mine uu____53391)
               | uu____53397 -> p_X e)
          | uu____53398 -> p_X e

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
        let uu____53405 =
          let uu____53406 = p_lident lid  in
          let uu____53407 =
            let uu____53408 = p_appTerm e1  in
            FStar_Pprint.op_Hat_Slash_Hat FStar_Pprint.colon uu____53408  in
          FStar_Pprint.op_Hat_Slash_Hat uu____53406 uu____53407  in
        FStar_Pprint.group uu____53405
    | FStar_Parser_AST.Refine (b,phi) -> p_refinedBinder b phi
    | uu____53411 -> p_appTerm e

and (p_with_clause : FStar_Parser_AST.term -> FStar_Pprint.document) =
  fun e  ->
    let uu____53413 = p_appTerm e  in
    let uu____53414 =
      let uu____53415 =
        let uu____53416 = str "with"  in
        FStar_Pprint.op_Hat_Hat uu____53416 break1  in
      FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____53415  in
    FStar_Pprint.op_Hat_Hat uu____53413 uu____53414

and (p_refinedBinder :
  FStar_Parser_AST.binder -> FStar_Parser_AST.term -> FStar_Pprint.document)
  =
  fun b  ->
    fun phi  ->
      match b.FStar_Parser_AST.b with
      | FStar_Parser_AST.Annotated (lid,t) ->
          let uu____53422 = p_lident lid  in
          p_refinement b.FStar_Parser_AST.aqual uu____53422 t phi
      | FStar_Parser_AST.TAnnotated uu____53423 ->
          failwith "Is this still used ?"
      | FStar_Parser_AST.Variable uu____53429 ->
          let uu____53430 =
            let uu____53432 = FStar_Parser_AST.binder_to_string b  in
            FStar_Util.format1
              "Imposible : a refined binder ought to be annotated %s"
              uu____53432
             in
          failwith uu____53430
      | FStar_Parser_AST.TVariable uu____53435 ->
          let uu____53436 =
            let uu____53438 = FStar_Parser_AST.binder_to_string b  in
            FStar_Util.format1
              "Imposible : a refined binder ought to be annotated %s"
              uu____53438
             in
          failwith uu____53436
      | FStar_Parser_AST.NoName uu____53441 ->
          let uu____53442 =
            let uu____53444 = FStar_Parser_AST.binder_to_string b  in
            FStar_Util.format1
              "Imposible : a refined binder ought to be annotated %s"
              uu____53444
             in
          failwith uu____53442

and (p_simpleDef :
  Prims.bool ->
    (FStar_Ident.lid * FStar_Parser_AST.term) -> FStar_Pprint.document)
  =
  fun ps  ->
    fun uu____53448  ->
      match uu____53448 with
      | (lid,e) ->
          let uu____53456 =
            let uu____53457 = p_qlident lid  in
            let uu____53458 =
              let uu____53459 = p_noSeqTermAndComment ps false e  in
              FStar_Pprint.op_Hat_Slash_Hat FStar_Pprint.equals uu____53459
               in
            FStar_Pprint.op_Hat_Slash_Hat uu____53457 uu____53458  in
          FStar_Pprint.group uu____53456

and (p_appTerm : FStar_Parser_AST.term -> FStar_Pprint.document) =
  fun e  ->
    match e.FStar_Parser_AST.tm with
    | FStar_Parser_AST.App uu____53462 when is_general_application e ->
        let uu____53469 = head_and_args e  in
        (match uu____53469 with
         | (head1,args) ->
             (match args with
              | e1::e2::[] when
                  (FStar_Pervasives_Native.snd e1) = FStar_Parser_AST.Infix
                  ->
                  let uu____53516 = p_argTerm e1  in
                  let uu____53517 =
                    let uu____53518 =
                      let uu____53519 =
                        let uu____53520 = str "`"  in
                        let uu____53522 =
                          let uu____53523 = p_indexingTerm head1  in
                          let uu____53524 = str "`"  in
                          FStar_Pprint.op_Hat_Hat uu____53523 uu____53524  in
                        FStar_Pprint.op_Hat_Hat uu____53520 uu____53522  in
                      FStar_Pprint.group uu____53519  in
                    let uu____53526 = p_argTerm e2  in
                    FStar_Pprint.op_Hat_Slash_Hat uu____53518 uu____53526  in
                  FStar_Pprint.op_Hat_Slash_Hat uu____53516 uu____53517
              | uu____53527 ->
                  let uu____53534 =
                    let uu____53545 =
                      FStar_ST.op_Bang should_print_fs_typ_app  in
                    if uu____53545
                    then
                      let uu____53579 =
                        FStar_Util.take
                          (fun uu____53603  ->
                             match uu____53603 with
                             | (uu____53609,aq) ->
                                 aq = FStar_Parser_AST.FsTypApp) args
                         in
                      match uu____53579 with
                      | (fs_typ_args,args1) ->
                          let uu____53647 =
                            let uu____53648 = p_indexingTerm head1  in
                            let uu____53649 =
                              let uu____53650 =
                                FStar_Pprint.op_Hat_Hat FStar_Pprint.comma
                                  break1
                                 in
                              soft_surround_map_or_flow (Prims.parse_int "2")
                                (Prims.parse_int "0") FStar_Pprint.empty
                                FStar_Pprint.langle uu____53650
                                FStar_Pprint.rangle p_fsTypArg fs_typ_args
                               in
                            FStar_Pprint.op_Hat_Hat uu____53648 uu____53649
                             in
                          (uu____53647, args1)
                    else
                      (let uu____53665 = p_indexingTerm head1  in
                       (uu____53665, args))
                     in
                  (match uu____53534 with
                   | (head_doc,args1) ->
                       let uu____53686 =
                         let uu____53687 =
                           FStar_Pprint.op_Hat_Hat head_doc
                             FStar_Pprint.space
                            in
                         soft_surround_map_or_flow (Prims.parse_int "2")
                           (Prims.parse_int "0") head_doc uu____53687 break1
                           FStar_Pprint.empty p_argTerm args1
                          in
                       FStar_Pprint.group uu____53686)))
    | FStar_Parser_AST.Construct (lid,args) when
        (is_general_construction e) &&
          (let uu____53709 = is_dtuple_constructor lid  in
           Prims.op_Negation uu____53709)
        ->
        (match args with
         | [] -> p_quident lid
         | arg::[] ->
             let uu____53728 =
               let uu____53729 = p_quident lid  in
               let uu____53730 = p_argTerm arg  in
               FStar_Pprint.op_Hat_Slash_Hat uu____53729 uu____53730  in
             FStar_Pprint.group uu____53728
         | hd1::tl1 ->
             let uu____53747 =
               let uu____53748 =
                 let uu____53749 =
                   let uu____53750 = p_quident lid  in
                   let uu____53751 = p_argTerm hd1  in
                   prefix2 uu____53750 uu____53751  in
                 FStar_Pprint.group uu____53749  in
               let uu____53752 =
                 let uu____53753 =
                   FStar_Pprint.separate_map break1 p_argTerm tl1  in
                 jump2 uu____53753  in
               FStar_Pprint.op_Hat_Hat uu____53748 uu____53752  in
             FStar_Pprint.group uu____53747)
    | uu____53758 -> p_indexingTerm e

and (p_argTerm :
  (FStar_Parser_AST.term * FStar_Parser_AST.imp) -> FStar_Pprint.document) =
  fun arg_imp  ->
    match arg_imp with
    | (u,FStar_Parser_AST.UnivApp ) -> p_universe u
    | (e,FStar_Parser_AST.FsTypApp ) ->
        (FStar_Errors.log_issue e.FStar_Parser_AST.range
           (FStar_Errors.Warning_UnexpectedFsTypApp,
             "Unexpected FsTypApp, output might not be formatted correctly.");
         (let uu____53769 = p_indexingTerm e  in
          FStar_Pprint.surround (Prims.parse_int "2") (Prims.parse_int "1")
            FStar_Pprint.langle uu____53769 FStar_Pprint.rangle))
    | (e,FStar_Parser_AST.Hash ) ->
        let uu____53773 = str "#"  in
        let uu____53775 = p_indexingTerm e  in
        FStar_Pprint.op_Hat_Hat uu____53773 uu____53775
    | (e,FStar_Parser_AST.HashBrace t) ->
        let uu____53778 = str "#["  in
        let uu____53780 =
          let uu____53781 = p_indexingTerm t  in
          let uu____53782 =
            let uu____53783 = str "]"  in
            let uu____53785 = p_indexingTerm e  in
            FStar_Pprint.op_Hat_Hat uu____53783 uu____53785  in
          FStar_Pprint.op_Hat_Hat uu____53781 uu____53782  in
        FStar_Pprint.op_Hat_Hat uu____53778 uu____53780
    | (e,FStar_Parser_AST.Infix ) -> p_indexingTerm e
    | (e,FStar_Parser_AST.Nothing ) -> p_indexingTerm e

and (p_fsTypArg :
  (FStar_Parser_AST.term * FStar_Parser_AST.imp) -> FStar_Pprint.document) =
  fun uu____53788  ->
    match uu____53788 with | (e,uu____53794) -> p_indexingTerm e

and (p_indexingTerm_aux :
  (FStar_Parser_AST.term -> FStar_Pprint.document) ->
    FStar_Parser_AST.term -> FStar_Pprint.document)
  =
  fun exit1  ->
    fun e  ->
      match e.FStar_Parser_AST.tm with
      | FStar_Parser_AST.Op
          ({ FStar_Ident.idText = ".()"; FStar_Ident.idRange = uu____53799;_},e1::e2::[])
          ->
          let uu____53805 =
            let uu____53806 = p_indexingTerm_aux p_atomicTermNotQUident e1
               in
            let uu____53807 =
              let uu____53808 =
                let uu____53809 = p_term false false e2  in
                soft_parens_with_nesting uu____53809  in
              FStar_Pprint.op_Hat_Hat FStar_Pprint.dot uu____53808  in
            FStar_Pprint.op_Hat_Hat uu____53806 uu____53807  in
          FStar_Pprint.group uu____53805
      | FStar_Parser_AST.Op
          ({ FStar_Ident.idText = ".[]"; FStar_Ident.idRange = uu____53812;_},e1::e2::[])
          ->
          let uu____53818 =
            let uu____53819 = p_indexingTerm_aux p_atomicTermNotQUident e1
               in
            let uu____53820 =
              let uu____53821 =
                let uu____53822 = p_term false false e2  in
                soft_brackets_with_nesting uu____53822  in
              FStar_Pprint.op_Hat_Hat FStar_Pprint.dot uu____53821  in
            FStar_Pprint.op_Hat_Hat uu____53819 uu____53820  in
          FStar_Pprint.group uu____53818
      | uu____53825 -> exit1 e

and (p_indexingTerm : FStar_Parser_AST.term -> FStar_Pprint.document) =
  fun e  -> p_indexingTerm_aux p_atomicTerm e

and (p_atomicTerm : FStar_Parser_AST.term -> FStar_Pprint.document) =
  fun e  ->
    match e.FStar_Parser_AST.tm with
    | FStar_Parser_AST.LetOpen (lid,e1) ->
        let uu____53830 = p_quident lid  in
        let uu____53831 =
          let uu____53832 =
            let uu____53833 = p_term false false e1  in
            soft_parens_with_nesting uu____53833  in
          FStar_Pprint.op_Hat_Hat FStar_Pprint.dot uu____53832  in
        FStar_Pprint.op_Hat_Hat uu____53830 uu____53831
    | FStar_Parser_AST.Name lid -> p_quident lid
    | FStar_Parser_AST.Op (op,e1::[]) when is_general_prefix_op op ->
        let uu____53841 =
          let uu____53842 = FStar_Ident.text_of_id op  in str uu____53842  in
        let uu____53844 = p_atomicTerm e1  in
        FStar_Pprint.op_Hat_Hat uu____53841 uu____53844
    | uu____53845 -> p_atomicTermNotQUident e

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
         | uu____53858 -> p_constant c)
    | FStar_Parser_AST.Name lid when
        FStar_Ident.lid_equals lid FStar_Parser_Const.true_lid -> str "True"
    | FStar_Parser_AST.Name lid when
        FStar_Ident.lid_equals lid FStar_Parser_Const.false_lid ->
        str "False"
    | FStar_Parser_AST.Op (op,e1::[]) when is_general_prefix_op op ->
        let uu____53867 =
          let uu____53868 = FStar_Ident.text_of_id op  in str uu____53868  in
        let uu____53870 = p_atomicTermNotQUident e1  in
        FStar_Pprint.op_Hat_Hat uu____53867 uu____53870
    | FStar_Parser_AST.Op (op,[]) ->
        let uu____53874 =
          let uu____53875 =
            let uu____53876 =
              let uu____53877 = FStar_Ident.text_of_id op  in str uu____53877
               in
            let uu____53879 =
              FStar_Pprint.op_Hat_Hat FStar_Pprint.space FStar_Pprint.rparen
               in
            FStar_Pprint.op_Hat_Hat uu____53876 uu____53879  in
          FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____53875  in
        FStar_Pprint.op_Hat_Hat FStar_Pprint.lparen uu____53874
    | FStar_Parser_AST.Construct (lid,args) when is_dtuple_constructor lid ->
        let uu____53894 = all_explicit args  in
        if uu____53894
        then
          let uu____53897 =
            FStar_Pprint.op_Hat_Hat FStar_Pprint.lparen FStar_Pprint.bar  in
          let uu____53898 =
            let uu____53899 =
              FStar_Pprint.op_Hat_Hat FStar_Pprint.comma break1  in
            let uu____53900 = FStar_List.map FStar_Pervasives_Native.fst args
               in
            FStar_Pprint.separate_map uu____53899 p_tmEq uu____53900  in
          let uu____53907 =
            FStar_Pprint.op_Hat_Hat FStar_Pprint.bar FStar_Pprint.rparen  in
          FStar_Pprint.surround (Prims.parse_int "2") (Prims.parse_int "1")
            uu____53897 uu____53898 uu____53907
        else
          (match args with
           | [] -> p_quident lid
           | arg::[] ->
               let uu____53929 =
                 let uu____53930 = p_quident lid  in
                 let uu____53931 = p_argTerm arg  in
                 FStar_Pprint.op_Hat_Slash_Hat uu____53930 uu____53931  in
               FStar_Pprint.group uu____53929
           | hd1::tl1 ->
               let uu____53948 =
                 let uu____53949 =
                   let uu____53950 =
                     let uu____53951 = p_quident lid  in
                     let uu____53952 = p_argTerm hd1  in
                     prefix2 uu____53951 uu____53952  in
                   FStar_Pprint.group uu____53950  in
                 let uu____53953 =
                   let uu____53954 =
                     FStar_Pprint.separate_map break1 p_argTerm tl1  in
                   jump2 uu____53954  in
                 FStar_Pprint.op_Hat_Hat uu____53949 uu____53953  in
               FStar_Pprint.group uu____53948)
    | FStar_Parser_AST.Project (e1,lid) ->
        let uu____53961 =
          let uu____53962 = p_atomicTermNotQUident e1  in
          let uu____53963 =
            let uu____53964 = p_qlident lid  in
            FStar_Pprint.op_Hat_Hat FStar_Pprint.dot uu____53964  in
          FStar_Pprint.prefix (Prims.parse_int "2") (Prims.parse_int "0")
            uu____53962 uu____53963
           in
        FStar_Pprint.group uu____53961
    | uu____53967 -> p_projectionLHS e

and (p_projectionLHS : FStar_Parser_AST.term -> FStar_Pprint.document) =
  fun e  ->
    match e.FStar_Parser_AST.tm with
    | FStar_Parser_AST.Var lid -> p_qlident lid
    | FStar_Parser_AST.Projector (constr_lid,field_lid) ->
        let uu____53972 = p_quident constr_lid  in
        let uu____53973 =
          let uu____53974 =
            let uu____53975 = p_lident field_lid  in
            FStar_Pprint.op_Hat_Hat FStar_Pprint.dot uu____53975  in
          FStar_Pprint.op_Hat_Hat FStar_Pprint.qmark uu____53974  in
        FStar_Pprint.op_Hat_Hat uu____53972 uu____53973
    | FStar_Parser_AST.Discrim constr_lid ->
        let uu____53977 = p_quident constr_lid  in
        FStar_Pprint.op_Hat_Hat uu____53977 FStar_Pprint.qmark
    | FStar_Parser_AST.Paren e1 ->
        let uu____53979 = p_term_sep false false e1  in
        (match uu____53979 with
         | (comm,t) ->
             let doc1 = soft_parens_with_nesting t  in
             if comm = FStar_Pprint.empty
             then doc1
             else
               (let uu____53992 =
                  FStar_Pprint.op_Hat_Hat FStar_Pprint.hardline doc1  in
                FStar_Pprint.op_Hat_Hat comm uu____53992))
    | uu____53993 when is_array e ->
        let es = extract_from_list e  in
        let uu____53997 =
          FStar_Pprint.op_Hat_Hat FStar_Pprint.lbracket FStar_Pprint.bar  in
        let uu____53998 =
          let uu____53999 = FStar_Pprint.op_Hat_Hat FStar_Pprint.semi break1
             in
          separate_map_or_flow_last uu____53999
            (fun ps  -> p_noSeqTermAndComment ps false) es
           in
        let uu____54004 =
          FStar_Pprint.op_Hat_Hat FStar_Pprint.bar FStar_Pprint.rbracket  in
        FStar_Pprint.surround (Prims.parse_int "2") (Prims.parse_int "0")
          uu____53997 uu____53998 uu____54004
    | uu____54007 when is_list e ->
        let uu____54008 =
          let uu____54009 = FStar_Pprint.op_Hat_Hat FStar_Pprint.semi break1
             in
          let uu____54010 = extract_from_list e  in
          separate_map_or_flow_last uu____54009
            (fun ps  -> p_noSeqTermAndComment ps false) uu____54010
           in
        FStar_Pprint.surround (Prims.parse_int "2") (Prims.parse_int "0")
          FStar_Pprint.lbracket uu____54008 FStar_Pprint.rbracket
    | uu____54019 when is_lex_list e ->
        let uu____54020 =
          FStar_Pprint.op_Hat_Hat FStar_Pprint.percent FStar_Pprint.lbracket
           in
        let uu____54021 =
          let uu____54022 = FStar_Pprint.op_Hat_Hat FStar_Pprint.semi break1
             in
          let uu____54023 = extract_from_list e  in
          separate_map_or_flow_last uu____54022
            (fun ps  -> p_noSeqTermAndComment ps false) uu____54023
           in
        FStar_Pprint.surround (Prims.parse_int "2") (Prims.parse_int "1")
          uu____54020 uu____54021 FStar_Pprint.rbracket
    | uu____54032 when is_ref_set e ->
        let es = extract_from_ref_set e  in
        let uu____54036 =
          FStar_Pprint.op_Hat_Hat FStar_Pprint.bang FStar_Pprint.lbrace  in
        let uu____54037 =
          let uu____54038 = FStar_Pprint.op_Hat_Hat FStar_Pprint.comma break1
             in
          separate_map_or_flow uu____54038 p_appTerm es  in
        FStar_Pprint.surround (Prims.parse_int "2") (Prims.parse_int "0")
          uu____54036 uu____54037 FStar_Pprint.rbrace
    | FStar_Parser_AST.Labeled (e1,s,b) ->
        let uu____54048 = str (Prims.op_Hat "(*" (Prims.op_Hat s "*)"))  in
        let uu____54051 = p_term false false e1  in
        FStar_Pprint.op_Hat_Slash_Hat uu____54048 uu____54051
    | FStar_Parser_AST.Op (op,args) when
        let uu____54060 = handleable_op op args  in
        Prims.op_Negation uu____54060 ->
        let uu____54062 =
          let uu____54064 =
            let uu____54066 = FStar_Ident.text_of_id op  in
            let uu____54068 =
              let uu____54070 =
                let uu____54072 =
                  FStar_Util.string_of_int (FStar_List.length args)  in
                Prims.op_Hat uu____54072
                  " arguments couldn't be handled by the pretty printer"
                 in
              Prims.op_Hat " with " uu____54070  in
            Prims.op_Hat uu____54066 uu____54068  in
          Prims.op_Hat "Operation " uu____54064  in
        failwith uu____54062
    | FStar_Parser_AST.Uvar id1 ->
        failwith "Unexpected universe variable out of universe context"
    | FStar_Parser_AST.Wild  ->
        let uu____54079 = p_term false false e  in
        soft_parens_with_nesting uu____54079
    | FStar_Parser_AST.Const uu____54082 ->
        let uu____54083 = p_term false false e  in
        soft_parens_with_nesting uu____54083
    | FStar_Parser_AST.Op uu____54086 ->
        let uu____54093 = p_term false false e  in
        soft_parens_with_nesting uu____54093
    | FStar_Parser_AST.Tvar uu____54096 ->
        let uu____54097 = p_term false false e  in
        soft_parens_with_nesting uu____54097
    | FStar_Parser_AST.Var uu____54100 ->
        let uu____54101 = p_term false false e  in
        soft_parens_with_nesting uu____54101
    | FStar_Parser_AST.Name uu____54104 ->
        let uu____54105 = p_term false false e  in
        soft_parens_with_nesting uu____54105
    | FStar_Parser_AST.Construct uu____54108 ->
        let uu____54119 = p_term false false e  in
        soft_parens_with_nesting uu____54119
    | FStar_Parser_AST.Abs uu____54122 ->
        let uu____54129 = p_term false false e  in
        soft_parens_with_nesting uu____54129
    | FStar_Parser_AST.App uu____54132 ->
        let uu____54139 = p_term false false e  in
        soft_parens_with_nesting uu____54139
    | FStar_Parser_AST.Let uu____54142 ->
        let uu____54163 = p_term false false e  in
        soft_parens_with_nesting uu____54163
    | FStar_Parser_AST.LetOpen uu____54166 ->
        let uu____54171 = p_term false false e  in
        soft_parens_with_nesting uu____54171
    | FStar_Parser_AST.Seq uu____54174 ->
        let uu____54179 = p_term false false e  in
        soft_parens_with_nesting uu____54179
    | FStar_Parser_AST.Bind uu____54182 ->
        let uu____54189 = p_term false false e  in
        soft_parens_with_nesting uu____54189
    | FStar_Parser_AST.If uu____54192 ->
        let uu____54199 = p_term false false e  in
        soft_parens_with_nesting uu____54199
    | FStar_Parser_AST.Match uu____54202 ->
        let uu____54217 = p_term false false e  in
        soft_parens_with_nesting uu____54217
    | FStar_Parser_AST.TryWith uu____54220 ->
        let uu____54235 = p_term false false e  in
        soft_parens_with_nesting uu____54235
    | FStar_Parser_AST.Ascribed uu____54238 ->
        let uu____54247 = p_term false false e  in
        soft_parens_with_nesting uu____54247
    | FStar_Parser_AST.Record uu____54250 ->
        let uu____54263 = p_term false false e  in
        soft_parens_with_nesting uu____54263
    | FStar_Parser_AST.Project uu____54266 ->
        let uu____54271 = p_term false false e  in
        soft_parens_with_nesting uu____54271
    | FStar_Parser_AST.Product uu____54274 ->
        let uu____54281 = p_term false false e  in
        soft_parens_with_nesting uu____54281
    | FStar_Parser_AST.Sum uu____54284 ->
        let uu____54295 = p_term false false e  in
        soft_parens_with_nesting uu____54295
    | FStar_Parser_AST.QForall uu____54298 ->
        let uu____54311 = p_term false false e  in
        soft_parens_with_nesting uu____54311
    | FStar_Parser_AST.QExists uu____54314 ->
        let uu____54327 = p_term false false e  in
        soft_parens_with_nesting uu____54327
    | FStar_Parser_AST.Refine uu____54330 ->
        let uu____54335 = p_term false false e  in
        soft_parens_with_nesting uu____54335
    | FStar_Parser_AST.NamedTyp uu____54338 ->
        let uu____54343 = p_term false false e  in
        soft_parens_with_nesting uu____54343
    | FStar_Parser_AST.Requires uu____54346 ->
        let uu____54354 = p_term false false e  in
        soft_parens_with_nesting uu____54354
    | FStar_Parser_AST.Ensures uu____54357 ->
        let uu____54365 = p_term false false e  in
        soft_parens_with_nesting uu____54365
    | FStar_Parser_AST.Attributes uu____54368 ->
        let uu____54371 = p_term false false e  in
        soft_parens_with_nesting uu____54371
    | FStar_Parser_AST.Quote uu____54374 ->
        let uu____54379 = p_term false false e  in
        soft_parens_with_nesting uu____54379
    | FStar_Parser_AST.VQuote uu____54382 ->
        let uu____54383 = p_term false false e  in
        soft_parens_with_nesting uu____54383
    | FStar_Parser_AST.Antiquote uu____54386 ->
        let uu____54387 = p_term false false e  in
        soft_parens_with_nesting uu____54387
    | FStar_Parser_AST.CalcProof uu____54390 ->
        let uu____54399 = p_term false false e  in
        soft_parens_with_nesting uu____54399

and (p_constant : FStar_Const.sconst -> FStar_Pprint.document) =
  fun uu___339_54402  ->
    match uu___339_54402 with
    | FStar_Const.Const_effect  -> str "Effect"
    | FStar_Const.Const_unit  -> str "()"
    | FStar_Const.Const_bool b -> FStar_Pprint.doc_of_bool b
    | FStar_Const.Const_real r -> str (Prims.op_Hat r "R")
    | FStar_Const.Const_float x -> str (FStar_Util.string_of_float x)
    | FStar_Const.Const_char x -> FStar_Pprint.doc_of_char x
    | FStar_Const.Const_string (s,uu____54414) ->
        let uu____54417 = str (FStar_String.escaped s)  in
        FStar_Pprint.dquotes uu____54417
    | FStar_Const.Const_bytearray (bytes,uu____54419) ->
        let uu____54424 =
          let uu____54425 = str (FStar_Util.string_of_bytes bytes)  in
          FStar_Pprint.dquotes uu____54425  in
        let uu____54426 = str "B"  in
        FStar_Pprint.op_Hat_Hat uu____54424 uu____54426
    | FStar_Const.Const_int (repr,sign_width_opt) ->
        let signedness uu___337_54449 =
          match uu___337_54449 with
          | FStar_Const.Unsigned  -> str "u"
          | FStar_Const.Signed  -> FStar_Pprint.empty  in
        let width uu___338_54456 =
          match uu___338_54456 with
          | FStar_Const.Int8  -> str "y"
          | FStar_Const.Int16  -> str "s"
          | FStar_Const.Int32  -> str "l"
          | FStar_Const.Int64  -> str "L"  in
        let ending =
          default_or_map FStar_Pprint.empty
            (fun uu____54471  ->
               match uu____54471 with
               | (s,w) ->
                   let uu____54478 = signedness s  in
                   let uu____54479 = width w  in
                   FStar_Pprint.op_Hat_Hat uu____54478 uu____54479)
            sign_width_opt
           in
        let uu____54480 = str repr  in
        FStar_Pprint.op_Hat_Hat uu____54480 ending
    | FStar_Const.Const_range_of  -> str "range_of"
    | FStar_Const.Const_set_range_of  -> str "set_range_of"
    | FStar_Const.Const_range r ->
        let uu____54484 = FStar_Range.string_of_range r  in str uu____54484
    | FStar_Const.Const_reify  -> str "reify"
    | FStar_Const.Const_reflect lid ->
        let uu____54488 = p_quident lid  in
        let uu____54489 =
          let uu____54490 =
            let uu____54491 = str "reflect"  in
            FStar_Pprint.op_Hat_Hat FStar_Pprint.dot uu____54491  in
          FStar_Pprint.op_Hat_Hat FStar_Pprint.qmark uu____54490  in
        FStar_Pprint.op_Hat_Hat uu____54488 uu____54489

and (p_universe : FStar_Parser_AST.term -> FStar_Pprint.document) =
  fun u  ->
    let uu____54494 = str "u#"  in
    let uu____54496 = p_atomicUniverse u  in
    FStar_Pprint.op_Hat_Hat uu____54494 uu____54496

and (p_universeFrom : FStar_Parser_AST.term -> FStar_Pprint.document) =
  fun u  ->
    match u.FStar_Parser_AST.tm with
    | FStar_Parser_AST.Op
        ({ FStar_Ident.idText = "+"; FStar_Ident.idRange = uu____54498;_},u1::u2::[])
        ->
        let uu____54504 =
          let uu____54505 = p_universeFrom u1  in
          let uu____54506 =
            let uu____54507 = p_universeFrom u2  in
            FStar_Pprint.op_Hat_Slash_Hat FStar_Pprint.plus uu____54507  in
          FStar_Pprint.op_Hat_Slash_Hat uu____54505 uu____54506  in
        FStar_Pprint.group uu____54504
    | FStar_Parser_AST.App uu____54508 ->
        let uu____54515 = head_and_args u  in
        (match uu____54515 with
         | (head1,args) ->
             (match head1.FStar_Parser_AST.tm with
              | FStar_Parser_AST.Var maybe_max_lid when
                  FStar_Ident.lid_equals maybe_max_lid
                    FStar_Parser_Const.max_lid
                  ->
                  let uu____54541 =
                    let uu____54542 = p_qlident FStar_Parser_Const.max_lid
                       in
                    let uu____54543 =
                      FStar_Pprint.separate_map FStar_Pprint.space
                        (fun uu____54551  ->
                           match uu____54551 with
                           | (u1,uu____54557) -> p_atomicUniverse u1) args
                       in
                    op_Hat_Slash_Plus_Hat uu____54542 uu____54543  in
                  FStar_Pprint.group uu____54541
              | uu____54558 ->
                  let uu____54559 =
                    let uu____54561 = FStar_Parser_AST.term_to_string u  in
                    FStar_Util.format1 "Invalid term in universe context %s"
                      uu____54561
                     in
                  failwith uu____54559))
    | uu____54564 -> p_atomicUniverse u

and (p_atomicUniverse : FStar_Parser_AST.term -> FStar_Pprint.document) =
  fun u  ->
    match u.FStar_Parser_AST.tm with
    | FStar_Parser_AST.Wild  -> FStar_Pprint.underscore
    | FStar_Parser_AST.Const (FStar_Const.Const_int (r,sw)) ->
        p_constant (FStar_Const.Const_int (r, sw))
    | FStar_Parser_AST.Uvar id1 ->
        let uu____54590 = FStar_Ident.text_of_id id1  in str uu____54590
    | FStar_Parser_AST.Paren u1 ->
        let uu____54593 = p_universeFrom u1  in
        soft_parens_with_nesting uu____54593
    | FStar_Parser_AST.Op
        ({ FStar_Ident.idText = "+"; FStar_Ident.idRange = uu____54594;_},uu____54595::uu____54596::[])
        ->
        let uu____54600 = p_universeFrom u  in
        soft_parens_with_nesting uu____54600
    | FStar_Parser_AST.App uu____54601 ->
        let uu____54608 = p_universeFrom u  in
        soft_parens_with_nesting uu____54608
    | uu____54609 ->
        let uu____54610 =
          let uu____54612 = FStar_Parser_AST.term_to_string u  in
          FStar_Util.format1 "Invalid term in universe context %s"
            uu____54612
           in
        failwith uu____54610

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
       | FStar_Parser_AST.Module (uu____54701,decls) ->
           let uu____54707 =
             FStar_All.pipe_right decls (FStar_List.map decl_to_document)  in
           FStar_All.pipe_right uu____54707
             (FStar_Pprint.separate FStar_Pprint.hardline)
       | FStar_Parser_AST.Interface (uu____54716,decls,uu____54718) ->
           let uu____54725 =
             FStar_All.pipe_right decls (FStar_List.map decl_to_document)  in
           FStar_All.pipe_right uu____54725
             (FStar_Pprint.separate FStar_Pprint.hardline)
        in
     FStar_ST.op_Colon_Equals should_print_fs_typ_app false; res)
  
let (comments_to_document :
  (Prims.string * FStar_Range.range) Prims.list -> FStar_Pprint.document) =
  fun comments  ->
    FStar_Pprint.separate_map FStar_Pprint.hardline
      (fun uu____54785  ->
         match uu____54785 with | (comment,range) -> str comment) comments
  
let (extract_decl_range : FStar_Parser_AST.decl -> decl_meta) =
  fun d  ->
    let has_qs =
      match ((d.FStar_Parser_AST.quals), (d.FStar_Parser_AST.d)) with
      | ((FStar_Parser_AST.Assumption )::[],FStar_Parser_AST.Assume
         (id1,uu____54807)) -> false
      | ([],uu____54811) -> false
      | uu____54815 -> true  in
    {
      r = (d.FStar_Parser_AST.drange);
      has_qs;
      has_attrs =
        (Prims.op_Negation (FStar_List.isEmpty d.FStar_Parser_AST.attrs));
      has_fsdoc = (FStar_Util.is_some d.FStar_Parser_AST.doc);
      is_fsdoc =
        (match d.FStar_Parser_AST.d with
         | FStar_Parser_AST.Fsdoc uu____54825 -> true
         | uu____54827 -> false)
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
        | FStar_Parser_AST.Module (uu____54870,decls) -> decls
        | FStar_Parser_AST.Interface (uu____54876,decls,uu____54878) -> decls
         in
      FStar_ST.op_Colon_Equals should_print_fs_typ_app false;
      (match decls with
       | [] -> (FStar_Pprint.empty, comments)
       | d::ds ->
           let uu____54930 =
             match ds with
             | {
                 FStar_Parser_AST.d = FStar_Parser_AST.Pragma
                   (FStar_Parser_AST.LightOff );
                 FStar_Parser_AST.drange = uu____54943;
                 FStar_Parser_AST.doc = uu____54944;
                 FStar_Parser_AST.quals = uu____54945;
                 FStar_Parser_AST.attrs = uu____54946;_}::uu____54947 ->
                 let d0 = FStar_List.hd ds  in
                 let uu____54953 =
                   let uu____54956 =
                     let uu____54959 = FStar_List.tl ds  in d :: uu____54959
                      in
                   d0 :: uu____54956  in
                 (uu____54953, (d0.FStar_Parser_AST.drange))
             | uu____54964 -> ((d :: ds), (d.FStar_Parser_AST.drange))  in
           (match uu____54930 with
            | (decls1,first_range) ->
                (FStar_ST.op_Colon_Equals comment_stack comments;
                 (let initial_comment =
                    let uu____55021 = FStar_Range.start_of_range first_range
                       in
                    place_comments_until_pos (Prims.parse_int "0")
                      (Prims.parse_int "1") uu____55021 dummy_meta
                      FStar_Pprint.empty false true
                     in
                  let doc1 =
                    separate_map_with_comments FStar_Pprint.empty
                      FStar_Pprint.empty p_decl decls1 extract_decl_range
                     in
                  let comments1 = FStar_ST.op_Bang comment_stack  in
                  FStar_ST.op_Colon_Equals comment_stack [];
                  FStar_ST.op_Colon_Equals should_print_fs_typ_app false;
                  (let uu____55130 =
                     FStar_Pprint.op_Hat_Hat initial_comment doc1  in
                   (uu____55130, comments1))))))
  