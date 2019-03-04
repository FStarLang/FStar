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
            let uu____43270 = let uu____43273 = f x  in uu____43273 :: acc
               in
            aux xs uu____43270
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
            let uu____43340 = f x  in
            (match uu____43340 with
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
          let uu____43396 = f x  in if uu____43396 then all f xs else false
  
let (all_explicit :
  (FStar_Parser_AST.term * FStar_Parser_AST.imp) Prims.list -> Prims.bool) =
  fun args  ->
    FStar_Util.for_all
      (fun uu___324_43429  ->
         match uu___324_43429 with
         | (uu____43435,FStar_Parser_AST.Nothing ) -> true
         | uu____43437 -> false) args
  
let (should_print_fs_typ_app : Prims.bool FStar_ST.ref) =
  FStar_Util.mk_ref false 
let (unfold_tuples : Prims.bool FStar_ST.ref) = FStar_Util.mk_ref true 
let with_fs_typ_app :
  'Auu____43488 'Auu____43489 .
    Prims.bool ->
      ('Auu____43488 -> 'Auu____43489) -> 'Auu____43488 -> 'Auu____43489
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
  'Auu____43599 'Auu____43600 .
    'Auu____43599 ->
      ('Auu____43600 -> 'Auu____43599) ->
        'Auu____43600 FStar_Pervasives_Native.option -> 'Auu____43599
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
  'Auu____43713 .
    FStar_Pprint.document ->
      ('Auu____43713 -> FStar_Pprint.document) ->
        'Auu____43713 Prims.list -> FStar_Pprint.document
  =
  fun sep  ->
    fun f  ->
      fun l  ->
        let uu____43738 =
          let uu____43739 =
            let uu____43740 = FStar_Pprint.op_Hat_Hat sep break1  in
            FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____43740  in
          FStar_Pprint.separate_map uu____43739 f l  in
        FStar_Pprint.group uu____43738
  
let precede_break_separate_map :
  'Auu____43752 .
    FStar_Pprint.document ->
      FStar_Pprint.document ->
        ('Auu____43752 -> FStar_Pprint.document) ->
          'Auu____43752 Prims.list -> FStar_Pprint.document
  =
  fun prec  ->
    fun sep  ->
      fun f  ->
        fun l  ->
          let uu____43782 =
            let uu____43783 = FStar_Pprint.op_Hat_Hat prec FStar_Pprint.space
               in
            let uu____43784 =
              let uu____43785 = FStar_List.hd l  in
              FStar_All.pipe_right uu____43785 f  in
            FStar_Pprint.precede uu____43783 uu____43784  in
          let uu____43786 =
            let uu____43787 = FStar_List.tl l  in
            FStar_Pprint.concat_map
              (fun x  ->
                 let uu____43793 =
                   let uu____43794 =
                     let uu____43795 = f x  in
                     FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____43795
                      in
                   FStar_Pprint.op_Hat_Hat sep uu____43794  in
                 FStar_Pprint.op_Hat_Hat break1 uu____43793) uu____43787
             in
          FStar_Pprint.op_Hat_Hat uu____43782 uu____43786
  
let concat_break_map :
  'Auu____43803 .
    ('Auu____43803 -> FStar_Pprint.document) ->
      'Auu____43803 Prims.list -> FStar_Pprint.document
  =
  fun f  ->
    fun l  ->
      let uu____43823 =
        FStar_Pprint.concat_map
          (fun x  ->
             let uu____43827 = f x  in
             FStar_Pprint.op_Hat_Hat uu____43827 break1) l
         in
      FStar_Pprint.group uu____43823
  
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
    let uu____43890 = str "begin"  in
    let uu____43892 = str "end"  in
    FStar_Pprint.soft_surround (Prims.parse_int "2") (Prims.parse_int "1")
      uu____43890 contents uu____43892
  
let separate_map_last :
  'Auu____43905 .
    FStar_Pprint.document ->
      (Prims.bool -> 'Auu____43905 -> FStar_Pprint.document) ->
        'Auu____43905 Prims.list -> FStar_Pprint.document
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
  'Auu____43963 .
    FStar_Pprint.document ->
      (Prims.bool -> 'Auu____43963 -> FStar_Pprint.document) ->
        'Auu____43963 Prims.list -> FStar_Pprint.document
  =
  fun sep  ->
    fun f  ->
      fun l  ->
        let uu____43995 =
          let uu____43996 =
            let uu____43997 = FStar_Pprint.op_Hat_Hat sep break1  in
            FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____43997  in
          separate_map_last uu____43996 f l  in
        FStar_Pprint.group uu____43995
  
let separate_map_or_flow :
  'Auu____44007 .
    FStar_Pprint.document ->
      ('Auu____44007 -> FStar_Pprint.document) ->
        'Auu____44007 Prims.list -> FStar_Pprint.document
  =
  fun sep  ->
    fun f  ->
      fun l  ->
        if (FStar_List.length l) < (Prims.parse_int "10")
        then FStar_Pprint.separate_map sep f l
        else FStar_Pprint.flow_map sep f l
  
let flow_map_last :
  'Auu____44045 .
    FStar_Pprint.document ->
      (Prims.bool -> 'Auu____44045 -> FStar_Pprint.document) ->
        'Auu____44045 Prims.list -> FStar_Pprint.document
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
  'Auu____44103 .
    FStar_Pprint.document ->
      (Prims.bool -> 'Auu____44103 -> FStar_Pprint.document) ->
        'Auu____44103 Prims.list -> FStar_Pprint.document
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
              let uu____44185 = FStar_Pprint.op_Hat_Slash_Hat doc1 doc3  in
              FStar_Pprint.group uu____44185
            else FStar_Pprint.surround n1 b doc1 doc2 doc3
  
let soft_surround_separate_map :
  'Auu____44207 .
    Prims.int ->
      Prims.int ->
        FStar_Pprint.document ->
          FStar_Pprint.document ->
            FStar_Pprint.document ->
              FStar_Pprint.document ->
                ('Auu____44207 -> FStar_Pprint.document) ->
                  'Auu____44207 Prims.list -> FStar_Pprint.document
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
                    (let uu____44266 = FStar_Pprint.separate_map sep f xs  in
                     FStar_Pprint.soft_surround n1 b opening uu____44266
                       closing)
  
let soft_surround_map_or_flow :
  'Auu____44286 .
    Prims.int ->
      Prims.int ->
        FStar_Pprint.document ->
          FStar_Pprint.document ->
            FStar_Pprint.document ->
              FStar_Pprint.document ->
                ('Auu____44286 -> FStar_Pprint.document) ->
                  'Auu____44286 Prims.list -> FStar_Pprint.document
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
                    (let uu____44345 = separate_map_or_flow sep f xs  in
                     FStar_Pprint.soft_surround n1 b opening uu____44345
                       closing)
  
let (doc_of_fsdoc :
  (Prims.string * (Prims.string * Prims.string) Prims.list) ->
    FStar_Pprint.document)
  =
  fun uu____44364  ->
    match uu____44364 with
    | (comment,keywords) ->
        let uu____44398 =
          let uu____44399 =
            let uu____44402 = str comment  in
            let uu____44403 =
              let uu____44406 =
                let uu____44409 =
                  FStar_Pprint.separate_map FStar_Pprint.comma
                    (fun uu____44420  ->
                       match uu____44420 with
                       | (k,v1) ->
                           let uu____44433 =
                             let uu____44436 = str k  in
                             let uu____44437 =
                               let uu____44440 =
                                 let uu____44443 = str v1  in [uu____44443]
                                  in
                               FStar_Pprint.rarrow :: uu____44440  in
                             uu____44436 :: uu____44437  in
                           FStar_Pprint.concat uu____44433) keywords
                   in
                [uu____44409]  in
              FStar_Pprint.space :: uu____44406  in
            uu____44402 :: uu____44403  in
          FStar_Pprint.concat uu____44399  in
        FStar_Pprint.group uu____44398
  
let (is_unit : FStar_Parser_AST.term -> Prims.bool) =
  fun e  ->
    match e.FStar_Parser_AST.tm with
    | FStar_Parser_AST.Const (FStar_Const.Const_unit ) -> true
    | uu____44453 -> false
  
let (matches_var : FStar_Parser_AST.term -> FStar_Ident.ident -> Prims.bool)
  =
  fun t  ->
    fun x  ->
      match t.FStar_Parser_AST.tm with
      | FStar_Parser_AST.Var y ->
          let uu____44469 = FStar_Ident.text_of_lid y  in
          x.FStar_Ident.idText = uu____44469
      | uu____44472 -> false
  
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
        | FStar_Parser_AST.Construct (lid,uu____44523::(e2,uu____44525)::[])
            -> (FStar_Ident.lid_equals lid cons_lid1) && (aux e2)
        | uu____44548 -> false  in
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
    | FStar_Parser_AST.Construct (uu____44572,[]) -> []
    | FStar_Parser_AST.Construct
        (uu____44583,(e1,FStar_Parser_AST.Nothing )::(e2,FStar_Parser_AST.Nothing
                                                      )::[])
        -> let uu____44604 = extract_from_list e2  in e1 :: uu____44604
    | uu____44607 ->
        let uu____44608 =
          let uu____44610 = FStar_Parser_AST.term_to_string e  in
          FStar_Util.format1 "Not a list %s" uu____44610  in
        failwith uu____44608
  
let (is_array : FStar_Parser_AST.term -> Prims.bool) =
  fun e  ->
    match e.FStar_Parser_AST.tm with
    | FStar_Parser_AST.App
        ({ FStar_Parser_AST.tm = FStar_Parser_AST.Var lid;
           FStar_Parser_AST.range = uu____44624;
           FStar_Parser_AST.level = uu____44625;_},l,FStar_Parser_AST.Nothing
         )
        ->
        (FStar_Ident.lid_equals lid FStar_Parser_Const.array_mk_array_lid) &&
          (is_list l)
    | uu____44627 -> false
  
let rec (is_ref_set : FStar_Parser_AST.term -> Prims.bool) =
  fun e  ->
    match e.FStar_Parser_AST.tm with
    | FStar_Parser_AST.Var maybe_empty_lid ->
        FStar_Ident.lid_equals maybe_empty_lid FStar_Parser_Const.set_empty
    | FStar_Parser_AST.App
        ({ FStar_Parser_AST.tm = FStar_Parser_AST.Var maybe_singleton_lid;
           FStar_Parser_AST.range = uu____44639;
           FStar_Parser_AST.level = uu____44640;_},{
                                                     FStar_Parser_AST.tm =
                                                       FStar_Parser_AST.App
                                                       ({
                                                          FStar_Parser_AST.tm
                                                            =
                                                            FStar_Parser_AST.Var
                                                            maybe_addr_of_lid;
                                                          FStar_Parser_AST.range
                                                            = uu____44642;
                                                          FStar_Parser_AST.level
                                                            = uu____44643;_},e1,FStar_Parser_AST.Nothing
                                                        );
                                                     FStar_Parser_AST.range =
                                                       uu____44645;
                                                     FStar_Parser_AST.level =
                                                       uu____44646;_},FStar_Parser_AST.Nothing
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
                FStar_Parser_AST.range = uu____44648;
                FStar_Parser_AST.level = uu____44649;_},e1,FStar_Parser_AST.Nothing
              );
           FStar_Parser_AST.range = uu____44651;
           FStar_Parser_AST.level = uu____44652;_},e2,FStar_Parser_AST.Nothing
         )
        ->
        ((FStar_Ident.lid_equals maybe_union_lid FStar_Parser_Const.set_union)
           && (is_ref_set e1))
          && (is_ref_set e2)
    | uu____44654 -> false
  
let rec (extract_from_ref_set :
  FStar_Parser_AST.term -> FStar_Parser_AST.term Prims.list) =
  fun e  ->
    match e.FStar_Parser_AST.tm with
    | FStar_Parser_AST.Var uu____44666 -> []
    | FStar_Parser_AST.App
        ({ FStar_Parser_AST.tm = FStar_Parser_AST.Var uu____44667;
           FStar_Parser_AST.range = uu____44668;
           FStar_Parser_AST.level = uu____44669;_},{
                                                     FStar_Parser_AST.tm =
                                                       FStar_Parser_AST.App
                                                       ({
                                                          FStar_Parser_AST.tm
                                                            =
                                                            FStar_Parser_AST.Var
                                                            uu____44670;
                                                          FStar_Parser_AST.range
                                                            = uu____44671;
                                                          FStar_Parser_AST.level
                                                            = uu____44672;_},e1,FStar_Parser_AST.Nothing
                                                        );
                                                     FStar_Parser_AST.range =
                                                       uu____44674;
                                                     FStar_Parser_AST.level =
                                                       uu____44675;_},FStar_Parser_AST.Nothing
         )
        -> [e1]
    | FStar_Parser_AST.App
        ({
           FStar_Parser_AST.tm = FStar_Parser_AST.App
             ({ FStar_Parser_AST.tm = FStar_Parser_AST.Var uu____44676;
                FStar_Parser_AST.range = uu____44677;
                FStar_Parser_AST.level = uu____44678;_},e1,FStar_Parser_AST.Nothing
              );
           FStar_Parser_AST.range = uu____44680;
           FStar_Parser_AST.level = uu____44681;_},e2,FStar_Parser_AST.Nothing
         )
        ->
        let uu____44683 = extract_from_ref_set e1  in
        let uu____44686 = extract_from_ref_set e2  in
        FStar_List.append uu____44683 uu____44686
    | uu____44689 ->
        let uu____44690 =
          let uu____44692 = FStar_Parser_AST.term_to_string e  in
          FStar_Util.format1 "Not a ref set %s" uu____44692  in
        failwith uu____44690
  
let (is_general_application : FStar_Parser_AST.term -> Prims.bool) =
  fun e  ->
    let uu____44704 = (is_array e) || (is_ref_set e)  in
    Prims.op_Negation uu____44704
  
let (is_general_construction : FStar_Parser_AST.term -> Prims.bool) =
  fun e  ->
    let uu____44713 = (is_list e) || (is_lex_list e)  in
    Prims.op_Negation uu____44713
  
let (is_general_prefix_op : FStar_Ident.ident -> Prims.bool) =
  fun op  ->
    let op_starting_char =
      let uu____44724 = FStar_Ident.text_of_id op  in
      FStar_Util.char_at uu____44724 (Prims.parse_int "0")  in
    ((op_starting_char = 33) || (op_starting_char = 63)) ||
      ((op_starting_char = 126) &&
         (let uu____44734 = FStar_Ident.text_of_id op  in uu____44734 <> "~"))
  
let (head_and_args :
  FStar_Parser_AST.term ->
    (FStar_Parser_AST.term * (FStar_Parser_AST.term * FStar_Parser_AST.imp)
      Prims.list))
  =
  fun e  ->
    let rec aux e1 acc =
      match e1.FStar_Parser_AST.tm with
      | FStar_Parser_AST.App (head1,arg,imp) -> aux head1 ((arg, imp) :: acc)
      | uu____44804 -> (e1, acc)  in
    aux e []
  
type associativity =
  | Left 
  | Right 
  | NonAssoc 
let (uu___is_Left : associativity -> Prims.bool) =
  fun projectee  ->
    match projectee with | Left  -> true | uu____44824 -> false
  
let (uu___is_Right : associativity -> Prims.bool) =
  fun projectee  ->
    match projectee with | Right  -> true | uu____44835 -> false
  
let (uu___is_NonAssoc : associativity -> Prims.bool) =
  fun projectee  ->
    match projectee with | NonAssoc  -> true | uu____44846 -> false
  
type token = (FStar_Char.char,Prims.string) FStar_Util.either
type associativity_level = (associativity * token Prims.list)
let (token_to_string :
  (FStar_BaseTypes.char,Prims.string) FStar_Util.either -> Prims.string) =
  fun uu___325_44872  ->
    match uu___325_44872 with
    | FStar_Util.Inl c -> Prims.op_Hat (FStar_Util.string_of_char c) ".*"
    | FStar_Util.Inr s -> s
  
let (matches_token :
  Prims.string ->
    (FStar_Char.char,Prims.string) FStar_Util.either -> Prims.bool)
  =
  fun s  ->
    fun uu___326_44907  ->
      match uu___326_44907 with
      | FStar_Util.Inl c ->
          let uu____44920 = FStar_String.get s (Prims.parse_int "0")  in
          uu____44920 = c
      | FStar_Util.Inr s' -> s = s'
  
let matches_level :
  'Auu____44936 .
    Prims.string ->
      ('Auu____44936 * (FStar_Char.char,Prims.string) FStar_Util.either
        Prims.list) -> Prims.bool
  =
  fun s  ->
    fun uu____44960  ->
      match uu____44960 with
      | (assoc_levels,tokens) ->
          let uu____44992 = FStar_List.tryFind (matches_token s) tokens  in
          uu____44992 <> FStar_Pervasives_Native.None
  
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
  let levels_from_associativity l uu___327_45164 =
    match uu___327_45164 with
    | Left  -> (l, l, (l - (Prims.parse_int "1")))
    | Right  -> ((l - (Prims.parse_int "1")), l, l)
    | NonAssoc  ->
        ((l - (Prims.parse_int "1")), l, (l - (Prims.parse_int "1")))
     in
  FStar_List.mapi
    (fun i  ->
       fun uu____45214  ->
         match uu____45214 with
         | (assoc1,tokens) -> ((levels_from_associativity i assoc1), tokens))
    level_associativity_spec
  
let (assign_levels :
  associativity_level Prims.list ->
    Prims.string -> (Prims.int * Prims.int * Prims.int))
  =
  fun token_associativity_spec  ->
    fun s  ->
      let uu____45289 = FStar_List.tryFind (matches_level s) level_table  in
      match uu____45289 with
      | FStar_Pervasives_Native.Some (assoc_levels,uu____45341) ->
          assoc_levels
      | uu____45379 -> failwith (Prims.op_Hat "Unrecognized operator " s)
  
let max_level :
  'Auu____45412 . ('Auu____45412 * token Prims.list) Prims.list -> Prims.int
  =
  fun l  ->
    let find_level_and_max n1 level =
      let uu____45461 =
        FStar_List.tryFind
          (fun uu____45497  ->
             match uu____45497 with
             | (uu____45514,tokens) ->
                 tokens = (FStar_Pervasives_Native.snd level)) level_table
         in
      match uu____45461 with
      | FStar_Pervasives_Native.Some
          ((uu____45543,l1,uu____45545),uu____45546) -> max n1 l1
      | FStar_Pervasives_Native.None  ->
          let uu____45596 =
            let uu____45598 =
              let uu____45600 =
                FStar_List.map token_to_string
                  (FStar_Pervasives_Native.snd level)
                 in
              FStar_String.concat "," uu____45600  in
            FStar_Util.format1 "Undefined associativity level %s" uu____45598
             in
          failwith uu____45596
       in
    FStar_List.fold_left find_level_and_max (Prims.parse_int "0") l
  
let (levels : Prims.string -> (Prims.int * Prims.int * Prims.int)) =
  fun op  ->
    let uu____45635 = assign_levels level_associativity_spec op  in
    match uu____45635 with
    | (left1,mine,right1) ->
        if op = "*"
        then ((left1 - (Prims.parse_int "1")), mine, right1)
        else (left1, mine, right1)
  
let (operatorInfix0ad12 : associativity_level Prims.list) =
  [opinfix0a; opinfix0b; opinfix0c; opinfix0d; opinfix1; opinfix2] 
let (is_operatorInfix0ad12 : FStar_Ident.ident -> Prims.bool) =
  fun op  ->
    let uu____45694 =
      let uu____45697 =
        let uu____45703 = FStar_Ident.text_of_id op  in
        FStar_All.pipe_left matches_level uu____45703  in
      FStar_List.tryFind uu____45697 operatorInfix0ad12  in
    uu____45694 <> FStar_Pervasives_Native.None
  
let (is_operatorInfix34 : FStar_Ident.ident -> Prims.bool) =
  let opinfix34 = [opinfix3; opinfix4]  in
  fun op  ->
    let uu____45770 =
      let uu____45785 =
        let uu____45803 = FStar_Ident.text_of_id op  in
        FStar_All.pipe_left matches_level uu____45803  in
      FStar_List.tryFind uu____45785 opinfix34  in
    uu____45770 <> FStar_Pervasives_Native.None
  
let (handleable_args_length : FStar_Ident.ident -> Prims.int) =
  fun op  ->
    let op_s = FStar_Ident.text_of_id op  in
    let uu____45869 =
      (is_general_prefix_op op) || (FStar_List.mem op_s ["-"; "~"])  in
    if uu____45869
    then (Prims.parse_int "1")
    else
      (let uu____45882 =
         ((is_operatorInfix0ad12 op) || (is_operatorInfix34 op)) ||
           (FStar_List.mem op_s
              ["<==>"; "==>"; "\\/"; "/\\"; "="; "|>"; ":="; ".()"; ".[]"])
          in
       if uu____45882
       then (Prims.parse_int "2")
       else
         if FStar_List.mem op_s [".()<-"; ".[]<-"]
         then (Prims.parse_int "3")
         else (Prims.parse_int "0"))
  
let handleable_op :
  'Auu____45928 . FStar_Ident.ident -> 'Auu____45928 Prims.list -> Prims.bool
  =
  fun op  ->
    fun args  ->
      match FStar_List.length args with
      | _45944 when _45944 = (Prims.parse_int "0") -> true
      | _45946 when _45946 = (Prims.parse_int "1") ->
          (is_general_prefix_op op) ||
            (let uu____45948 = FStar_Ident.text_of_id op  in
             FStar_List.mem uu____45948 ["-"; "~"])
      | _45956 when _45956 = (Prims.parse_int "2") ->
          ((is_operatorInfix0ad12 op) || (is_operatorInfix34 op)) ||
            (let uu____45958 = FStar_Ident.text_of_id op  in
             FStar_List.mem uu____45958
               ["<==>"; "==>"; "\\/"; "/\\"; "="; "|>"; ":="; ".()"; ".[]"])
      | _45980 when _45980 = (Prims.parse_int "3") ->
          let uu____45981 = FStar_Ident.text_of_id op  in
          FStar_List.mem uu____45981 [".()<-"; ".[]<-"]
      | uu____45989 -> false
  
type annotation_style =
  | Binders of (Prims.int * Prims.int * Prims.bool) 
  | Arrows of (Prims.int * Prims.int) 
let (uu___is_Binders : annotation_style -> Prims.bool) =
  fun projectee  ->
    match projectee with | Binders _0 -> true | uu____46035 -> false
  
let (__proj__Binders__item___0 :
  annotation_style -> (Prims.int * Prims.int * Prims.bool)) =
  fun projectee  -> match projectee with | Binders _0 -> _0 
let (uu___is_Arrows : annotation_style -> Prims.bool) =
  fun projectee  ->
    match projectee with | Arrows _0 -> true | uu____46088 -> false
  
let (__proj__Arrows__item___0 : annotation_style -> (Prims.int * Prims.int))
  = fun projectee  -> match projectee with | Arrows _0 -> _0 
let (all_binders_annot : FStar_Parser_AST.term -> Prims.bool) =
  fun e  ->
    let is_binder_annot b =
      match b.FStar_Parser_AST.b with
      | FStar_Parser_AST.Annotated uu____46131 -> true
      | uu____46137 -> false  in
    let rec all_binders e1 l =
      match e1.FStar_Parser_AST.tm with
      | FStar_Parser_AST.Product (bs,tgt) ->
          let uu____46170 = FStar_List.for_all is_binder_annot bs  in
          if uu____46170
          then all_binders tgt (l + (FStar_List.length bs))
          else (false, (Prims.parse_int "0"))
      | uu____46185 -> (true, (l + (Prims.parse_int "1")))  in
    let uu____46190 = all_binders e (Prims.parse_int "0")  in
    match uu____46190 with
    | (b,l) -> if b && (l > (Prims.parse_int "1")) then true else false
  
type catf =
  FStar_Pprint.document -> FStar_Pprint.document -> FStar_Pprint.document
let (cat_with_colon :
  FStar_Pprint.document -> FStar_Pprint.document -> FStar_Pprint.document) =
  fun x  ->
    fun y  ->
      let uu____46229 = FStar_Pprint.op_Hat_Slash_Hat FStar_Pprint.colon y
         in
      FStar_Pprint.op_Hat_Hat x uu____46229
  
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
  'Auu____46389 .
    ('Auu____46389 -> FStar_Pprint.document) ->
      'Auu____46389 -> FStar_Range.range -> FStar_Pprint.document
  =
  fun printer  ->
    fun tm  ->
      fun tmrange  ->
        let rec comments_before_pos acc print_pos lookahead_pos =
          let uu____46431 = FStar_ST.op_Bang comment_stack  in
          match uu____46431 with
          | [] -> (acc, false)
          | (c,crange)::cs ->
              let comment =
                let uu____46502 = str c  in
                FStar_Pprint.op_Hat_Hat uu____46502 FStar_Pprint.hardline  in
              let uu____46503 = FStar_Range.range_before_pos crange print_pos
                 in
              if uu____46503
              then
                (FStar_ST.op_Colon_Equals comment_stack cs;
                 (let uu____46545 = FStar_Pprint.op_Hat_Hat acc comment  in
                  comments_before_pos uu____46545 print_pos lookahead_pos))
              else
                (let uu____46548 =
                   FStar_Range.range_before_pos crange lookahead_pos  in
                 (acc, uu____46548))
           in
        let uu____46551 =
          let uu____46557 =
            let uu____46558 = FStar_Range.start_of_range tmrange  in
            FStar_Range.end_of_line uu____46558  in
          let uu____46559 = FStar_Range.end_of_range tmrange  in
          comments_before_pos FStar_Pprint.empty uu____46557 uu____46559  in
        match uu____46551 with
        | (comments,has_lookahead) ->
            let printed_e = printer tm  in
            let comments1 =
              if has_lookahead
              then
                let pos = FStar_Range.end_of_range tmrange  in
                let uu____46568 = comments_before_pos comments pos pos  in
                FStar_Pervasives_Native.fst uu____46568
              else comments  in
            if comments1 = FStar_Pprint.empty
            then printed_e
            else
              (let uu____46580 = FStar_Pprint.op_Hat_Hat comments1 printed_e
                  in
               FStar_Pprint.group uu____46580)
  
let with_comment_sep :
  'Auu____46592 'Auu____46593 .
    ('Auu____46592 -> 'Auu____46593) ->
      'Auu____46592 ->
        FStar_Range.range -> (FStar_Pprint.document * 'Auu____46593)
  =
  fun printer  ->
    fun tm  ->
      fun tmrange  ->
        let rec comments_before_pos acc print_pos lookahead_pos =
          let uu____46639 = FStar_ST.op_Bang comment_stack  in
          match uu____46639 with
          | [] -> (acc, false)
          | (c,crange)::cs ->
              let comment = str c  in
              let uu____46710 = FStar_Range.range_before_pos crange print_pos
                 in
              if uu____46710
              then
                (FStar_ST.op_Colon_Equals comment_stack cs;
                 (let uu____46752 =
                    if acc = FStar_Pprint.empty
                    then comment
                    else
                      (let uu____46756 =
                         FStar_Pprint.op_Hat_Hat FStar_Pprint.hardline
                           comment
                          in
                       FStar_Pprint.op_Hat_Hat acc uu____46756)
                     in
                  comments_before_pos uu____46752 print_pos lookahead_pos))
              else
                (let uu____46759 =
                   FStar_Range.range_before_pos crange lookahead_pos  in
                 (acc, uu____46759))
           in
        let uu____46762 =
          let uu____46768 =
            let uu____46769 = FStar_Range.start_of_range tmrange  in
            FStar_Range.end_of_line uu____46769  in
          let uu____46770 = FStar_Range.end_of_range tmrange  in
          comments_before_pos FStar_Pprint.empty uu____46768 uu____46770  in
        match uu____46762 with
        | (comments,has_lookahead) ->
            let printed_e = printer tm  in
            let comments1 =
              if has_lookahead
              then
                let pos = FStar_Range.end_of_range tmrange  in
                let uu____46783 = comments_before_pos comments pos pos  in
                FStar_Pervasives_Native.fst uu____46783
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
                let uu____46836 = FStar_ST.op_Bang comment_stack  in
                match uu____46836 with
                | (comment,crange)::cs when
                    FStar_Range.range_before_pos crange pos ->
                    (FStar_ST.op_Colon_Equals comment_stack cs;
                     (let lnum =
                        let uu____46930 =
                          let uu____46932 =
                            let uu____46934 =
                              FStar_Range.start_of_range crange  in
                            FStar_Range.line_of_pos uu____46934  in
                          uu____46932 - lbegin  in
                        max k uu____46930  in
                      let lnum1 = min (Prims.parse_int "2") lnum  in
                      let doc2 =
                        let uu____46939 =
                          let uu____46940 =
                            FStar_Pprint.repeat lnum1 FStar_Pprint.hardline
                             in
                          let uu____46941 = str comment  in
                          FStar_Pprint.op_Hat_Hat uu____46940 uu____46941  in
                        FStar_Pprint.op_Hat_Hat doc1 uu____46939  in
                      let uu____46942 =
                        let uu____46944 = FStar_Range.end_of_range crange  in
                        FStar_Range.line_of_pos uu____46944  in
                      place_comments_until_pos (Prims.parse_int "1")
                        uu____46942 pos meta_decl doc2 true init1))
                | uu____46947 ->
                    if doc1 = FStar_Pprint.empty
                    then FStar_Pprint.empty
                    else
                      (let lnum =
                         let uu____46960 = FStar_Range.line_of_pos pos  in
                         uu____46960 - lbegin  in
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
                       let uu____47002 =
                         FStar_Pprint.repeat lnum7 FStar_Pprint.hardline  in
                       FStar_Pprint.op_Hat_Hat doc1 uu____47002)
  
let separate_map_with_comments :
  'Auu____47016 .
    FStar_Pprint.document ->
      FStar_Pprint.document ->
        ('Auu____47016 -> FStar_Pprint.document) ->
          'Auu____47016 Prims.list ->
            ('Auu____47016 -> decl_meta) -> FStar_Pprint.document
  =
  fun prefix1  ->
    fun sep  ->
      fun f  ->
        fun xs  ->
          fun extract_meta  ->
            let fold_fun uu____47075 x =
              match uu____47075 with
              | (last_line,doc1) ->
                  let meta_decl = extract_meta x  in
                  let r = meta_decl.r  in
                  let doc2 =
                    let uu____47094 = FStar_Range.start_of_range r  in
                    place_comments_until_pos (Prims.parse_int "1") last_line
                      uu____47094 meta_decl doc1 false false
                     in
                  let uu____47098 =
                    let uu____47100 = FStar_Range.end_of_range r  in
                    FStar_Range.line_of_pos uu____47100  in
                  let uu____47101 =
                    let uu____47102 =
                      let uu____47103 = f x  in
                      FStar_Pprint.op_Hat_Hat sep uu____47103  in
                    FStar_Pprint.op_Hat_Hat doc2 uu____47102  in
                  (uu____47098, uu____47101)
               in
            let uu____47105 =
              let uu____47112 = FStar_List.hd xs  in
              let uu____47113 = FStar_List.tl xs  in
              (uu____47112, uu____47113)  in
            match uu____47105 with
            | (x,xs1) ->
                let init1 =
                  let meta_decl = extract_meta x  in
                  let uu____47131 =
                    let uu____47133 = FStar_Range.end_of_range meta_decl.r
                       in
                    FStar_Range.line_of_pos uu____47133  in
                  let uu____47134 =
                    let uu____47135 = f x  in
                    FStar_Pprint.op_Hat_Hat prefix1 uu____47135  in
                  (uu____47131, uu____47134)  in
                let uu____47137 = FStar_List.fold_left fold_fun init1 xs1  in
                FStar_Pervasives_Native.snd uu____47137
  
let separate_map_with_comments_kw :
  'Auu____47164 'Auu____47165 .
    'Auu____47164 ->
      'Auu____47164 ->
        ('Auu____47164 -> 'Auu____47165 -> FStar_Pprint.document) ->
          'Auu____47165 Prims.list ->
            ('Auu____47165 -> decl_meta) -> FStar_Pprint.document
  =
  fun prefix1  ->
    fun sep  ->
      fun f  ->
        fun xs  ->
          fun extract_meta  ->
            let fold_fun uu____47229 x =
              match uu____47229 with
              | (last_line,doc1) ->
                  let meta_decl = extract_meta x  in
                  let r = meta_decl.r  in
                  let doc2 =
                    let uu____47248 = FStar_Range.start_of_range r  in
                    place_comments_until_pos (Prims.parse_int "1") last_line
                      uu____47248 meta_decl doc1 false false
                     in
                  let uu____47252 =
                    let uu____47254 = FStar_Range.end_of_range r  in
                    FStar_Range.line_of_pos uu____47254  in
                  let uu____47255 =
                    let uu____47256 = f sep x  in
                    FStar_Pprint.op_Hat_Hat doc2 uu____47256  in
                  (uu____47252, uu____47255)
               in
            let uu____47258 =
              let uu____47265 = FStar_List.hd xs  in
              let uu____47266 = FStar_List.tl xs  in
              (uu____47265, uu____47266)  in
            match uu____47258 with
            | (x,xs1) ->
                let init1 =
                  let meta_decl = extract_meta x  in
                  let uu____47284 =
                    let uu____47286 = FStar_Range.end_of_range meta_decl.r
                       in
                    FStar_Range.line_of_pos uu____47286  in
                  let uu____47287 = f prefix1 x  in
                  (uu____47284, uu____47287)  in
                let uu____47289 = FStar_List.fold_left fold_fun init1 xs1  in
                FStar_Pervasives_Native.snd uu____47289
  
let rec (p_decl : FStar_Parser_AST.decl -> FStar_Pprint.document) =
  fun d  ->
    let qualifiers =
      match ((d.FStar_Parser_AST.quals), (d.FStar_Parser_AST.d)) with
      | ((FStar_Parser_AST.Assumption )::[],FStar_Parser_AST.Assume
         (id1,uu____48275)) ->
          let uu____48278 =
            let uu____48280 =
              FStar_Util.char_at id1.FStar_Ident.idText (Prims.parse_int "0")
               in
            FStar_All.pipe_right uu____48280 FStar_Util.is_upper  in
          if uu____48278
          then
            let uu____48286 = p_qualifier FStar_Parser_AST.Assumption  in
            FStar_Pprint.op_Hat_Hat uu____48286 FStar_Pprint.space
          else p_qualifiers d.FStar_Parser_AST.quals
      | uu____48289 -> p_qualifiers d.FStar_Parser_AST.quals  in
    let uu____48296 =
      FStar_Pprint.optional (fun d1  -> p_fsdoc d1) d.FStar_Parser_AST.doc
       in
    let uu____48299 =
      let uu____48300 = p_attributes d.FStar_Parser_AST.attrs  in
      let uu____48301 =
        let uu____48302 = p_rawDecl d  in
        FStar_Pprint.op_Hat_Hat qualifiers uu____48302  in
      FStar_Pprint.op_Hat_Hat uu____48300 uu____48301  in
    FStar_Pprint.op_Hat_Hat uu____48296 uu____48299

and (p_attributes : FStar_Parser_AST.attributes_ -> FStar_Pprint.document) =
  fun attrs  ->
    match attrs with
    | [] -> FStar_Pprint.empty
    | uu____48304 ->
        let uu____48305 =
          let uu____48306 = str "@ "  in
          let uu____48308 =
            let uu____48309 =
              let uu____48310 =
                let uu____48311 =
                  let uu____48312 = FStar_List.map p_atomicTerm attrs  in
                  FStar_Pprint.flow break1 uu____48312  in
                FStar_Pprint.op_Hat_Hat uu____48311 FStar_Pprint.rbracket  in
              FStar_Pprint.align uu____48310  in
            FStar_Pprint.op_Hat_Hat uu____48309 FStar_Pprint.hardline  in
          FStar_Pprint.op_Hat_Hat uu____48306 uu____48308  in
        FStar_Pprint.op_Hat_Hat FStar_Pprint.lbracket uu____48305

and (p_fsdoc : FStar_Parser_AST.fsdoc -> FStar_Pprint.document) =
  fun uu____48315  ->
    match uu____48315 with
    | (doc1,kwd_args) ->
        let kwd_args_doc =
          match kwd_args with
          | [] -> FStar_Pprint.empty
          | kwd_args1 ->
              let process_kwd_arg uu____48363 =
                match uu____48363 with
                | (kwd,arg) ->
                    let uu____48376 = str "@"  in
                    let uu____48378 =
                      let uu____48379 = str kwd  in
                      let uu____48380 =
                        let uu____48381 = str arg  in
                        FStar_Pprint.op_Hat_Hat FStar_Pprint.space
                          uu____48381
                         in
                      FStar_Pprint.op_Hat_Hat uu____48379 uu____48380  in
                    FStar_Pprint.op_Hat_Hat uu____48376 uu____48378
                 in
              let uu____48382 =
                FStar_Pprint.separate_map FStar_Pprint.hardline
                  process_kwd_arg kwd_args1
                 in
              FStar_Pprint.op_Hat_Hat uu____48382 FStar_Pprint.hardline
           in
        let uu____48389 =
          let uu____48390 =
            let uu____48391 =
              let uu____48392 = str doc1  in
              let uu____48393 =
                let uu____48394 =
                  let uu____48395 =
                    FStar_Pprint.op_Hat_Hat FStar_Pprint.rparen
                      FStar_Pprint.hardline
                     in
                  FStar_Pprint.op_Hat_Hat FStar_Pprint.star uu____48395  in
                FStar_Pprint.op_Hat_Hat kwd_args_doc uu____48394  in
              FStar_Pprint.op_Hat_Hat uu____48392 uu____48393  in
            FStar_Pprint.op_Hat_Hat FStar_Pprint.star uu____48391  in
          FStar_Pprint.op_Hat_Hat FStar_Pprint.star uu____48390  in
        FStar_Pprint.op_Hat_Hat FStar_Pprint.lparen uu____48389

and (p_justSig : FStar_Parser_AST.decl -> FStar_Pprint.document) =
  fun d  ->
    match d.FStar_Parser_AST.d with
    | FStar_Parser_AST.Val (lid,t) ->
        let uu____48399 =
          let uu____48400 = str "val"  in
          let uu____48402 =
            let uu____48403 =
              let uu____48404 = p_lident lid  in
              let uu____48405 =
                FStar_Pprint.op_Hat_Hat FStar_Pprint.space FStar_Pprint.colon
                 in
              FStar_Pprint.op_Hat_Hat uu____48404 uu____48405  in
            FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____48403  in
          FStar_Pprint.op_Hat_Hat uu____48400 uu____48402  in
        let uu____48406 = p_typ false false t  in
        FStar_Pprint.op_Hat_Hat uu____48399 uu____48406
    | FStar_Parser_AST.TopLevelLet (uu____48409,lbs) ->
        FStar_Pprint.separate_map FStar_Pprint.hardline
          (fun lb  ->
             let uu____48434 =
               let uu____48435 = str "let"  in p_letlhs uu____48435 lb false
                in
             FStar_Pprint.group uu____48434) lbs
    | uu____48438 -> FStar_Pprint.empty

and (p_list :
  (FStar_Ident.ident -> FStar_Pprint.document) ->
    FStar_Pprint.document ->
      FStar_Ident.ident Prims.list -> FStar_Pprint.document)
  =
  fun f  ->
    fun sep  ->
      fun l  ->
        let rec p_list' uu___328_48453 =
          match uu___328_48453 with
          | [] -> FStar_Pprint.empty
          | x::[] -> f x
          | x::xs ->
              let uu____48461 = f x  in
              let uu____48462 =
                let uu____48463 = p_list' xs  in
                FStar_Pprint.op_Hat_Hat sep uu____48463  in
              FStar_Pprint.op_Hat_Hat uu____48461 uu____48462
           in
        let uu____48464 = str "["  in
        let uu____48466 =
          let uu____48467 = p_list' l  in
          let uu____48468 = str "]"  in
          FStar_Pprint.op_Hat_Hat uu____48467 uu____48468  in
        FStar_Pprint.op_Hat_Hat uu____48464 uu____48466

and (p_rawDecl : FStar_Parser_AST.decl -> FStar_Pprint.document) =
  fun d  ->
    match d.FStar_Parser_AST.d with
    | FStar_Parser_AST.Open uid ->
        let uu____48472 =
          let uu____48473 = str "open"  in
          let uu____48475 = p_quident uid  in
          FStar_Pprint.op_Hat_Slash_Hat uu____48473 uu____48475  in
        FStar_Pprint.group uu____48472
    | FStar_Parser_AST.Include uid ->
        let uu____48477 =
          let uu____48478 = str "include"  in
          let uu____48480 = p_quident uid  in
          FStar_Pprint.op_Hat_Slash_Hat uu____48478 uu____48480  in
        FStar_Pprint.group uu____48477
    | FStar_Parser_AST.Friend uid ->
        let uu____48482 =
          let uu____48483 = str "friend"  in
          let uu____48485 = p_quident uid  in
          FStar_Pprint.op_Hat_Slash_Hat uu____48483 uu____48485  in
        FStar_Pprint.group uu____48482
    | FStar_Parser_AST.ModuleAbbrev (uid1,uid2) ->
        let uu____48488 =
          let uu____48489 = str "module"  in
          let uu____48491 =
            let uu____48492 =
              let uu____48493 = p_uident uid1  in
              let uu____48494 =
                FStar_Pprint.op_Hat_Hat FStar_Pprint.space
                  FStar_Pprint.equals
                 in
              FStar_Pprint.op_Hat_Hat uu____48493 uu____48494  in
            FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____48492  in
          FStar_Pprint.op_Hat_Hat uu____48489 uu____48491  in
        let uu____48495 = p_quident uid2  in
        op_Hat_Slash_Plus_Hat uu____48488 uu____48495
    | FStar_Parser_AST.TopLevelModule uid ->
        let uu____48497 =
          let uu____48498 = str "module"  in
          let uu____48500 =
            let uu____48501 = p_quident uid  in
            FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____48501  in
          FStar_Pprint.op_Hat_Hat uu____48498 uu____48500  in
        FStar_Pprint.group uu____48497
    | FStar_Parser_AST.Tycon
        (true
         ,uu____48502,(FStar_Parser_AST.TyconAbbrev
                       (uid,tpars,FStar_Pervasives_Native.None ,t),FStar_Pervasives_Native.None
                       )::[])
        ->
        let effect_prefix_doc =
          let uu____48539 = str "effect"  in
          let uu____48541 =
            let uu____48542 = p_uident uid  in
            FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____48542  in
          FStar_Pprint.op_Hat_Hat uu____48539 uu____48541  in
        let uu____48543 =
          let uu____48544 = p_typars tpars  in
          FStar_Pprint.surround (Prims.parse_int "2") (Prims.parse_int "1")
            effect_prefix_doc uu____48544 FStar_Pprint.equals
           in
        let uu____48547 = p_typ false false t  in
        op_Hat_Slash_Plus_Hat uu____48543 uu____48547
    | FStar_Parser_AST.Tycon (false ,tc,tcdefs) ->
        let s = if tc then str "class" else str "type"  in
        let uu____48578 =
          let uu____48579 = FStar_List.hd tcdefs  in
          p_fsdocTypeDeclPairs s uu____48579  in
        let uu____48592 =
          let uu____48593 = FStar_List.tl tcdefs  in
          FStar_All.pipe_left
            (FStar_Pprint.concat_map
               (fun x  ->
                  let uu____48631 =
                    let uu____48632 = str "and"  in
                    p_fsdocTypeDeclPairs uu____48632 x  in
                  FStar_Pprint.op_Hat_Hat break1 uu____48631)) uu____48593
           in
        FStar_Pprint.op_Hat_Hat uu____48578 uu____48592
    | FStar_Parser_AST.TopLevelLet (q,lbs) ->
        let let_doc =
          let uu____48649 = str "let"  in
          let uu____48651 = p_letqualifier q  in
          FStar_Pprint.op_Hat_Hat uu____48649 uu____48651  in
        let uu____48652 = str "and"  in
        separate_map_with_comments_kw let_doc uu____48652 p_letbinding lbs
          (fun uu____48662  ->
             match uu____48662 with
             | (p,t) ->
                 let uu____48669 =
                   FStar_Range.union_ranges p.FStar_Parser_AST.prange
                     t.FStar_Parser_AST.range
                    in
                 {
                   r = uu____48669;
                   has_qs = false;
                   has_attrs = false;
                   has_fsdoc = (FStar_Util.is_some d.FStar_Parser_AST.doc);
                   is_fsdoc = false
                 })
    | FStar_Parser_AST.Val (lid,t) ->
        let uu____48675 =
          let uu____48676 = str "val"  in
          let uu____48678 =
            let uu____48679 =
              let uu____48680 = p_lident lid  in
              let uu____48681 = sig_as_binders_if_possible t false  in
              FStar_Pprint.op_Hat_Hat uu____48680 uu____48681  in
            FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____48679  in
          FStar_Pprint.op_Hat_Hat uu____48676 uu____48678  in
        FStar_All.pipe_left FStar_Pprint.group uu____48675
    | FStar_Parser_AST.Assume (id1,t) ->
        let decl_keyword =
          let uu____48686 =
            let uu____48688 =
              FStar_Util.char_at id1.FStar_Ident.idText (Prims.parse_int "0")
               in
            FStar_All.pipe_right uu____48688 FStar_Util.is_upper  in
          if uu____48686
          then FStar_Pprint.empty
          else
            (let uu____48696 = str "val"  in
             FStar_Pprint.op_Hat_Hat uu____48696 FStar_Pprint.space)
           in
        let uu____48698 =
          let uu____48699 = p_ident id1  in
          let uu____48700 =
            let uu____48701 =
              let uu____48702 =
                let uu____48703 = p_typ false false t  in
                FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____48703  in
              FStar_Pprint.op_Hat_Hat FStar_Pprint.colon uu____48702  in
            FStar_Pprint.group uu____48701  in
          FStar_Pprint.op_Hat_Hat uu____48699 uu____48700  in
        FStar_Pprint.op_Hat_Hat decl_keyword uu____48698
    | FStar_Parser_AST.Exception (uid,t_opt) ->
        let uu____48712 = str "exception"  in
        let uu____48714 =
          let uu____48715 =
            let uu____48716 = p_uident uid  in
            let uu____48717 =
              FStar_Pprint.optional
                (fun t  ->
                   let uu____48721 =
                     let uu____48722 = str "of"  in
                     let uu____48724 = p_typ false false t  in
                     op_Hat_Slash_Plus_Hat uu____48722 uu____48724  in
                   FStar_Pprint.op_Hat_Hat break1 uu____48721) t_opt
               in
            FStar_Pprint.op_Hat_Hat uu____48716 uu____48717  in
          FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____48715  in
        FStar_Pprint.op_Hat_Hat uu____48712 uu____48714
    | FStar_Parser_AST.NewEffect ne ->
        let uu____48728 = str "new_effect"  in
        let uu____48730 =
          let uu____48731 = p_newEffect ne  in
          FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____48731  in
        FStar_Pprint.op_Hat_Hat uu____48728 uu____48730
    | FStar_Parser_AST.SubEffect se ->
        let uu____48733 = str "sub_effect"  in
        let uu____48735 =
          let uu____48736 = p_subEffect se  in
          FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____48736  in
        FStar_Pprint.op_Hat_Hat uu____48733 uu____48735
    | FStar_Parser_AST.Pragma p -> p_pragma p
    | FStar_Parser_AST.Fsdoc doc1 -> p_fsdoc doc1
    | FStar_Parser_AST.Main uu____48739 ->
        failwith "*Main declaration* : Is that really still in use ??"
    | FStar_Parser_AST.Tycon (true ,uu____48741,uu____48742) ->
        failwith
          "Effect abbreviation is expected to be defined by an abbreviation"
    | FStar_Parser_AST.Splice (ids,t) ->
        let uu____48770 = str "%splice"  in
        let uu____48772 =
          let uu____48773 =
            let uu____48774 = str ";"  in p_list p_uident uu____48774 ids  in
          let uu____48776 =
            let uu____48777 = p_term false false t  in
            FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____48777  in
          FStar_Pprint.op_Hat_Hat uu____48773 uu____48776  in
        FStar_Pprint.op_Hat_Hat uu____48770 uu____48772

and (p_pragma : FStar_Parser_AST.pragma -> FStar_Pprint.document) =
  fun uu___329_48780  ->
    match uu___329_48780 with
    | FStar_Parser_AST.SetOptions s ->
        let uu____48783 = str "#set-options"  in
        let uu____48785 =
          let uu____48786 =
            let uu____48787 = str s  in FStar_Pprint.dquotes uu____48787  in
          FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____48786  in
        FStar_Pprint.op_Hat_Hat uu____48783 uu____48785
    | FStar_Parser_AST.ResetOptions s_opt ->
        let uu____48792 = str "#reset-options"  in
        let uu____48794 =
          FStar_Pprint.optional
            (fun s  ->
               let uu____48800 =
                 let uu____48801 = str s  in FStar_Pprint.dquotes uu____48801
                  in
               FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____48800) s_opt
           in
        FStar_Pprint.op_Hat_Hat uu____48792 uu____48794
    | FStar_Parser_AST.PushOptions s_opt ->
        let uu____48806 = str "#push-options"  in
        let uu____48808 =
          FStar_Pprint.optional
            (fun s  ->
               let uu____48814 =
                 let uu____48815 = str s  in FStar_Pprint.dquotes uu____48815
                  in
               FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____48814) s_opt
           in
        FStar_Pprint.op_Hat_Hat uu____48806 uu____48808
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
    fun uu____48846  ->
      match uu____48846 with
      | (typedecl,fsdoc_opt) ->
          let uu____48859 = p_typeDecl (kw, fsdoc_opt) typedecl  in
          (match uu____48859 with
           | (comm,decl,body,pre) ->
               if comm = FStar_Pprint.empty
               then
                 let uu____48884 = pre body  in
                 FStar_Pprint.op_Hat_Hat decl uu____48884
               else
                 (let uu____48887 =
                    let uu____48888 =
                      let uu____48889 =
                        let uu____48890 = pre body  in
                        FStar_Pprint.op_Hat_Slash_Hat uu____48890 comm  in
                      FStar_Pprint.op_Hat_Hat decl uu____48889  in
                    let uu____48891 =
                      let uu____48892 =
                        let uu____48893 =
                          let uu____48894 =
                            let uu____48895 =
                              FStar_Pprint.op_Hat_Hat FStar_Pprint.hardline
                                body
                               in
                            FStar_Pprint.op_Hat_Hat comm uu____48895  in
                          FStar_Pprint.op_Hat_Hat FStar_Pprint.hardline
                            uu____48894
                           in
                        FStar_Pprint.nest (Prims.parse_int "2") uu____48893
                         in
                      FStar_Pprint.op_Hat_Hat decl uu____48892  in
                    FStar_Pprint.ifflat uu____48888 uu____48891  in
                  FStar_All.pipe_left FStar_Pprint.group uu____48887))

and (p_typeDecl :
  (FStar_Pprint.document * FStar_Parser_AST.fsdoc
    FStar_Pervasives_Native.option) ->
    FStar_Parser_AST.tycon ->
      (FStar_Pprint.document * FStar_Pprint.document * FStar_Pprint.document
        * (FStar_Pprint.document -> FStar_Pprint.document)))
  =
  fun pre  ->
    fun uu___330_48898  ->
      match uu___330_48898 with
      | FStar_Parser_AST.TyconAbstract (lid,bs,typ_opt) ->
          let uu____48927 = p_typeDeclPrefix pre false lid bs typ_opt  in
          (FStar_Pprint.empty, uu____48927, FStar_Pprint.empty,
            FStar_Pervasives.id)
      | FStar_Parser_AST.TyconAbbrev (lid,bs,typ_opt,t) ->
          let uu____48944 = p_typ_sep false false t  in
          (match uu____48944 with
           | (comm,doc1) ->
               let uu____48964 = p_typeDeclPrefix pre true lid bs typ_opt  in
               (comm, uu____48964, doc1, jump2))
      | FStar_Parser_AST.TyconRecord (lid,bs,typ_opt,record_field_decls) ->
          let p_recordFieldAndComments ps uu____49020 =
            match uu____49020 with
            | (lid1,t,doc_opt) ->
                let uu____49037 =
                  let uu____49042 =
                    FStar_Range.extend_to_end_of_line
                      t.FStar_Parser_AST.range
                     in
                  with_comment_sep (p_recordFieldDecl ps) (lid1, t, doc_opt)
                    uu____49042
                   in
                (match uu____49037 with
                 | (comm,field) ->
                     let sep =
                       if ps then FStar_Pprint.semi else FStar_Pprint.empty
                        in
                     inline_comment_or_above comm field sep)
             in
          let p_fields =
            let uu____49060 =
              separate_map_last FStar_Pprint.hardline
                p_recordFieldAndComments record_field_decls
               in
            braces_with_nesting uu____49060  in
          let uu____49069 = p_typeDeclPrefix pre true lid bs typ_opt  in
          (FStar_Pprint.empty, uu____49069, p_fields,
            ((fun d  -> FStar_Pprint.op_Hat_Hat FStar_Pprint.space d)))
      | FStar_Parser_AST.TyconVariant (lid,bs,typ_opt,ct_decls) ->
          let p_constructorBranchAndComments uu____49136 =
            match uu____49136 with
            | (uid,t_opt,doc_opt,use_of) ->
                let range =
                  let uu____49165 =
                    let uu____49166 =
                      FStar_Util.map_opt t_opt
                        (fun t  -> t.FStar_Parser_AST.range)
                       in
                    FStar_Util.dflt uid.FStar_Ident.idRange uu____49166  in
                  FStar_Range.extend_to_end_of_line uu____49165  in
                let uu____49171 =
                  with_comment_sep p_constructorBranch
                    (uid, t_opt, doc_opt, use_of) range
                   in
                (match uu____49171 with
                 | (comm,ctor) ->
                     inline_comment_or_above comm ctor FStar_Pprint.empty)
             in
          let datacon_doc =
            FStar_Pprint.separate_map FStar_Pprint.hardline
              p_constructorBranchAndComments ct_decls
             in
          let uu____49210 = p_typeDeclPrefix pre true lid bs typ_opt  in
          (FStar_Pprint.empty, uu____49210, datacon_doc, jump2)

and (p_typeDeclPrefix :
  (FStar_Pprint.document * FStar_Parser_AST.fsdoc
    FStar_Pervasives_Native.option) ->
    Prims.bool ->
      FStar_Ident.ident ->
        FStar_Parser_AST.binder Prims.list ->
          FStar_Parser_AST.knd FStar_Pervasives_Native.option ->
            FStar_Pprint.document)
  =
  fun uu____49215  ->
    fun eq1  ->
      fun lid  ->
        fun bs  ->
          fun typ_opt  ->
            match uu____49215 with
            | (kw,fsdoc_opt) ->
                let maybe_with_fsdoc cont =
                  let lid_doc = p_ident lid  in
                  let kw_lid =
                    let uu____49250 =
                      FStar_Pprint.op_Hat_Slash_Hat kw lid_doc  in
                    FStar_Pprint.group uu____49250  in
                  match fsdoc_opt with
                  | FStar_Pervasives_Native.None  -> cont kw_lid
                  | FStar_Pervasives_Native.Some fsdoc ->
                      let uu____49252 =
                        let uu____49255 =
                          let uu____49258 = p_fsdoc fsdoc  in
                          let uu____49259 =
                            let uu____49262 = cont lid_doc  in [uu____49262]
                             in
                          uu____49258 :: uu____49259  in
                        kw :: uu____49255  in
                      FStar_Pprint.separate FStar_Pprint.hardline uu____49252
                   in
                let typ =
                  let maybe_eq =
                    if eq1 then FStar_Pprint.equals else FStar_Pprint.empty
                     in
                  match typ_opt with
                  | FStar_Pervasives_Native.None  -> maybe_eq
                  | FStar_Pervasives_Native.Some t ->
                      let uu____49269 =
                        let uu____49270 =
                          let uu____49271 = p_typ false false t  in
                          FStar_Pprint.op_Hat_Slash_Hat uu____49271 maybe_eq
                           in
                        FStar_Pprint.op_Hat_Hat FStar_Pprint.space
                          uu____49270
                         in
                      FStar_Pprint.op_Hat_Hat FStar_Pprint.colon uu____49269
                   in
                if bs = []
                then maybe_with_fsdoc (fun n1  -> prefix2 n1 typ)
                else
                  (let binders = p_binders_list true bs  in
                   maybe_with_fsdoc
                     (fun n1  ->
                        let uu____49291 =
                          let uu____49292 = FStar_Pprint.flow break1 binders
                             in
                          prefix2 n1 uu____49292  in
                        prefix2 uu____49291 typ))

and (p_recordFieldDecl :
  Prims.bool ->
    (FStar_Ident.ident * FStar_Parser_AST.term * FStar_Parser_AST.fsdoc
      FStar_Pervasives_Native.option) -> FStar_Pprint.document)
  =
  fun ps  ->
    fun uu____49294  ->
      match uu____49294 with
      | (lid,t,doc_opt) ->
          let uu____49311 =
            let uu____49312 = FStar_Pprint.optional p_fsdoc doc_opt  in
            let uu____49313 =
              let uu____49314 = p_lident lid  in
              let uu____49315 =
                let uu____49316 = p_typ ps false t  in
                FStar_Pprint.op_Hat_Hat FStar_Pprint.colon uu____49316  in
              FStar_Pprint.op_Hat_Hat uu____49314 uu____49315  in
            FStar_Pprint.op_Hat_Hat uu____49312 uu____49313  in
          FStar_Pprint.group uu____49311

and (p_constructorBranch :
  (FStar_Ident.ident * FStar_Parser_AST.term FStar_Pervasives_Native.option *
    FStar_Parser_AST.fsdoc FStar_Pervasives_Native.option * Prims.bool) ->
    FStar_Pprint.document)
  =
  fun uu____49318  ->
    match uu____49318 with
    | (uid,t_opt,doc_opt,use_of) ->
        let sep = if use_of then str "of" else FStar_Pprint.colon  in
        let uid_doc =
          let uu____49352 =
            let uu____49353 =
              let uu____49354 = p_uident uid  in
              FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____49354  in
            FStar_Pprint.op_Hat_Hat FStar_Pprint.bar uu____49353  in
          FStar_Pprint.group uu____49352  in
        let uu____49355 = FStar_Pprint.optional p_fsdoc doc_opt  in
        let uu____49356 =
          default_or_map uid_doc
            (fun t  ->
               let uu____49360 =
                 let uu____49361 =
                   let uu____49362 =
                     let uu____49363 =
                       let uu____49364 = p_typ false false t  in
                       FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____49364
                        in
                     FStar_Pprint.op_Hat_Hat sep uu____49363  in
                   FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____49362  in
                 FStar_Pprint.op_Hat_Hat uid_doc uu____49361  in
               FStar_Pprint.group uu____49360) t_opt
           in
        FStar_Pprint.op_Hat_Hat uu____49355 uu____49356

and (p_letlhs :
  FStar_Pprint.document ->
    (FStar_Parser_AST.pattern * FStar_Parser_AST.term) ->
      Prims.bool -> FStar_Pprint.document)
  =
  fun kw  ->
    fun uu____49368  ->
      fun inner_let  ->
        match uu____49368 with
        | (pat,uu____49376) ->
            let uu____49377 =
              match pat.FStar_Parser_AST.pat with
              | FStar_Parser_AST.PatAscribed
                  (pat1,(t,FStar_Pervasives_Native.None )) ->
                  (pat1,
                    (FStar_Pervasives_Native.Some (t, FStar_Pprint.empty)))
              | FStar_Parser_AST.PatAscribed
                  (pat1,(t,FStar_Pervasives_Native.Some tac)) ->
                  let uu____49429 =
                    let uu____49436 =
                      let uu____49441 =
                        let uu____49442 =
                          let uu____49443 =
                            let uu____49444 = str "by"  in
                            let uu____49446 =
                              let uu____49447 = p_atomicTerm tac  in
                              FStar_Pprint.op_Hat_Hat FStar_Pprint.space
                                uu____49447
                               in
                            FStar_Pprint.op_Hat_Hat uu____49444 uu____49446
                             in
                          FStar_Pprint.op_Hat_Hat FStar_Pprint.space
                            uu____49443
                           in
                        FStar_Pprint.group uu____49442  in
                      (t, uu____49441)  in
                    FStar_Pervasives_Native.Some uu____49436  in
                  (pat1, uu____49429)
              | uu____49458 -> (pat, FStar_Pervasives_Native.None)  in
            (match uu____49377 with
             | (pat1,ascr) ->
                 (match pat1.FStar_Parser_AST.pat with
                  | FStar_Parser_AST.PatApp
                      ({
                         FStar_Parser_AST.pat = FStar_Parser_AST.PatVar
                           (lid,uu____49484);
                         FStar_Parser_AST.prange = uu____49485;_},pats)
                      ->
                      let ascr_doc =
                        match ascr with
                        | FStar_Pervasives_Native.Some (t,tac) ->
                            let uu____49502 =
                              sig_as_binders_if_possible t true  in
                            FStar_Pprint.op_Hat_Hat uu____49502 tac
                        | FStar_Pervasives_Native.None  -> FStar_Pprint.empty
                         in
                      let uu____49508 =
                        if inner_let
                        then
                          let uu____49522 = pats_as_binders_if_possible pats
                             in
                          match uu____49522 with
                          | (bs,style) ->
                              ((FStar_List.append bs [ascr_doc]), style)
                        else
                          (let uu____49545 = pats_as_binders_if_possible pats
                              in
                           match uu____49545 with
                           | (bs,style) ->
                               ((FStar_List.append bs [ascr_doc]), style))
                         in
                      (match uu____49508 with
                       | (terms,style) ->
                           let uu____49572 =
                             let uu____49573 =
                               let uu____49574 =
                                 let uu____49575 = p_lident lid  in
                                 let uu____49576 =
                                   format_sig style terms true true  in
                                 FStar_Pprint.op_Hat_Hat uu____49575
                                   uu____49576
                                  in
                               FStar_Pprint.op_Hat_Hat FStar_Pprint.space
                                 uu____49574
                                in
                             FStar_Pprint.op_Hat_Hat kw uu____49573  in
                           FStar_All.pipe_left FStar_Pprint.group uu____49572)
                  | uu____49579 ->
                      let ascr_doc =
                        match ascr with
                        | FStar_Pervasives_Native.Some (t,tac) ->
                            let uu____49587 =
                              let uu____49588 =
                                let uu____49589 =
                                  p_typ_top
                                    (Arrows
                                       ((Prims.parse_int "2"),
                                         (Prims.parse_int "2"))) false false
                                    t
                                   in
                                FStar_Pprint.op_Hat_Hat FStar_Pprint.colon
                                  uu____49589
                                 in
                              FStar_Pprint.group uu____49588  in
                            FStar_Pprint.op_Hat_Hat uu____49587 tac
                        | FStar_Pervasives_Native.None  -> FStar_Pprint.empty
                         in
                      let uu____49600 =
                        let uu____49601 =
                          let uu____49602 =
                            let uu____49603 = p_tuplePattern pat1  in
                            FStar_Pprint.op_Hat_Slash_Hat kw uu____49603  in
                          FStar_Pprint.group uu____49602  in
                        FStar_Pprint.op_Hat_Hat uu____49601 ascr_doc  in
                      FStar_Pprint.group uu____49600))

and (p_letbinding :
  FStar_Pprint.document ->
    (FStar_Parser_AST.pattern * FStar_Parser_AST.term) ->
      FStar_Pprint.document)
  =
  fun kw  ->
    fun uu____49605  ->
      match uu____49605 with
      | (pat,e) ->
          let doc_pat = p_letlhs kw (pat, e) false  in
          let uu____49614 = p_term_sep false false e  in
          (match uu____49614 with
           | (comm,doc_expr) ->
               let doc_expr1 =
                 inline_comment_or_above comm doc_expr FStar_Pprint.empty  in
               let uu____49624 =
                 let uu____49625 =
                   FStar_Pprint.op_Hat_Slash_Hat FStar_Pprint.equals
                     doc_expr1
                    in
                 FStar_Pprint.op_Hat_Slash_Hat doc_pat uu____49625  in
               let uu____49626 =
                 let uu____49627 =
                   let uu____49628 =
                     let uu____49629 =
                       let uu____49630 = jump2 doc_expr1  in
                       FStar_Pprint.op_Hat_Hat FStar_Pprint.equals
                         uu____49630
                        in
                     FStar_Pprint.group uu____49629  in
                   FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____49628  in
                 FStar_Pprint.op_Hat_Hat doc_pat uu____49627  in
               FStar_Pprint.ifflat uu____49624 uu____49626)

and (p_newEffect : FStar_Parser_AST.effect_decl -> FStar_Pprint.document) =
  fun uu___331_49631  ->
    match uu___331_49631 with
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
        let uu____49656 = p_uident uid  in
        let uu____49657 = p_binders true bs  in
        let uu____49659 =
          let uu____49660 = p_simpleTerm false false t  in
          prefix2 FStar_Pprint.equals uu____49660  in
        surround_maybe_empty (Prims.parse_int "2") (Prims.parse_int "1")
          uu____49656 uu____49657 uu____49659

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
          let uu____49675 =
            let uu____49676 =
              let uu____49677 =
                let uu____49678 = p_uident uid  in
                let uu____49679 = p_binders true bs  in
                let uu____49681 =
                  let uu____49682 = p_typ false false t  in
                  prefix2 FStar_Pprint.colon uu____49682  in
                surround_maybe_empty (Prims.parse_int "2")
                  (Prims.parse_int "1") uu____49678 uu____49679 uu____49681
                 in
              FStar_Pprint.group uu____49677  in
            let uu____49687 =
              let uu____49688 = str "with"  in
              let uu____49690 =
                let uu____49691 =
                  let uu____49692 =
                    let uu____49693 =
                      let uu____49694 =
                        let uu____49695 =
                          FStar_Pprint.op_Hat_Hat FStar_Pprint.semi
                            FStar_Pprint.space
                           in
                        FStar_Pprint.op_Hat_Hat FStar_Pprint.hardline
                          uu____49695
                         in
                      separate_map_last uu____49694 p_effectDecl eff_decls
                       in
                    FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____49693
                     in
                  FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____49692  in
                FStar_Pprint.op_Hat_Hat FStar_Pprint.hardline uu____49691  in
              FStar_Pprint.op_Hat_Hat uu____49688 uu____49690  in
            FStar_Pprint.op_Hat_Slash_Hat uu____49676 uu____49687  in
          braces_with_nesting uu____49675

and (p_effectDecl :
  Prims.bool -> FStar_Parser_AST.decl -> FStar_Pprint.document) =
  fun ps  ->
    fun d  ->
      match d.FStar_Parser_AST.d with
      | FStar_Parser_AST.Tycon
          (false
           ,uu____49699,(FStar_Parser_AST.TyconAbbrev
                         (lid,[],FStar_Pervasives_Native.None ,e),FStar_Pervasives_Native.None
                         )::[])
          ->
          let uu____49732 =
            let uu____49733 = p_lident lid  in
            let uu____49734 =
              FStar_Pprint.op_Hat_Hat FStar_Pprint.space FStar_Pprint.equals
               in
            FStar_Pprint.op_Hat_Hat uu____49733 uu____49734  in
          let uu____49735 = p_simpleTerm ps false e  in
          prefix2 uu____49732 uu____49735
      | uu____49737 ->
          let uu____49738 =
            let uu____49740 = FStar_Parser_AST.decl_to_string d  in
            FStar_Util.format1
              "Not a declaration of an effect member... or at least I hope so : %s"
              uu____49740
             in
          failwith uu____49738

and (p_subEffect : FStar_Parser_AST.lift -> FStar_Pprint.document) =
  fun lift  ->
    let lift_op_doc =
      let lifts =
        match lift.FStar_Parser_AST.lift_op with
        | FStar_Parser_AST.NonReifiableLift t -> [("lift_wp", t)]
        | FStar_Parser_AST.ReifiableLift (t1,t2) ->
            [("lift_wp", t1); ("lift", t2)]
        | FStar_Parser_AST.LiftForFree t -> [("lift", t)]  in
      let p_lift ps uu____49823 =
        match uu____49823 with
        | (kwd,t) ->
            let uu____49834 =
              let uu____49835 = str kwd  in
              let uu____49836 =
                FStar_Pprint.op_Hat_Hat FStar_Pprint.space
                  FStar_Pprint.equals
                 in
              FStar_Pprint.op_Hat_Hat uu____49835 uu____49836  in
            let uu____49837 = p_simpleTerm ps false t  in
            prefix2 uu____49834 uu____49837
         in
      separate_break_map_last FStar_Pprint.semi p_lift lifts  in
    let uu____49844 =
      let uu____49845 =
        let uu____49846 = p_quident lift.FStar_Parser_AST.msource  in
        let uu____49847 =
          let uu____49848 = str "~>"  in
          FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____49848  in
        FStar_Pprint.op_Hat_Hat uu____49846 uu____49847  in
      let uu____49850 = p_quident lift.FStar_Parser_AST.mdest  in
      prefix2 uu____49845 uu____49850  in
    let uu____49851 =
      let uu____49852 = braces_with_nesting lift_op_doc  in
      FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____49852  in
    FStar_Pprint.op_Hat_Hat uu____49844 uu____49851

and (p_qualifier : FStar_Parser_AST.qualifier -> FStar_Pprint.document) =
  fun uu___332_49853  ->
    match uu___332_49853 with
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
        let uu____49873 = p_qualifier q  in
        FStar_Pprint.op_Hat_Hat uu____49873 FStar_Pprint.hardline
    | uu____49874 ->
        let uu____49875 =
          let uu____49876 = FStar_List.map p_qualifier qs  in
          FStar_Pprint.flow break1 uu____49876  in
        FStar_Pprint.op_Hat_Hat uu____49875 FStar_Pprint.hardline

and (p_letqualifier :
  FStar_Parser_AST.let_qualifier -> FStar_Pprint.document) =
  fun uu___333_49879  ->
    match uu___333_49879 with
    | FStar_Parser_AST.Rec  ->
        let uu____49880 = str "rec"  in
        FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____49880
    | FStar_Parser_AST.NoLetQualifier  -> FStar_Pprint.empty

and (p_aqual : FStar_Parser_AST.arg_qualifier -> FStar_Pprint.document) =
  fun uu___334_49882  ->
    match uu___334_49882 with
    | FStar_Parser_AST.Implicit  -> str "#"
    | FStar_Parser_AST.Equality  -> str "$"
    | FStar_Parser_AST.Meta t ->
        let t1 =
          match t.FStar_Parser_AST.tm with
          | FStar_Parser_AST.Abs (uu____49887,e) -> e
          | uu____49893 ->
              FStar_Parser_AST.mk_term
                (FStar_Parser_AST.App
                   (t,
                     (FStar_Parser_AST.unit_const t.FStar_Parser_AST.range),
                     FStar_Parser_AST.Nothing)) t.FStar_Parser_AST.range
                FStar_Parser_AST.Expr
           in
        let uu____49894 = str "#["  in
        let uu____49896 =
          let uu____49897 = p_term false false t1  in
          let uu____49900 =
            let uu____49901 = str "]"  in
            FStar_Pprint.op_Hat_Hat uu____49901 break1  in
          FStar_Pprint.op_Hat_Hat uu____49897 uu____49900  in
        FStar_Pprint.op_Hat_Hat uu____49894 uu____49896

and (p_disjunctivePattern :
  FStar_Parser_AST.pattern -> FStar_Pprint.document) =
  fun p  ->
    match p.FStar_Parser_AST.pat with
    | FStar_Parser_AST.PatOr pats ->
        let uu____49907 =
          let uu____49908 =
            let uu____49909 =
              FStar_Pprint.op_Hat_Hat FStar_Pprint.bar FStar_Pprint.space  in
            FStar_Pprint.op_Hat_Hat break1 uu____49909  in
          FStar_Pprint.separate_map uu____49908 p_tuplePattern pats  in
        FStar_Pprint.group uu____49907
    | uu____49910 -> p_tuplePattern p

and (p_tuplePattern : FStar_Parser_AST.pattern -> FStar_Pprint.document) =
  fun p  ->
    match p.FStar_Parser_AST.pat with
    | FStar_Parser_AST.PatTuple (pats,false ) ->
        let uu____49919 =
          let uu____49920 = FStar_Pprint.op_Hat_Hat FStar_Pprint.comma break1
             in
          FStar_Pprint.separate_map uu____49920 p_constructorPattern pats  in
        FStar_Pprint.group uu____49919
    | uu____49921 -> p_constructorPattern p

and (p_constructorPattern :
  FStar_Parser_AST.pattern -> FStar_Pprint.document) =
  fun p  ->
    match p.FStar_Parser_AST.pat with
    | FStar_Parser_AST.PatApp
        ({ FStar_Parser_AST.pat = FStar_Parser_AST.PatName maybe_cons_lid;
           FStar_Parser_AST.prange = uu____49924;_},hd1::tl1::[])
        when
        FStar_Ident.lid_equals maybe_cons_lid FStar_Parser_Const.cons_lid ->
        let uu____49929 =
          FStar_Pprint.op_Hat_Hat FStar_Pprint.colon FStar_Pprint.colon  in
        let uu____49930 = p_constructorPattern hd1  in
        let uu____49931 = p_constructorPattern tl1  in
        infix0 uu____49929 uu____49930 uu____49931
    | FStar_Parser_AST.PatApp
        ({ FStar_Parser_AST.pat = FStar_Parser_AST.PatName uid;
           FStar_Parser_AST.prange = uu____49933;_},pats)
        ->
        let uu____49939 = p_quident uid  in
        let uu____49940 =
          FStar_Pprint.separate_map break1 p_atomicPattern pats  in
        prefix2 uu____49939 uu____49940
    | uu____49941 -> p_atomicPattern p

and (p_atomicPattern : FStar_Parser_AST.pattern -> FStar_Pprint.document) =
  fun p  ->
    match p.FStar_Parser_AST.pat with
    | FStar_Parser_AST.PatAscribed (pat,(t,FStar_Pervasives_Native.None )) ->
        (match ((pat.FStar_Parser_AST.pat), (t.FStar_Parser_AST.tm)) with
         | (FStar_Parser_AST.PatVar (lid,aqual),FStar_Parser_AST.Refine
            ({ FStar_Parser_AST.b = FStar_Parser_AST.Annotated (lid',t1);
               FStar_Parser_AST.brange = uu____49957;
               FStar_Parser_AST.blevel = uu____49958;
               FStar_Parser_AST.aqual = uu____49959;_},phi))
             when lid.FStar_Ident.idText = lid'.FStar_Ident.idText ->
             let uu____49968 =
               let uu____49969 = p_ident lid  in
               p_refinement aqual uu____49969 t1 phi  in
             soft_parens_with_nesting uu____49968
         | (FStar_Parser_AST.PatWild aqual,FStar_Parser_AST.Refine
            ({ FStar_Parser_AST.b = FStar_Parser_AST.NoName t1;
               FStar_Parser_AST.brange = uu____49972;
               FStar_Parser_AST.blevel = uu____49973;
               FStar_Parser_AST.aqual = uu____49974;_},phi))
             ->
             let uu____49980 =
               p_refinement aqual FStar_Pprint.underscore t1 phi  in
             soft_parens_with_nesting uu____49980
         | uu____49981 ->
             let uu____49986 =
               let uu____49987 = p_tuplePattern pat  in
               let uu____49988 =
                 let uu____49989 = p_tmEqNoRefinement t  in
                 FStar_Pprint.op_Hat_Slash_Hat FStar_Pprint.colon uu____49989
                  in
               FStar_Pprint.op_Hat_Hat uu____49987 uu____49988  in
             soft_parens_with_nesting uu____49986)
    | FStar_Parser_AST.PatList pats ->
        let uu____49993 =
          separate_break_map FStar_Pprint.semi p_tuplePattern pats  in
        FStar_Pprint.surround (Prims.parse_int "2") (Prims.parse_int "0")
          FStar_Pprint.lbracket uu____49993 FStar_Pprint.rbracket
    | FStar_Parser_AST.PatRecord pats ->
        let p_recordFieldPat uu____50012 =
          match uu____50012 with
          | (lid,pat) ->
              let uu____50019 = p_qlident lid  in
              let uu____50020 = p_tuplePattern pat  in
              infix2 FStar_Pprint.equals uu____50019 uu____50020
           in
        let uu____50021 =
          separate_break_map FStar_Pprint.semi p_recordFieldPat pats  in
        soft_braces_with_nesting uu____50021
    | FStar_Parser_AST.PatTuple (pats,true ) ->
        let uu____50033 =
          FStar_Pprint.op_Hat_Hat FStar_Pprint.lparen FStar_Pprint.bar  in
        let uu____50034 =
          separate_break_map FStar_Pprint.comma p_constructorPattern pats  in
        let uu____50035 =
          FStar_Pprint.op_Hat_Hat FStar_Pprint.bar FStar_Pprint.rparen  in
        FStar_Pprint.surround (Prims.parse_int "2") (Prims.parse_int "1")
          uu____50033 uu____50034 uu____50035
    | FStar_Parser_AST.PatTvar (tv,arg_qualifier_opt) -> p_tvar tv
    | FStar_Parser_AST.PatOp op ->
        let uu____50046 =
          let uu____50047 =
            let uu____50048 =
              let uu____50049 = FStar_Ident.text_of_id op  in str uu____50049
               in
            let uu____50051 =
              FStar_Pprint.op_Hat_Hat FStar_Pprint.space FStar_Pprint.rparen
               in
            FStar_Pprint.op_Hat_Hat uu____50048 uu____50051  in
          FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____50047  in
        FStar_Pprint.op_Hat_Hat FStar_Pprint.lparen uu____50046
    | FStar_Parser_AST.PatWild aqual ->
        let uu____50055 = FStar_Pprint.optional p_aqual aqual  in
        FStar_Pprint.op_Hat_Hat uu____50055 FStar_Pprint.underscore
    | FStar_Parser_AST.PatConst c -> p_constant c
    | FStar_Parser_AST.PatVar (lid,aqual) ->
        let uu____50063 = FStar_Pprint.optional p_aqual aqual  in
        let uu____50064 = p_lident lid  in
        FStar_Pprint.op_Hat_Hat uu____50063 uu____50064
    | FStar_Parser_AST.PatName uid -> p_quident uid
    | FStar_Parser_AST.PatOr uu____50066 -> failwith "Inner or pattern !"
    | FStar_Parser_AST.PatApp
        ({ FStar_Parser_AST.pat = FStar_Parser_AST.PatName uu____50070;
           FStar_Parser_AST.prange = uu____50071;_},uu____50072)
        ->
        let uu____50077 = p_tuplePattern p  in
        soft_parens_with_nesting uu____50077
    | FStar_Parser_AST.PatTuple (uu____50078,false ) ->
        let uu____50085 = p_tuplePattern p  in
        soft_parens_with_nesting uu____50085
    | uu____50086 ->
        let uu____50087 =
          let uu____50089 = FStar_Parser_AST.pat_to_string p  in
          FStar_Util.format1 "Invalid pattern %s" uu____50089  in
        failwith uu____50087

and (is_typ_tuple : FStar_Parser_AST.term -> Prims.bool) =
  fun e  ->
    match e.FStar_Parser_AST.tm with
    | FStar_Parser_AST.Op
        ({ FStar_Ident.idText = "*"; FStar_Ident.idRange = uu____50094;_},uu____50095)
        -> true
    | uu____50102 -> false

and (is_meta_qualifier :
  FStar_Parser_AST.arg_qualifier FStar_Pervasives_Native.option -> Prims.bool)
  =
  fun aq  ->
    match aq with
    | FStar_Pervasives_Native.Some (FStar_Parser_AST.Meta uu____50108) ->
        true
    | uu____50110 -> false

and (p_binder :
  Prims.bool -> FStar_Parser_AST.binder -> FStar_Pprint.document) =
  fun is_atomic  ->
    fun b  ->
      let uu____50117 = p_binder' is_atomic b  in
      match uu____50117 with
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
          let uu____50156 =
            let uu____50157 =
              FStar_Pprint.optional p_aqual b.FStar_Parser_AST.aqual  in
            let uu____50158 = p_lident lid  in
            FStar_Pprint.op_Hat_Hat uu____50157 uu____50158  in
          (uu____50156, FStar_Pervasives_Native.None, cat_with_colon)
      | FStar_Parser_AST.TVariable lid ->
          let uu____50164 = p_lident lid  in
          (uu____50164, FStar_Pervasives_Native.None, cat_with_colon)
      | FStar_Parser_AST.Annotated (lid,t) ->
          let uu____50171 =
            match t.FStar_Parser_AST.tm with
            | FStar_Parser_AST.Refine
                ({ FStar_Parser_AST.b = FStar_Parser_AST.Annotated (lid',t1);
                   FStar_Parser_AST.brange = uu____50182;
                   FStar_Parser_AST.blevel = uu____50183;
                   FStar_Parser_AST.aqual = uu____50184;_},phi)
                when lid.FStar_Ident.idText = lid'.FStar_Ident.idText ->
                let uu____50189 = p_lident lid  in
                p_refinement' b.FStar_Parser_AST.aqual uu____50189 t1 phi
            | uu____50190 ->
                let t' =
                  let uu____50192 = is_typ_tuple t  in
                  if uu____50192
                  then
                    let uu____50195 = p_tmFormula t  in
                    soft_parens_with_nesting uu____50195
                  else p_tmFormula t  in
                let uu____50198 =
                  let uu____50199 =
                    FStar_Pprint.optional p_aqual b.FStar_Parser_AST.aqual
                     in
                  let uu____50200 = p_lident lid  in
                  FStar_Pprint.op_Hat_Hat uu____50199 uu____50200  in
                (uu____50198, t')
             in
          (match uu____50171 with
           | (b',t') ->
               let catf =
                 let uu____50218 =
                   is_atomic || (is_meta_qualifier b.FStar_Parser_AST.aqual)
                    in
                 if uu____50218
                 then
                   fun x  ->
                     fun y  ->
                       let uu____50225 =
                         let uu____50226 =
                           let uu____50227 = cat_with_colon x y  in
                           FStar_Pprint.op_Hat_Hat uu____50227
                             FStar_Pprint.rparen
                            in
                         FStar_Pprint.op_Hat_Hat FStar_Pprint.lparen
                           uu____50226
                          in
                       FStar_Pprint.group uu____50225
                 else
                   (fun x  ->
                      fun y  ->
                        let uu____50232 = cat_with_colon x y  in
                        FStar_Pprint.group uu____50232)
                  in
               (b', (FStar_Pervasives_Native.Some t'), catf))
      | FStar_Parser_AST.TAnnotated uu____50241 ->
          failwith "Is this still used ?"
      | FStar_Parser_AST.NoName t ->
          (match t.FStar_Parser_AST.tm with
           | FStar_Parser_AST.Refine
               ({ FStar_Parser_AST.b = FStar_Parser_AST.NoName t1;
                  FStar_Parser_AST.brange = uu____50269;
                  FStar_Parser_AST.blevel = uu____50270;
                  FStar_Parser_AST.aqual = uu____50271;_},phi)
               ->
               let uu____50275 =
                 p_refinement' b.FStar_Parser_AST.aqual
                   FStar_Pprint.underscore t1 phi
                  in
               (match uu____50275 with
                | (b',t') ->
                    (b', (FStar_Pervasives_Native.Some t'), cat_with_colon))
           | uu____50296 ->
               if is_atomic
               then
                 let uu____50308 = p_atomicTerm t  in
                 (uu____50308, FStar_Pervasives_Native.None, cat_with_colon)
               else
                 (let uu____50315 = p_appTerm t  in
                  (uu____50315, FStar_Pervasives_Native.None, cat_with_colon)))

and (p_refinement :
  FStar_Parser_AST.arg_qualifier FStar_Pervasives_Native.option ->
    FStar_Pprint.document ->
      FStar_Parser_AST.term -> FStar_Parser_AST.term -> FStar_Pprint.document)
  =
  fun aqual_opt  ->
    fun binder  ->
      fun t  ->
        fun phi  ->
          let uu____50326 = p_refinement' aqual_opt binder t phi  in
          match uu____50326 with | (b,typ) -> cat_with_colon b typ

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
            | FStar_Parser_AST.Construct uu____50342 -> false
            | FStar_Parser_AST.App uu____50354 -> false
            | FStar_Parser_AST.Op uu____50362 -> false
            | uu____50370 -> true  in
          let uu____50372 = p_noSeqTerm false false phi  in
          match uu____50372 with
          | (comm,phi1) ->
              let phi2 =
                if comm = FStar_Pprint.empty
                then phi1
                else
                  (let uu____50389 =
                     FStar_Pprint.op_Hat_Hat FStar_Pprint.hardline phi1  in
                   FStar_Pprint.op_Hat_Hat comm uu____50389)
                 in
              let jump_break =
                if is_t_atomic
                then (Prims.parse_int "0")
                else (Prims.parse_int "1")  in
              let uu____50398 =
                let uu____50399 = FStar_Pprint.optional p_aqual aqual_opt  in
                FStar_Pprint.op_Hat_Hat uu____50399 binder  in
              let uu____50400 =
                let uu____50401 = p_appTerm t  in
                let uu____50402 =
                  let uu____50403 =
                    let uu____50404 =
                      let uu____50405 = soft_braces_with_nesting_tight phi2
                         in
                      let uu____50406 = soft_braces_with_nesting phi2  in
                      FStar_Pprint.ifflat uu____50405 uu____50406  in
                    FStar_Pprint.group uu____50404  in
                  FStar_Pprint.jump (Prims.parse_int "2") jump_break
                    uu____50403
                   in
                FStar_Pprint.op_Hat_Hat uu____50401 uu____50402  in
              (uu____50398, uu____50400)

and (p_binders_list :
  Prims.bool ->
    FStar_Parser_AST.binder Prims.list -> FStar_Pprint.document Prims.list)
  = fun is_atomic  -> fun bs  -> FStar_List.map (p_binder is_atomic) bs

and (p_binders :
  Prims.bool -> FStar_Parser_AST.binder Prims.list -> FStar_Pprint.document)
  =
  fun is_atomic  ->
    fun bs  ->
      let uu____50420 = p_binders_list is_atomic bs  in
      separate_or_flow break1 uu____50420

and (text_of_id_or_underscore : FStar_Ident.ident -> FStar_Pprint.document) =
  fun lid  ->
    let uu____50424 =
      (FStar_Util.starts_with lid.FStar_Ident.idText
         FStar_Ident.reserved_prefix)
        &&
        (let uu____50427 = FStar_Options.print_real_names ()  in
         Prims.op_Negation uu____50427)
       in
    if uu____50424
    then FStar_Pprint.underscore
    else (let uu____50432 = FStar_Ident.text_of_id lid  in str uu____50432)

and (text_of_lid_or_underscore : FStar_Ident.lident -> FStar_Pprint.document)
  =
  fun lid  ->
    let uu____50435 =
      (FStar_Util.starts_with (lid.FStar_Ident.ident).FStar_Ident.idText
         FStar_Ident.reserved_prefix)
        &&
        (let uu____50438 = FStar_Options.print_real_names ()  in
         Prims.op_Negation uu____50438)
       in
    if uu____50435
    then FStar_Pprint.underscore
    else (let uu____50443 = FStar_Ident.text_of_lid lid  in str uu____50443)

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
          let uu____50464 = FStar_Pprint.op_Hat_Hat doc1 sep  in
          FStar_Pprint.group uu____50464
        else
          (let uu____50467 =
             let uu____50468 =
               let uu____50469 =
                 let uu____50470 =
                   let uu____50471 = FStar_Pprint.op_Hat_Hat break1 comm  in
                   FStar_Pprint.op_Hat_Hat sep uu____50471  in
                 FStar_Pprint.op_Hat_Hat doc1 uu____50470  in
               FStar_Pprint.group uu____50469  in
             let uu____50472 =
               let uu____50473 =
                 let uu____50474 = FStar_Pprint.op_Hat_Hat doc1 sep  in
                 FStar_Pprint.op_Hat_Hat FStar_Pprint.hardline uu____50474
                  in
               FStar_Pprint.op_Hat_Hat comm uu____50473  in
             FStar_Pprint.ifflat uu____50468 uu____50472  in
           FStar_All.pipe_left FStar_Pprint.group uu____50467)

and (p_term :
  Prims.bool -> Prims.bool -> FStar_Parser_AST.term -> FStar_Pprint.document)
  =
  fun ps  ->
    fun pb  ->
      fun e  ->
        match e.FStar_Parser_AST.tm with
        | FStar_Parser_AST.Seq (e1,e2) ->
            let uu____50482 = p_noSeqTerm true false e1  in
            (match uu____50482 with
             | (comm,t1) ->
                 let uu____50491 =
                   inline_comment_or_above comm t1 FStar_Pprint.semi  in
                 let uu____50492 =
                   let uu____50493 = p_term ps pb e2  in
                   FStar_Pprint.op_Hat_Hat FStar_Pprint.hardline uu____50493
                    in
                 FStar_Pprint.op_Hat_Hat uu____50491 uu____50492)
        | FStar_Parser_AST.Bind (x,e1,e2) ->
            let uu____50497 =
              let uu____50498 =
                let uu____50499 =
                  let uu____50500 = p_lident x  in
                  let uu____50501 =
                    FStar_Pprint.op_Hat_Hat FStar_Pprint.space
                      FStar_Pprint.long_left_arrow
                     in
                  FStar_Pprint.op_Hat_Hat uu____50500 uu____50501  in
                let uu____50502 =
                  let uu____50503 = p_noSeqTermAndComment true false e1  in
                  let uu____50506 =
                    FStar_Pprint.op_Hat_Hat FStar_Pprint.space
                      FStar_Pprint.semi
                     in
                  FStar_Pprint.op_Hat_Hat uu____50503 uu____50506  in
                op_Hat_Slash_Plus_Hat uu____50499 uu____50502  in
              FStar_Pprint.group uu____50498  in
            let uu____50507 = p_term ps pb e2  in
            FStar_Pprint.op_Hat_Slash_Hat uu____50497 uu____50507
        | uu____50508 ->
            let uu____50509 = p_noSeqTermAndComment ps pb e  in
            FStar_Pprint.group uu____50509

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
            let uu____50521 = p_noSeqTerm true false e1  in
            (match uu____50521 with
             | (comm,t1) ->
                 let uu____50534 =
                   let uu____50535 =
                     let uu____50536 =
                       FStar_Pprint.op_Hat_Hat t1 FStar_Pprint.semi  in
                     FStar_Pprint.group uu____50536  in
                   let uu____50537 =
                     let uu____50538 = p_term ps pb e2  in
                     FStar_Pprint.op_Hat_Hat FStar_Pprint.hardline
                       uu____50538
                      in
                   FStar_Pprint.op_Hat_Hat uu____50535 uu____50537  in
                 (comm, uu____50534))
        | FStar_Parser_AST.Bind (x,e1,e2) ->
            let uu____50542 =
              let uu____50543 =
                let uu____50544 =
                  let uu____50545 =
                    let uu____50546 = p_lident x  in
                    let uu____50547 =
                      FStar_Pprint.op_Hat_Hat FStar_Pprint.space
                        FStar_Pprint.long_left_arrow
                       in
                    FStar_Pprint.op_Hat_Hat uu____50546 uu____50547  in
                  let uu____50548 =
                    let uu____50549 = p_noSeqTermAndComment true false e1  in
                    let uu____50552 =
                      FStar_Pprint.op_Hat_Hat FStar_Pprint.space
                        FStar_Pprint.semi
                       in
                    FStar_Pprint.op_Hat_Hat uu____50549 uu____50552  in
                  op_Hat_Slash_Plus_Hat uu____50545 uu____50548  in
                FStar_Pprint.group uu____50544  in
              let uu____50553 = p_term ps pb e2  in
              FStar_Pprint.op_Hat_Slash_Hat uu____50543 uu____50553  in
            (FStar_Pprint.empty, uu____50542)
        | uu____50554 -> p_noSeqTerm ps pb e

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
            let uu____50574 =
              let uu____50575 = p_tmIff e1  in
              let uu____50576 =
                let uu____50577 =
                  let uu____50578 = p_typ ps pb t  in
                  FStar_Pprint.op_Hat_Slash_Hat FStar_Pprint.colon
                    uu____50578
                   in
                FStar_Pprint.op_Hat_Hat FStar_Pprint.langle uu____50577  in
              FStar_Pprint.op_Hat_Slash_Hat uu____50575 uu____50576  in
            FStar_Pprint.group uu____50574
        | FStar_Parser_AST.Ascribed (e1,t,FStar_Pervasives_Native.Some tac)
            ->
            let uu____50584 =
              let uu____50585 = p_tmIff e1  in
              let uu____50586 =
                let uu____50587 =
                  let uu____50588 =
                    let uu____50589 = p_typ false false t  in
                    let uu____50592 =
                      let uu____50593 = str "by"  in
                      let uu____50595 = p_typ ps pb tac  in
                      FStar_Pprint.op_Hat_Slash_Hat uu____50593 uu____50595
                       in
                    FStar_Pprint.op_Hat_Slash_Hat uu____50589 uu____50592  in
                  FStar_Pprint.op_Hat_Slash_Hat FStar_Pprint.colon
                    uu____50588
                   in
                FStar_Pprint.op_Hat_Hat FStar_Pprint.langle uu____50587  in
              FStar_Pprint.op_Hat_Slash_Hat uu____50585 uu____50586  in
            FStar_Pprint.group uu____50584
        | FStar_Parser_AST.Op
            ({ FStar_Ident.idText = ".()<-";
               FStar_Ident.idRange = uu____50596;_},e1::e2::e3::[])
            ->
            let uu____50603 =
              let uu____50604 =
                let uu____50605 =
                  let uu____50606 = p_atomicTermNotQUident e1  in
                  let uu____50607 =
                    let uu____50608 =
                      let uu____50609 =
                        let uu____50610 = p_term false false e2  in
                        soft_parens_with_nesting uu____50610  in
                      let uu____50613 =
                        FStar_Pprint.op_Hat_Hat FStar_Pprint.space
                          FStar_Pprint.larrow
                         in
                      FStar_Pprint.op_Hat_Hat uu____50609 uu____50613  in
                    FStar_Pprint.op_Hat_Hat FStar_Pprint.dot uu____50608  in
                  FStar_Pprint.op_Hat_Hat uu____50606 uu____50607  in
                FStar_Pprint.group uu____50605  in
              let uu____50614 =
                let uu____50615 = p_noSeqTermAndComment ps pb e3  in
                jump2 uu____50615  in
              FStar_Pprint.op_Hat_Hat uu____50604 uu____50614  in
            FStar_Pprint.group uu____50603
        | FStar_Parser_AST.Op
            ({ FStar_Ident.idText = ".[]<-";
               FStar_Ident.idRange = uu____50616;_},e1::e2::e3::[])
            ->
            let uu____50623 =
              let uu____50624 =
                let uu____50625 =
                  let uu____50626 = p_atomicTermNotQUident e1  in
                  let uu____50627 =
                    let uu____50628 =
                      let uu____50629 =
                        let uu____50630 = p_term false false e2  in
                        soft_brackets_with_nesting uu____50630  in
                      let uu____50633 =
                        FStar_Pprint.op_Hat_Hat FStar_Pprint.space
                          FStar_Pprint.larrow
                         in
                      FStar_Pprint.op_Hat_Hat uu____50629 uu____50633  in
                    FStar_Pprint.op_Hat_Hat FStar_Pprint.dot uu____50628  in
                  FStar_Pprint.op_Hat_Hat uu____50626 uu____50627  in
                FStar_Pprint.group uu____50625  in
              let uu____50634 =
                let uu____50635 = p_noSeqTermAndComment ps pb e3  in
                jump2 uu____50635  in
              FStar_Pprint.op_Hat_Hat uu____50624 uu____50634  in
            FStar_Pprint.group uu____50623
        | FStar_Parser_AST.Requires (e1,wtf) ->
            let uu____50645 =
              let uu____50646 = str "requires"  in
              let uu____50648 = p_typ ps pb e1  in
              FStar_Pprint.op_Hat_Slash_Hat uu____50646 uu____50648  in
            FStar_Pprint.group uu____50645
        | FStar_Parser_AST.Ensures (e1,wtf) ->
            let uu____50658 =
              let uu____50659 = str "ensures"  in
              let uu____50661 = p_typ ps pb e1  in
              FStar_Pprint.op_Hat_Slash_Hat uu____50659 uu____50661  in
            FStar_Pprint.group uu____50658
        | FStar_Parser_AST.Attributes es ->
            let uu____50665 =
              let uu____50666 = str "attributes"  in
              let uu____50668 =
                FStar_Pprint.separate_map break1 p_atomicTerm es  in
              FStar_Pprint.op_Hat_Slash_Hat uu____50666 uu____50668  in
            FStar_Pprint.group uu____50665
        | FStar_Parser_AST.If (e1,e2,e3) ->
            if is_unit e3
            then
              let uu____50673 =
                let uu____50674 =
                  let uu____50675 = str "if"  in
                  let uu____50677 = p_noSeqTermAndComment false false e1  in
                  op_Hat_Slash_Plus_Hat uu____50675 uu____50677  in
                let uu____50680 =
                  let uu____50681 = str "then"  in
                  let uu____50683 = p_noSeqTermAndComment ps pb e2  in
                  op_Hat_Slash_Plus_Hat uu____50681 uu____50683  in
                FStar_Pprint.op_Hat_Slash_Hat uu____50674 uu____50680  in
              FStar_Pprint.group uu____50673
            else
              (let e2_doc =
                 match e2.FStar_Parser_AST.tm with
                 | FStar_Parser_AST.If (uu____50687,uu____50688,e31) when
                     is_unit e31 ->
                     let uu____50690 = p_noSeqTermAndComment false false e2
                        in
                     soft_parens_with_nesting uu____50690
                 | uu____50693 -> p_noSeqTermAndComment false false e2  in
               let uu____50696 =
                 let uu____50697 =
                   let uu____50698 = str "if"  in
                   let uu____50700 = p_noSeqTermAndComment false false e1  in
                   op_Hat_Slash_Plus_Hat uu____50698 uu____50700  in
                 let uu____50703 =
                   let uu____50704 =
                     let uu____50705 = str "then"  in
                     op_Hat_Slash_Plus_Hat uu____50705 e2_doc  in
                   let uu____50707 =
                     let uu____50708 = str "else"  in
                     let uu____50710 = p_noSeqTermAndComment ps pb e3  in
                     op_Hat_Slash_Plus_Hat uu____50708 uu____50710  in
                   FStar_Pprint.op_Hat_Slash_Hat uu____50704 uu____50707  in
                 FStar_Pprint.op_Hat_Slash_Hat uu____50697 uu____50703  in
               FStar_Pprint.group uu____50696)
        | FStar_Parser_AST.TryWith (e1,branches) ->
            let uu____50733 =
              let uu____50734 =
                let uu____50735 =
                  let uu____50736 = str "try"  in
                  let uu____50738 = p_noSeqTermAndComment false false e1  in
                  prefix2 uu____50736 uu____50738  in
                let uu____50741 =
                  let uu____50742 = str "with"  in
                  let uu____50744 =
                    separate_map_last FStar_Pprint.hardline p_patternBranch
                      branches
                     in
                  FStar_Pprint.op_Hat_Slash_Hat uu____50742 uu____50744  in
                FStar_Pprint.op_Hat_Slash_Hat uu____50735 uu____50741  in
              FStar_Pprint.group uu____50734  in
            let uu____50753 = paren_if (ps || pb)  in uu____50753 uu____50733
        | FStar_Parser_AST.Match (e1,branches) ->
            let uu____50780 =
              let uu____50781 =
                let uu____50782 =
                  let uu____50783 = str "match"  in
                  let uu____50785 = p_noSeqTermAndComment false false e1  in
                  let uu____50788 = str "with"  in
                  FStar_Pprint.surround (Prims.parse_int "2")
                    (Prims.parse_int "1") uu____50783 uu____50785 uu____50788
                   in
                let uu____50792 =
                  separate_map_last FStar_Pprint.hardline p_patternBranch
                    branches
                   in
                FStar_Pprint.op_Hat_Slash_Hat uu____50782 uu____50792  in
              FStar_Pprint.group uu____50781  in
            let uu____50801 = paren_if (ps || pb)  in uu____50801 uu____50780
        | FStar_Parser_AST.LetOpen (uid,e1) ->
            let uu____50808 =
              let uu____50809 =
                let uu____50810 =
                  let uu____50811 = str "let open"  in
                  let uu____50813 = p_quident uid  in
                  let uu____50814 = str "in"  in
                  FStar_Pprint.surround (Prims.parse_int "2")
                    (Prims.parse_int "1") uu____50811 uu____50813 uu____50814
                   in
                let uu____50818 = p_term false pb e1  in
                FStar_Pprint.op_Hat_Slash_Hat uu____50810 uu____50818  in
              FStar_Pprint.group uu____50809  in
            let uu____50820 = paren_if ps  in uu____50820 uu____50808
        | FStar_Parser_AST.Let (q,lbs,e1) ->
            let p_lb q1 uu____50885 is_last =
              match uu____50885 with
              | (a,(pat,e2)) ->
                  let attrs = p_attrs_opt a  in
                  let doc_let_or_and =
                    match q1 with
                    | FStar_Pervasives_Native.Some (FStar_Parser_AST.Rec ) ->
                        let uu____50919 =
                          let uu____50920 = str "let"  in
                          let uu____50922 = str "rec"  in
                          FStar_Pprint.op_Hat_Slash_Hat uu____50920
                            uu____50922
                           in
                        FStar_Pprint.group uu____50919
                    | FStar_Pervasives_Native.Some
                        (FStar_Parser_AST.NoLetQualifier ) -> str "let"
                    | uu____50925 -> str "and"  in
                  let doc_pat = p_letlhs doc_let_or_and (pat, e2) true  in
                  let uu____50931 = p_term_sep false false e2  in
                  (match uu____50931 with
                   | (comm,doc_expr) ->
                       let doc_expr1 =
                         inline_comment_or_above comm doc_expr
                           FStar_Pprint.empty
                          in
                       let uu____50941 =
                         if is_last
                         then
                           let uu____50943 =
                             FStar_Pprint.flow break1
                               [doc_pat; FStar_Pprint.equals]
                              in
                           let uu____50944 = str "in"  in
                           FStar_Pprint.surround (Prims.parse_int "2")
                             (Prims.parse_int "1") uu____50943 doc_expr1
                             uu____50944
                         else
                           (let uu____50950 =
                              FStar_Pprint.flow break1
                                [doc_pat; FStar_Pprint.equals; doc_expr1]
                               in
                            FStar_Pprint.hang (Prims.parse_int "2")
                              uu____50950)
                          in
                       FStar_Pprint.op_Hat_Hat attrs uu____50941)
               in
            let l = FStar_List.length lbs  in
            let lbs_docs =
              FStar_List.mapi
                (fun i  ->
                   fun lb  ->
                     if i = (Prims.parse_int "0")
                     then
                       let uu____51001 =
                         p_lb (FStar_Pervasives_Native.Some q) lb
                           (i = (l - (Prims.parse_int "1")))
                          in
                       FStar_Pprint.group uu____51001
                     else
                       (let uu____51012 =
                          p_lb FStar_Pervasives_Native.None lb
                            (i = (l - (Prims.parse_int "1")))
                           in
                        FStar_Pprint.group uu____51012)) lbs
               in
            let lbs_doc =
              let uu____51022 = FStar_Pprint.separate break1 lbs_docs  in
              FStar_Pprint.group uu____51022  in
            let uu____51023 =
              let uu____51024 =
                let uu____51025 =
                  let uu____51026 = p_term false pb e1  in
                  FStar_Pprint.op_Hat_Hat FStar_Pprint.hardline uu____51026
                   in
                FStar_Pprint.op_Hat_Hat lbs_doc uu____51025  in
              FStar_Pprint.group uu____51024  in
            let uu____51028 = paren_if ps  in uu____51028 uu____51023
        | FStar_Parser_AST.Abs
            ({ FStar_Parser_AST.pat = FStar_Parser_AST.PatVar (x,typ_opt);
               FStar_Parser_AST.prange = uu____51035;_}::[],{
                                                              FStar_Parser_AST.tm
                                                                =
                                                                FStar_Parser_AST.Match
                                                                (maybe_x,branches);
                                                              FStar_Parser_AST.range
                                                                = uu____51038;
                                                              FStar_Parser_AST.level
                                                                = uu____51039;_})
            when matches_var maybe_x x ->
            let uu____51066 =
              let uu____51067 =
                let uu____51068 = str "function"  in
                let uu____51070 =
                  separate_map_last FStar_Pprint.hardline p_patternBranch
                    branches
                   in
                FStar_Pprint.op_Hat_Slash_Hat uu____51068 uu____51070  in
              FStar_Pprint.group uu____51067  in
            let uu____51079 = paren_if (ps || pb)  in uu____51079 uu____51066
        | FStar_Parser_AST.Quote (e1,FStar_Parser_AST.Dynamic ) ->
            let uu____51085 =
              let uu____51086 = str "quote"  in
              let uu____51088 = p_noSeqTermAndComment ps pb e1  in
              FStar_Pprint.op_Hat_Slash_Hat uu____51086 uu____51088  in
            FStar_Pprint.group uu____51085
        | FStar_Parser_AST.Quote (e1,FStar_Parser_AST.Static ) ->
            let uu____51090 =
              let uu____51091 = str "`"  in
              let uu____51093 = p_noSeqTermAndComment ps pb e1  in
              FStar_Pprint.op_Hat_Hat uu____51091 uu____51093  in
            FStar_Pprint.group uu____51090
        | FStar_Parser_AST.VQuote e1 ->
            let uu____51095 =
              let uu____51096 = str "`%"  in
              let uu____51098 = p_noSeqTermAndComment ps pb e1  in
              FStar_Pprint.op_Hat_Hat uu____51096 uu____51098  in
            FStar_Pprint.group uu____51095
        | FStar_Parser_AST.Antiquote
            {
              FStar_Parser_AST.tm = FStar_Parser_AST.Quote
                (e1,FStar_Parser_AST.Dynamic );
              FStar_Parser_AST.range = uu____51100;
              FStar_Parser_AST.level = uu____51101;_}
            ->
            let uu____51102 =
              let uu____51103 = str "`@"  in
              let uu____51105 = p_noSeqTermAndComment ps pb e1  in
              FStar_Pprint.op_Hat_Hat uu____51103 uu____51105  in
            FStar_Pprint.group uu____51102
        | FStar_Parser_AST.Antiquote e1 ->
            let uu____51107 =
              let uu____51108 = str "`#"  in
              let uu____51110 = p_noSeqTermAndComment ps pb e1  in
              FStar_Pprint.op_Hat_Hat uu____51108 uu____51110  in
            FStar_Pprint.group uu____51107
        | FStar_Parser_AST.CalcProof (rel,init1,steps) ->
            let head1 =
              let uu____51119 = str "calc"  in
              let uu____51121 =
                let uu____51122 =
                  let uu____51123 = p_noSeqTermAndComment false false rel  in
                  let uu____51126 =
                    FStar_Pprint.op_Hat_Hat FStar_Pprint.space
                      FStar_Pprint.lbrace
                     in
                  FStar_Pprint.op_Hat_Hat uu____51123 uu____51126  in
                FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____51122  in
              FStar_Pprint.op_Hat_Hat uu____51119 uu____51121  in
            let bot = FStar_Pprint.rbrace  in
            let uu____51128 =
              FStar_Pprint.op_Hat_Hat FStar_Pprint.hardline bot  in
            let uu____51129 =
              let uu____51130 =
                let uu____51131 =
                  let uu____51132 = p_noSeqTermAndComment false false init1
                     in
                  let uu____51135 =
                    let uu____51136 = str ";"  in
                    let uu____51138 =
                      let uu____51139 =
                        separate_map_last FStar_Pprint.hardline p_calcStep
                          steps
                         in
                      FStar_Pprint.op_Hat_Hat FStar_Pprint.hardline
                        uu____51139
                       in
                    FStar_Pprint.op_Hat_Hat uu____51136 uu____51138  in
                  FStar_Pprint.op_Hat_Hat uu____51132 uu____51135  in
                FStar_Pprint.op_Hat_Hat FStar_Pprint.hardline uu____51131  in
              FStar_All.pipe_left (FStar_Pprint.nest (Prims.parse_int "2"))
                uu____51130
               in
            FStar_Pprint.enclose head1 uu____51128 uu____51129
        | uu____51141 -> p_typ ps pb e

and (p_calcStep :
  Prims.bool -> FStar_Parser_AST.calc_step -> FStar_Pprint.document) =
  fun uu____51142  ->
    fun uu____51143  ->
      match uu____51143 with
      | FStar_Parser_AST.CalcStep (rel,just,next) ->
          let uu____51148 =
            let uu____51149 = p_noSeqTermAndComment false false rel  in
            let uu____51152 =
              let uu____51153 =
                let uu____51154 =
                  let uu____51155 =
                    let uu____51156 = p_noSeqTermAndComment false false just
                       in
                    let uu____51159 =
                      let uu____51160 =
                        let uu____51161 =
                          let uu____51162 =
                            let uu____51163 =
                              p_noSeqTermAndComment false false next  in
                            let uu____51166 = str ";"  in
                            FStar_Pprint.op_Hat_Hat uu____51163 uu____51166
                             in
                          FStar_Pprint.op_Hat_Hat FStar_Pprint.hardline
                            uu____51162
                           in
                        FStar_Pprint.op_Hat_Hat FStar_Pprint.rbrace
                          uu____51161
                         in
                      FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____51160
                       in
                    FStar_Pprint.op_Hat_Hat uu____51156 uu____51159  in
                  FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____51155  in
                FStar_Pprint.op_Hat_Hat FStar_Pprint.lbrace uu____51154  in
              FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____51153  in
            FStar_Pprint.op_Hat_Hat uu____51149 uu____51152  in
          FStar_Pprint.group uu____51148

and (p_attrs_opt :
  FStar_Parser_AST.term Prims.list FStar_Pervasives_Native.option ->
    FStar_Pprint.document)
  =
  fun uu___335_51168  ->
    match uu___335_51168 with
    | FStar_Pervasives_Native.None  -> FStar_Pprint.empty
    | FStar_Pervasives_Native.Some terms ->
        let uu____51180 =
          let uu____51181 = str "[@"  in
          let uu____51183 =
            let uu____51184 =
              FStar_Pprint.separate_map break1 p_atomicTerm terms  in
            let uu____51185 = str "]"  in
            FStar_Pprint.op_Hat_Slash_Hat uu____51184 uu____51185  in
          FStar_Pprint.op_Hat_Slash_Hat uu____51181 uu____51183  in
        FStar_Pprint.group uu____51180

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
                 let uu____51222 =
                   let uu____51223 =
                     let uu____51224 = p_quantifier e  in
                     FStar_Pprint.op_Hat_Hat uu____51224 FStar_Pprint.space
                      in
                   FStar_Pprint.soft_surround (Prims.parse_int "2")
                     (Prims.parse_int "0") uu____51223 binders_doc
                     FStar_Pprint.dot
                    in
                 prefix2 uu____51222 term_doc
             | pats ->
                 let uu____51232 =
                   let uu____51233 =
                     let uu____51234 =
                       let uu____51235 =
                         let uu____51236 = p_quantifier e  in
                         FStar_Pprint.op_Hat_Hat uu____51236
                           FStar_Pprint.space
                          in
                       FStar_Pprint.soft_surround (Prims.parse_int "2")
                         (Prims.parse_int "0") uu____51235 binders_doc
                         FStar_Pprint.dot
                        in
                     let uu____51239 = p_trigger trigger  in
                     prefix2 uu____51234 uu____51239  in
                   FStar_Pprint.group uu____51233  in
                 prefix2 uu____51232 term_doc)
        | FStar_Parser_AST.QExists (bs,trigger,e1) ->
            let binders_doc = p_binders true bs  in
            let term_doc = p_noSeqTermAndComment ps pb e1  in
            (match trigger with
             | [] ->
                 let uu____51260 =
                   let uu____51261 =
                     let uu____51262 = p_quantifier e  in
                     FStar_Pprint.op_Hat_Hat uu____51262 FStar_Pprint.space
                      in
                   FStar_Pprint.soft_surround (Prims.parse_int "2")
                     (Prims.parse_int "0") uu____51261 binders_doc
                     FStar_Pprint.dot
                    in
                 prefix2 uu____51260 term_doc
             | pats ->
                 let uu____51270 =
                   let uu____51271 =
                     let uu____51272 =
                       let uu____51273 =
                         let uu____51274 = p_quantifier e  in
                         FStar_Pprint.op_Hat_Hat uu____51274
                           FStar_Pprint.space
                          in
                       FStar_Pprint.soft_surround (Prims.parse_int "2")
                         (Prims.parse_int "0") uu____51273 binders_doc
                         FStar_Pprint.dot
                        in
                     let uu____51277 = p_trigger trigger  in
                     prefix2 uu____51272 uu____51277  in
                   FStar_Pprint.group uu____51271  in
                 prefix2 uu____51270 term_doc)
        | uu____51278 -> p_simpleTerm ps pb e

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
      let uu____51299 = all_binders_annot t  in
      if uu____51299
      then
        let uu____51302 =
          p_typ_top
            (Binders ((Prims.parse_int "4"), (Prims.parse_int "0"), true))
            false false t
           in
        FStar_Pprint.op_Hat_Hat s uu____51302
      else
        (let uu____51313 =
           let uu____51314 =
             let uu____51315 =
               p_typ_top
                 (Arrows ((Prims.parse_int "2"), (Prims.parse_int "2")))
                 false false t
                in
             FStar_Pprint.op_Hat_Hat s uu____51315  in
           FStar_Pprint.op_Hat_Hat FStar_Pprint.colon uu____51314  in
         FStar_Pprint.group uu____51313)

and (collapse_pats :
  (FStar_Pprint.document * FStar_Pprint.document) Prims.list ->
    FStar_Pprint.document Prims.list)
  =
  fun pats  ->
    let fold_fun bs x =
      let uu____51374 = x  in
      match uu____51374 with
      | (b1,t1) ->
          (match bs with
           | [] -> [([b1], t1)]
           | hd1::tl1 ->
               let uu____51439 = hd1  in
               (match uu____51439 with
                | (b2s,t2) ->
                    if t1 = t2
                    then ((FStar_List.append b2s [b1]), t1) :: tl1
                    else ([b1], t1) :: hd1 :: tl1))
       in
    let p_collapsed_binder cb =
      let uu____51511 = cb  in
      match uu____51511 with
      | (bs,typ) ->
          (match bs with
           | [] -> failwith "Impossible"
           | b::[] -> cat_with_colon b typ
           | hd1::tl1 ->
               let uu____51530 =
                 FStar_List.fold_left
                   (fun x  ->
                      fun y  ->
                        let uu____51536 =
                          FStar_Pprint.op_Hat_Hat FStar_Pprint.space y  in
                        FStar_Pprint.op_Hat_Hat x uu____51536) hd1 tl1
                  in
               cat_with_colon uu____51530 typ)
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
                 FStar_Parser_AST.brange = uu____51615;
                 FStar_Parser_AST.blevel = uu____51616;
                 FStar_Parser_AST.aqual = uu____51617;_},phi))
               when lid.FStar_Ident.idText = lid'.FStar_Ident.idText ->
               let uu____51626 =
                 let uu____51631 = p_ident lid  in
                 p_refinement' aqual uu____51631 t1 phi  in
               FStar_Pervasives_Native.Some uu____51626
           | (FStar_Parser_AST.PatVar (lid,aqual),uu____51638) ->
               let uu____51643 =
                 let uu____51648 =
                   let uu____51649 = FStar_Pprint.optional p_aqual aqual  in
                   let uu____51650 = p_ident lid  in
                   FStar_Pprint.op_Hat_Hat uu____51649 uu____51650  in
                 let uu____51651 = p_tmEqNoRefinement t  in
                 (uu____51648, uu____51651)  in
               FStar_Pervasives_Native.Some uu____51643
           | uu____51656 -> FStar_Pervasives_Native.None)
      | uu____51665 -> FStar_Pervasives_Native.None  in
    let all_unbound p =
      match p.FStar_Parser_AST.pat with
      | FStar_Parser_AST.PatAscribed uu____51678 -> false
      | uu____51690 -> true  in
    let uu____51692 = map_if_all all_binders pats  in
    match uu____51692 with
    | FStar_Pervasives_Native.Some bs ->
        let uu____51724 = collapse_pats bs  in
        (uu____51724,
          (Binders ((Prims.parse_int "4"), (Prims.parse_int "0"), true)))
    | FStar_Pervasives_Native.None  ->
        let uu____51741 = FStar_List.map p_atomicPattern pats  in
        (uu____51741,
          (Binders ((Prims.parse_int "4"), (Prims.parse_int "0"), false)))

and (p_quantifier : FStar_Parser_AST.term -> FStar_Pprint.document) =
  fun e  ->
    match e.FStar_Parser_AST.tm with
    | FStar_Parser_AST.QForall uu____51753 -> str "forall"
    | FStar_Parser_AST.QExists uu____51767 -> str "exists"
    | uu____51781 ->
        failwith "Imposible : p_quantifier called on a non-quantifier term"

and (p_trigger :
  FStar_Parser_AST.term Prims.list Prims.list -> FStar_Pprint.document) =
  fun uu___336_51783  ->
    match uu___336_51783 with
    | [] -> FStar_Pprint.empty
    | pats ->
        let uu____51795 =
          let uu____51796 =
            let uu____51797 =
              let uu____51798 = str "pattern"  in
              let uu____51800 =
                let uu____51801 =
                  let uu____51802 = p_disjunctivePats pats  in
                  FStar_Pprint.jump (Prims.parse_int "2")
                    (Prims.parse_int "0") uu____51802
                   in
                FStar_Pprint.op_Hat_Hat uu____51801 FStar_Pprint.rbrace  in
              FStar_Pprint.op_Hat_Slash_Hat uu____51798 uu____51800  in
            FStar_Pprint.op_Hat_Hat FStar_Pprint.colon uu____51797  in
          FStar_Pprint.op_Hat_Hat FStar_Pprint.lbrace uu____51796  in
        FStar_Pprint.group uu____51795

and (p_disjunctivePats :
  FStar_Parser_AST.term Prims.list Prims.list -> FStar_Pprint.document) =
  fun pats  ->
    let uu____51810 = str "\\/"  in
    FStar_Pprint.separate_map uu____51810 p_conjunctivePats pats

and (p_conjunctivePats :
  FStar_Parser_AST.term Prims.list -> FStar_Pprint.document) =
  fun pats  ->
    let uu____51817 =
      let uu____51818 = FStar_Pprint.op_Hat_Hat FStar_Pprint.semi break1  in
      FStar_Pprint.separate_map uu____51818 p_appTerm pats  in
    FStar_Pprint.group uu____51817

and (p_simpleTerm :
  Prims.bool -> Prims.bool -> FStar_Parser_AST.term -> FStar_Pprint.document)
  =
  fun ps  ->
    fun pb  ->
      fun e  ->
        match e.FStar_Parser_AST.tm with
        | FStar_Parser_AST.Abs (pats,e1) ->
            let uu____51830 = p_term_sep false pb e1  in
            (match uu____51830 with
             | (comm,doc1) ->
                 let prefix1 =
                   let uu____51839 = str "fun"  in
                   let uu____51841 =
                     let uu____51842 =
                       FStar_Pprint.separate_map break1 p_atomicPattern pats
                        in
                     FStar_Pprint.op_Hat_Slash_Hat uu____51842
                       FStar_Pprint.rarrow
                      in
                   op_Hat_Slash_Plus_Hat uu____51839 uu____51841  in
                 let uu____51843 =
                   if comm <> FStar_Pprint.empty
                   then
                     let uu____51845 =
                       let uu____51846 =
                         let uu____51847 =
                           FStar_Pprint.op_Hat_Hat FStar_Pprint.hardline doc1
                            in
                         FStar_Pprint.op_Hat_Hat comm uu____51847  in
                       FStar_Pprint.op_Hat_Hat FStar_Pprint.hardline
                         uu____51846
                        in
                     FStar_Pprint.op_Hat_Hat prefix1 uu____51845
                   else
                     (let uu____51850 = op_Hat_Slash_Plus_Hat prefix1 doc1
                         in
                      FStar_Pprint.group uu____51850)
                    in
                 let uu____51851 = paren_if ps  in uu____51851 uu____51843)
        | uu____51856 -> p_tmIff e

and (p_maybeFocusArrow : Prims.bool -> FStar_Pprint.document) =
  fun b  -> if b then str "~>" else FStar_Pprint.rarrow

and (p_patternBranch :
  Prims.bool ->
    (FStar_Parser_AST.pattern * FStar_Parser_AST.term
      FStar_Pervasives_Native.option * FStar_Parser_AST.term) ->
      FStar_Pprint.document)
  =
  fun pb  ->
    fun uu____51864  ->
      match uu____51864 with
      | (pat,when_opt,e) ->
          let one_pattern_branch p =
            let branch =
              match when_opt with
              | FStar_Pervasives_Native.None  ->
                  let uu____51888 =
                    let uu____51889 =
                      let uu____51890 =
                        let uu____51891 = p_tuplePattern p  in
                        let uu____51892 =
                          FStar_Pprint.op_Hat_Hat FStar_Pprint.space
                            FStar_Pprint.rarrow
                           in
                        FStar_Pprint.op_Hat_Hat uu____51891 uu____51892  in
                      FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____51890
                       in
                    FStar_Pprint.op_Hat_Hat FStar_Pprint.bar uu____51889  in
                  FStar_Pprint.group uu____51888
              | FStar_Pervasives_Native.Some f ->
                  let uu____51894 =
                    let uu____51895 =
                      let uu____51896 =
                        let uu____51897 =
                          let uu____51898 =
                            let uu____51899 = p_tuplePattern p  in
                            let uu____51900 = str "when"  in
                            FStar_Pprint.op_Hat_Slash_Hat uu____51899
                              uu____51900
                             in
                          FStar_Pprint.group uu____51898  in
                        let uu____51902 =
                          let uu____51903 =
                            let uu____51906 = p_tmFormula f  in
                            [uu____51906; FStar_Pprint.rarrow]  in
                          FStar_Pprint.flow break1 uu____51903  in
                        FStar_Pprint.op_Hat_Slash_Hat uu____51897 uu____51902
                         in
                      FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____51896
                       in
                    FStar_Pprint.op_Hat_Hat FStar_Pprint.bar uu____51895  in
                  FStar_Pprint.hang (Prims.parse_int "2") uu____51894
               in
            let uu____51908 = p_term_sep false pb e  in
            match uu____51908 with
            | (comm,doc1) ->
                if pb
                then
                  (if comm = FStar_Pprint.empty
                   then
                     let uu____51918 = op_Hat_Slash_Plus_Hat branch doc1  in
                     FStar_Pprint.group uu____51918
                   else
                     (let uu____51921 =
                        let uu____51922 =
                          let uu____51923 =
                            let uu____51924 =
                              let uu____51925 =
                                FStar_Pprint.op_Hat_Hat break1 comm  in
                              FStar_Pprint.op_Hat_Hat doc1 uu____51925  in
                            op_Hat_Slash_Plus_Hat branch uu____51924  in
                          FStar_Pprint.group uu____51923  in
                        let uu____51926 =
                          let uu____51927 =
                            let uu____51928 =
                              inline_comment_or_above comm doc1
                                FStar_Pprint.empty
                               in
                            jump2 uu____51928  in
                          FStar_Pprint.op_Hat_Hat branch uu____51927  in
                        FStar_Pprint.ifflat uu____51922 uu____51926  in
                      FStar_Pprint.group uu____51921))
                else
                  if comm <> FStar_Pprint.empty
                  then
                    (let uu____51932 =
                       let uu____51933 =
                         FStar_Pprint.op_Hat_Hat FStar_Pprint.hardline doc1
                          in
                       FStar_Pprint.op_Hat_Hat comm uu____51933  in
                     op_Hat_Slash_Plus_Hat branch uu____51932)
                  else op_Hat_Slash_Plus_Hat branch doc1
             in
          (match pat.FStar_Parser_AST.pat with
           | FStar_Parser_AST.PatOr pats ->
               (match FStar_List.rev pats with
                | hd1::tl1 ->
                    let last_pat_branch = one_pattern_branch hd1  in
                    let uu____51944 =
                      let uu____51945 =
                        let uu____51946 =
                          let uu____51947 =
                            let uu____51948 =
                              let uu____51949 =
                                FStar_Pprint.op_Hat_Hat FStar_Pprint.bar
                                  FStar_Pprint.space
                                 in
                              FStar_Pprint.op_Hat_Hat break1 uu____51949  in
                            FStar_Pprint.separate_map uu____51948
                              p_tuplePattern (FStar_List.rev tl1)
                             in
                          FStar_Pprint.op_Hat_Slash_Hat uu____51947
                            last_pat_branch
                           in
                        FStar_Pprint.op_Hat_Hat FStar_Pprint.space
                          uu____51946
                         in
                      FStar_Pprint.op_Hat_Hat FStar_Pprint.bar uu____51945
                       in
                    FStar_Pprint.group uu____51944
                | [] ->
                    failwith "Impossible: disjunctive pattern can't be empty")
           | uu____51951 -> one_pattern_branch pat)

and (p_tmIff : FStar_Parser_AST.term -> FStar_Pprint.document) =
  fun e  ->
    match e.FStar_Parser_AST.tm with
    | FStar_Parser_AST.Op
        ({ FStar_Ident.idText = "<==>"; FStar_Ident.idRange = uu____51953;_},e1::e2::[])
        ->
        let uu____51959 = str "<==>"  in
        let uu____51961 = p_tmImplies e1  in
        let uu____51962 = p_tmIff e2  in
        infix0 uu____51959 uu____51961 uu____51962
    | uu____51963 -> p_tmImplies e

and (p_tmImplies : FStar_Parser_AST.term -> FStar_Pprint.document) =
  fun e  ->
    match e.FStar_Parser_AST.tm with
    | FStar_Parser_AST.Op
        ({ FStar_Ident.idText = "==>"; FStar_Ident.idRange = uu____51965;_},e1::e2::[])
        ->
        let uu____51971 = str "==>"  in
        let uu____51973 =
          p_tmArrow (Arrows ((Prims.parse_int "2"), (Prims.parse_int "2")))
            false p_tmFormula e1
           in
        let uu____51979 = p_tmImplies e2  in
        infix0 uu____51971 uu____51973 uu____51979
    | uu____51980 ->
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
          let uu____51994 =
            FStar_List.splitAt
              ((FStar_List.length terms) - (Prims.parse_int "1")) terms
             in
          match uu____51994 with
          | (terms',last1) ->
              let uu____52014 =
                match style with
                | Arrows (n1,ln) ->
                    let uu____52049 =
                      let uu____52050 =
                        FStar_Pprint.op_Hat_Hat FStar_Pprint.rarrow break1
                         in
                      FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____52050
                       in
                    let uu____52051 =
                      FStar_Pprint.op_Hat_Hat FStar_Pprint.rarrow
                        FStar_Pprint.space
                       in
                    (n1, ln, terms', uu____52049, uu____52051)
                | Binders (n1,ln,parens1) ->
                    let uu____52065 =
                      if parens1
                      then FStar_List.map soft_parens_with_nesting terms'
                      else terms'  in
                    let uu____52073 =
                      FStar_Pprint.op_Hat_Hat FStar_Pprint.colon
                        FStar_Pprint.space
                       in
                    (n1, ln, uu____52065, break1, uu____52073)
                 in
              (match uu____52014 with
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
                    | _52106 when _52106 = (Prims.parse_int "1") ->
                        FStar_List.hd terms
                    | uu____52107 ->
                        let uu____52108 =
                          let uu____52109 =
                            let uu____52110 =
                              let uu____52111 =
                                FStar_Pprint.separate sep terms'1  in
                              let uu____52112 =
                                let uu____52113 =
                                  FStar_Pprint.op_Hat_Hat last_op1 last2  in
                                FStar_Pprint.op_Hat_Hat one_line_space
                                  uu____52113
                                 in
                              FStar_Pprint.op_Hat_Hat uu____52111 uu____52112
                               in
                            FStar_Pprint.op_Hat_Hat fs uu____52110  in
                          let uu____52114 =
                            let uu____52115 =
                              let uu____52116 =
                                let uu____52117 =
                                  let uu____52118 =
                                    FStar_Pprint.separate sep terms'1  in
                                  FStar_Pprint.op_Hat_Hat fs uu____52118  in
                                let uu____52119 =
                                  let uu____52120 =
                                    let uu____52121 =
                                      let uu____52122 =
                                        FStar_Pprint.op_Hat_Hat sep
                                          single_line_arg_indent
                                         in
                                      let uu____52123 =
                                        FStar_List.map
                                          (fun x  ->
                                             let uu____52129 =
                                               FStar_Pprint.hang
                                                 (Prims.parse_int "2") x
                                                in
                                             FStar_Pprint.align uu____52129)
                                          terms'1
                                         in
                                      FStar_Pprint.separate uu____52122
                                        uu____52123
                                       in
                                    FStar_Pprint.op_Hat_Hat
                                      single_line_arg_indent uu____52121
                                     in
                                  jump2 uu____52120  in
                                FStar_Pprint.ifflat uu____52117 uu____52119
                                 in
                              FStar_Pprint.group uu____52116  in
                            let uu____52131 =
                              let uu____52132 =
                                let uu____52133 =
                                  FStar_Pprint.op_Hat_Hat last_op1 last2  in
                                FStar_Pprint.hang last_n uu____52133  in
                              FStar_Pprint.align uu____52132  in
                            FStar_Pprint.prefix n1 (Prims.parse_int "1")
                              uu____52115 uu____52131
                             in
                          FStar_Pprint.ifflat uu____52109 uu____52114  in
                        FStar_Pprint.group uu____52108))

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
            | Arrows uu____52147 -> p_tmArrow' p_Tm e
            | Binders uu____52154 -> collapse_binders p_Tm e  in
          format_sig style terms false flat_space

and (p_tmArrow' :
  (FStar_Parser_AST.term -> FStar_Pprint.document) ->
    FStar_Parser_AST.term -> FStar_Pprint.document Prims.list)
  =
  fun p_Tm  ->
    fun e  ->
      match e.FStar_Parser_AST.tm with
      | FStar_Parser_AST.Product (bs,tgt) ->
          let uu____52177 = FStar_List.map (fun b  -> p_binder false b) bs
             in
          let uu____52183 = p_tmArrow' p_Tm tgt  in
          FStar_List.append uu____52177 uu____52183
      | uu____52186 -> let uu____52187 = p_Tm e  in [uu____52187]

and (collapse_binders :
  (FStar_Parser_AST.term -> FStar_Pprint.document) ->
    FStar_Parser_AST.term -> FStar_Pprint.document Prims.list)
  =
  fun p_Tm  ->
    fun e  ->
      let rec accumulate_binders p_Tm1 e1 =
        match e1.FStar_Parser_AST.tm with
        | FStar_Parser_AST.Product (bs,tgt) ->
            let uu____52240 = FStar_List.map (fun b  -> p_binder' false b) bs
               in
            let uu____52266 = accumulate_binders p_Tm1 tgt  in
            FStar_List.append uu____52240 uu____52266
        | uu____52289 ->
            let uu____52290 =
              let uu____52301 = p_Tm1 e1  in
              (uu____52301, FStar_Pervasives_Native.None, cat_with_colon)  in
            [uu____52290]
         in
      let fold_fun bs x =
        let uu____52399 = x  in
        match uu____52399 with
        | (b1,t1,f1) ->
            (match bs with
             | [] -> [([b1], t1, f1)]
             | hd1::tl1 ->
                 let uu____52535 = hd1  in
                 (match uu____52535 with
                  | (b2s,t2,uu____52564) ->
                      (match (t1, t2) with
                       | (FStar_Pervasives_Native.Some
                          typ1,FStar_Pervasives_Native.Some typ2) ->
                           if typ1 = typ2
                           then ((FStar_List.append b2s [b1]), t1, f1) :: tl1
                           else ([b1], t1, f1) :: hd1 :: tl1
                       | uu____52674 -> ([b1], t1, f1) :: bs)))
         in
      let p_collapsed_binder cb =
        let uu____52735 = cb  in
        match uu____52735 with
        | (bs,t,f) ->
            (match t with
             | FStar_Pervasives_Native.None  ->
                 (match bs with
                  | b::[] -> b
                  | uu____52764 -> failwith "Impossible")
             | FStar_Pervasives_Native.Some typ ->
                 (match bs with
                  | [] -> failwith "Impossible"
                  | b::[] -> f b typ
                  | hd1::tl1 ->
                      let uu____52777 =
                        FStar_List.fold_left
                          (fun x  ->
                             fun y  ->
                               let uu____52783 =
                                 FStar_Pprint.op_Hat_Hat FStar_Pprint.space y
                                  in
                               FStar_Pprint.op_Hat_Hat x uu____52783) hd1 tl1
                         in
                      f uu____52777 typ))
         in
      let binders =
        let uu____52801 = accumulate_binders p_Tm e  in
        FStar_List.fold_left fold_fun [] uu____52801  in
      map_rev p_collapsed_binder binders

and (p_tmFormula : FStar_Parser_AST.term -> FStar_Pprint.document) =
  fun e  ->
    let conj =
      let uu____52864 =
        let uu____52865 = str "/\\"  in
        FStar_Pprint.op_Hat_Hat uu____52865 break1  in
      FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____52864  in
    let disj =
      let uu____52868 =
        let uu____52869 = str "\\/"  in
        FStar_Pprint.op_Hat_Hat uu____52869 break1  in
      FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____52868  in
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
        ({ FStar_Ident.idText = "\\/"; FStar_Ident.idRange = uu____52889;_},e1::e2::[])
        ->
        let uu____52895 = p_tmDisjunction e1  in
        let uu____52900 =
          let uu____52905 = p_tmConjunction e2  in [uu____52905]  in
        FStar_List.append uu____52895 uu____52900
    | uu____52914 -> let uu____52915 = p_tmConjunction e  in [uu____52915]

and (p_tmConjunction :
  FStar_Parser_AST.term -> FStar_Pprint.document Prims.list) =
  fun e  ->
    match e.FStar_Parser_AST.tm with
    | FStar_Parser_AST.Op
        ({ FStar_Ident.idText = "/\\"; FStar_Ident.idRange = uu____52925;_},e1::e2::[])
        ->
        let uu____52931 = p_tmConjunction e1  in
        let uu____52934 = let uu____52937 = p_tmTuple e2  in [uu____52937]
           in
        FStar_List.append uu____52931 uu____52934
    | uu____52938 -> let uu____52939 = p_tmTuple e  in [uu____52939]

and (p_tmTuple : FStar_Parser_AST.term -> FStar_Pprint.document) =
  fun e  -> with_comment p_tmTuple' e e.FStar_Parser_AST.range

and (p_tmTuple' : FStar_Parser_AST.term -> FStar_Pprint.document) =
  fun e  ->
    match e.FStar_Parser_AST.tm with
    | FStar_Parser_AST.Construct (lid,args) when
        (is_tuple_constructor lid) && (all_explicit args) ->
        let uu____52956 = FStar_Pprint.op_Hat_Hat FStar_Pprint.comma break1
           in
        FStar_Pprint.separate_map uu____52956
          (fun uu____52964  ->
             match uu____52964 with | (e1,uu____52970) -> p_tmEq e1) args
    | uu____52971 -> p_tmEq e

and (paren_if_gt :
  Prims.int -> Prims.int -> FStar_Pprint.document -> FStar_Pprint.document) =
  fun curr  ->
    fun mine  ->
      fun doc1  ->
        if mine <= curr
        then doc1
        else
          (let uu____52980 =
             let uu____52981 =
               FStar_Pprint.op_Hat_Hat doc1 FStar_Pprint.rparen  in
             FStar_Pprint.op_Hat_Hat FStar_Pprint.lparen uu____52981  in
           FStar_Pprint.group uu____52980)

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
               (let uu____53000 = FStar_Ident.text_of_id op  in
                uu____53000 = "="))
              ||
              (let uu____53005 = FStar_Ident.text_of_id op  in
               uu____53005 = "|>")
            ->
            let op1 = FStar_Ident.text_of_id op  in
            let uu____53011 = levels op1  in
            (match uu____53011 with
             | (left1,mine,right1) ->
                 let uu____53030 =
                   let uu____53031 = FStar_All.pipe_left str op1  in
                   let uu____53033 = p_tmEqWith' p_X left1 e1  in
                   let uu____53034 = p_tmEqWith' p_X right1 e2  in
                   infix0 uu____53031 uu____53033 uu____53034  in
                 paren_if_gt curr mine uu____53030)
        | FStar_Parser_AST.Op
            ({ FStar_Ident.idText = ":=";
               FStar_Ident.idRange = uu____53035;_},e1::e2::[])
            ->
            let uu____53041 =
              let uu____53042 = p_tmEqWith p_X e1  in
              let uu____53043 =
                let uu____53044 =
                  let uu____53045 =
                    let uu____53046 = p_tmEqWith p_X e2  in
                    op_Hat_Slash_Plus_Hat FStar_Pprint.equals uu____53046  in
                  FStar_Pprint.op_Hat_Hat FStar_Pprint.colon uu____53045  in
                FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____53044  in
              FStar_Pprint.op_Hat_Hat uu____53042 uu____53043  in
            FStar_Pprint.group uu____53041
        | FStar_Parser_AST.Op
            ({ FStar_Ident.idText = "-"; FStar_Ident.idRange = uu____53047;_},e1::[])
            ->
            let uu____53052 = levels "-"  in
            (match uu____53052 with
             | (left1,mine,right1) ->
                 let uu____53072 = p_tmEqWith' p_X mine e1  in
                 FStar_Pprint.op_Hat_Slash_Hat FStar_Pprint.minus uu____53072)
        | uu____53073 -> p_tmNoEqWith p_X e

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
              (lid,(e1,uu____53121)::(e2,uu____53123)::[]) when
              (FStar_Ident.lid_equals lid FStar_Parser_Const.cons_lid) &&
                (let uu____53143 = is_list e  in
                 Prims.op_Negation uu____53143)
              ->
              let op = "::"  in
              let uu____53148 = levels op  in
              (match uu____53148 with
               | (left1,mine,right1) ->
                   let uu____53167 =
                     let uu____53168 = str op  in
                     let uu____53169 = p_tmNoEqWith' false p_X left1 e1  in
                     let uu____53171 = p_tmNoEqWith' false p_X right1 e2  in
                     infix0 uu____53168 uu____53169 uu____53171  in
                   paren_if_gt curr mine uu____53167)
          | FStar_Parser_AST.Sum (binders,res) ->
              let op = "&"  in
              let uu____53190 = levels op  in
              (match uu____53190 with
               | (left1,mine,right1) ->
                   let p_dsumfst bt =
                     match bt with
                     | FStar_Util.Inl b ->
                         let uu____53224 = p_binder false b  in
                         let uu____53226 =
                           let uu____53227 =
                             let uu____53228 = str op  in
                             FStar_Pprint.op_Hat_Hat uu____53228 break1  in
                           FStar_Pprint.op_Hat_Hat FStar_Pprint.space
                             uu____53227
                            in
                         FStar_Pprint.op_Hat_Hat uu____53224 uu____53226
                     | FStar_Util.Inr t ->
                         let uu____53230 = p_tmNoEqWith' false p_X left1 t
                            in
                         let uu____53232 =
                           let uu____53233 =
                             let uu____53234 = str op  in
                             FStar_Pprint.op_Hat_Hat uu____53234 break1  in
                           FStar_Pprint.op_Hat_Hat FStar_Pprint.space
                             uu____53233
                            in
                         FStar_Pprint.op_Hat_Hat uu____53230 uu____53232
                      in
                   let uu____53235 =
                     let uu____53236 =
                       FStar_Pprint.concat_map p_dsumfst binders  in
                     let uu____53241 = p_tmNoEqWith' false p_X right1 res  in
                     FStar_Pprint.op_Hat_Hat uu____53236 uu____53241  in
                   paren_if_gt curr mine uu____53235)
          | FStar_Parser_AST.Op
              ({ FStar_Ident.idText = "*";
                 FStar_Ident.idRange = uu____53243;_},e1::e2::[])
              when FStar_ST.op_Bang unfold_tuples ->
              let op = "*"  in
              let uu____53273 = levels op  in
              (match uu____53273 with
               | (left1,mine,right1) ->
                   if inside_tuple
                   then
                     let uu____53293 = str op  in
                     let uu____53294 = p_tmNoEqWith' true p_X left1 e1  in
                     let uu____53296 = p_tmNoEqWith' true p_X right1 e2  in
                     infix0 uu____53293 uu____53294 uu____53296
                   else
                     (let uu____53300 =
                        let uu____53301 = str op  in
                        let uu____53302 = p_tmNoEqWith' true p_X left1 e1  in
                        let uu____53304 = p_tmNoEqWith' true p_X right1 e2
                           in
                        infix0 uu____53301 uu____53302 uu____53304  in
                      paren_if_gt curr mine uu____53300))
          | FStar_Parser_AST.Op (op,e1::e2::[]) when is_operatorInfix34 op ->
              let op1 = FStar_Ident.text_of_id op  in
              let uu____53313 = levels op1  in
              (match uu____53313 with
               | (left1,mine,right1) ->
                   let uu____53332 =
                     let uu____53333 = str op1  in
                     let uu____53334 = p_tmNoEqWith' false p_X left1 e1  in
                     let uu____53336 = p_tmNoEqWith' false p_X right1 e2  in
                     infix0 uu____53333 uu____53334 uu____53336  in
                   paren_if_gt curr mine uu____53332)
          | FStar_Parser_AST.Record (with_opt,record_fields) ->
              let uu____53356 =
                let uu____53357 =
                  default_or_map FStar_Pprint.empty p_with_clause with_opt
                   in
                let uu____53358 =
                  let uu____53359 =
                    FStar_Pprint.op_Hat_Hat FStar_Pprint.semi break1  in
                  separate_map_last uu____53359 p_simpleDef record_fields  in
                FStar_Pprint.op_Hat_Hat uu____53357 uu____53358  in
              braces_with_nesting uu____53356
          | FStar_Parser_AST.Op
              ({ FStar_Ident.idText = "~";
                 FStar_Ident.idRange = uu____53364;_},e1::[])
              ->
              let uu____53369 =
                let uu____53370 = str "~"  in
                let uu____53372 = p_atomicTerm e1  in
                FStar_Pprint.op_Hat_Hat uu____53370 uu____53372  in
              FStar_Pprint.group uu____53369
          | FStar_Parser_AST.Paren p when inside_tuple ->
              (match p.FStar_Parser_AST.tm with
               | FStar_Parser_AST.Op
                   ({ FStar_Ident.idText = "*";
                      FStar_Ident.idRange = uu____53374;_},e1::e2::[])
                   ->
                   let op = "*"  in
                   let uu____53383 = levels op  in
                   (match uu____53383 with
                    | (left1,mine,right1) ->
                        let uu____53402 =
                          let uu____53403 = str op  in
                          let uu____53404 = p_tmNoEqWith' true p_X left1 e1
                             in
                          let uu____53406 = p_tmNoEqWith' true p_X right1 e2
                             in
                          infix0 uu____53403 uu____53404 uu____53406  in
                        paren_if_gt curr mine uu____53402)
               | uu____53408 -> p_X e)
          | uu____53409 -> p_X e

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
        let uu____53416 =
          let uu____53417 = p_lident lid  in
          let uu____53418 =
            let uu____53419 = p_appTerm e1  in
            FStar_Pprint.op_Hat_Slash_Hat FStar_Pprint.colon uu____53419  in
          FStar_Pprint.op_Hat_Slash_Hat uu____53417 uu____53418  in
        FStar_Pprint.group uu____53416
    | FStar_Parser_AST.Refine (b,phi) -> p_refinedBinder b phi
    | uu____53422 -> p_appTerm e

and (p_with_clause : FStar_Parser_AST.term -> FStar_Pprint.document) =
  fun e  ->
    let uu____53424 = p_appTerm e  in
    let uu____53425 =
      let uu____53426 =
        let uu____53427 = str "with"  in
        FStar_Pprint.op_Hat_Hat uu____53427 break1  in
      FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____53426  in
    FStar_Pprint.op_Hat_Hat uu____53424 uu____53425

and (p_refinedBinder :
  FStar_Parser_AST.binder -> FStar_Parser_AST.term -> FStar_Pprint.document)
  =
  fun b  ->
    fun phi  ->
      match b.FStar_Parser_AST.b with
      | FStar_Parser_AST.Annotated (lid,t) ->
          let uu____53433 = p_lident lid  in
          p_refinement b.FStar_Parser_AST.aqual uu____53433 t phi
      | FStar_Parser_AST.TAnnotated uu____53434 ->
          failwith "Is this still used ?"
      | FStar_Parser_AST.Variable uu____53440 ->
          let uu____53441 =
            let uu____53443 = FStar_Parser_AST.binder_to_string b  in
            FStar_Util.format1
              "Imposible : a refined binder ought to be annotated %s"
              uu____53443
             in
          failwith uu____53441
      | FStar_Parser_AST.TVariable uu____53446 ->
          let uu____53447 =
            let uu____53449 = FStar_Parser_AST.binder_to_string b  in
            FStar_Util.format1
              "Imposible : a refined binder ought to be annotated %s"
              uu____53449
             in
          failwith uu____53447
      | FStar_Parser_AST.NoName uu____53452 ->
          let uu____53453 =
            let uu____53455 = FStar_Parser_AST.binder_to_string b  in
            FStar_Util.format1
              "Imposible : a refined binder ought to be annotated %s"
              uu____53455
             in
          failwith uu____53453

and (p_simpleDef :
  Prims.bool ->
    (FStar_Ident.lid * FStar_Parser_AST.term) -> FStar_Pprint.document)
  =
  fun ps  ->
    fun uu____53459  ->
      match uu____53459 with
      | (lid,e) ->
          let uu____53467 =
            let uu____53468 = p_qlident lid  in
            let uu____53469 =
              let uu____53470 = p_noSeqTermAndComment ps false e  in
              FStar_Pprint.op_Hat_Slash_Hat FStar_Pprint.equals uu____53470
               in
            FStar_Pprint.op_Hat_Slash_Hat uu____53468 uu____53469  in
          FStar_Pprint.group uu____53467

and (p_appTerm : FStar_Parser_AST.term -> FStar_Pprint.document) =
  fun e  ->
    match e.FStar_Parser_AST.tm with
    | FStar_Parser_AST.App uu____53473 when is_general_application e ->
        let uu____53480 = head_and_args e  in
        (match uu____53480 with
         | (head1,args) ->
             (match args with
              | e1::e2::[] when
                  (FStar_Pervasives_Native.snd e1) = FStar_Parser_AST.Infix
                  ->
                  let uu____53527 = p_argTerm e1  in
                  let uu____53528 =
                    let uu____53529 =
                      let uu____53530 =
                        let uu____53531 = str "`"  in
                        let uu____53533 =
                          let uu____53534 = p_indexingTerm head1  in
                          let uu____53535 = str "`"  in
                          FStar_Pprint.op_Hat_Hat uu____53534 uu____53535  in
                        FStar_Pprint.op_Hat_Hat uu____53531 uu____53533  in
                      FStar_Pprint.group uu____53530  in
                    let uu____53537 = p_argTerm e2  in
                    FStar_Pprint.op_Hat_Slash_Hat uu____53529 uu____53537  in
                  FStar_Pprint.op_Hat_Slash_Hat uu____53527 uu____53528
              | uu____53538 ->
                  let uu____53545 =
                    let uu____53556 =
                      FStar_ST.op_Bang should_print_fs_typ_app  in
                    if uu____53556
                    then
                      let uu____53590 =
                        FStar_Util.take
                          (fun uu____53614  ->
                             match uu____53614 with
                             | (uu____53620,aq) ->
                                 aq = FStar_Parser_AST.FsTypApp) args
                         in
                      match uu____53590 with
                      | (fs_typ_args,args1) ->
                          let uu____53658 =
                            let uu____53659 = p_indexingTerm head1  in
                            let uu____53660 =
                              let uu____53661 =
                                FStar_Pprint.op_Hat_Hat FStar_Pprint.comma
                                  break1
                                 in
                              soft_surround_map_or_flow (Prims.parse_int "2")
                                (Prims.parse_int "0") FStar_Pprint.empty
                                FStar_Pprint.langle uu____53661
                                FStar_Pprint.rangle p_fsTypArg fs_typ_args
                               in
                            FStar_Pprint.op_Hat_Hat uu____53659 uu____53660
                             in
                          (uu____53658, args1)
                    else
                      (let uu____53676 = p_indexingTerm head1  in
                       (uu____53676, args))
                     in
                  (match uu____53545 with
                   | (head_doc,args1) ->
                       let uu____53697 =
                         let uu____53698 =
                           FStar_Pprint.op_Hat_Hat head_doc
                             FStar_Pprint.space
                            in
                         soft_surround_map_or_flow (Prims.parse_int "2")
                           (Prims.parse_int "0") head_doc uu____53698 break1
                           FStar_Pprint.empty p_argTerm args1
                          in
                       FStar_Pprint.group uu____53697)))
    | FStar_Parser_AST.Construct (lid,args) when
        (is_general_construction e) &&
          (let uu____53720 = is_dtuple_constructor lid  in
           Prims.op_Negation uu____53720)
        ->
        (match args with
         | [] -> p_quident lid
         | arg::[] ->
             let uu____53739 =
               let uu____53740 = p_quident lid  in
               let uu____53741 = p_argTerm arg  in
               FStar_Pprint.op_Hat_Slash_Hat uu____53740 uu____53741  in
             FStar_Pprint.group uu____53739
         | hd1::tl1 ->
             let uu____53758 =
               let uu____53759 =
                 let uu____53760 =
                   let uu____53761 = p_quident lid  in
                   let uu____53762 = p_argTerm hd1  in
                   prefix2 uu____53761 uu____53762  in
                 FStar_Pprint.group uu____53760  in
               let uu____53763 =
                 let uu____53764 =
                   FStar_Pprint.separate_map break1 p_argTerm tl1  in
                 jump2 uu____53764  in
               FStar_Pprint.op_Hat_Hat uu____53759 uu____53763  in
             FStar_Pprint.group uu____53758)
    | uu____53769 -> p_indexingTerm e

and (p_argTerm :
  (FStar_Parser_AST.term * FStar_Parser_AST.imp) -> FStar_Pprint.document) =
  fun arg_imp  ->
    match arg_imp with
    | (u,FStar_Parser_AST.UnivApp ) -> p_universe u
    | (e,FStar_Parser_AST.FsTypApp ) ->
        (FStar_Errors.log_issue e.FStar_Parser_AST.range
           (FStar_Errors.Warning_UnexpectedFsTypApp,
             "Unexpected FsTypApp, output might not be formatted correctly.");
         (let uu____53780 = p_indexingTerm e  in
          FStar_Pprint.surround (Prims.parse_int "2") (Prims.parse_int "1")
            FStar_Pprint.langle uu____53780 FStar_Pprint.rangle))
    | (e,FStar_Parser_AST.Hash ) ->
        let uu____53784 = str "#"  in
        let uu____53786 = p_indexingTerm e  in
        FStar_Pprint.op_Hat_Hat uu____53784 uu____53786
    | (e,FStar_Parser_AST.HashBrace t) ->
        let uu____53789 = str "#["  in
        let uu____53791 =
          let uu____53792 = p_indexingTerm t  in
          let uu____53793 =
            let uu____53794 = str "]"  in
            let uu____53796 = p_indexingTerm e  in
            FStar_Pprint.op_Hat_Hat uu____53794 uu____53796  in
          FStar_Pprint.op_Hat_Hat uu____53792 uu____53793  in
        FStar_Pprint.op_Hat_Hat uu____53789 uu____53791
    | (e,FStar_Parser_AST.Infix ) -> p_indexingTerm e
    | (e,FStar_Parser_AST.Nothing ) -> p_indexingTerm e

and (p_fsTypArg :
  (FStar_Parser_AST.term * FStar_Parser_AST.imp) -> FStar_Pprint.document) =
  fun uu____53799  ->
    match uu____53799 with | (e,uu____53805) -> p_indexingTerm e

and (p_indexingTerm_aux :
  (FStar_Parser_AST.term -> FStar_Pprint.document) ->
    FStar_Parser_AST.term -> FStar_Pprint.document)
  =
  fun exit1  ->
    fun e  ->
      match e.FStar_Parser_AST.tm with
      | FStar_Parser_AST.Op
          ({ FStar_Ident.idText = ".()"; FStar_Ident.idRange = uu____53810;_},e1::e2::[])
          ->
          let uu____53816 =
            let uu____53817 = p_indexingTerm_aux p_atomicTermNotQUident e1
               in
            let uu____53818 =
              let uu____53819 =
                let uu____53820 = p_term false false e2  in
                soft_parens_with_nesting uu____53820  in
              FStar_Pprint.op_Hat_Hat FStar_Pprint.dot uu____53819  in
            FStar_Pprint.op_Hat_Hat uu____53817 uu____53818  in
          FStar_Pprint.group uu____53816
      | FStar_Parser_AST.Op
          ({ FStar_Ident.idText = ".[]"; FStar_Ident.idRange = uu____53823;_},e1::e2::[])
          ->
          let uu____53829 =
            let uu____53830 = p_indexingTerm_aux p_atomicTermNotQUident e1
               in
            let uu____53831 =
              let uu____53832 =
                let uu____53833 = p_term false false e2  in
                soft_brackets_with_nesting uu____53833  in
              FStar_Pprint.op_Hat_Hat FStar_Pprint.dot uu____53832  in
            FStar_Pprint.op_Hat_Hat uu____53830 uu____53831  in
          FStar_Pprint.group uu____53829
      | uu____53836 -> exit1 e

and (p_indexingTerm : FStar_Parser_AST.term -> FStar_Pprint.document) =
  fun e  -> p_indexingTerm_aux p_atomicTerm e

and (p_atomicTerm : FStar_Parser_AST.term -> FStar_Pprint.document) =
  fun e  ->
    match e.FStar_Parser_AST.tm with
    | FStar_Parser_AST.LetOpen (lid,e1) ->
        let uu____53841 = p_quident lid  in
        let uu____53842 =
          let uu____53843 =
            let uu____53844 = p_term false false e1  in
            soft_parens_with_nesting uu____53844  in
          FStar_Pprint.op_Hat_Hat FStar_Pprint.dot uu____53843  in
        FStar_Pprint.op_Hat_Hat uu____53841 uu____53842
    | FStar_Parser_AST.Name lid -> p_quident lid
    | FStar_Parser_AST.Op (op,e1::[]) when is_general_prefix_op op ->
        let uu____53852 =
          let uu____53853 = FStar_Ident.text_of_id op  in str uu____53853  in
        let uu____53855 = p_atomicTerm e1  in
        FStar_Pprint.op_Hat_Hat uu____53852 uu____53855
    | uu____53856 -> p_atomicTermNotQUident e

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
         | uu____53869 -> p_constant c)
    | FStar_Parser_AST.Name lid when
        FStar_Ident.lid_equals lid FStar_Parser_Const.true_lid -> str "True"
    | FStar_Parser_AST.Name lid when
        FStar_Ident.lid_equals lid FStar_Parser_Const.false_lid ->
        str "False"
    | FStar_Parser_AST.Op (op,e1::[]) when is_general_prefix_op op ->
        let uu____53878 =
          let uu____53879 = FStar_Ident.text_of_id op  in str uu____53879  in
        let uu____53881 = p_atomicTermNotQUident e1  in
        FStar_Pprint.op_Hat_Hat uu____53878 uu____53881
    | FStar_Parser_AST.Op (op,[]) ->
        let uu____53885 =
          let uu____53886 =
            let uu____53887 =
              let uu____53888 = FStar_Ident.text_of_id op  in str uu____53888
               in
            let uu____53890 =
              FStar_Pprint.op_Hat_Hat FStar_Pprint.space FStar_Pprint.rparen
               in
            FStar_Pprint.op_Hat_Hat uu____53887 uu____53890  in
          FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____53886  in
        FStar_Pprint.op_Hat_Hat FStar_Pprint.lparen uu____53885
    | FStar_Parser_AST.Construct (lid,args) when is_dtuple_constructor lid ->
        let uu____53905 = all_explicit args  in
        if uu____53905
        then
          let uu____53908 =
            FStar_Pprint.op_Hat_Hat FStar_Pprint.lparen FStar_Pprint.bar  in
          let uu____53909 =
            let uu____53910 =
              FStar_Pprint.op_Hat_Hat FStar_Pprint.comma break1  in
            let uu____53911 = FStar_List.map FStar_Pervasives_Native.fst args
               in
            FStar_Pprint.separate_map uu____53910 p_tmEq uu____53911  in
          let uu____53918 =
            FStar_Pprint.op_Hat_Hat FStar_Pprint.bar FStar_Pprint.rparen  in
          FStar_Pprint.surround (Prims.parse_int "2") (Prims.parse_int "1")
            uu____53908 uu____53909 uu____53918
        else
          (match args with
           | [] -> p_quident lid
           | arg::[] ->
               let uu____53940 =
                 let uu____53941 = p_quident lid  in
                 let uu____53942 = p_argTerm arg  in
                 FStar_Pprint.op_Hat_Slash_Hat uu____53941 uu____53942  in
               FStar_Pprint.group uu____53940
           | hd1::tl1 ->
               let uu____53959 =
                 let uu____53960 =
                   let uu____53961 =
                     let uu____53962 = p_quident lid  in
                     let uu____53963 = p_argTerm hd1  in
                     prefix2 uu____53962 uu____53963  in
                   FStar_Pprint.group uu____53961  in
                 let uu____53964 =
                   let uu____53965 =
                     FStar_Pprint.separate_map break1 p_argTerm tl1  in
                   jump2 uu____53965  in
                 FStar_Pprint.op_Hat_Hat uu____53960 uu____53964  in
               FStar_Pprint.group uu____53959)
    | FStar_Parser_AST.Project (e1,lid) ->
        let uu____53972 =
          let uu____53973 = p_atomicTermNotQUident e1  in
          let uu____53974 =
            let uu____53975 = p_qlident lid  in
            FStar_Pprint.op_Hat_Hat FStar_Pprint.dot uu____53975  in
          FStar_Pprint.prefix (Prims.parse_int "2") (Prims.parse_int "0")
            uu____53973 uu____53974
           in
        FStar_Pprint.group uu____53972
    | uu____53978 -> p_projectionLHS e

and (p_projectionLHS : FStar_Parser_AST.term -> FStar_Pprint.document) =
  fun e  ->
    match e.FStar_Parser_AST.tm with
    | FStar_Parser_AST.Var lid -> p_qlident lid
    | FStar_Parser_AST.Projector (constr_lid,field_lid) ->
        let uu____53983 = p_quident constr_lid  in
        let uu____53984 =
          let uu____53985 =
            let uu____53986 = p_lident field_lid  in
            FStar_Pprint.op_Hat_Hat FStar_Pprint.dot uu____53986  in
          FStar_Pprint.op_Hat_Hat FStar_Pprint.qmark uu____53985  in
        FStar_Pprint.op_Hat_Hat uu____53983 uu____53984
    | FStar_Parser_AST.Discrim constr_lid ->
        let uu____53988 = p_quident constr_lid  in
        FStar_Pprint.op_Hat_Hat uu____53988 FStar_Pprint.qmark
    | FStar_Parser_AST.Paren e1 ->
        let uu____53990 = p_term_sep false false e1  in
        (match uu____53990 with
         | (comm,t) ->
             let doc1 = soft_parens_with_nesting t  in
             if comm = FStar_Pprint.empty
             then doc1
             else
               (let uu____54003 =
                  FStar_Pprint.op_Hat_Hat FStar_Pprint.hardline doc1  in
                FStar_Pprint.op_Hat_Hat comm uu____54003))
    | uu____54004 when is_array e ->
        let es = extract_from_list e  in
        let uu____54008 =
          FStar_Pprint.op_Hat_Hat FStar_Pprint.lbracket FStar_Pprint.bar  in
        let uu____54009 =
          let uu____54010 = FStar_Pprint.op_Hat_Hat FStar_Pprint.semi break1
             in
          separate_map_or_flow_last uu____54010
            (fun ps  -> p_noSeqTermAndComment ps false) es
           in
        let uu____54015 =
          FStar_Pprint.op_Hat_Hat FStar_Pprint.bar FStar_Pprint.rbracket  in
        FStar_Pprint.surround (Prims.parse_int "2") (Prims.parse_int "0")
          uu____54008 uu____54009 uu____54015
    | uu____54018 when is_list e ->
        let uu____54019 =
          let uu____54020 = FStar_Pprint.op_Hat_Hat FStar_Pprint.semi break1
             in
          let uu____54021 = extract_from_list e  in
          separate_map_or_flow_last uu____54020
            (fun ps  -> p_noSeqTermAndComment ps false) uu____54021
           in
        FStar_Pprint.surround (Prims.parse_int "2") (Prims.parse_int "0")
          FStar_Pprint.lbracket uu____54019 FStar_Pprint.rbracket
    | uu____54030 when is_lex_list e ->
        let uu____54031 =
          FStar_Pprint.op_Hat_Hat FStar_Pprint.percent FStar_Pprint.lbracket
           in
        let uu____54032 =
          let uu____54033 = FStar_Pprint.op_Hat_Hat FStar_Pprint.semi break1
             in
          let uu____54034 = extract_from_list e  in
          separate_map_or_flow_last uu____54033
            (fun ps  -> p_noSeqTermAndComment ps false) uu____54034
           in
        FStar_Pprint.surround (Prims.parse_int "2") (Prims.parse_int "1")
          uu____54031 uu____54032 FStar_Pprint.rbracket
    | uu____54043 when is_ref_set e ->
        let es = extract_from_ref_set e  in
        let uu____54047 =
          FStar_Pprint.op_Hat_Hat FStar_Pprint.bang FStar_Pprint.lbrace  in
        let uu____54048 =
          let uu____54049 = FStar_Pprint.op_Hat_Hat FStar_Pprint.comma break1
             in
          separate_map_or_flow uu____54049 p_appTerm es  in
        FStar_Pprint.surround (Prims.parse_int "2") (Prims.parse_int "0")
          uu____54047 uu____54048 FStar_Pprint.rbrace
    | FStar_Parser_AST.Labeled (e1,s,b) ->
        let uu____54059 = str (Prims.op_Hat "(*" (Prims.op_Hat s "*)"))  in
        let uu____54062 = p_term false false e1  in
        FStar_Pprint.op_Hat_Slash_Hat uu____54059 uu____54062
    | FStar_Parser_AST.Op (op,args) when
        let uu____54071 = handleable_op op args  in
        Prims.op_Negation uu____54071 ->
        let uu____54073 =
          let uu____54075 =
            let uu____54077 = FStar_Ident.text_of_id op  in
            let uu____54079 =
              let uu____54081 =
                let uu____54083 =
                  FStar_Util.string_of_int (FStar_List.length args)  in
                Prims.op_Hat uu____54083
                  " arguments couldn't be handled by the pretty printer"
                 in
              Prims.op_Hat " with " uu____54081  in
            Prims.op_Hat uu____54077 uu____54079  in
          Prims.op_Hat "Operation " uu____54075  in
        failwith uu____54073
    | FStar_Parser_AST.Uvar id1 ->
        failwith "Unexpected universe variable out of universe context"
    | FStar_Parser_AST.Wild  ->
        let uu____54090 = p_term false false e  in
        soft_parens_with_nesting uu____54090
    | FStar_Parser_AST.Const uu____54093 ->
        let uu____54094 = p_term false false e  in
        soft_parens_with_nesting uu____54094
    | FStar_Parser_AST.Op uu____54097 ->
        let uu____54104 = p_term false false e  in
        soft_parens_with_nesting uu____54104
    | FStar_Parser_AST.Tvar uu____54107 ->
        let uu____54108 = p_term false false e  in
        soft_parens_with_nesting uu____54108
    | FStar_Parser_AST.Var uu____54111 ->
        let uu____54112 = p_term false false e  in
        soft_parens_with_nesting uu____54112
    | FStar_Parser_AST.Name uu____54115 ->
        let uu____54116 = p_term false false e  in
        soft_parens_with_nesting uu____54116
    | FStar_Parser_AST.Construct uu____54119 ->
        let uu____54130 = p_term false false e  in
        soft_parens_with_nesting uu____54130
    | FStar_Parser_AST.Abs uu____54133 ->
        let uu____54140 = p_term false false e  in
        soft_parens_with_nesting uu____54140
    | FStar_Parser_AST.App uu____54143 ->
        let uu____54150 = p_term false false e  in
        soft_parens_with_nesting uu____54150
    | FStar_Parser_AST.Let uu____54153 ->
        let uu____54174 = p_term false false e  in
        soft_parens_with_nesting uu____54174
    | FStar_Parser_AST.LetOpen uu____54177 ->
        let uu____54182 = p_term false false e  in
        soft_parens_with_nesting uu____54182
    | FStar_Parser_AST.Seq uu____54185 ->
        let uu____54190 = p_term false false e  in
        soft_parens_with_nesting uu____54190
    | FStar_Parser_AST.Bind uu____54193 ->
        let uu____54200 = p_term false false e  in
        soft_parens_with_nesting uu____54200
    | FStar_Parser_AST.If uu____54203 ->
        let uu____54210 = p_term false false e  in
        soft_parens_with_nesting uu____54210
    | FStar_Parser_AST.Match uu____54213 ->
        let uu____54228 = p_term false false e  in
        soft_parens_with_nesting uu____54228
    | FStar_Parser_AST.TryWith uu____54231 ->
        let uu____54246 = p_term false false e  in
        soft_parens_with_nesting uu____54246
    | FStar_Parser_AST.Ascribed uu____54249 ->
        let uu____54258 = p_term false false e  in
        soft_parens_with_nesting uu____54258
    | FStar_Parser_AST.Record uu____54261 ->
        let uu____54274 = p_term false false e  in
        soft_parens_with_nesting uu____54274
    | FStar_Parser_AST.Project uu____54277 ->
        let uu____54282 = p_term false false e  in
        soft_parens_with_nesting uu____54282
    | FStar_Parser_AST.Product uu____54285 ->
        let uu____54292 = p_term false false e  in
        soft_parens_with_nesting uu____54292
    | FStar_Parser_AST.Sum uu____54295 ->
        let uu____54306 = p_term false false e  in
        soft_parens_with_nesting uu____54306
    | FStar_Parser_AST.QForall uu____54309 ->
        let uu____54322 = p_term false false e  in
        soft_parens_with_nesting uu____54322
    | FStar_Parser_AST.QExists uu____54325 ->
        let uu____54338 = p_term false false e  in
        soft_parens_with_nesting uu____54338
    | FStar_Parser_AST.Refine uu____54341 ->
        let uu____54346 = p_term false false e  in
        soft_parens_with_nesting uu____54346
    | FStar_Parser_AST.NamedTyp uu____54349 ->
        let uu____54354 = p_term false false e  in
        soft_parens_with_nesting uu____54354
    | FStar_Parser_AST.Requires uu____54357 ->
        let uu____54365 = p_term false false e  in
        soft_parens_with_nesting uu____54365
    | FStar_Parser_AST.Ensures uu____54368 ->
        let uu____54376 = p_term false false e  in
        soft_parens_with_nesting uu____54376
    | FStar_Parser_AST.Attributes uu____54379 ->
        let uu____54382 = p_term false false e  in
        soft_parens_with_nesting uu____54382
    | FStar_Parser_AST.Quote uu____54385 ->
        let uu____54390 = p_term false false e  in
        soft_parens_with_nesting uu____54390
    | FStar_Parser_AST.VQuote uu____54393 ->
        let uu____54394 = p_term false false e  in
        soft_parens_with_nesting uu____54394
    | FStar_Parser_AST.Antiquote uu____54397 ->
        let uu____54398 = p_term false false e  in
        soft_parens_with_nesting uu____54398
    | FStar_Parser_AST.CalcProof uu____54401 ->
        let uu____54410 = p_term false false e  in
        soft_parens_with_nesting uu____54410

and (p_constant : FStar_Const.sconst -> FStar_Pprint.document) =
  fun uu___339_54413  ->
    match uu___339_54413 with
    | FStar_Const.Const_effect  -> str "Effect"
    | FStar_Const.Const_unit  -> str "()"
    | FStar_Const.Const_bool b -> FStar_Pprint.doc_of_bool b
    | FStar_Const.Const_real r -> str (Prims.op_Hat r "R")
    | FStar_Const.Const_float x -> str (FStar_Util.string_of_float x)
    | FStar_Const.Const_char x -> FStar_Pprint.doc_of_char x
    | FStar_Const.Const_string (s,uu____54425) ->
        let uu____54428 = str (FStar_String.escaped s)  in
        FStar_Pprint.dquotes uu____54428
    | FStar_Const.Const_bytearray (bytes,uu____54430) ->
        let uu____54435 =
          let uu____54436 = str (FStar_Util.string_of_bytes bytes)  in
          FStar_Pprint.dquotes uu____54436  in
        let uu____54437 = str "B"  in
        FStar_Pprint.op_Hat_Hat uu____54435 uu____54437
    | FStar_Const.Const_int (repr,sign_width_opt) ->
        let signedness uu___337_54460 =
          match uu___337_54460 with
          | FStar_Const.Unsigned  -> str "u"
          | FStar_Const.Signed  -> FStar_Pprint.empty  in
        let width uu___338_54467 =
          match uu___338_54467 with
          | FStar_Const.Int8  -> str "y"
          | FStar_Const.Int16  -> str "s"
          | FStar_Const.Int32  -> str "l"
          | FStar_Const.Int64  -> str "L"  in
        let ending =
          default_or_map FStar_Pprint.empty
            (fun uu____54482  ->
               match uu____54482 with
               | (s,w) ->
                   let uu____54489 = signedness s  in
                   let uu____54490 = width w  in
                   FStar_Pprint.op_Hat_Hat uu____54489 uu____54490)
            sign_width_opt
           in
        let uu____54491 = str repr  in
        FStar_Pprint.op_Hat_Hat uu____54491 ending
    | FStar_Const.Const_range_of  -> str "range_of"
    | FStar_Const.Const_set_range_of  -> str "set_range_of"
    | FStar_Const.Const_range r ->
        let uu____54495 = FStar_Range.string_of_range r  in str uu____54495
    | FStar_Const.Const_reify  -> str "reify"
    | FStar_Const.Const_reflect lid ->
        let uu____54499 = p_quident lid  in
        let uu____54500 =
          let uu____54501 =
            let uu____54502 = str "reflect"  in
            FStar_Pprint.op_Hat_Hat FStar_Pprint.dot uu____54502  in
          FStar_Pprint.op_Hat_Hat FStar_Pprint.qmark uu____54501  in
        FStar_Pprint.op_Hat_Hat uu____54499 uu____54500

and (p_universe : FStar_Parser_AST.term -> FStar_Pprint.document) =
  fun u  ->
    let uu____54505 = str "u#"  in
    let uu____54507 = p_atomicUniverse u  in
    FStar_Pprint.op_Hat_Hat uu____54505 uu____54507

and (p_universeFrom : FStar_Parser_AST.term -> FStar_Pprint.document) =
  fun u  ->
    match u.FStar_Parser_AST.tm with
    | FStar_Parser_AST.Op
        ({ FStar_Ident.idText = "+"; FStar_Ident.idRange = uu____54509;_},u1::u2::[])
        ->
        let uu____54515 =
          let uu____54516 = p_universeFrom u1  in
          let uu____54517 =
            let uu____54518 = p_universeFrom u2  in
            FStar_Pprint.op_Hat_Slash_Hat FStar_Pprint.plus uu____54518  in
          FStar_Pprint.op_Hat_Slash_Hat uu____54516 uu____54517  in
        FStar_Pprint.group uu____54515
    | FStar_Parser_AST.App uu____54519 ->
        let uu____54526 = head_and_args u  in
        (match uu____54526 with
         | (head1,args) ->
             (match head1.FStar_Parser_AST.tm with
              | FStar_Parser_AST.Var maybe_max_lid when
                  FStar_Ident.lid_equals maybe_max_lid
                    FStar_Parser_Const.max_lid
                  ->
                  let uu____54552 =
                    let uu____54553 = p_qlident FStar_Parser_Const.max_lid
                       in
                    let uu____54554 =
                      FStar_Pprint.separate_map FStar_Pprint.space
                        (fun uu____54562  ->
                           match uu____54562 with
                           | (u1,uu____54568) -> p_atomicUniverse u1) args
                       in
                    op_Hat_Slash_Plus_Hat uu____54553 uu____54554  in
                  FStar_Pprint.group uu____54552
              | uu____54569 ->
                  let uu____54570 =
                    let uu____54572 = FStar_Parser_AST.term_to_string u  in
                    FStar_Util.format1 "Invalid term in universe context %s"
                      uu____54572
                     in
                  failwith uu____54570))
    | uu____54575 -> p_atomicUniverse u

and (p_atomicUniverse : FStar_Parser_AST.term -> FStar_Pprint.document) =
  fun u  ->
    match u.FStar_Parser_AST.tm with
    | FStar_Parser_AST.Wild  -> FStar_Pprint.underscore
    | FStar_Parser_AST.Const (FStar_Const.Const_int (r,sw)) ->
        p_constant (FStar_Const.Const_int (r, sw))
    | FStar_Parser_AST.Uvar id1 ->
        let uu____54601 = FStar_Ident.text_of_id id1  in str uu____54601
    | FStar_Parser_AST.Paren u1 ->
        let uu____54604 = p_universeFrom u1  in
        soft_parens_with_nesting uu____54604
    | FStar_Parser_AST.Op
        ({ FStar_Ident.idText = "+"; FStar_Ident.idRange = uu____54605;_},uu____54606::uu____54607::[])
        ->
        let uu____54611 = p_universeFrom u  in
        soft_parens_with_nesting uu____54611
    | FStar_Parser_AST.App uu____54612 ->
        let uu____54619 = p_universeFrom u  in
        soft_parens_with_nesting uu____54619
    | uu____54620 ->
        let uu____54621 =
          let uu____54623 = FStar_Parser_AST.term_to_string u  in
          FStar_Util.format1 "Invalid term in universe context %s"
            uu____54623
           in
        failwith uu____54621

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
       | FStar_Parser_AST.Module (uu____54712,decls) ->
           let uu____54718 =
             FStar_All.pipe_right decls (FStar_List.map decl_to_document)  in
           FStar_All.pipe_right uu____54718
             (FStar_Pprint.separate FStar_Pprint.hardline)
       | FStar_Parser_AST.Interface (uu____54727,decls,uu____54729) ->
           let uu____54736 =
             FStar_All.pipe_right decls (FStar_List.map decl_to_document)  in
           FStar_All.pipe_right uu____54736
             (FStar_Pprint.separate FStar_Pprint.hardline)
        in
     FStar_ST.op_Colon_Equals should_print_fs_typ_app false; res)
  
let (comments_to_document :
  (Prims.string * FStar_Range.range) Prims.list -> FStar_Pprint.document) =
  fun comments  ->
    FStar_Pprint.separate_map FStar_Pprint.hardline
      (fun uu____54796  ->
         match uu____54796 with | (comment,range) -> str comment) comments
  
let (extract_decl_range : FStar_Parser_AST.decl -> decl_meta) =
  fun d  ->
    let has_qs =
      match ((d.FStar_Parser_AST.quals), (d.FStar_Parser_AST.d)) with
      | ((FStar_Parser_AST.Assumption )::[],FStar_Parser_AST.Assume
         (id1,uu____54818)) -> false
      | ([],uu____54822) -> false
      | uu____54826 -> true  in
    {
      r = (d.FStar_Parser_AST.drange);
      has_qs;
      has_attrs =
        (Prims.op_Negation (FStar_List.isEmpty d.FStar_Parser_AST.attrs));
      has_fsdoc = (FStar_Util.is_some d.FStar_Parser_AST.doc);
      is_fsdoc =
        (match d.FStar_Parser_AST.d with
         | FStar_Parser_AST.Fsdoc uu____54836 -> true
         | uu____54838 -> false)
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
        | FStar_Parser_AST.Module (uu____54881,decls) -> decls
        | FStar_Parser_AST.Interface (uu____54887,decls,uu____54889) -> decls
         in
      FStar_ST.op_Colon_Equals should_print_fs_typ_app false;
      (match decls with
       | [] -> (FStar_Pprint.empty, comments)
       | d::ds ->
           let uu____54941 =
             match ds with
             | {
                 FStar_Parser_AST.d = FStar_Parser_AST.Pragma
                   (FStar_Parser_AST.LightOff );
                 FStar_Parser_AST.drange = uu____54954;
                 FStar_Parser_AST.doc = uu____54955;
                 FStar_Parser_AST.quals = uu____54956;
                 FStar_Parser_AST.attrs = uu____54957;_}::uu____54958 ->
                 let d0 = FStar_List.hd ds  in
                 let uu____54964 =
                   let uu____54967 =
                     let uu____54970 = FStar_List.tl ds  in d :: uu____54970
                      in
                   d0 :: uu____54967  in
                 (uu____54964, (d0.FStar_Parser_AST.drange))
             | uu____54975 -> ((d :: ds), (d.FStar_Parser_AST.drange))  in
           (match uu____54941 with
            | (decls1,first_range) ->
                (FStar_ST.op_Colon_Equals comment_stack comments;
                 (let initial_comment =
                    let uu____55032 = FStar_Range.start_of_range first_range
                       in
                    place_comments_until_pos (Prims.parse_int "0")
                      (Prims.parse_int "1") uu____55032 dummy_meta
                      FStar_Pprint.empty false true
                     in
                  let doc1 =
                    separate_map_with_comments FStar_Pprint.empty
                      FStar_Pprint.empty p_decl decls1 extract_decl_range
                     in
                  let comments1 = FStar_ST.op_Bang comment_stack  in
                  FStar_ST.op_Colon_Equals comment_stack [];
                  FStar_ST.op_Colon_Equals should_print_fs_typ_app false;
                  (let uu____55141 =
                     FStar_Pprint.op_Hat_Hat initial_comment doc1  in
                   (uu____55141, comments1))))))
  