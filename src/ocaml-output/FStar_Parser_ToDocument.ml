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
            let uu____43265 = let uu____43268 = f x  in uu____43268 :: acc
               in
            aux xs uu____43265
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
            let uu____43335 = f x  in
            (match uu____43335 with
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
          let uu____43391 = f x  in if uu____43391 then all f xs else false
  
let (all_explicit :
  (FStar_Parser_AST.term * FStar_Parser_AST.imp) Prims.list -> Prims.bool) =
  fun args  ->
    FStar_Util.for_all
      (fun uu___324_43424  ->
         match uu___324_43424 with
         | (uu____43430,FStar_Parser_AST.Nothing ) -> true
         | uu____43432 -> false) args
  
let (should_print_fs_typ_app : Prims.bool FStar_ST.ref) =
  FStar_Util.mk_ref false 
let (unfold_tuples : Prims.bool FStar_ST.ref) = FStar_Util.mk_ref true 
let with_fs_typ_app :
  'Auu____43483 'Auu____43484 .
    Prims.bool ->
      ('Auu____43483 -> 'Auu____43484) -> 'Auu____43483 -> 'Auu____43484
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
  'Auu____43594 'Auu____43595 .
    'Auu____43594 ->
      ('Auu____43595 -> 'Auu____43594) ->
        'Auu____43595 FStar_Pervasives_Native.option -> 'Auu____43594
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
  'Auu____43708 .
    FStar_Pprint.document ->
      ('Auu____43708 -> FStar_Pprint.document) ->
        'Auu____43708 Prims.list -> FStar_Pprint.document
  =
  fun sep  ->
    fun f  ->
      fun l  ->
        let uu____43733 =
          let uu____43734 =
            let uu____43735 = FStar_Pprint.op_Hat_Hat sep break1  in
            FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____43735  in
          FStar_Pprint.separate_map uu____43734 f l  in
        FStar_Pprint.group uu____43733
  
let precede_break_separate_map :
  'Auu____43747 .
    FStar_Pprint.document ->
      FStar_Pprint.document ->
        ('Auu____43747 -> FStar_Pprint.document) ->
          'Auu____43747 Prims.list -> FStar_Pprint.document
  =
  fun prec  ->
    fun sep  ->
      fun f  ->
        fun l  ->
          let uu____43777 =
            let uu____43778 = FStar_Pprint.op_Hat_Hat prec FStar_Pprint.space
               in
            let uu____43779 =
              let uu____43780 = FStar_List.hd l  in
              FStar_All.pipe_right uu____43780 f  in
            FStar_Pprint.precede uu____43778 uu____43779  in
          let uu____43781 =
            let uu____43782 = FStar_List.tl l  in
            FStar_Pprint.concat_map
              (fun x  ->
                 let uu____43788 =
                   let uu____43789 =
                     let uu____43790 = f x  in
                     FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____43790
                      in
                   FStar_Pprint.op_Hat_Hat sep uu____43789  in
                 FStar_Pprint.op_Hat_Hat break1 uu____43788) uu____43782
             in
          FStar_Pprint.op_Hat_Hat uu____43777 uu____43781
  
let concat_break_map :
  'Auu____43798 .
    ('Auu____43798 -> FStar_Pprint.document) ->
      'Auu____43798 Prims.list -> FStar_Pprint.document
  =
  fun f  ->
    fun l  ->
      let uu____43818 =
        FStar_Pprint.concat_map
          (fun x  ->
             let uu____43822 = f x  in
             FStar_Pprint.op_Hat_Hat uu____43822 break1) l
         in
      FStar_Pprint.group uu____43818
  
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
    let uu____43885 = str "begin"  in
    let uu____43887 = str "end"  in
    FStar_Pprint.soft_surround (Prims.parse_int "2") (Prims.parse_int "1")
      uu____43885 contents uu____43887
  
let separate_map_last :
  'Auu____43900 .
    FStar_Pprint.document ->
      (Prims.bool -> 'Auu____43900 -> FStar_Pprint.document) ->
        'Auu____43900 Prims.list -> FStar_Pprint.document
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
  'Auu____43958 .
    FStar_Pprint.document ->
      (Prims.bool -> 'Auu____43958 -> FStar_Pprint.document) ->
        'Auu____43958 Prims.list -> FStar_Pprint.document
  =
  fun sep  ->
    fun f  ->
      fun l  ->
        let uu____43990 =
          let uu____43991 =
            let uu____43992 = FStar_Pprint.op_Hat_Hat sep break1  in
            FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____43992  in
          separate_map_last uu____43991 f l  in
        FStar_Pprint.group uu____43990
  
let separate_map_or_flow :
  'Auu____44002 .
    FStar_Pprint.document ->
      ('Auu____44002 -> FStar_Pprint.document) ->
        'Auu____44002 Prims.list -> FStar_Pprint.document
  =
  fun sep  ->
    fun f  ->
      fun l  ->
        if (FStar_List.length l) < (Prims.parse_int "10")
        then FStar_Pprint.separate_map sep f l
        else FStar_Pprint.flow_map sep f l
  
let flow_map_last :
  'Auu____44040 .
    FStar_Pprint.document ->
      (Prims.bool -> 'Auu____44040 -> FStar_Pprint.document) ->
        'Auu____44040 Prims.list -> FStar_Pprint.document
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
  'Auu____44098 .
    FStar_Pprint.document ->
      (Prims.bool -> 'Auu____44098 -> FStar_Pprint.document) ->
        'Auu____44098 Prims.list -> FStar_Pprint.document
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
              let uu____44180 = FStar_Pprint.op_Hat_Slash_Hat doc1 doc3  in
              FStar_Pprint.group uu____44180
            else FStar_Pprint.surround n1 b doc1 doc2 doc3
  
let soft_surround_separate_map :
  'Auu____44202 .
    Prims.int ->
      Prims.int ->
        FStar_Pprint.document ->
          FStar_Pprint.document ->
            FStar_Pprint.document ->
              FStar_Pprint.document ->
                ('Auu____44202 -> FStar_Pprint.document) ->
                  'Auu____44202 Prims.list -> FStar_Pprint.document
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
                    (let uu____44261 = FStar_Pprint.separate_map sep f xs  in
                     FStar_Pprint.soft_surround n1 b opening uu____44261
                       closing)
  
let soft_surround_map_or_flow :
  'Auu____44281 .
    Prims.int ->
      Prims.int ->
        FStar_Pprint.document ->
          FStar_Pprint.document ->
            FStar_Pprint.document ->
              FStar_Pprint.document ->
                ('Auu____44281 -> FStar_Pprint.document) ->
                  'Auu____44281 Prims.list -> FStar_Pprint.document
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
                    (let uu____44340 = separate_map_or_flow sep f xs  in
                     FStar_Pprint.soft_surround n1 b opening uu____44340
                       closing)
  
let (doc_of_fsdoc :
  (Prims.string * (Prims.string * Prims.string) Prims.list) ->
    FStar_Pprint.document)
  =
  fun uu____44359  ->
    match uu____44359 with
    | (comment,keywords) ->
        let uu____44393 =
          let uu____44394 =
            let uu____44397 = str comment  in
            let uu____44398 =
              let uu____44401 =
                let uu____44404 =
                  FStar_Pprint.separate_map FStar_Pprint.comma
                    (fun uu____44415  ->
                       match uu____44415 with
                       | (k,v1) ->
                           let uu____44428 =
                             let uu____44431 = str k  in
                             let uu____44432 =
                               let uu____44435 =
                                 let uu____44438 = str v1  in [uu____44438]
                                  in
                               FStar_Pprint.rarrow :: uu____44435  in
                             uu____44431 :: uu____44432  in
                           FStar_Pprint.concat uu____44428) keywords
                   in
                [uu____44404]  in
              FStar_Pprint.space :: uu____44401  in
            uu____44397 :: uu____44398  in
          FStar_Pprint.concat uu____44394  in
        FStar_Pprint.group uu____44393
  
let (is_unit : FStar_Parser_AST.term -> Prims.bool) =
  fun e  ->
    match e.FStar_Parser_AST.tm with
    | FStar_Parser_AST.Const (FStar_Const.Const_unit ) -> true
    | uu____44448 -> false
  
let (matches_var : FStar_Parser_AST.term -> FStar_Ident.ident -> Prims.bool)
  =
  fun t  ->
    fun x  ->
      match t.FStar_Parser_AST.tm with
      | FStar_Parser_AST.Var y ->
          let uu____44464 = FStar_Ident.text_of_lid y  in
          x.FStar_Ident.idText = uu____44464
      | uu____44467 -> false
  
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
        | FStar_Parser_AST.Construct (lid,uu____44518::(e2,uu____44520)::[])
            -> (FStar_Ident.lid_equals lid cons_lid1) && (aux e2)
        | uu____44543 -> false  in
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
    | FStar_Parser_AST.Construct (uu____44567,[]) -> []
    | FStar_Parser_AST.Construct
        (uu____44578,(e1,FStar_Parser_AST.Nothing )::(e2,FStar_Parser_AST.Nothing
                                                      )::[])
        -> let uu____44599 = extract_from_list e2  in e1 :: uu____44599
    | uu____44602 ->
        let uu____44603 =
          let uu____44605 = FStar_Parser_AST.term_to_string e  in
          FStar_Util.format1 "Not a list %s" uu____44605  in
        failwith uu____44603
  
let (is_array : FStar_Parser_AST.term -> Prims.bool) =
  fun e  ->
    match e.FStar_Parser_AST.tm with
    | FStar_Parser_AST.App
        ({ FStar_Parser_AST.tm = FStar_Parser_AST.Var lid;
           FStar_Parser_AST.range = uu____44619;
           FStar_Parser_AST.level = uu____44620;_},l,FStar_Parser_AST.Nothing
         )
        ->
        (FStar_Ident.lid_equals lid FStar_Parser_Const.array_mk_array_lid) &&
          (is_list l)
    | uu____44622 -> false
  
let rec (is_ref_set : FStar_Parser_AST.term -> Prims.bool) =
  fun e  ->
    match e.FStar_Parser_AST.tm with
    | FStar_Parser_AST.Var maybe_empty_lid ->
        FStar_Ident.lid_equals maybe_empty_lid FStar_Parser_Const.set_empty
    | FStar_Parser_AST.App
        ({ FStar_Parser_AST.tm = FStar_Parser_AST.Var maybe_singleton_lid;
           FStar_Parser_AST.range = uu____44634;
           FStar_Parser_AST.level = uu____44635;_},{
                                                     FStar_Parser_AST.tm =
                                                       FStar_Parser_AST.App
                                                       ({
                                                          FStar_Parser_AST.tm
                                                            =
                                                            FStar_Parser_AST.Var
                                                            maybe_addr_of_lid;
                                                          FStar_Parser_AST.range
                                                            = uu____44637;
                                                          FStar_Parser_AST.level
                                                            = uu____44638;_},e1,FStar_Parser_AST.Nothing
                                                        );
                                                     FStar_Parser_AST.range =
                                                       uu____44640;
                                                     FStar_Parser_AST.level =
                                                       uu____44641;_},FStar_Parser_AST.Nothing
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
                FStar_Parser_AST.range = uu____44643;
                FStar_Parser_AST.level = uu____44644;_},e1,FStar_Parser_AST.Nothing
              );
           FStar_Parser_AST.range = uu____44646;
           FStar_Parser_AST.level = uu____44647;_},e2,FStar_Parser_AST.Nothing
         )
        ->
        ((FStar_Ident.lid_equals maybe_union_lid FStar_Parser_Const.set_union)
           && (is_ref_set e1))
          && (is_ref_set e2)
    | uu____44649 -> false
  
let rec (extract_from_ref_set :
  FStar_Parser_AST.term -> FStar_Parser_AST.term Prims.list) =
  fun e  ->
    match e.FStar_Parser_AST.tm with
    | FStar_Parser_AST.Var uu____44661 -> []
    | FStar_Parser_AST.App
        ({ FStar_Parser_AST.tm = FStar_Parser_AST.Var uu____44662;
           FStar_Parser_AST.range = uu____44663;
           FStar_Parser_AST.level = uu____44664;_},{
                                                     FStar_Parser_AST.tm =
                                                       FStar_Parser_AST.App
                                                       ({
                                                          FStar_Parser_AST.tm
                                                            =
                                                            FStar_Parser_AST.Var
                                                            uu____44665;
                                                          FStar_Parser_AST.range
                                                            = uu____44666;
                                                          FStar_Parser_AST.level
                                                            = uu____44667;_},e1,FStar_Parser_AST.Nothing
                                                        );
                                                     FStar_Parser_AST.range =
                                                       uu____44669;
                                                     FStar_Parser_AST.level =
                                                       uu____44670;_},FStar_Parser_AST.Nothing
         )
        -> [e1]
    | FStar_Parser_AST.App
        ({
           FStar_Parser_AST.tm = FStar_Parser_AST.App
             ({ FStar_Parser_AST.tm = FStar_Parser_AST.Var uu____44671;
                FStar_Parser_AST.range = uu____44672;
                FStar_Parser_AST.level = uu____44673;_},e1,FStar_Parser_AST.Nothing
              );
           FStar_Parser_AST.range = uu____44675;
           FStar_Parser_AST.level = uu____44676;_},e2,FStar_Parser_AST.Nothing
         )
        ->
        let uu____44678 = extract_from_ref_set e1  in
        let uu____44681 = extract_from_ref_set e2  in
        FStar_List.append uu____44678 uu____44681
    | uu____44684 ->
        let uu____44685 =
          let uu____44687 = FStar_Parser_AST.term_to_string e  in
          FStar_Util.format1 "Not a ref set %s" uu____44687  in
        failwith uu____44685
  
let (is_general_application : FStar_Parser_AST.term -> Prims.bool) =
  fun e  ->
    let uu____44699 = (is_array e) || (is_ref_set e)  in
    Prims.op_Negation uu____44699
  
let (is_general_construction : FStar_Parser_AST.term -> Prims.bool) =
  fun e  ->
    let uu____44708 = (is_list e) || (is_lex_list e)  in
    Prims.op_Negation uu____44708
  
let (is_general_prefix_op : FStar_Ident.ident -> Prims.bool) =
  fun op  ->
    let op_starting_char =
      let uu____44719 = FStar_Ident.text_of_id op  in
      FStar_Util.char_at uu____44719 (Prims.parse_int "0")  in
    ((op_starting_char = 33) || (op_starting_char = 63)) ||
      ((op_starting_char = 126) &&
         (let uu____44729 = FStar_Ident.text_of_id op  in uu____44729 <> "~"))
  
let (head_and_args :
  FStar_Parser_AST.term ->
    (FStar_Parser_AST.term * (FStar_Parser_AST.term * FStar_Parser_AST.imp)
      Prims.list))
  =
  fun e  ->
    let rec aux e1 acc =
      match e1.FStar_Parser_AST.tm with
      | FStar_Parser_AST.App (head1,arg,imp) -> aux head1 ((arg, imp) :: acc)
      | uu____44799 -> (e1, acc)  in
    aux e []
  
type associativity =
  | Left 
  | Right 
  | NonAssoc 
let (uu___is_Left : associativity -> Prims.bool) =
  fun projectee  ->
    match projectee with | Left  -> true | uu____44819 -> false
  
let (uu___is_Right : associativity -> Prims.bool) =
  fun projectee  ->
    match projectee with | Right  -> true | uu____44830 -> false
  
let (uu___is_NonAssoc : associativity -> Prims.bool) =
  fun projectee  ->
    match projectee with | NonAssoc  -> true | uu____44841 -> false
  
type token = (FStar_Char.char,Prims.string) FStar_Util.either
type associativity_level = (associativity * token Prims.list)
let (token_to_string :
  (FStar_BaseTypes.char,Prims.string) FStar_Util.either -> Prims.string) =
  fun uu___325_44867  ->
    match uu___325_44867 with
    | FStar_Util.Inl c -> Prims.op_Hat (FStar_Util.string_of_char c) ".*"
    | FStar_Util.Inr s -> s
  
let (matches_token :
  Prims.string ->
    (FStar_Char.char,Prims.string) FStar_Util.either -> Prims.bool)
  =
  fun s  ->
    fun uu___326_44902  ->
      match uu___326_44902 with
      | FStar_Util.Inl c ->
          let uu____44915 = FStar_String.get s (Prims.parse_int "0")  in
          uu____44915 = c
      | FStar_Util.Inr s' -> s = s'
  
let matches_level :
  'Auu____44931 .
    Prims.string ->
      ('Auu____44931 * (FStar_Char.char,Prims.string) FStar_Util.either
        Prims.list) -> Prims.bool
  =
  fun s  ->
    fun uu____44955  ->
      match uu____44955 with
      | (assoc_levels,tokens) ->
          let uu____44987 = FStar_List.tryFind (matches_token s) tokens  in
          uu____44987 <> FStar_Pervasives_Native.None
  
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
  let levels_from_associativity l uu___327_45159 =
    match uu___327_45159 with
    | Left  -> (l, l, (l - (Prims.parse_int "1")))
    | Right  -> ((l - (Prims.parse_int "1")), l, l)
    | NonAssoc  ->
        ((l - (Prims.parse_int "1")), l, (l - (Prims.parse_int "1")))
     in
  FStar_List.mapi
    (fun i  ->
       fun uu____45209  ->
         match uu____45209 with
         | (assoc1,tokens) -> ((levels_from_associativity i assoc1), tokens))
    level_associativity_spec
  
let (assign_levels :
  associativity_level Prims.list ->
    Prims.string -> (Prims.int * Prims.int * Prims.int))
  =
  fun token_associativity_spec  ->
    fun s  ->
      let uu____45284 = FStar_List.tryFind (matches_level s) level_table  in
      match uu____45284 with
      | FStar_Pervasives_Native.Some (assoc_levels,uu____45336) ->
          assoc_levels
      | uu____45374 -> failwith (Prims.op_Hat "Unrecognized operator " s)
  
let max_level :
  'Auu____45407 . ('Auu____45407 * token Prims.list) Prims.list -> Prims.int
  =
  fun l  ->
    let find_level_and_max n1 level =
      let uu____45456 =
        FStar_List.tryFind
          (fun uu____45492  ->
             match uu____45492 with
             | (uu____45509,tokens) ->
                 tokens = (FStar_Pervasives_Native.snd level)) level_table
         in
      match uu____45456 with
      | FStar_Pervasives_Native.Some
          ((uu____45538,l1,uu____45540),uu____45541) -> max n1 l1
      | FStar_Pervasives_Native.None  ->
          let uu____45591 =
            let uu____45593 =
              let uu____45595 =
                FStar_List.map token_to_string
                  (FStar_Pervasives_Native.snd level)
                 in
              FStar_String.concat "," uu____45595  in
            FStar_Util.format1 "Undefined associativity level %s" uu____45593
             in
          failwith uu____45591
       in
    FStar_List.fold_left find_level_and_max (Prims.parse_int "0") l
  
let (levels : Prims.string -> (Prims.int * Prims.int * Prims.int)) =
  fun op  ->
    let uu____45630 = assign_levels level_associativity_spec op  in
    match uu____45630 with
    | (left1,mine,right1) ->
        if op = "*"
        then ((left1 - (Prims.parse_int "1")), mine, right1)
        else (left1, mine, right1)
  
let (operatorInfix0ad12 : associativity_level Prims.list) =
  [opinfix0a; opinfix0b; opinfix0c; opinfix0d; opinfix1; opinfix2] 
let (is_operatorInfix0ad12 : FStar_Ident.ident -> Prims.bool) =
  fun op  ->
    let uu____45689 =
      let uu____45692 =
        let uu____45698 = FStar_Ident.text_of_id op  in
        FStar_All.pipe_left matches_level uu____45698  in
      FStar_List.tryFind uu____45692 operatorInfix0ad12  in
    uu____45689 <> FStar_Pervasives_Native.None
  
let (is_operatorInfix34 : FStar_Ident.ident -> Prims.bool) =
  let opinfix34 = [opinfix3; opinfix4]  in
  fun op  ->
    let uu____45765 =
      let uu____45780 =
        let uu____45798 = FStar_Ident.text_of_id op  in
        FStar_All.pipe_left matches_level uu____45798  in
      FStar_List.tryFind uu____45780 opinfix34  in
    uu____45765 <> FStar_Pervasives_Native.None
  
let (handleable_args_length : FStar_Ident.ident -> Prims.int) =
  fun op  ->
    let op_s = FStar_Ident.text_of_id op  in
    let uu____45864 =
      (is_general_prefix_op op) || (FStar_List.mem op_s ["-"; "~"])  in
    if uu____45864
    then (Prims.parse_int "1")
    else
      (let uu____45877 =
         ((is_operatorInfix0ad12 op) || (is_operatorInfix34 op)) ||
           (FStar_List.mem op_s
              ["<==>"; "==>"; "\\/"; "/\\"; "="; "|>"; ":="; ".()"; ".[]"])
          in
       if uu____45877
       then (Prims.parse_int "2")
       else
         if FStar_List.mem op_s [".()<-"; ".[]<-"]
         then (Prims.parse_int "3")
         else (Prims.parse_int "0"))
  
let handleable_op :
  'Auu____45923 . FStar_Ident.ident -> 'Auu____45923 Prims.list -> Prims.bool
  =
  fun op  ->
    fun args  ->
      match FStar_List.length args with
      | _45939 when _45939 = (Prims.parse_int "0") -> true
      | _45941 when _45941 = (Prims.parse_int "1") ->
          (is_general_prefix_op op) ||
            (let uu____45943 = FStar_Ident.text_of_id op  in
             FStar_List.mem uu____45943 ["-"; "~"])
      | _45951 when _45951 = (Prims.parse_int "2") ->
          ((is_operatorInfix0ad12 op) || (is_operatorInfix34 op)) ||
            (let uu____45953 = FStar_Ident.text_of_id op  in
             FStar_List.mem uu____45953
               ["<==>"; "==>"; "\\/"; "/\\"; "="; "|>"; ":="; ".()"; ".[]"])
      | _45975 when _45975 = (Prims.parse_int "3") ->
          let uu____45976 = FStar_Ident.text_of_id op  in
          FStar_List.mem uu____45976 [".()<-"; ".[]<-"]
      | uu____45984 -> false
  
type annotation_style =
  | Binders of (Prims.int * Prims.int * Prims.bool) 
  | Arrows of (Prims.int * Prims.int) 
let (uu___is_Binders : annotation_style -> Prims.bool) =
  fun projectee  ->
    match projectee with | Binders _0 -> true | uu____46030 -> false
  
let (__proj__Binders__item___0 :
  annotation_style -> (Prims.int * Prims.int * Prims.bool)) =
  fun projectee  -> match projectee with | Binders _0 -> _0 
let (uu___is_Arrows : annotation_style -> Prims.bool) =
  fun projectee  ->
    match projectee with | Arrows _0 -> true | uu____46083 -> false
  
let (__proj__Arrows__item___0 : annotation_style -> (Prims.int * Prims.int))
  = fun projectee  -> match projectee with | Arrows _0 -> _0 
let (all_binders_annot : FStar_Parser_AST.term -> Prims.bool) =
  fun e  ->
    let is_binder_annot b =
      match b.FStar_Parser_AST.b with
      | FStar_Parser_AST.Annotated uu____46126 -> true
      | uu____46132 -> false  in
    let rec all_binders e1 l =
      match e1.FStar_Parser_AST.tm with
      | FStar_Parser_AST.Product (bs,tgt) ->
          let uu____46165 = FStar_List.for_all is_binder_annot bs  in
          if uu____46165
          then all_binders tgt (l + (FStar_List.length bs))
          else (false, (Prims.parse_int "0"))
      | uu____46180 -> (true, (l + (Prims.parse_int "1")))  in
    let uu____46185 = all_binders e (Prims.parse_int "0")  in
    match uu____46185 with
    | (b,l) -> if b && (l > (Prims.parse_int "1")) then true else false
  
type catf =
  FStar_Pprint.document -> FStar_Pprint.document -> FStar_Pprint.document
let (cat_with_colon :
  FStar_Pprint.document -> FStar_Pprint.document -> FStar_Pprint.document) =
  fun x  ->
    fun y  ->
      let uu____46224 = FStar_Pprint.op_Hat_Slash_Hat FStar_Pprint.colon y
         in
      FStar_Pprint.op_Hat_Hat x uu____46224
  
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
  'Auu____46384 .
    ('Auu____46384 -> FStar_Pprint.document) ->
      'Auu____46384 -> FStar_Range.range -> FStar_Pprint.document
  =
  fun printer  ->
    fun tm  ->
      fun tmrange  ->
        let rec comments_before_pos acc print_pos lookahead_pos =
          let uu____46426 = FStar_ST.op_Bang comment_stack  in
          match uu____46426 with
          | [] -> (acc, false)
          | (c,crange)::cs ->
              let comment =
                let uu____46497 = str c  in
                FStar_Pprint.op_Hat_Hat uu____46497 FStar_Pprint.hardline  in
              let uu____46498 = FStar_Range.range_before_pos crange print_pos
                 in
              if uu____46498
              then
                (FStar_ST.op_Colon_Equals comment_stack cs;
                 (let uu____46540 = FStar_Pprint.op_Hat_Hat acc comment  in
                  comments_before_pos uu____46540 print_pos lookahead_pos))
              else
                (let uu____46543 =
                   FStar_Range.range_before_pos crange lookahead_pos  in
                 (acc, uu____46543))
           in
        let uu____46546 =
          let uu____46552 =
            let uu____46553 = FStar_Range.start_of_range tmrange  in
            FStar_Range.end_of_line uu____46553  in
          let uu____46554 = FStar_Range.end_of_range tmrange  in
          comments_before_pos FStar_Pprint.empty uu____46552 uu____46554  in
        match uu____46546 with
        | (comments,has_lookahead) ->
            let printed_e = printer tm  in
            let comments1 =
              if has_lookahead
              then
                let pos = FStar_Range.end_of_range tmrange  in
                let uu____46563 = comments_before_pos comments pos pos  in
                FStar_Pervasives_Native.fst uu____46563
              else comments  in
            if comments1 = FStar_Pprint.empty
            then printed_e
            else
              (let uu____46575 = FStar_Pprint.op_Hat_Hat comments1 printed_e
                  in
               FStar_Pprint.group uu____46575)
  
let with_comment_sep :
  'Auu____46587 'Auu____46588 .
    ('Auu____46587 -> 'Auu____46588) ->
      'Auu____46587 ->
        FStar_Range.range -> (FStar_Pprint.document * 'Auu____46588)
  =
  fun printer  ->
    fun tm  ->
      fun tmrange  ->
        let rec comments_before_pos acc print_pos lookahead_pos =
          let uu____46634 = FStar_ST.op_Bang comment_stack  in
          match uu____46634 with
          | [] -> (acc, false)
          | (c,crange)::cs ->
              let comment = str c  in
              let uu____46705 = FStar_Range.range_before_pos crange print_pos
                 in
              if uu____46705
              then
                (FStar_ST.op_Colon_Equals comment_stack cs;
                 (let uu____46747 =
                    if acc = FStar_Pprint.empty
                    then comment
                    else
                      (let uu____46751 =
                         FStar_Pprint.op_Hat_Hat FStar_Pprint.hardline
                           comment
                          in
                       FStar_Pprint.op_Hat_Hat acc uu____46751)
                     in
                  comments_before_pos uu____46747 print_pos lookahead_pos))
              else
                (let uu____46754 =
                   FStar_Range.range_before_pos crange lookahead_pos  in
                 (acc, uu____46754))
           in
        let uu____46757 =
          let uu____46763 =
            let uu____46764 = FStar_Range.start_of_range tmrange  in
            FStar_Range.end_of_line uu____46764  in
          let uu____46765 = FStar_Range.end_of_range tmrange  in
          comments_before_pos FStar_Pprint.empty uu____46763 uu____46765  in
        match uu____46757 with
        | (comments,has_lookahead) ->
            let printed_e = printer tm  in
            let comments1 =
              if has_lookahead
              then
                let pos = FStar_Range.end_of_range tmrange  in
                let uu____46778 = comments_before_pos comments pos pos  in
                FStar_Pervasives_Native.fst uu____46778
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
                let uu____46831 = FStar_ST.op_Bang comment_stack  in
                match uu____46831 with
                | (comment,crange)::cs when
                    FStar_Range.range_before_pos crange pos ->
                    (FStar_ST.op_Colon_Equals comment_stack cs;
                     (let lnum =
                        let uu____46925 =
                          let uu____46927 =
                            let uu____46929 =
                              FStar_Range.start_of_range crange  in
                            FStar_Range.line_of_pos uu____46929  in
                          uu____46927 - lbegin  in
                        max k uu____46925  in
                      let lnum1 = min (Prims.parse_int "2") lnum  in
                      let doc2 =
                        let uu____46934 =
                          let uu____46935 =
                            FStar_Pprint.repeat lnum1 FStar_Pprint.hardline
                             in
                          let uu____46936 = str comment  in
                          FStar_Pprint.op_Hat_Hat uu____46935 uu____46936  in
                        FStar_Pprint.op_Hat_Hat doc1 uu____46934  in
                      let uu____46937 =
                        let uu____46939 = FStar_Range.end_of_range crange  in
                        FStar_Range.line_of_pos uu____46939  in
                      place_comments_until_pos (Prims.parse_int "1")
                        uu____46937 pos meta_decl doc2 true init1))
                | uu____46942 ->
                    if doc1 = FStar_Pprint.empty
                    then FStar_Pprint.empty
                    else
                      (let lnum =
                         let uu____46955 = FStar_Range.line_of_pos pos  in
                         uu____46955 - lbegin  in
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
                       let uu____46997 =
                         FStar_Pprint.repeat lnum7 FStar_Pprint.hardline  in
                       FStar_Pprint.op_Hat_Hat doc1 uu____46997)
  
let separate_map_with_comments :
  'Auu____47011 .
    FStar_Pprint.document ->
      FStar_Pprint.document ->
        ('Auu____47011 -> FStar_Pprint.document) ->
          'Auu____47011 Prims.list ->
            ('Auu____47011 -> decl_meta) -> FStar_Pprint.document
  =
  fun prefix1  ->
    fun sep  ->
      fun f  ->
        fun xs  ->
          fun extract_meta  ->
            let fold_fun uu____47070 x =
              match uu____47070 with
              | (last_line,doc1) ->
                  let meta_decl = extract_meta x  in
                  let r = meta_decl.r  in
                  let doc2 =
                    let uu____47089 = FStar_Range.start_of_range r  in
                    place_comments_until_pos (Prims.parse_int "1") last_line
                      uu____47089 meta_decl doc1 false false
                     in
                  let uu____47093 =
                    let uu____47095 = FStar_Range.end_of_range r  in
                    FStar_Range.line_of_pos uu____47095  in
                  let uu____47096 =
                    let uu____47097 =
                      let uu____47098 = f x  in
                      FStar_Pprint.op_Hat_Hat sep uu____47098  in
                    FStar_Pprint.op_Hat_Hat doc2 uu____47097  in
                  (uu____47093, uu____47096)
               in
            let uu____47100 =
              let uu____47107 = FStar_List.hd xs  in
              let uu____47108 = FStar_List.tl xs  in
              (uu____47107, uu____47108)  in
            match uu____47100 with
            | (x,xs1) ->
                let init1 =
                  let meta_decl = extract_meta x  in
                  let uu____47126 =
                    let uu____47128 = FStar_Range.end_of_range meta_decl.r
                       in
                    FStar_Range.line_of_pos uu____47128  in
                  let uu____47129 =
                    let uu____47130 = f x  in
                    FStar_Pprint.op_Hat_Hat prefix1 uu____47130  in
                  (uu____47126, uu____47129)  in
                let uu____47132 = FStar_List.fold_left fold_fun init1 xs1  in
                FStar_Pervasives_Native.snd uu____47132
  
let separate_map_with_comments_kw :
  'Auu____47159 'Auu____47160 .
    'Auu____47159 ->
      'Auu____47159 ->
        ('Auu____47159 -> 'Auu____47160 -> FStar_Pprint.document) ->
          'Auu____47160 Prims.list ->
            ('Auu____47160 -> decl_meta) -> FStar_Pprint.document
  =
  fun prefix1  ->
    fun sep  ->
      fun f  ->
        fun xs  ->
          fun extract_meta  ->
            let fold_fun uu____47224 x =
              match uu____47224 with
              | (last_line,doc1) ->
                  let meta_decl = extract_meta x  in
                  let r = meta_decl.r  in
                  let doc2 =
                    let uu____47243 = FStar_Range.start_of_range r  in
                    place_comments_until_pos (Prims.parse_int "1") last_line
                      uu____47243 meta_decl doc1 false false
                     in
                  let uu____47247 =
                    let uu____47249 = FStar_Range.end_of_range r  in
                    FStar_Range.line_of_pos uu____47249  in
                  let uu____47250 =
                    let uu____47251 = f sep x  in
                    FStar_Pprint.op_Hat_Hat doc2 uu____47251  in
                  (uu____47247, uu____47250)
               in
            let uu____47253 =
              let uu____47260 = FStar_List.hd xs  in
              let uu____47261 = FStar_List.tl xs  in
              (uu____47260, uu____47261)  in
            match uu____47253 with
            | (x,xs1) ->
                let init1 =
                  let meta_decl = extract_meta x  in
                  let uu____47279 =
                    let uu____47281 = FStar_Range.end_of_range meta_decl.r
                       in
                    FStar_Range.line_of_pos uu____47281  in
                  let uu____47282 = f prefix1 x  in
                  (uu____47279, uu____47282)  in
                let uu____47284 = FStar_List.fold_left fold_fun init1 xs1  in
                FStar_Pervasives_Native.snd uu____47284
  
let rec (p_decl : FStar_Parser_AST.decl -> FStar_Pprint.document) =
  fun d  ->
    let qualifiers =
      match ((d.FStar_Parser_AST.quals), (d.FStar_Parser_AST.d)) with
      | ((FStar_Parser_AST.Assumption )::[],FStar_Parser_AST.Assume
         (id1,uu____48270)) ->
          let uu____48273 =
            let uu____48275 =
              FStar_Util.char_at id1.FStar_Ident.idText (Prims.parse_int "0")
               in
            FStar_All.pipe_right uu____48275 FStar_Util.is_upper  in
          if uu____48273
          then
            let uu____48281 = p_qualifier FStar_Parser_AST.Assumption  in
            FStar_Pprint.op_Hat_Hat uu____48281 FStar_Pprint.space
          else p_qualifiers d.FStar_Parser_AST.quals
      | uu____48284 -> p_qualifiers d.FStar_Parser_AST.quals  in
    let uu____48291 =
      FStar_Pprint.optional (fun d1  -> p_fsdoc d1) d.FStar_Parser_AST.doc
       in
    let uu____48294 =
      let uu____48295 = p_attributes d.FStar_Parser_AST.attrs  in
      let uu____48296 =
        let uu____48297 = p_rawDecl d  in
        FStar_Pprint.op_Hat_Hat qualifiers uu____48297  in
      FStar_Pprint.op_Hat_Hat uu____48295 uu____48296  in
    FStar_Pprint.op_Hat_Hat uu____48291 uu____48294

and (p_attributes : FStar_Parser_AST.attributes_ -> FStar_Pprint.document) =
  fun attrs  ->
    match attrs with
    | [] -> FStar_Pprint.empty
    | uu____48299 ->
        let uu____48300 =
          let uu____48301 = str "@ "  in
          let uu____48303 =
            let uu____48304 =
              let uu____48305 =
                let uu____48306 =
                  let uu____48307 = FStar_List.map p_atomicTerm attrs  in
                  FStar_Pprint.flow break1 uu____48307  in
                FStar_Pprint.op_Hat_Hat uu____48306 FStar_Pprint.rbracket  in
              FStar_Pprint.align uu____48305  in
            FStar_Pprint.op_Hat_Hat uu____48304 FStar_Pprint.hardline  in
          FStar_Pprint.op_Hat_Hat uu____48301 uu____48303  in
        FStar_Pprint.op_Hat_Hat FStar_Pprint.lbracket uu____48300

and (p_fsdoc : FStar_Parser_AST.fsdoc -> FStar_Pprint.document) =
  fun uu____48310  ->
    match uu____48310 with
    | (doc1,kwd_args) ->
        let kwd_args_doc =
          match kwd_args with
          | [] -> FStar_Pprint.empty
          | kwd_args1 ->
              let process_kwd_arg uu____48358 =
                match uu____48358 with
                | (kwd,arg) ->
                    let uu____48371 = str "@"  in
                    let uu____48373 =
                      let uu____48374 = str kwd  in
                      let uu____48375 =
                        let uu____48376 = str arg  in
                        FStar_Pprint.op_Hat_Hat FStar_Pprint.space
                          uu____48376
                         in
                      FStar_Pprint.op_Hat_Hat uu____48374 uu____48375  in
                    FStar_Pprint.op_Hat_Hat uu____48371 uu____48373
                 in
              let uu____48377 =
                FStar_Pprint.separate_map FStar_Pprint.hardline
                  process_kwd_arg kwd_args1
                 in
              FStar_Pprint.op_Hat_Hat uu____48377 FStar_Pprint.hardline
           in
        let uu____48384 =
          let uu____48385 =
            let uu____48386 =
              let uu____48387 = str doc1  in
              let uu____48388 =
                let uu____48389 =
                  let uu____48390 =
                    FStar_Pprint.op_Hat_Hat FStar_Pprint.rparen
                      FStar_Pprint.hardline
                     in
                  FStar_Pprint.op_Hat_Hat FStar_Pprint.star uu____48390  in
                FStar_Pprint.op_Hat_Hat kwd_args_doc uu____48389  in
              FStar_Pprint.op_Hat_Hat uu____48387 uu____48388  in
            FStar_Pprint.op_Hat_Hat FStar_Pprint.star uu____48386  in
          FStar_Pprint.op_Hat_Hat FStar_Pprint.star uu____48385  in
        FStar_Pprint.op_Hat_Hat FStar_Pprint.lparen uu____48384

and (p_justSig : FStar_Parser_AST.decl -> FStar_Pprint.document) =
  fun d  ->
    match d.FStar_Parser_AST.d with
    | FStar_Parser_AST.Val (lid,t) ->
        let uu____48394 =
          let uu____48395 = str "val"  in
          let uu____48397 =
            let uu____48398 =
              let uu____48399 = p_lident lid  in
              let uu____48400 =
                FStar_Pprint.op_Hat_Hat FStar_Pprint.space FStar_Pprint.colon
                 in
              FStar_Pprint.op_Hat_Hat uu____48399 uu____48400  in
            FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____48398  in
          FStar_Pprint.op_Hat_Hat uu____48395 uu____48397  in
        let uu____48401 = p_typ false false t  in
        FStar_Pprint.op_Hat_Hat uu____48394 uu____48401
    | FStar_Parser_AST.TopLevelLet (uu____48404,lbs) ->
        FStar_Pprint.separate_map FStar_Pprint.hardline
          (fun lb  ->
             let uu____48429 =
               let uu____48430 = str "let"  in p_letlhs uu____48430 lb false
                in
             FStar_Pprint.group uu____48429) lbs
    | uu____48433 -> FStar_Pprint.empty

and (p_list :
  (FStar_Ident.ident -> FStar_Pprint.document) ->
    FStar_Pprint.document ->
      FStar_Ident.ident Prims.list -> FStar_Pprint.document)
  =
  fun f  ->
    fun sep  ->
      fun l  ->
        let rec p_list' uu___328_48448 =
          match uu___328_48448 with
          | [] -> FStar_Pprint.empty
          | x::[] -> f x
          | x::xs ->
              let uu____48456 = f x  in
              let uu____48457 =
                let uu____48458 = p_list' xs  in
                FStar_Pprint.op_Hat_Hat sep uu____48458  in
              FStar_Pprint.op_Hat_Hat uu____48456 uu____48457
           in
        let uu____48459 = str "["  in
        let uu____48461 =
          let uu____48462 = p_list' l  in
          let uu____48463 = str "]"  in
          FStar_Pprint.op_Hat_Hat uu____48462 uu____48463  in
        FStar_Pprint.op_Hat_Hat uu____48459 uu____48461

and (p_rawDecl : FStar_Parser_AST.decl -> FStar_Pprint.document) =
  fun d  ->
    match d.FStar_Parser_AST.d with
    | FStar_Parser_AST.Open uid ->
        let uu____48467 =
          let uu____48468 = str "open"  in
          let uu____48470 = p_quident uid  in
          FStar_Pprint.op_Hat_Slash_Hat uu____48468 uu____48470  in
        FStar_Pprint.group uu____48467
    | FStar_Parser_AST.Include uid ->
        let uu____48472 =
          let uu____48473 = str "include"  in
          let uu____48475 = p_quident uid  in
          FStar_Pprint.op_Hat_Slash_Hat uu____48473 uu____48475  in
        FStar_Pprint.group uu____48472
    | FStar_Parser_AST.Friend uid ->
        let uu____48477 =
          let uu____48478 = str "friend"  in
          let uu____48480 = p_quident uid  in
          FStar_Pprint.op_Hat_Slash_Hat uu____48478 uu____48480  in
        FStar_Pprint.group uu____48477
    | FStar_Parser_AST.ModuleAbbrev (uid1,uid2) ->
        let uu____48483 =
          let uu____48484 = str "module"  in
          let uu____48486 =
            let uu____48487 =
              let uu____48488 = p_uident uid1  in
              let uu____48489 =
                FStar_Pprint.op_Hat_Hat FStar_Pprint.space
                  FStar_Pprint.equals
                 in
              FStar_Pprint.op_Hat_Hat uu____48488 uu____48489  in
            FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____48487  in
          FStar_Pprint.op_Hat_Hat uu____48484 uu____48486  in
        let uu____48490 = p_quident uid2  in
        op_Hat_Slash_Plus_Hat uu____48483 uu____48490
    | FStar_Parser_AST.TopLevelModule uid ->
        let uu____48492 =
          let uu____48493 = str "module"  in
          let uu____48495 =
            let uu____48496 = p_quident uid  in
            FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____48496  in
          FStar_Pprint.op_Hat_Hat uu____48493 uu____48495  in
        FStar_Pprint.group uu____48492
    | FStar_Parser_AST.Tycon
        (true
         ,uu____48497,(FStar_Parser_AST.TyconAbbrev
                       (uid,tpars,FStar_Pervasives_Native.None ,t),FStar_Pervasives_Native.None
                       )::[])
        ->
        let effect_prefix_doc =
          let uu____48534 = str "effect"  in
          let uu____48536 =
            let uu____48537 = p_uident uid  in
            FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____48537  in
          FStar_Pprint.op_Hat_Hat uu____48534 uu____48536  in
        let uu____48538 =
          let uu____48539 = p_typars tpars  in
          FStar_Pprint.surround (Prims.parse_int "2") (Prims.parse_int "1")
            effect_prefix_doc uu____48539 FStar_Pprint.equals
           in
        let uu____48542 = p_typ false false t  in
        op_Hat_Slash_Plus_Hat uu____48538 uu____48542
    | FStar_Parser_AST.Tycon (false ,tc,tcdefs) ->
        let s = if tc then str "class" else str "type"  in
        let uu____48573 =
          let uu____48574 = FStar_List.hd tcdefs  in
          p_fsdocTypeDeclPairs s uu____48574  in
        let uu____48587 =
          let uu____48588 = FStar_List.tl tcdefs  in
          FStar_All.pipe_left
            (FStar_Pprint.concat_map
               (fun x  ->
                  let uu____48626 =
                    let uu____48627 = str "and"  in
                    p_fsdocTypeDeclPairs uu____48627 x  in
                  FStar_Pprint.op_Hat_Hat break1 uu____48626)) uu____48588
           in
        FStar_Pprint.op_Hat_Hat uu____48573 uu____48587
    | FStar_Parser_AST.TopLevelLet (q,lbs) ->
        let let_doc =
          let uu____48644 = str "let"  in
          let uu____48646 = p_letqualifier q  in
          FStar_Pprint.op_Hat_Hat uu____48644 uu____48646  in
        let uu____48647 = str "and"  in
        separate_map_with_comments_kw let_doc uu____48647 p_letbinding lbs
          (fun uu____48657  ->
             match uu____48657 with
             | (p,t) ->
                 let uu____48664 =
                   FStar_Range.union_ranges p.FStar_Parser_AST.prange
                     t.FStar_Parser_AST.range
                    in
                 {
                   r = uu____48664;
                   has_qs = false;
                   has_attrs = false;
                   has_fsdoc = (FStar_Util.is_some d.FStar_Parser_AST.doc);
                   is_fsdoc = false
                 })
    | FStar_Parser_AST.Val (lid,t) ->
        let uu____48670 =
          let uu____48671 = str "val"  in
          let uu____48673 =
            let uu____48674 =
              let uu____48675 = p_lident lid  in
              let uu____48676 = sig_as_binders_if_possible t false  in
              FStar_Pprint.op_Hat_Hat uu____48675 uu____48676  in
            FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____48674  in
          FStar_Pprint.op_Hat_Hat uu____48671 uu____48673  in
        FStar_All.pipe_left FStar_Pprint.group uu____48670
    | FStar_Parser_AST.Assume (id1,t) ->
        let decl_keyword =
          let uu____48681 =
            let uu____48683 =
              FStar_Util.char_at id1.FStar_Ident.idText (Prims.parse_int "0")
               in
            FStar_All.pipe_right uu____48683 FStar_Util.is_upper  in
          if uu____48681
          then FStar_Pprint.empty
          else
            (let uu____48691 = str "val"  in
             FStar_Pprint.op_Hat_Hat uu____48691 FStar_Pprint.space)
           in
        let uu____48693 =
          let uu____48694 = p_ident id1  in
          let uu____48695 =
            let uu____48696 =
              let uu____48697 =
                let uu____48698 = p_typ false false t  in
                FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____48698  in
              FStar_Pprint.op_Hat_Hat FStar_Pprint.colon uu____48697  in
            FStar_Pprint.group uu____48696  in
          FStar_Pprint.op_Hat_Hat uu____48694 uu____48695  in
        FStar_Pprint.op_Hat_Hat decl_keyword uu____48693
    | FStar_Parser_AST.Exception (uid,t_opt) ->
        let uu____48707 = str "exception"  in
        let uu____48709 =
          let uu____48710 =
            let uu____48711 = p_uident uid  in
            let uu____48712 =
              FStar_Pprint.optional
                (fun t  ->
                   let uu____48716 =
                     let uu____48717 = str "of"  in
                     let uu____48719 = p_typ false false t  in
                     op_Hat_Slash_Plus_Hat uu____48717 uu____48719  in
                   FStar_Pprint.op_Hat_Hat break1 uu____48716) t_opt
               in
            FStar_Pprint.op_Hat_Hat uu____48711 uu____48712  in
          FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____48710  in
        FStar_Pprint.op_Hat_Hat uu____48707 uu____48709
    | FStar_Parser_AST.NewEffect ne ->
        let uu____48723 = str "new_effect"  in
        let uu____48725 =
          let uu____48726 = p_newEffect ne  in
          FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____48726  in
        FStar_Pprint.op_Hat_Hat uu____48723 uu____48725
    | FStar_Parser_AST.SubEffect se ->
        let uu____48728 = str "sub_effect"  in
        let uu____48730 =
          let uu____48731 = p_subEffect se  in
          FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____48731  in
        FStar_Pprint.op_Hat_Hat uu____48728 uu____48730
    | FStar_Parser_AST.Pragma p -> p_pragma p
    | FStar_Parser_AST.Fsdoc doc1 -> p_fsdoc doc1
    | FStar_Parser_AST.Main uu____48734 ->
        failwith "*Main declaration* : Is that really still in use ??"
    | FStar_Parser_AST.Tycon (true ,uu____48736,uu____48737) ->
        failwith
          "Effect abbreviation is expected to be defined by an abbreviation"
    | FStar_Parser_AST.Splice (ids,t) ->
        let uu____48765 = str "%splice"  in
        let uu____48767 =
          let uu____48768 =
            let uu____48769 = str ";"  in p_list p_uident uu____48769 ids  in
          let uu____48771 =
            let uu____48772 = p_term false false t  in
            FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____48772  in
          FStar_Pprint.op_Hat_Hat uu____48768 uu____48771  in
        FStar_Pprint.op_Hat_Hat uu____48765 uu____48767

and (p_pragma : FStar_Parser_AST.pragma -> FStar_Pprint.document) =
  fun uu___329_48775  ->
    match uu___329_48775 with
    | FStar_Parser_AST.SetOptions s ->
        let uu____48778 = str "#set-options"  in
        let uu____48780 =
          let uu____48781 =
            let uu____48782 = str s  in FStar_Pprint.dquotes uu____48782  in
          FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____48781  in
        FStar_Pprint.op_Hat_Hat uu____48778 uu____48780
    | FStar_Parser_AST.ResetOptions s_opt ->
        let uu____48787 = str "#reset-options"  in
        let uu____48789 =
          FStar_Pprint.optional
            (fun s  ->
               let uu____48795 =
                 let uu____48796 = str s  in FStar_Pprint.dquotes uu____48796
                  in
               FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____48795) s_opt
           in
        FStar_Pprint.op_Hat_Hat uu____48787 uu____48789
    | FStar_Parser_AST.PushOptions s_opt ->
        let uu____48801 = str "#push-options"  in
        let uu____48803 =
          FStar_Pprint.optional
            (fun s  ->
               let uu____48809 =
                 let uu____48810 = str s  in FStar_Pprint.dquotes uu____48810
                  in
               FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____48809) s_opt
           in
        FStar_Pprint.op_Hat_Hat uu____48801 uu____48803
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
    fun uu____48841  ->
      match uu____48841 with
      | (typedecl,fsdoc_opt) ->
          let uu____48854 = p_typeDecl (kw, fsdoc_opt) typedecl  in
          (match uu____48854 with
           | (comm,decl,body,pre) ->
               if comm = FStar_Pprint.empty
               then
                 let uu____48879 = pre body  in
                 FStar_Pprint.op_Hat_Hat decl uu____48879
               else
                 (let uu____48882 =
                    let uu____48883 =
                      let uu____48884 =
                        let uu____48885 = pre body  in
                        FStar_Pprint.op_Hat_Slash_Hat uu____48885 comm  in
                      FStar_Pprint.op_Hat_Hat decl uu____48884  in
                    let uu____48886 =
                      let uu____48887 =
                        let uu____48888 =
                          let uu____48889 =
                            let uu____48890 =
                              FStar_Pprint.op_Hat_Hat FStar_Pprint.hardline
                                body
                               in
                            FStar_Pprint.op_Hat_Hat comm uu____48890  in
                          FStar_Pprint.op_Hat_Hat FStar_Pprint.hardline
                            uu____48889
                           in
                        FStar_Pprint.nest (Prims.parse_int "2") uu____48888
                         in
                      FStar_Pprint.op_Hat_Hat decl uu____48887  in
                    FStar_Pprint.ifflat uu____48883 uu____48886  in
                  FStar_All.pipe_left FStar_Pprint.group uu____48882))

and (p_typeDecl :
  (FStar_Pprint.document * FStar_Parser_AST.fsdoc
    FStar_Pervasives_Native.option) ->
    FStar_Parser_AST.tycon ->
      (FStar_Pprint.document * FStar_Pprint.document * FStar_Pprint.document
        * (FStar_Pprint.document -> FStar_Pprint.document)))
  =
  fun pre  ->
    fun uu___330_48893  ->
      match uu___330_48893 with
      | FStar_Parser_AST.TyconAbstract (lid,bs,typ_opt) ->
          let uu____48922 = p_typeDeclPrefix pre false lid bs typ_opt  in
          (FStar_Pprint.empty, uu____48922, FStar_Pprint.empty,
            FStar_Pervasives.id)
      | FStar_Parser_AST.TyconAbbrev (lid,bs,typ_opt,t) ->
          let uu____48939 = p_typ_sep false false t  in
          (match uu____48939 with
           | (comm,doc1) ->
               let uu____48959 = p_typeDeclPrefix pre true lid bs typ_opt  in
               (comm, uu____48959, doc1, jump2))
      | FStar_Parser_AST.TyconRecord (lid,bs,typ_opt,record_field_decls) ->
          let p_recordFieldAndComments ps uu____49015 =
            match uu____49015 with
            | (lid1,t,doc_opt) ->
                let uu____49032 =
                  let uu____49037 =
                    FStar_Range.extend_to_end_of_line
                      t.FStar_Parser_AST.range
                     in
                  with_comment_sep (p_recordFieldDecl ps) (lid1, t, doc_opt)
                    uu____49037
                   in
                (match uu____49032 with
                 | (comm,field) ->
                     let sep =
                       if ps then FStar_Pprint.semi else FStar_Pprint.empty
                        in
                     inline_comment_or_above comm field sep)
             in
          let p_fields =
            let uu____49055 =
              separate_map_last FStar_Pprint.hardline
                p_recordFieldAndComments record_field_decls
               in
            braces_with_nesting uu____49055  in
          let uu____49064 = p_typeDeclPrefix pre true lid bs typ_opt  in
          (FStar_Pprint.empty, uu____49064, p_fields,
            ((fun d  -> FStar_Pprint.op_Hat_Hat FStar_Pprint.space d)))
      | FStar_Parser_AST.TyconVariant (lid,bs,typ_opt,ct_decls) ->
          let p_constructorBranchAndComments uu____49131 =
            match uu____49131 with
            | (uid,t_opt,doc_opt,use_of) ->
                let range =
                  let uu____49160 =
                    let uu____49161 =
                      FStar_Util.map_opt t_opt
                        (fun t  -> t.FStar_Parser_AST.range)
                       in
                    FStar_Util.dflt uid.FStar_Ident.idRange uu____49161  in
                  FStar_Range.extend_to_end_of_line uu____49160  in
                let uu____49166 =
                  with_comment_sep p_constructorBranch
                    (uid, t_opt, doc_opt, use_of) range
                   in
                (match uu____49166 with
                 | (comm,ctor) ->
                     inline_comment_or_above comm ctor FStar_Pprint.empty)
             in
          let datacon_doc =
            FStar_Pprint.separate_map FStar_Pprint.hardline
              p_constructorBranchAndComments ct_decls
             in
          let uu____49205 = p_typeDeclPrefix pre true lid bs typ_opt  in
          (FStar_Pprint.empty, uu____49205, datacon_doc, jump2)

and (p_typeDeclPrefix :
  (FStar_Pprint.document * FStar_Parser_AST.fsdoc
    FStar_Pervasives_Native.option) ->
    Prims.bool ->
      FStar_Ident.ident ->
        FStar_Parser_AST.binder Prims.list ->
          FStar_Parser_AST.knd FStar_Pervasives_Native.option ->
            FStar_Pprint.document)
  =
  fun uu____49210  ->
    fun eq1  ->
      fun lid  ->
        fun bs  ->
          fun typ_opt  ->
            match uu____49210 with
            | (kw,fsdoc_opt) ->
                let maybe_with_fsdoc cont =
                  let lid_doc = p_ident lid  in
                  let kw_lid =
                    let uu____49245 =
                      FStar_Pprint.op_Hat_Slash_Hat kw lid_doc  in
                    FStar_Pprint.group uu____49245  in
                  match fsdoc_opt with
                  | FStar_Pervasives_Native.None  -> cont kw_lid
                  | FStar_Pervasives_Native.Some fsdoc ->
                      let uu____49247 =
                        let uu____49250 =
                          let uu____49253 = p_fsdoc fsdoc  in
                          let uu____49254 =
                            let uu____49257 = cont lid_doc  in [uu____49257]
                             in
                          uu____49253 :: uu____49254  in
                        kw :: uu____49250  in
                      FStar_Pprint.separate FStar_Pprint.hardline uu____49247
                   in
                let typ =
                  let maybe_eq =
                    if eq1 then FStar_Pprint.equals else FStar_Pprint.empty
                     in
                  match typ_opt with
                  | FStar_Pervasives_Native.None  -> maybe_eq
                  | FStar_Pervasives_Native.Some t ->
                      let uu____49264 =
                        let uu____49265 =
                          let uu____49266 = p_typ false false t  in
                          FStar_Pprint.op_Hat_Slash_Hat uu____49266 maybe_eq
                           in
                        FStar_Pprint.op_Hat_Hat FStar_Pprint.space
                          uu____49265
                         in
                      FStar_Pprint.op_Hat_Hat FStar_Pprint.colon uu____49264
                   in
                if bs = []
                then maybe_with_fsdoc (fun n1  -> prefix2 n1 typ)
                else
                  (let binders = p_binders_list true bs  in
                   maybe_with_fsdoc
                     (fun n1  ->
                        let uu____49286 =
                          let uu____49287 = FStar_Pprint.flow break1 binders
                             in
                          prefix2 n1 uu____49287  in
                        prefix2 uu____49286 typ))

and (p_recordFieldDecl :
  Prims.bool ->
    (FStar_Ident.ident * FStar_Parser_AST.term * FStar_Parser_AST.fsdoc
      FStar_Pervasives_Native.option) -> FStar_Pprint.document)
  =
  fun ps  ->
    fun uu____49289  ->
      match uu____49289 with
      | (lid,t,doc_opt) ->
          let uu____49306 =
            let uu____49307 = FStar_Pprint.optional p_fsdoc doc_opt  in
            let uu____49308 =
              let uu____49309 = p_lident lid  in
              let uu____49310 =
                let uu____49311 = p_typ ps false t  in
                FStar_Pprint.op_Hat_Hat FStar_Pprint.colon uu____49311  in
              FStar_Pprint.op_Hat_Hat uu____49309 uu____49310  in
            FStar_Pprint.op_Hat_Hat uu____49307 uu____49308  in
          FStar_Pprint.group uu____49306

and (p_constructorBranch :
  (FStar_Ident.ident * FStar_Parser_AST.term FStar_Pervasives_Native.option *
    FStar_Parser_AST.fsdoc FStar_Pervasives_Native.option * Prims.bool) ->
    FStar_Pprint.document)
  =
  fun uu____49313  ->
    match uu____49313 with
    | (uid,t_opt,doc_opt,use_of) ->
        let sep = if use_of then str "of" else FStar_Pprint.colon  in
        let uid_doc =
          let uu____49347 =
            let uu____49348 =
              let uu____49349 = p_uident uid  in
              FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____49349  in
            FStar_Pprint.op_Hat_Hat FStar_Pprint.bar uu____49348  in
          FStar_Pprint.group uu____49347  in
        let uu____49350 = FStar_Pprint.optional p_fsdoc doc_opt  in
        let uu____49351 =
          default_or_map uid_doc
            (fun t  ->
               let uu____49355 =
                 let uu____49356 =
                   let uu____49357 =
                     let uu____49358 =
                       let uu____49359 = p_typ false false t  in
                       FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____49359
                        in
                     FStar_Pprint.op_Hat_Hat sep uu____49358  in
                   FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____49357  in
                 FStar_Pprint.op_Hat_Hat uid_doc uu____49356  in
               FStar_Pprint.group uu____49355) t_opt
           in
        FStar_Pprint.op_Hat_Hat uu____49350 uu____49351

and (p_letlhs :
  FStar_Pprint.document ->
    (FStar_Parser_AST.pattern * FStar_Parser_AST.term) ->
      Prims.bool -> FStar_Pprint.document)
  =
  fun kw  ->
    fun uu____49363  ->
      fun inner_let  ->
        match uu____49363 with
        | (pat,uu____49371) ->
            let uu____49372 =
              match pat.FStar_Parser_AST.pat with
              | FStar_Parser_AST.PatAscribed
                  (pat1,(t,FStar_Pervasives_Native.None )) ->
                  (pat1,
                    (FStar_Pervasives_Native.Some (t, FStar_Pprint.empty)))
              | FStar_Parser_AST.PatAscribed
                  (pat1,(t,FStar_Pervasives_Native.Some tac)) ->
                  let uu____49424 =
                    let uu____49431 =
                      let uu____49436 =
                        let uu____49437 =
                          let uu____49438 =
                            let uu____49439 = str "by"  in
                            let uu____49441 =
                              let uu____49442 = p_atomicTerm tac  in
                              FStar_Pprint.op_Hat_Hat FStar_Pprint.space
                                uu____49442
                               in
                            FStar_Pprint.op_Hat_Hat uu____49439 uu____49441
                             in
                          FStar_Pprint.op_Hat_Hat FStar_Pprint.space
                            uu____49438
                           in
                        FStar_Pprint.group uu____49437  in
                      (t, uu____49436)  in
                    FStar_Pervasives_Native.Some uu____49431  in
                  (pat1, uu____49424)
              | uu____49453 -> (pat, FStar_Pervasives_Native.None)  in
            (match uu____49372 with
             | (pat1,ascr) ->
                 (match pat1.FStar_Parser_AST.pat with
                  | FStar_Parser_AST.PatApp
                      ({
                         FStar_Parser_AST.pat = FStar_Parser_AST.PatVar
                           (lid,uu____49479);
                         FStar_Parser_AST.prange = uu____49480;_},pats)
                      ->
                      let ascr_doc =
                        match ascr with
                        | FStar_Pervasives_Native.Some (t,tac) ->
                            let uu____49497 =
                              sig_as_binders_if_possible t true  in
                            FStar_Pprint.op_Hat_Hat uu____49497 tac
                        | FStar_Pervasives_Native.None  -> FStar_Pprint.empty
                         in
                      let uu____49503 =
                        if inner_let
                        then
                          let uu____49517 = pats_as_binders_if_possible pats
                             in
                          match uu____49517 with
                          | (bs,style) ->
                              ((FStar_List.append bs [ascr_doc]), style)
                        else
                          (let uu____49540 = pats_as_binders_if_possible pats
                              in
                           match uu____49540 with
                           | (bs,style) ->
                               ((FStar_List.append bs [ascr_doc]), style))
                         in
                      (match uu____49503 with
                       | (terms,style) ->
                           let uu____49567 =
                             let uu____49568 =
                               let uu____49569 =
                                 let uu____49570 = p_lident lid  in
                                 let uu____49571 =
                                   format_sig style terms true true  in
                                 FStar_Pprint.op_Hat_Hat uu____49570
                                   uu____49571
                                  in
                               FStar_Pprint.op_Hat_Hat FStar_Pprint.space
                                 uu____49569
                                in
                             FStar_Pprint.op_Hat_Hat kw uu____49568  in
                           FStar_All.pipe_left FStar_Pprint.group uu____49567)
                  | uu____49574 ->
                      let ascr_doc =
                        match ascr with
                        | FStar_Pervasives_Native.Some (t,tac) ->
                            let uu____49582 =
                              let uu____49583 =
                                let uu____49584 =
                                  p_typ_top
                                    (Arrows
                                       ((Prims.parse_int "2"),
                                         (Prims.parse_int "2"))) false false
                                    t
                                   in
                                FStar_Pprint.op_Hat_Hat FStar_Pprint.colon
                                  uu____49584
                                 in
                              FStar_Pprint.group uu____49583  in
                            FStar_Pprint.op_Hat_Hat uu____49582 tac
                        | FStar_Pervasives_Native.None  -> FStar_Pprint.empty
                         in
                      let uu____49595 =
                        let uu____49596 =
                          let uu____49597 =
                            let uu____49598 = p_tuplePattern pat1  in
                            FStar_Pprint.op_Hat_Slash_Hat kw uu____49598  in
                          FStar_Pprint.group uu____49597  in
                        FStar_Pprint.op_Hat_Hat uu____49596 ascr_doc  in
                      FStar_Pprint.group uu____49595))

and (p_letbinding :
  FStar_Pprint.document ->
    (FStar_Parser_AST.pattern * FStar_Parser_AST.term) ->
      FStar_Pprint.document)
  =
  fun kw  ->
    fun uu____49600  ->
      match uu____49600 with
      | (pat,e) ->
          let doc_pat = p_letlhs kw (pat, e) false  in
          let uu____49609 = p_term_sep false false e  in
          (match uu____49609 with
           | (comm,doc_expr) ->
               let doc_expr1 =
                 inline_comment_or_above comm doc_expr FStar_Pprint.empty  in
               let uu____49619 =
                 let uu____49620 =
                   FStar_Pprint.op_Hat_Slash_Hat FStar_Pprint.equals
                     doc_expr1
                    in
                 FStar_Pprint.op_Hat_Slash_Hat doc_pat uu____49620  in
               let uu____49621 =
                 let uu____49622 =
                   let uu____49623 =
                     let uu____49624 =
                       let uu____49625 = jump2 doc_expr1  in
                       FStar_Pprint.op_Hat_Hat FStar_Pprint.equals
                         uu____49625
                        in
                     FStar_Pprint.group uu____49624  in
                   FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____49623  in
                 FStar_Pprint.op_Hat_Hat doc_pat uu____49622  in
               FStar_Pprint.ifflat uu____49619 uu____49621)

and (p_newEffect : FStar_Parser_AST.effect_decl -> FStar_Pprint.document) =
  fun uu___331_49626  ->
    match uu___331_49626 with
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
        let uu____49651 = p_uident uid  in
        let uu____49652 = p_binders true bs  in
        let uu____49654 =
          let uu____49655 = p_simpleTerm false false t  in
          prefix2 FStar_Pprint.equals uu____49655  in
        surround_maybe_empty (Prims.parse_int "2") (Prims.parse_int "1")
          uu____49651 uu____49652 uu____49654

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
          let uu____49670 =
            let uu____49671 =
              let uu____49672 =
                let uu____49673 = p_uident uid  in
                let uu____49674 = p_binders true bs  in
                let uu____49676 =
                  let uu____49677 = p_typ false false t  in
                  prefix2 FStar_Pprint.colon uu____49677  in
                surround_maybe_empty (Prims.parse_int "2")
                  (Prims.parse_int "1") uu____49673 uu____49674 uu____49676
                 in
              FStar_Pprint.group uu____49672  in
            let uu____49682 =
              let uu____49683 = str "with"  in
              let uu____49685 =
                let uu____49686 =
                  let uu____49687 =
                    let uu____49688 =
                      let uu____49689 =
                        let uu____49690 =
                          FStar_Pprint.op_Hat_Hat FStar_Pprint.semi
                            FStar_Pprint.space
                           in
                        FStar_Pprint.op_Hat_Hat FStar_Pprint.hardline
                          uu____49690
                         in
                      separate_map_last uu____49689 p_effectDecl eff_decls
                       in
                    FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____49688
                     in
                  FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____49687  in
                FStar_Pprint.op_Hat_Hat FStar_Pprint.hardline uu____49686  in
              FStar_Pprint.op_Hat_Hat uu____49683 uu____49685  in
            FStar_Pprint.op_Hat_Slash_Hat uu____49671 uu____49682  in
          braces_with_nesting uu____49670

and (p_effectDecl :
  Prims.bool -> FStar_Parser_AST.decl -> FStar_Pprint.document) =
  fun ps  ->
    fun d  ->
      match d.FStar_Parser_AST.d with
      | FStar_Parser_AST.Tycon
          (false
           ,uu____49694,(FStar_Parser_AST.TyconAbbrev
                         (lid,[],FStar_Pervasives_Native.None ,e),FStar_Pervasives_Native.None
                         )::[])
          ->
          let uu____49727 =
            let uu____49728 = p_lident lid  in
            let uu____49729 =
              FStar_Pprint.op_Hat_Hat FStar_Pprint.space FStar_Pprint.equals
               in
            FStar_Pprint.op_Hat_Hat uu____49728 uu____49729  in
          let uu____49730 = p_simpleTerm ps false e  in
          prefix2 uu____49727 uu____49730
      | uu____49732 ->
          let uu____49733 =
            let uu____49735 = FStar_Parser_AST.decl_to_string d  in
            FStar_Util.format1
              "Not a declaration of an effect member... or at least I hope so : %s"
              uu____49735
             in
          failwith uu____49733

and (p_subEffect : FStar_Parser_AST.lift -> FStar_Pprint.document) =
  fun lift  ->
    let lift_op_doc =
      let lifts =
        match lift.FStar_Parser_AST.lift_op with
        | FStar_Parser_AST.NonReifiableLift t -> [("lift_wp", t)]
        | FStar_Parser_AST.ReifiableLift (t1,t2) ->
            [("lift_wp", t1); ("lift", t2)]
        | FStar_Parser_AST.LiftForFree t -> [("lift", t)]  in
      let p_lift ps uu____49818 =
        match uu____49818 with
        | (kwd,t) ->
            let uu____49829 =
              let uu____49830 = str kwd  in
              let uu____49831 =
                FStar_Pprint.op_Hat_Hat FStar_Pprint.space
                  FStar_Pprint.equals
                 in
              FStar_Pprint.op_Hat_Hat uu____49830 uu____49831  in
            let uu____49832 = p_simpleTerm ps false t  in
            prefix2 uu____49829 uu____49832
         in
      separate_break_map_last FStar_Pprint.semi p_lift lifts  in
    let uu____49839 =
      let uu____49840 =
        let uu____49841 = p_quident lift.FStar_Parser_AST.msource  in
        let uu____49842 =
          let uu____49843 = str "~>"  in
          FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____49843  in
        FStar_Pprint.op_Hat_Hat uu____49841 uu____49842  in
      let uu____49845 = p_quident lift.FStar_Parser_AST.mdest  in
      prefix2 uu____49840 uu____49845  in
    let uu____49846 =
      let uu____49847 = braces_with_nesting lift_op_doc  in
      FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____49847  in
    FStar_Pprint.op_Hat_Hat uu____49839 uu____49846

and (p_qualifier : FStar_Parser_AST.qualifier -> FStar_Pprint.document) =
  fun uu___332_49848  ->
    match uu___332_49848 with
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
        let uu____49868 = p_qualifier q  in
        FStar_Pprint.op_Hat_Hat uu____49868 FStar_Pprint.hardline
    | uu____49869 ->
        let uu____49870 =
          let uu____49871 = FStar_List.map p_qualifier qs  in
          FStar_Pprint.flow break1 uu____49871  in
        FStar_Pprint.op_Hat_Hat uu____49870 FStar_Pprint.hardline

and (p_letqualifier :
  FStar_Parser_AST.let_qualifier -> FStar_Pprint.document) =
  fun uu___333_49874  ->
    match uu___333_49874 with
    | FStar_Parser_AST.Rec  ->
        let uu____49875 = str "rec"  in
        FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____49875
    | FStar_Parser_AST.NoLetQualifier  -> FStar_Pprint.empty

and (p_aqual : FStar_Parser_AST.arg_qualifier -> FStar_Pprint.document) =
  fun uu___334_49877  ->
    match uu___334_49877 with
    | FStar_Parser_AST.Implicit  -> str "#"
    | FStar_Parser_AST.Equality  -> str "$"
    | FStar_Parser_AST.Meta t ->
        let t1 =
          match t.FStar_Parser_AST.tm with
          | FStar_Parser_AST.Abs (uu____49882,e) -> e
          | uu____49888 ->
              FStar_Parser_AST.mk_term
                (FStar_Parser_AST.App
                   (t,
                     (FStar_Parser_AST.unit_const t.FStar_Parser_AST.range),
                     FStar_Parser_AST.Nothing)) t.FStar_Parser_AST.range
                FStar_Parser_AST.Expr
           in
        let uu____49889 = str "#["  in
        let uu____49891 =
          let uu____49892 = p_term false false t1  in
          let uu____49895 =
            let uu____49896 = str "]"  in
            FStar_Pprint.op_Hat_Hat uu____49896 break1  in
          FStar_Pprint.op_Hat_Hat uu____49892 uu____49895  in
        FStar_Pprint.op_Hat_Hat uu____49889 uu____49891

and (p_disjunctivePattern :
  FStar_Parser_AST.pattern -> FStar_Pprint.document) =
  fun p  ->
    match p.FStar_Parser_AST.pat with
    | FStar_Parser_AST.PatOr pats ->
        let uu____49902 =
          let uu____49903 =
            let uu____49904 =
              FStar_Pprint.op_Hat_Hat FStar_Pprint.bar FStar_Pprint.space  in
            FStar_Pprint.op_Hat_Hat break1 uu____49904  in
          FStar_Pprint.separate_map uu____49903 p_tuplePattern pats  in
        FStar_Pprint.group uu____49902
    | uu____49905 -> p_tuplePattern p

and (p_tuplePattern : FStar_Parser_AST.pattern -> FStar_Pprint.document) =
  fun p  ->
    match p.FStar_Parser_AST.pat with
    | FStar_Parser_AST.PatTuple (pats,false ) ->
        let uu____49914 =
          let uu____49915 = FStar_Pprint.op_Hat_Hat FStar_Pprint.comma break1
             in
          FStar_Pprint.separate_map uu____49915 p_constructorPattern pats  in
        FStar_Pprint.group uu____49914
    | uu____49916 -> p_constructorPattern p

and (p_constructorPattern :
  FStar_Parser_AST.pattern -> FStar_Pprint.document) =
  fun p  ->
    match p.FStar_Parser_AST.pat with
    | FStar_Parser_AST.PatApp
        ({ FStar_Parser_AST.pat = FStar_Parser_AST.PatName maybe_cons_lid;
           FStar_Parser_AST.prange = uu____49919;_},hd1::tl1::[])
        when
        FStar_Ident.lid_equals maybe_cons_lid FStar_Parser_Const.cons_lid ->
        let uu____49924 =
          FStar_Pprint.op_Hat_Hat FStar_Pprint.colon FStar_Pprint.colon  in
        let uu____49925 = p_constructorPattern hd1  in
        let uu____49926 = p_constructorPattern tl1  in
        infix0 uu____49924 uu____49925 uu____49926
    | FStar_Parser_AST.PatApp
        ({ FStar_Parser_AST.pat = FStar_Parser_AST.PatName uid;
           FStar_Parser_AST.prange = uu____49928;_},pats)
        ->
        let uu____49934 = p_quident uid  in
        let uu____49935 =
          FStar_Pprint.separate_map break1 p_atomicPattern pats  in
        prefix2 uu____49934 uu____49935
    | uu____49936 -> p_atomicPattern p

and (p_atomicPattern : FStar_Parser_AST.pattern -> FStar_Pprint.document) =
  fun p  ->
    match p.FStar_Parser_AST.pat with
    | FStar_Parser_AST.PatAscribed (pat,(t,FStar_Pervasives_Native.None )) ->
        (match ((pat.FStar_Parser_AST.pat), (t.FStar_Parser_AST.tm)) with
         | (FStar_Parser_AST.PatVar (lid,aqual),FStar_Parser_AST.Refine
            ({ FStar_Parser_AST.b = FStar_Parser_AST.Annotated (lid',t1);
               FStar_Parser_AST.brange = uu____49952;
               FStar_Parser_AST.blevel = uu____49953;
               FStar_Parser_AST.aqual = uu____49954;_},phi))
             when lid.FStar_Ident.idText = lid'.FStar_Ident.idText ->
             let uu____49963 =
               let uu____49964 = p_ident lid  in
               p_refinement aqual uu____49964 t1 phi  in
             soft_parens_with_nesting uu____49963
         | (FStar_Parser_AST.PatWild aqual,FStar_Parser_AST.Refine
            ({ FStar_Parser_AST.b = FStar_Parser_AST.NoName t1;
               FStar_Parser_AST.brange = uu____49967;
               FStar_Parser_AST.blevel = uu____49968;
               FStar_Parser_AST.aqual = uu____49969;_},phi))
             ->
             let uu____49975 =
               p_refinement aqual FStar_Pprint.underscore t1 phi  in
             soft_parens_with_nesting uu____49975
         | uu____49976 ->
             let uu____49981 =
               let uu____49982 = p_tuplePattern pat  in
               let uu____49983 =
                 let uu____49984 = p_tmEqNoRefinement t  in
                 FStar_Pprint.op_Hat_Slash_Hat FStar_Pprint.colon uu____49984
                  in
               FStar_Pprint.op_Hat_Hat uu____49982 uu____49983  in
             soft_parens_with_nesting uu____49981)
    | FStar_Parser_AST.PatList pats ->
        let uu____49988 =
          separate_break_map FStar_Pprint.semi p_tuplePattern pats  in
        FStar_Pprint.surround (Prims.parse_int "2") (Prims.parse_int "0")
          FStar_Pprint.lbracket uu____49988 FStar_Pprint.rbracket
    | FStar_Parser_AST.PatRecord pats ->
        let p_recordFieldPat uu____50007 =
          match uu____50007 with
          | (lid,pat) ->
              let uu____50014 = p_qlident lid  in
              let uu____50015 = p_tuplePattern pat  in
              infix2 FStar_Pprint.equals uu____50014 uu____50015
           in
        let uu____50016 =
          separate_break_map FStar_Pprint.semi p_recordFieldPat pats  in
        soft_braces_with_nesting uu____50016
    | FStar_Parser_AST.PatTuple (pats,true ) ->
        let uu____50028 =
          FStar_Pprint.op_Hat_Hat FStar_Pprint.lparen FStar_Pprint.bar  in
        let uu____50029 =
          separate_break_map FStar_Pprint.comma p_constructorPattern pats  in
        let uu____50030 =
          FStar_Pprint.op_Hat_Hat FStar_Pprint.bar FStar_Pprint.rparen  in
        FStar_Pprint.surround (Prims.parse_int "2") (Prims.parse_int "1")
          uu____50028 uu____50029 uu____50030
    | FStar_Parser_AST.PatTvar (tv,arg_qualifier_opt) -> p_tvar tv
    | FStar_Parser_AST.PatOp op ->
        let uu____50041 =
          let uu____50042 =
            let uu____50043 =
              let uu____50044 = FStar_Ident.text_of_id op  in str uu____50044
               in
            let uu____50046 =
              FStar_Pprint.op_Hat_Hat FStar_Pprint.space FStar_Pprint.rparen
               in
            FStar_Pprint.op_Hat_Hat uu____50043 uu____50046  in
          FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____50042  in
        FStar_Pprint.op_Hat_Hat FStar_Pprint.lparen uu____50041
    | FStar_Parser_AST.PatWild aqual ->
        let uu____50050 = FStar_Pprint.optional p_aqual aqual  in
        FStar_Pprint.op_Hat_Hat uu____50050 FStar_Pprint.underscore
    | FStar_Parser_AST.PatConst c -> p_constant c
    | FStar_Parser_AST.PatVar (lid,aqual) ->
        let uu____50058 = FStar_Pprint.optional p_aqual aqual  in
        let uu____50059 = p_lident lid  in
        FStar_Pprint.op_Hat_Hat uu____50058 uu____50059
    | FStar_Parser_AST.PatName uid -> p_quident uid
    | FStar_Parser_AST.PatOr uu____50061 -> failwith "Inner or pattern !"
    | FStar_Parser_AST.PatApp
        ({ FStar_Parser_AST.pat = FStar_Parser_AST.PatName uu____50065;
           FStar_Parser_AST.prange = uu____50066;_},uu____50067)
        ->
        let uu____50072 = p_tuplePattern p  in
        soft_parens_with_nesting uu____50072
    | FStar_Parser_AST.PatTuple (uu____50073,false ) ->
        let uu____50080 = p_tuplePattern p  in
        soft_parens_with_nesting uu____50080
    | uu____50081 ->
        let uu____50082 =
          let uu____50084 = FStar_Parser_AST.pat_to_string p  in
          FStar_Util.format1 "Invalid pattern %s" uu____50084  in
        failwith uu____50082

and (is_typ_tuple : FStar_Parser_AST.term -> Prims.bool) =
  fun e  ->
    match e.FStar_Parser_AST.tm with
    | FStar_Parser_AST.Op
        ({ FStar_Ident.idText = "*"; FStar_Ident.idRange = uu____50089;_},uu____50090)
        -> true
    | uu____50097 -> false

and (is_meta_qualifier :
  FStar_Parser_AST.arg_qualifier FStar_Pervasives_Native.option -> Prims.bool)
  =
  fun aq  ->
    match aq with
    | FStar_Pervasives_Native.Some (FStar_Parser_AST.Meta uu____50103) ->
        true
    | uu____50105 -> false

and (p_binder :
  Prims.bool -> FStar_Parser_AST.binder -> FStar_Pprint.document) =
  fun is_atomic  ->
    fun b  ->
      let uu____50112 = p_binder' is_atomic b  in
      match uu____50112 with
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
          let uu____50151 =
            let uu____50152 =
              FStar_Pprint.optional p_aqual b.FStar_Parser_AST.aqual  in
            let uu____50153 = p_lident lid  in
            FStar_Pprint.op_Hat_Hat uu____50152 uu____50153  in
          (uu____50151, FStar_Pervasives_Native.None, cat_with_colon)
      | FStar_Parser_AST.TVariable lid ->
          let uu____50159 = p_lident lid  in
          (uu____50159, FStar_Pervasives_Native.None, cat_with_colon)
      | FStar_Parser_AST.Annotated (lid,t) ->
          let uu____50166 =
            match t.FStar_Parser_AST.tm with
            | FStar_Parser_AST.Refine
                ({ FStar_Parser_AST.b = FStar_Parser_AST.Annotated (lid',t1);
                   FStar_Parser_AST.brange = uu____50177;
                   FStar_Parser_AST.blevel = uu____50178;
                   FStar_Parser_AST.aqual = uu____50179;_},phi)
                when lid.FStar_Ident.idText = lid'.FStar_Ident.idText ->
                let uu____50184 = p_lident lid  in
                p_refinement' b.FStar_Parser_AST.aqual uu____50184 t1 phi
            | uu____50185 ->
                let t' =
                  let uu____50187 = is_typ_tuple t  in
                  if uu____50187
                  then
                    let uu____50190 = p_tmFormula t  in
                    soft_parens_with_nesting uu____50190
                  else p_tmFormula t  in
                let uu____50193 =
                  let uu____50194 =
                    FStar_Pprint.optional p_aqual b.FStar_Parser_AST.aqual
                     in
                  let uu____50195 = p_lident lid  in
                  FStar_Pprint.op_Hat_Hat uu____50194 uu____50195  in
                (uu____50193, t')
             in
          (match uu____50166 with
           | (b',t') ->
               let catf =
                 let uu____50213 =
                   is_atomic || (is_meta_qualifier b.FStar_Parser_AST.aqual)
                    in
                 if uu____50213
                 then
                   fun x  ->
                     fun y  ->
                       let uu____50220 =
                         let uu____50221 =
                           let uu____50222 = cat_with_colon x y  in
                           FStar_Pprint.op_Hat_Hat uu____50222
                             FStar_Pprint.rparen
                            in
                         FStar_Pprint.op_Hat_Hat FStar_Pprint.lparen
                           uu____50221
                          in
                       FStar_Pprint.group uu____50220
                 else
                   (fun x  ->
                      fun y  ->
                        let uu____50227 = cat_with_colon x y  in
                        FStar_Pprint.group uu____50227)
                  in
               (b', (FStar_Pervasives_Native.Some t'), catf))
      | FStar_Parser_AST.TAnnotated uu____50236 ->
          failwith "Is this still used ?"
      | FStar_Parser_AST.NoName t ->
          (match t.FStar_Parser_AST.tm with
           | FStar_Parser_AST.Refine
               ({ FStar_Parser_AST.b = FStar_Parser_AST.NoName t1;
                  FStar_Parser_AST.brange = uu____50264;
                  FStar_Parser_AST.blevel = uu____50265;
                  FStar_Parser_AST.aqual = uu____50266;_},phi)
               ->
               let uu____50270 =
                 p_refinement' b.FStar_Parser_AST.aqual
                   FStar_Pprint.underscore t1 phi
                  in
               (match uu____50270 with
                | (b',t') ->
                    (b', (FStar_Pervasives_Native.Some t'), cat_with_colon))
           | uu____50291 ->
               if is_atomic
               then
                 let uu____50303 = p_atomicTerm t  in
                 (uu____50303, FStar_Pervasives_Native.None, cat_with_colon)
               else
                 (let uu____50310 = p_appTerm t  in
                  (uu____50310, FStar_Pervasives_Native.None, cat_with_colon)))

and (p_refinement :
  FStar_Parser_AST.arg_qualifier FStar_Pervasives_Native.option ->
    FStar_Pprint.document ->
      FStar_Parser_AST.term -> FStar_Parser_AST.term -> FStar_Pprint.document)
  =
  fun aqual_opt  ->
    fun binder  ->
      fun t  ->
        fun phi  ->
          let uu____50321 = p_refinement' aqual_opt binder t phi  in
          match uu____50321 with | (b,typ) -> cat_with_colon b typ

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
            | FStar_Parser_AST.Construct uu____50337 -> false
            | FStar_Parser_AST.App uu____50349 -> false
            | FStar_Parser_AST.Op uu____50357 -> false
            | uu____50365 -> true  in
          let uu____50367 = p_noSeqTerm false false phi  in
          match uu____50367 with
          | (comm,phi1) ->
              let phi2 =
                if comm = FStar_Pprint.empty
                then phi1
                else
                  (let uu____50384 =
                     FStar_Pprint.op_Hat_Hat FStar_Pprint.hardline phi1  in
                   FStar_Pprint.op_Hat_Hat comm uu____50384)
                 in
              let jump_break =
                if is_t_atomic
                then (Prims.parse_int "0")
                else (Prims.parse_int "1")  in
              let uu____50393 =
                let uu____50394 = FStar_Pprint.optional p_aqual aqual_opt  in
                FStar_Pprint.op_Hat_Hat uu____50394 binder  in
              let uu____50395 =
                let uu____50396 = p_appTerm t  in
                let uu____50397 =
                  let uu____50398 =
                    let uu____50399 =
                      let uu____50400 = soft_braces_with_nesting_tight phi2
                         in
                      let uu____50401 = soft_braces_with_nesting phi2  in
                      FStar_Pprint.ifflat uu____50400 uu____50401  in
                    FStar_Pprint.group uu____50399  in
                  FStar_Pprint.jump (Prims.parse_int "2") jump_break
                    uu____50398
                   in
                FStar_Pprint.op_Hat_Hat uu____50396 uu____50397  in
              (uu____50393, uu____50395)

and (p_binders_list :
  Prims.bool ->
    FStar_Parser_AST.binder Prims.list -> FStar_Pprint.document Prims.list)
  = fun is_atomic  -> fun bs  -> FStar_List.map (p_binder is_atomic) bs

and (p_binders :
  Prims.bool -> FStar_Parser_AST.binder Prims.list -> FStar_Pprint.document)
  =
  fun is_atomic  ->
    fun bs  ->
      let uu____50415 = p_binders_list is_atomic bs  in
      separate_or_flow break1 uu____50415

and (text_of_id_or_underscore : FStar_Ident.ident -> FStar_Pprint.document) =
  fun lid  ->
    let uu____50419 =
      (FStar_Util.starts_with lid.FStar_Ident.idText
         FStar_Ident.reserved_prefix)
        &&
        (let uu____50422 = FStar_Options.print_real_names ()  in
         Prims.op_Negation uu____50422)
       in
    if uu____50419
    then FStar_Pprint.underscore
    else (let uu____50427 = FStar_Ident.text_of_id lid  in str uu____50427)

and (text_of_lid_or_underscore : FStar_Ident.lident -> FStar_Pprint.document)
  =
  fun lid  ->
    let uu____50430 =
      (FStar_Util.starts_with (lid.FStar_Ident.ident).FStar_Ident.idText
         FStar_Ident.reserved_prefix)
        &&
        (let uu____50433 = FStar_Options.print_real_names ()  in
         Prims.op_Negation uu____50433)
       in
    if uu____50430
    then FStar_Pprint.underscore
    else (let uu____50438 = FStar_Ident.text_of_lid lid  in str uu____50438)

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
          let uu____50459 = FStar_Pprint.op_Hat_Hat doc1 sep  in
          FStar_Pprint.group uu____50459
        else
          (let uu____50462 =
             let uu____50463 =
               let uu____50464 =
                 let uu____50465 =
                   let uu____50466 = FStar_Pprint.op_Hat_Hat break1 comm  in
                   FStar_Pprint.op_Hat_Hat sep uu____50466  in
                 FStar_Pprint.op_Hat_Hat doc1 uu____50465  in
               FStar_Pprint.group uu____50464  in
             let uu____50467 =
               let uu____50468 =
                 let uu____50469 = FStar_Pprint.op_Hat_Hat doc1 sep  in
                 FStar_Pprint.op_Hat_Hat FStar_Pprint.hardline uu____50469
                  in
               FStar_Pprint.op_Hat_Hat comm uu____50468  in
             FStar_Pprint.ifflat uu____50463 uu____50467  in
           FStar_All.pipe_left FStar_Pprint.group uu____50462)

and (p_term :
  Prims.bool -> Prims.bool -> FStar_Parser_AST.term -> FStar_Pprint.document)
  =
  fun ps  ->
    fun pb  ->
      fun e  ->
        match e.FStar_Parser_AST.tm with
        | FStar_Parser_AST.Seq (e1,e2) ->
            let uu____50477 = p_noSeqTerm true false e1  in
            (match uu____50477 with
             | (comm,t1) ->
                 let uu____50486 =
                   inline_comment_or_above comm t1 FStar_Pprint.semi  in
                 let uu____50487 =
                   let uu____50488 = p_term ps pb e2  in
                   FStar_Pprint.op_Hat_Hat FStar_Pprint.hardline uu____50488
                    in
                 FStar_Pprint.op_Hat_Hat uu____50486 uu____50487)
        | FStar_Parser_AST.Bind (x,e1,e2) ->
            let uu____50492 =
              let uu____50493 =
                let uu____50494 =
                  let uu____50495 = p_lident x  in
                  let uu____50496 =
                    FStar_Pprint.op_Hat_Hat FStar_Pprint.space
                      FStar_Pprint.long_left_arrow
                     in
                  FStar_Pprint.op_Hat_Hat uu____50495 uu____50496  in
                let uu____50497 =
                  let uu____50498 = p_noSeqTermAndComment true false e1  in
                  let uu____50501 =
                    FStar_Pprint.op_Hat_Hat FStar_Pprint.space
                      FStar_Pprint.semi
                     in
                  FStar_Pprint.op_Hat_Hat uu____50498 uu____50501  in
                op_Hat_Slash_Plus_Hat uu____50494 uu____50497  in
              FStar_Pprint.group uu____50493  in
            let uu____50502 = p_term ps pb e2  in
            FStar_Pprint.op_Hat_Slash_Hat uu____50492 uu____50502
        | uu____50503 ->
            let uu____50504 = p_noSeqTermAndComment ps pb e  in
            FStar_Pprint.group uu____50504

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
            let uu____50516 = p_noSeqTerm true false e1  in
            (match uu____50516 with
             | (comm,t1) ->
                 let uu____50529 =
                   let uu____50530 =
                     let uu____50531 =
                       FStar_Pprint.op_Hat_Hat t1 FStar_Pprint.semi  in
                     FStar_Pprint.group uu____50531  in
                   let uu____50532 =
                     let uu____50533 = p_term ps pb e2  in
                     FStar_Pprint.op_Hat_Hat FStar_Pprint.hardline
                       uu____50533
                      in
                   FStar_Pprint.op_Hat_Hat uu____50530 uu____50532  in
                 (comm, uu____50529))
        | FStar_Parser_AST.Bind (x,e1,e2) ->
            let uu____50537 =
              let uu____50538 =
                let uu____50539 =
                  let uu____50540 =
                    let uu____50541 = p_lident x  in
                    let uu____50542 =
                      FStar_Pprint.op_Hat_Hat FStar_Pprint.space
                        FStar_Pprint.long_left_arrow
                       in
                    FStar_Pprint.op_Hat_Hat uu____50541 uu____50542  in
                  let uu____50543 =
                    let uu____50544 = p_noSeqTermAndComment true false e1  in
                    let uu____50547 =
                      FStar_Pprint.op_Hat_Hat FStar_Pprint.space
                        FStar_Pprint.semi
                       in
                    FStar_Pprint.op_Hat_Hat uu____50544 uu____50547  in
                  op_Hat_Slash_Plus_Hat uu____50540 uu____50543  in
                FStar_Pprint.group uu____50539  in
              let uu____50548 = p_term ps pb e2  in
              FStar_Pprint.op_Hat_Slash_Hat uu____50538 uu____50548  in
            (FStar_Pprint.empty, uu____50537)
        | uu____50549 -> p_noSeqTerm ps pb e

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
            let uu____50569 =
              let uu____50570 = p_tmIff e1  in
              let uu____50571 =
                let uu____50572 =
                  let uu____50573 = p_typ ps pb t  in
                  FStar_Pprint.op_Hat_Slash_Hat FStar_Pprint.colon
                    uu____50573
                   in
                FStar_Pprint.op_Hat_Hat FStar_Pprint.langle uu____50572  in
              FStar_Pprint.op_Hat_Slash_Hat uu____50570 uu____50571  in
            FStar_Pprint.group uu____50569
        | FStar_Parser_AST.Ascribed (e1,t,FStar_Pervasives_Native.Some tac)
            ->
            let uu____50579 =
              let uu____50580 = p_tmIff e1  in
              let uu____50581 =
                let uu____50582 =
                  let uu____50583 =
                    let uu____50584 = p_typ false false t  in
                    let uu____50587 =
                      let uu____50588 = str "by"  in
                      let uu____50590 = p_typ ps pb tac  in
                      FStar_Pprint.op_Hat_Slash_Hat uu____50588 uu____50590
                       in
                    FStar_Pprint.op_Hat_Slash_Hat uu____50584 uu____50587  in
                  FStar_Pprint.op_Hat_Slash_Hat FStar_Pprint.colon
                    uu____50583
                   in
                FStar_Pprint.op_Hat_Hat FStar_Pprint.langle uu____50582  in
              FStar_Pprint.op_Hat_Slash_Hat uu____50580 uu____50581  in
            FStar_Pprint.group uu____50579
        | FStar_Parser_AST.Op
            ({ FStar_Ident.idText = ".()<-";
               FStar_Ident.idRange = uu____50591;_},e1::e2::e3::[])
            ->
            let uu____50598 =
              let uu____50599 =
                let uu____50600 =
                  let uu____50601 = p_atomicTermNotQUident e1  in
                  let uu____50602 =
                    let uu____50603 =
                      let uu____50604 =
                        let uu____50605 = p_term false false e2  in
                        soft_parens_with_nesting uu____50605  in
                      let uu____50608 =
                        FStar_Pprint.op_Hat_Hat FStar_Pprint.space
                          FStar_Pprint.larrow
                         in
                      FStar_Pprint.op_Hat_Hat uu____50604 uu____50608  in
                    FStar_Pprint.op_Hat_Hat FStar_Pprint.dot uu____50603  in
                  FStar_Pprint.op_Hat_Hat uu____50601 uu____50602  in
                FStar_Pprint.group uu____50600  in
              let uu____50609 =
                let uu____50610 = p_noSeqTermAndComment ps pb e3  in
                jump2 uu____50610  in
              FStar_Pprint.op_Hat_Hat uu____50599 uu____50609  in
            FStar_Pprint.group uu____50598
        | FStar_Parser_AST.Op
            ({ FStar_Ident.idText = ".[]<-";
               FStar_Ident.idRange = uu____50611;_},e1::e2::e3::[])
            ->
            let uu____50618 =
              let uu____50619 =
                let uu____50620 =
                  let uu____50621 = p_atomicTermNotQUident e1  in
                  let uu____50622 =
                    let uu____50623 =
                      let uu____50624 =
                        let uu____50625 = p_term false false e2  in
                        soft_brackets_with_nesting uu____50625  in
                      let uu____50628 =
                        FStar_Pprint.op_Hat_Hat FStar_Pprint.space
                          FStar_Pprint.larrow
                         in
                      FStar_Pprint.op_Hat_Hat uu____50624 uu____50628  in
                    FStar_Pprint.op_Hat_Hat FStar_Pprint.dot uu____50623  in
                  FStar_Pprint.op_Hat_Hat uu____50621 uu____50622  in
                FStar_Pprint.group uu____50620  in
              let uu____50629 =
                let uu____50630 = p_noSeqTermAndComment ps pb e3  in
                jump2 uu____50630  in
              FStar_Pprint.op_Hat_Hat uu____50619 uu____50629  in
            FStar_Pprint.group uu____50618
        | FStar_Parser_AST.Requires (e1,wtf) ->
            let uu____50640 =
              let uu____50641 = str "requires"  in
              let uu____50643 = p_typ ps pb e1  in
              FStar_Pprint.op_Hat_Slash_Hat uu____50641 uu____50643  in
            FStar_Pprint.group uu____50640
        | FStar_Parser_AST.Ensures (e1,wtf) ->
            let uu____50653 =
              let uu____50654 = str "ensures"  in
              let uu____50656 = p_typ ps pb e1  in
              FStar_Pprint.op_Hat_Slash_Hat uu____50654 uu____50656  in
            FStar_Pprint.group uu____50653
        | FStar_Parser_AST.Attributes es ->
            let uu____50660 =
              let uu____50661 = str "attributes"  in
              let uu____50663 =
                FStar_Pprint.separate_map break1 p_atomicTerm es  in
              FStar_Pprint.op_Hat_Slash_Hat uu____50661 uu____50663  in
            FStar_Pprint.group uu____50660
        | FStar_Parser_AST.If (e1,e2,e3) ->
            if is_unit e3
            then
              let uu____50668 =
                let uu____50669 =
                  let uu____50670 = str "if"  in
                  let uu____50672 = p_noSeqTermAndComment false false e1  in
                  op_Hat_Slash_Plus_Hat uu____50670 uu____50672  in
                let uu____50675 =
                  let uu____50676 = str "then"  in
                  let uu____50678 = p_noSeqTermAndComment ps pb e2  in
                  op_Hat_Slash_Plus_Hat uu____50676 uu____50678  in
                FStar_Pprint.op_Hat_Slash_Hat uu____50669 uu____50675  in
              FStar_Pprint.group uu____50668
            else
              (let e2_doc =
                 match e2.FStar_Parser_AST.tm with
                 | FStar_Parser_AST.If (uu____50682,uu____50683,e31) when
                     is_unit e31 ->
                     let uu____50685 = p_noSeqTermAndComment false false e2
                        in
                     soft_parens_with_nesting uu____50685
                 | uu____50688 -> p_noSeqTermAndComment false false e2  in
               let uu____50691 =
                 let uu____50692 =
                   let uu____50693 = str "if"  in
                   let uu____50695 = p_noSeqTermAndComment false false e1  in
                   op_Hat_Slash_Plus_Hat uu____50693 uu____50695  in
                 let uu____50698 =
                   let uu____50699 =
                     let uu____50700 = str "then"  in
                     op_Hat_Slash_Plus_Hat uu____50700 e2_doc  in
                   let uu____50702 =
                     let uu____50703 = str "else"  in
                     let uu____50705 = p_noSeqTermAndComment ps pb e3  in
                     op_Hat_Slash_Plus_Hat uu____50703 uu____50705  in
                   FStar_Pprint.op_Hat_Slash_Hat uu____50699 uu____50702  in
                 FStar_Pprint.op_Hat_Slash_Hat uu____50692 uu____50698  in
               FStar_Pprint.group uu____50691)
        | FStar_Parser_AST.TryWith (e1,branches) ->
            let uu____50728 =
              let uu____50729 =
                let uu____50730 =
                  let uu____50731 = str "try"  in
                  let uu____50733 = p_noSeqTermAndComment false false e1  in
                  prefix2 uu____50731 uu____50733  in
                let uu____50736 =
                  let uu____50737 = str "with"  in
                  let uu____50739 =
                    separate_map_last FStar_Pprint.hardline p_patternBranch
                      branches
                     in
                  FStar_Pprint.op_Hat_Slash_Hat uu____50737 uu____50739  in
                FStar_Pprint.op_Hat_Slash_Hat uu____50730 uu____50736  in
              FStar_Pprint.group uu____50729  in
            let uu____50748 = paren_if (ps || pb)  in uu____50748 uu____50728
        | FStar_Parser_AST.Match (e1,branches) ->
            let uu____50775 =
              let uu____50776 =
                let uu____50777 =
                  let uu____50778 = str "match"  in
                  let uu____50780 = p_noSeqTermAndComment false false e1  in
                  let uu____50783 = str "with"  in
                  FStar_Pprint.surround (Prims.parse_int "2")
                    (Prims.parse_int "1") uu____50778 uu____50780 uu____50783
                   in
                let uu____50787 =
                  separate_map_last FStar_Pprint.hardline p_patternBranch
                    branches
                   in
                FStar_Pprint.op_Hat_Slash_Hat uu____50777 uu____50787  in
              FStar_Pprint.group uu____50776  in
            let uu____50796 = paren_if (ps || pb)  in uu____50796 uu____50775
        | FStar_Parser_AST.LetOpen (uid,e1) ->
            let uu____50803 =
              let uu____50804 =
                let uu____50805 =
                  let uu____50806 = str "let open"  in
                  let uu____50808 = p_quident uid  in
                  let uu____50809 = str "in"  in
                  FStar_Pprint.surround (Prims.parse_int "2")
                    (Prims.parse_int "1") uu____50806 uu____50808 uu____50809
                   in
                let uu____50813 = p_term false pb e1  in
                FStar_Pprint.op_Hat_Slash_Hat uu____50805 uu____50813  in
              FStar_Pprint.group uu____50804  in
            let uu____50815 = paren_if ps  in uu____50815 uu____50803
        | FStar_Parser_AST.Let (q,lbs,e1) ->
            let p_lb q1 uu____50880 is_last =
              match uu____50880 with
              | (a,(pat,e2)) ->
                  let attrs = p_attrs_opt a  in
                  let doc_let_or_and =
                    match q1 with
                    | FStar_Pervasives_Native.Some (FStar_Parser_AST.Rec ) ->
                        let uu____50914 =
                          let uu____50915 = str "let"  in
                          let uu____50917 = str "rec"  in
                          FStar_Pprint.op_Hat_Slash_Hat uu____50915
                            uu____50917
                           in
                        FStar_Pprint.group uu____50914
                    | FStar_Pervasives_Native.Some
                        (FStar_Parser_AST.NoLetQualifier ) -> str "let"
                    | uu____50920 -> str "and"  in
                  let doc_pat = p_letlhs doc_let_or_and (pat, e2) true  in
                  let uu____50926 = p_term_sep false false e2  in
                  (match uu____50926 with
                   | (comm,doc_expr) ->
                       let doc_expr1 =
                         inline_comment_or_above comm doc_expr
                           FStar_Pprint.empty
                          in
                       let uu____50936 =
                         if is_last
                         then
                           let uu____50938 =
                             FStar_Pprint.flow break1
                               [doc_pat; FStar_Pprint.equals]
                              in
                           let uu____50939 = str "in"  in
                           FStar_Pprint.surround (Prims.parse_int "2")
                             (Prims.parse_int "1") uu____50938 doc_expr1
                             uu____50939
                         else
                           (let uu____50945 =
                              FStar_Pprint.flow break1
                                [doc_pat; FStar_Pprint.equals; doc_expr1]
                               in
                            FStar_Pprint.hang (Prims.parse_int "2")
                              uu____50945)
                          in
                       FStar_Pprint.op_Hat_Hat attrs uu____50936)
               in
            let l = FStar_List.length lbs  in
            let lbs_docs =
              FStar_List.mapi
                (fun i  ->
                   fun lb  ->
                     if i = (Prims.parse_int "0")
                     then
                       let uu____50996 =
                         p_lb (FStar_Pervasives_Native.Some q) lb
                           (i = (l - (Prims.parse_int "1")))
                          in
                       FStar_Pprint.group uu____50996
                     else
                       (let uu____51007 =
                          p_lb FStar_Pervasives_Native.None lb
                            (i = (l - (Prims.parse_int "1")))
                           in
                        FStar_Pprint.group uu____51007)) lbs
               in
            let lbs_doc =
              let uu____51017 = FStar_Pprint.separate break1 lbs_docs  in
              FStar_Pprint.group uu____51017  in
            let uu____51018 =
              let uu____51019 =
                let uu____51020 =
                  let uu____51021 = p_term false pb e1  in
                  FStar_Pprint.op_Hat_Hat FStar_Pprint.hardline uu____51021
                   in
                FStar_Pprint.op_Hat_Hat lbs_doc uu____51020  in
              FStar_Pprint.group uu____51019  in
            let uu____51023 = paren_if ps  in uu____51023 uu____51018
        | FStar_Parser_AST.Abs
            ({ FStar_Parser_AST.pat = FStar_Parser_AST.PatVar (x,typ_opt);
               FStar_Parser_AST.prange = uu____51030;_}::[],{
                                                              FStar_Parser_AST.tm
                                                                =
                                                                FStar_Parser_AST.Match
                                                                (maybe_x,branches);
                                                              FStar_Parser_AST.range
                                                                = uu____51033;
                                                              FStar_Parser_AST.level
                                                                = uu____51034;_})
            when matches_var maybe_x x ->
            let uu____51061 =
              let uu____51062 =
                let uu____51063 = str "function"  in
                let uu____51065 =
                  separate_map_last FStar_Pprint.hardline p_patternBranch
                    branches
                   in
                FStar_Pprint.op_Hat_Slash_Hat uu____51063 uu____51065  in
              FStar_Pprint.group uu____51062  in
            let uu____51074 = paren_if (ps || pb)  in uu____51074 uu____51061
        | FStar_Parser_AST.Quote (e1,FStar_Parser_AST.Dynamic ) ->
            let uu____51080 =
              let uu____51081 = str "quote"  in
              let uu____51083 = p_noSeqTermAndComment ps pb e1  in
              FStar_Pprint.op_Hat_Slash_Hat uu____51081 uu____51083  in
            FStar_Pprint.group uu____51080
        | FStar_Parser_AST.Quote (e1,FStar_Parser_AST.Static ) ->
            let uu____51085 =
              let uu____51086 = str "`"  in
              let uu____51088 = p_noSeqTermAndComment ps pb e1  in
              FStar_Pprint.op_Hat_Hat uu____51086 uu____51088  in
            FStar_Pprint.group uu____51085
        | FStar_Parser_AST.VQuote e1 ->
            let uu____51090 =
              let uu____51091 = str "`%"  in
              let uu____51093 = p_noSeqTermAndComment ps pb e1  in
              FStar_Pprint.op_Hat_Hat uu____51091 uu____51093  in
            FStar_Pprint.group uu____51090
        | FStar_Parser_AST.Antiquote
            {
              FStar_Parser_AST.tm = FStar_Parser_AST.Quote
                (e1,FStar_Parser_AST.Dynamic );
              FStar_Parser_AST.range = uu____51095;
              FStar_Parser_AST.level = uu____51096;_}
            ->
            let uu____51097 =
              let uu____51098 = str "`@"  in
              let uu____51100 = p_noSeqTermAndComment ps pb e1  in
              FStar_Pprint.op_Hat_Hat uu____51098 uu____51100  in
            FStar_Pprint.group uu____51097
        | FStar_Parser_AST.Antiquote e1 ->
            let uu____51102 =
              let uu____51103 = str "`#"  in
              let uu____51105 = p_noSeqTermAndComment ps pb e1  in
              FStar_Pprint.op_Hat_Hat uu____51103 uu____51105  in
            FStar_Pprint.group uu____51102
        | FStar_Parser_AST.CalcProof (rel,init1,steps) ->
            let head1 =
              let uu____51114 = str "calc"  in
              let uu____51116 =
                let uu____51117 =
                  let uu____51118 = p_noSeqTermAndComment false false rel  in
                  let uu____51121 =
                    FStar_Pprint.op_Hat_Hat FStar_Pprint.space
                      FStar_Pprint.lbrace
                     in
                  FStar_Pprint.op_Hat_Hat uu____51118 uu____51121  in
                FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____51117  in
              FStar_Pprint.op_Hat_Hat uu____51114 uu____51116  in
            let bot = FStar_Pprint.rbrace  in
            let uu____51123 =
              FStar_Pprint.op_Hat_Hat FStar_Pprint.hardline bot  in
            let uu____51124 =
              let uu____51125 =
                let uu____51126 =
                  let uu____51127 = p_noSeqTermAndComment false false init1
                     in
                  let uu____51130 =
                    let uu____51131 = str ";"  in
                    let uu____51133 =
                      let uu____51134 =
                        separate_map_last FStar_Pprint.hardline p_calcStep
                          steps
                         in
                      FStar_Pprint.op_Hat_Hat FStar_Pprint.hardline
                        uu____51134
                       in
                    FStar_Pprint.op_Hat_Hat uu____51131 uu____51133  in
                  FStar_Pprint.op_Hat_Hat uu____51127 uu____51130  in
                FStar_Pprint.op_Hat_Hat FStar_Pprint.hardline uu____51126  in
              FStar_All.pipe_left (FStar_Pprint.nest (Prims.parse_int "2"))
                uu____51125
               in
            FStar_Pprint.enclose head1 uu____51123 uu____51124
        | uu____51136 -> p_typ ps pb e

and (p_calcStep :
  Prims.bool -> FStar_Parser_AST.calc_step -> FStar_Pprint.document) =
  fun uu____51137  ->
    fun uu____51138  ->
      match uu____51138 with
      | FStar_Parser_AST.CalcStep (rel,just,next) ->
          let uu____51143 =
            let uu____51144 = p_noSeqTermAndComment false false rel  in
            let uu____51147 =
              let uu____51148 =
                let uu____51149 =
                  let uu____51150 =
                    let uu____51151 = p_noSeqTermAndComment false false just
                       in
                    let uu____51154 =
                      let uu____51155 =
                        let uu____51156 =
                          let uu____51157 =
                            let uu____51158 =
                              p_noSeqTermAndComment false false next  in
                            let uu____51161 = str ";"  in
                            FStar_Pprint.op_Hat_Hat uu____51158 uu____51161
                             in
                          FStar_Pprint.op_Hat_Hat FStar_Pprint.hardline
                            uu____51157
                           in
                        FStar_Pprint.op_Hat_Hat FStar_Pprint.rbrace
                          uu____51156
                         in
                      FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____51155
                       in
                    FStar_Pprint.op_Hat_Hat uu____51151 uu____51154  in
                  FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____51150  in
                FStar_Pprint.op_Hat_Hat FStar_Pprint.lbrace uu____51149  in
              FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____51148  in
            FStar_Pprint.op_Hat_Hat uu____51144 uu____51147  in
          FStar_Pprint.group uu____51143

and (p_attrs_opt :
  FStar_Parser_AST.term Prims.list FStar_Pervasives_Native.option ->
    FStar_Pprint.document)
  =
  fun uu___335_51163  ->
    match uu___335_51163 with
    | FStar_Pervasives_Native.None  -> FStar_Pprint.empty
    | FStar_Pervasives_Native.Some terms ->
        let uu____51175 =
          let uu____51176 = str "[@"  in
          let uu____51178 =
            let uu____51179 =
              FStar_Pprint.separate_map break1 p_atomicTerm terms  in
            let uu____51180 = str "]"  in
            FStar_Pprint.op_Hat_Slash_Hat uu____51179 uu____51180  in
          FStar_Pprint.op_Hat_Slash_Hat uu____51176 uu____51178  in
        FStar_Pprint.group uu____51175

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
                 let uu____51217 =
                   let uu____51218 =
                     let uu____51219 = p_quantifier e  in
                     FStar_Pprint.op_Hat_Hat uu____51219 FStar_Pprint.space
                      in
                   FStar_Pprint.soft_surround (Prims.parse_int "2")
                     (Prims.parse_int "0") uu____51218 binders_doc
                     FStar_Pprint.dot
                    in
                 prefix2 uu____51217 term_doc
             | pats ->
                 let uu____51227 =
                   let uu____51228 =
                     let uu____51229 =
                       let uu____51230 =
                         let uu____51231 = p_quantifier e  in
                         FStar_Pprint.op_Hat_Hat uu____51231
                           FStar_Pprint.space
                          in
                       FStar_Pprint.soft_surround (Prims.parse_int "2")
                         (Prims.parse_int "0") uu____51230 binders_doc
                         FStar_Pprint.dot
                        in
                     let uu____51234 = p_trigger trigger  in
                     prefix2 uu____51229 uu____51234  in
                   FStar_Pprint.group uu____51228  in
                 prefix2 uu____51227 term_doc)
        | FStar_Parser_AST.QExists (bs,trigger,e1) ->
            let binders_doc = p_binders true bs  in
            let term_doc = p_noSeqTermAndComment ps pb e1  in
            (match trigger with
             | [] ->
                 let uu____51255 =
                   let uu____51256 =
                     let uu____51257 = p_quantifier e  in
                     FStar_Pprint.op_Hat_Hat uu____51257 FStar_Pprint.space
                      in
                   FStar_Pprint.soft_surround (Prims.parse_int "2")
                     (Prims.parse_int "0") uu____51256 binders_doc
                     FStar_Pprint.dot
                    in
                 prefix2 uu____51255 term_doc
             | pats ->
                 let uu____51265 =
                   let uu____51266 =
                     let uu____51267 =
                       let uu____51268 =
                         let uu____51269 = p_quantifier e  in
                         FStar_Pprint.op_Hat_Hat uu____51269
                           FStar_Pprint.space
                          in
                       FStar_Pprint.soft_surround (Prims.parse_int "2")
                         (Prims.parse_int "0") uu____51268 binders_doc
                         FStar_Pprint.dot
                        in
                     let uu____51272 = p_trigger trigger  in
                     prefix2 uu____51267 uu____51272  in
                   FStar_Pprint.group uu____51266  in
                 prefix2 uu____51265 term_doc)
        | uu____51273 -> p_simpleTerm ps pb e

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
      let uu____51294 = all_binders_annot t  in
      if uu____51294
      then
        let uu____51297 =
          p_typ_top
            (Binders ((Prims.parse_int "4"), (Prims.parse_int "0"), true))
            false false t
           in
        FStar_Pprint.op_Hat_Hat s uu____51297
      else
        (let uu____51308 =
           let uu____51309 =
             let uu____51310 =
               p_typ_top
                 (Arrows ((Prims.parse_int "2"), (Prims.parse_int "2")))
                 false false t
                in
             FStar_Pprint.op_Hat_Hat s uu____51310  in
           FStar_Pprint.op_Hat_Hat FStar_Pprint.colon uu____51309  in
         FStar_Pprint.group uu____51308)

and (collapse_pats :
  (FStar_Pprint.document * FStar_Pprint.document) Prims.list ->
    FStar_Pprint.document Prims.list)
  =
  fun pats  ->
    let fold_fun bs x =
      let uu____51369 = x  in
      match uu____51369 with
      | (b1,t1) ->
          (match bs with
           | [] -> [([b1], t1)]
           | hd1::tl1 ->
               let uu____51434 = hd1  in
               (match uu____51434 with
                | (b2s,t2) ->
                    if t1 = t2
                    then ((FStar_List.append b2s [b1]), t1) :: tl1
                    else ([b1], t1) :: hd1 :: tl1))
       in
    let p_collapsed_binder cb =
      let uu____51506 = cb  in
      match uu____51506 with
      | (bs,typ) ->
          (match bs with
           | [] -> failwith "Impossible"
           | b::[] -> cat_with_colon b typ
           | hd1::tl1 ->
               let uu____51525 =
                 FStar_List.fold_left
                   (fun x  ->
                      fun y  ->
                        let uu____51531 =
                          FStar_Pprint.op_Hat_Hat FStar_Pprint.space y  in
                        FStar_Pprint.op_Hat_Hat x uu____51531) hd1 tl1
                  in
               cat_with_colon uu____51525 typ)
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
                 FStar_Parser_AST.brange = uu____51610;
                 FStar_Parser_AST.blevel = uu____51611;
                 FStar_Parser_AST.aqual = uu____51612;_},phi))
               when lid.FStar_Ident.idText = lid'.FStar_Ident.idText ->
               let uu____51621 =
                 let uu____51626 = p_ident lid  in
                 p_refinement' aqual uu____51626 t1 phi  in
               FStar_Pervasives_Native.Some uu____51621
           | (FStar_Parser_AST.PatVar (lid,aqual),uu____51633) ->
               let uu____51638 =
                 let uu____51643 =
                   let uu____51644 = FStar_Pprint.optional p_aqual aqual  in
                   let uu____51645 = p_ident lid  in
                   FStar_Pprint.op_Hat_Hat uu____51644 uu____51645  in
                 let uu____51646 = p_tmEqNoRefinement t  in
                 (uu____51643, uu____51646)  in
               FStar_Pervasives_Native.Some uu____51638
           | uu____51651 -> FStar_Pervasives_Native.None)
      | uu____51660 -> FStar_Pervasives_Native.None  in
    let all_unbound p =
      match p.FStar_Parser_AST.pat with
      | FStar_Parser_AST.PatAscribed uu____51673 -> false
      | uu____51685 -> true  in
    let uu____51687 = map_if_all all_binders pats  in
    match uu____51687 with
    | FStar_Pervasives_Native.Some bs ->
        let uu____51719 = collapse_pats bs  in
        (uu____51719,
          (Binders ((Prims.parse_int "4"), (Prims.parse_int "0"), true)))
    | FStar_Pervasives_Native.None  ->
        let uu____51736 = FStar_List.map p_atomicPattern pats  in
        (uu____51736,
          (Binders ((Prims.parse_int "4"), (Prims.parse_int "0"), false)))

and (p_quantifier : FStar_Parser_AST.term -> FStar_Pprint.document) =
  fun e  ->
    match e.FStar_Parser_AST.tm with
    | FStar_Parser_AST.QForall uu____51748 -> str "forall"
    | FStar_Parser_AST.QExists uu____51762 -> str "exists"
    | uu____51776 ->
        failwith "Imposible : p_quantifier called on a non-quantifier term"

and (p_trigger :
  FStar_Parser_AST.term Prims.list Prims.list -> FStar_Pprint.document) =
  fun uu___336_51778  ->
    match uu___336_51778 with
    | [] -> FStar_Pprint.empty
    | pats ->
        let uu____51790 =
          let uu____51791 =
            let uu____51792 =
              let uu____51793 = str "pattern"  in
              let uu____51795 =
                let uu____51796 =
                  let uu____51797 = p_disjunctivePats pats  in
                  FStar_Pprint.jump (Prims.parse_int "2")
                    (Prims.parse_int "0") uu____51797
                   in
                FStar_Pprint.op_Hat_Hat uu____51796 FStar_Pprint.rbrace  in
              FStar_Pprint.op_Hat_Slash_Hat uu____51793 uu____51795  in
            FStar_Pprint.op_Hat_Hat FStar_Pprint.colon uu____51792  in
          FStar_Pprint.op_Hat_Hat FStar_Pprint.lbrace uu____51791  in
        FStar_Pprint.group uu____51790

and (p_disjunctivePats :
  FStar_Parser_AST.term Prims.list Prims.list -> FStar_Pprint.document) =
  fun pats  ->
    let uu____51805 = str "\\/"  in
    FStar_Pprint.separate_map uu____51805 p_conjunctivePats pats

and (p_conjunctivePats :
  FStar_Parser_AST.term Prims.list -> FStar_Pprint.document) =
  fun pats  ->
    let uu____51812 =
      let uu____51813 = FStar_Pprint.op_Hat_Hat FStar_Pprint.semi break1  in
      FStar_Pprint.separate_map uu____51813 p_appTerm pats  in
    FStar_Pprint.group uu____51812

and (p_simpleTerm :
  Prims.bool -> Prims.bool -> FStar_Parser_AST.term -> FStar_Pprint.document)
  =
  fun ps  ->
    fun pb  ->
      fun e  ->
        match e.FStar_Parser_AST.tm with
        | FStar_Parser_AST.Abs (pats,e1) ->
            let uu____51825 = p_term_sep false pb e1  in
            (match uu____51825 with
             | (comm,doc1) ->
                 let prefix1 =
                   let uu____51834 = str "fun"  in
                   let uu____51836 =
                     let uu____51837 =
                       FStar_Pprint.separate_map break1 p_atomicPattern pats
                        in
                     FStar_Pprint.op_Hat_Slash_Hat uu____51837
                       FStar_Pprint.rarrow
                      in
                   op_Hat_Slash_Plus_Hat uu____51834 uu____51836  in
                 let uu____51838 =
                   if comm <> FStar_Pprint.empty
                   then
                     let uu____51840 =
                       let uu____51841 =
                         let uu____51842 =
                           FStar_Pprint.op_Hat_Hat FStar_Pprint.hardline doc1
                            in
                         FStar_Pprint.op_Hat_Hat comm uu____51842  in
                       FStar_Pprint.op_Hat_Hat FStar_Pprint.hardline
                         uu____51841
                        in
                     FStar_Pprint.op_Hat_Hat prefix1 uu____51840
                   else
                     (let uu____51845 = op_Hat_Slash_Plus_Hat prefix1 doc1
                         in
                      FStar_Pprint.group uu____51845)
                    in
                 let uu____51846 = paren_if ps  in uu____51846 uu____51838)
        | uu____51851 -> p_tmIff e

and (p_maybeFocusArrow : Prims.bool -> FStar_Pprint.document) =
  fun b  -> if b then str "~>" else FStar_Pprint.rarrow

and (p_patternBranch :
  Prims.bool ->
    (FStar_Parser_AST.pattern * FStar_Parser_AST.term
      FStar_Pervasives_Native.option * FStar_Parser_AST.term) ->
      FStar_Pprint.document)
  =
  fun pb  ->
    fun uu____51859  ->
      match uu____51859 with
      | (pat,when_opt,e) ->
          let one_pattern_branch p =
            let branch =
              match when_opt with
              | FStar_Pervasives_Native.None  ->
                  let uu____51883 =
                    let uu____51884 =
                      let uu____51885 =
                        let uu____51886 = p_tuplePattern p  in
                        let uu____51887 =
                          FStar_Pprint.op_Hat_Hat FStar_Pprint.space
                            FStar_Pprint.rarrow
                           in
                        FStar_Pprint.op_Hat_Hat uu____51886 uu____51887  in
                      FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____51885
                       in
                    FStar_Pprint.op_Hat_Hat FStar_Pprint.bar uu____51884  in
                  FStar_Pprint.group uu____51883
              | FStar_Pervasives_Native.Some f ->
                  let uu____51889 =
                    let uu____51890 =
                      let uu____51891 =
                        let uu____51892 =
                          let uu____51893 =
                            let uu____51894 = p_tuplePattern p  in
                            let uu____51895 = str "when"  in
                            FStar_Pprint.op_Hat_Slash_Hat uu____51894
                              uu____51895
                             in
                          FStar_Pprint.group uu____51893  in
                        let uu____51897 =
                          let uu____51898 =
                            let uu____51901 = p_tmFormula f  in
                            [uu____51901; FStar_Pprint.rarrow]  in
                          FStar_Pprint.flow break1 uu____51898  in
                        FStar_Pprint.op_Hat_Slash_Hat uu____51892 uu____51897
                         in
                      FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____51891
                       in
                    FStar_Pprint.op_Hat_Hat FStar_Pprint.bar uu____51890  in
                  FStar_Pprint.hang (Prims.parse_int "2") uu____51889
               in
            let uu____51903 = p_term_sep false pb e  in
            match uu____51903 with
            | (comm,doc1) ->
                if pb
                then
                  (if comm = FStar_Pprint.empty
                   then
                     let uu____51913 = op_Hat_Slash_Plus_Hat branch doc1  in
                     FStar_Pprint.group uu____51913
                   else
                     (let uu____51916 =
                        let uu____51917 =
                          let uu____51918 =
                            let uu____51919 =
                              let uu____51920 =
                                FStar_Pprint.op_Hat_Hat break1 comm  in
                              FStar_Pprint.op_Hat_Hat doc1 uu____51920  in
                            op_Hat_Slash_Plus_Hat branch uu____51919  in
                          FStar_Pprint.group uu____51918  in
                        let uu____51921 =
                          let uu____51922 =
                            let uu____51923 =
                              inline_comment_or_above comm doc1
                                FStar_Pprint.empty
                               in
                            jump2 uu____51923  in
                          FStar_Pprint.op_Hat_Hat branch uu____51922  in
                        FStar_Pprint.ifflat uu____51917 uu____51921  in
                      FStar_Pprint.group uu____51916))
                else
                  if comm <> FStar_Pprint.empty
                  then
                    (let uu____51927 =
                       let uu____51928 =
                         FStar_Pprint.op_Hat_Hat FStar_Pprint.hardline doc1
                          in
                       FStar_Pprint.op_Hat_Hat comm uu____51928  in
                     op_Hat_Slash_Plus_Hat branch uu____51927)
                  else op_Hat_Slash_Plus_Hat branch doc1
             in
          (match pat.FStar_Parser_AST.pat with
           | FStar_Parser_AST.PatOr pats ->
               (match FStar_List.rev pats with
                | hd1::tl1 ->
                    let last_pat_branch = one_pattern_branch hd1  in
                    let uu____51939 =
                      let uu____51940 =
                        let uu____51941 =
                          let uu____51942 =
                            let uu____51943 =
                              let uu____51944 =
                                FStar_Pprint.op_Hat_Hat FStar_Pprint.bar
                                  FStar_Pprint.space
                                 in
                              FStar_Pprint.op_Hat_Hat break1 uu____51944  in
                            FStar_Pprint.separate_map uu____51943
                              p_tuplePattern (FStar_List.rev tl1)
                             in
                          FStar_Pprint.op_Hat_Slash_Hat uu____51942
                            last_pat_branch
                           in
                        FStar_Pprint.op_Hat_Hat FStar_Pprint.space
                          uu____51941
                         in
                      FStar_Pprint.op_Hat_Hat FStar_Pprint.bar uu____51940
                       in
                    FStar_Pprint.group uu____51939
                | [] ->
                    failwith "Impossible: disjunctive pattern can't be empty")
           | uu____51946 -> one_pattern_branch pat)

and (p_tmIff : FStar_Parser_AST.term -> FStar_Pprint.document) =
  fun e  ->
    match e.FStar_Parser_AST.tm with
    | FStar_Parser_AST.Op
        ({ FStar_Ident.idText = "<==>"; FStar_Ident.idRange = uu____51948;_},e1::e2::[])
        ->
        let uu____51954 = str "<==>"  in
        let uu____51956 = p_tmImplies e1  in
        let uu____51957 = p_tmIff e2  in
        infix0 uu____51954 uu____51956 uu____51957
    | uu____51958 -> p_tmImplies e

and (p_tmImplies : FStar_Parser_AST.term -> FStar_Pprint.document) =
  fun e  ->
    match e.FStar_Parser_AST.tm with
    | FStar_Parser_AST.Op
        ({ FStar_Ident.idText = "==>"; FStar_Ident.idRange = uu____51960;_},e1::e2::[])
        ->
        let uu____51966 = str "==>"  in
        let uu____51968 =
          p_tmArrow (Arrows ((Prims.parse_int "2"), (Prims.parse_int "2")))
            false p_tmFormula e1
           in
        let uu____51974 = p_tmImplies e2  in
        infix0 uu____51966 uu____51968 uu____51974
    | uu____51975 ->
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
          let uu____51989 =
            FStar_List.splitAt
              ((FStar_List.length terms) - (Prims.parse_int "1")) terms
             in
          match uu____51989 with
          | (terms',last1) ->
              let uu____52009 =
                match style with
                | Arrows (n1,ln) ->
                    let uu____52044 =
                      let uu____52045 =
                        FStar_Pprint.op_Hat_Hat FStar_Pprint.rarrow break1
                         in
                      FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____52045
                       in
                    let uu____52046 =
                      FStar_Pprint.op_Hat_Hat FStar_Pprint.rarrow
                        FStar_Pprint.space
                       in
                    (n1, ln, terms', uu____52044, uu____52046)
                | Binders (n1,ln,parens1) ->
                    let uu____52060 =
                      if parens1
                      then FStar_List.map soft_parens_with_nesting terms'
                      else terms'  in
                    let uu____52068 =
                      FStar_Pprint.op_Hat_Hat FStar_Pprint.colon
                        FStar_Pprint.space
                       in
                    (n1, ln, uu____52060, break1, uu____52068)
                 in
              (match uu____52009 with
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
                    | _52101 when _52101 = (Prims.parse_int "1") ->
                        FStar_List.hd terms
                    | uu____52102 ->
                        let uu____52103 =
                          let uu____52104 =
                            let uu____52105 =
                              let uu____52106 =
                                FStar_Pprint.separate sep terms'1  in
                              let uu____52107 =
                                let uu____52108 =
                                  FStar_Pprint.op_Hat_Hat last_op1 last2  in
                                FStar_Pprint.op_Hat_Hat one_line_space
                                  uu____52108
                                 in
                              FStar_Pprint.op_Hat_Hat uu____52106 uu____52107
                               in
                            FStar_Pprint.op_Hat_Hat fs uu____52105  in
                          let uu____52109 =
                            let uu____52110 =
                              let uu____52111 =
                                let uu____52112 =
                                  let uu____52113 =
                                    FStar_Pprint.separate sep terms'1  in
                                  FStar_Pprint.op_Hat_Hat fs uu____52113  in
                                let uu____52114 =
                                  let uu____52115 =
                                    let uu____52116 =
                                      let uu____52117 =
                                        FStar_Pprint.op_Hat_Hat sep
                                          single_line_arg_indent
                                         in
                                      let uu____52118 =
                                        FStar_List.map
                                          (fun x  ->
                                             let uu____52124 =
                                               FStar_Pprint.hang
                                                 (Prims.parse_int "2") x
                                                in
                                             FStar_Pprint.align uu____52124)
                                          terms'1
                                         in
                                      FStar_Pprint.separate uu____52117
                                        uu____52118
                                       in
                                    FStar_Pprint.op_Hat_Hat
                                      single_line_arg_indent uu____52116
                                     in
                                  jump2 uu____52115  in
                                FStar_Pprint.ifflat uu____52112 uu____52114
                                 in
                              FStar_Pprint.group uu____52111  in
                            let uu____52126 =
                              let uu____52127 =
                                let uu____52128 =
                                  FStar_Pprint.op_Hat_Hat last_op1 last2  in
                                FStar_Pprint.hang last_n uu____52128  in
                              FStar_Pprint.align uu____52127  in
                            FStar_Pprint.prefix n1 (Prims.parse_int "1")
                              uu____52110 uu____52126
                             in
                          FStar_Pprint.ifflat uu____52104 uu____52109  in
                        FStar_Pprint.group uu____52103))

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
            | Arrows uu____52142 -> p_tmArrow' p_Tm e
            | Binders uu____52149 -> collapse_binders p_Tm e  in
          format_sig style terms false flat_space

and (p_tmArrow' :
  (FStar_Parser_AST.term -> FStar_Pprint.document) ->
    FStar_Parser_AST.term -> FStar_Pprint.document Prims.list)
  =
  fun p_Tm  ->
    fun e  ->
      match e.FStar_Parser_AST.tm with
      | FStar_Parser_AST.Product (bs,tgt) ->
          let uu____52172 = FStar_List.map (fun b  -> p_binder false b) bs
             in
          let uu____52178 = p_tmArrow' p_Tm tgt  in
          FStar_List.append uu____52172 uu____52178
      | uu____52181 -> let uu____52182 = p_Tm e  in [uu____52182]

and (collapse_binders :
  (FStar_Parser_AST.term -> FStar_Pprint.document) ->
    FStar_Parser_AST.term -> FStar_Pprint.document Prims.list)
  =
  fun p_Tm  ->
    fun e  ->
      let rec accumulate_binders p_Tm1 e1 =
        match e1.FStar_Parser_AST.tm with
        | FStar_Parser_AST.Product (bs,tgt) ->
            let uu____52235 = FStar_List.map (fun b  -> p_binder' false b) bs
               in
            let uu____52261 = accumulate_binders p_Tm1 tgt  in
            FStar_List.append uu____52235 uu____52261
        | uu____52284 ->
            let uu____52285 =
              let uu____52296 = p_Tm1 e1  in
              (uu____52296, FStar_Pervasives_Native.None, cat_with_colon)  in
            [uu____52285]
         in
      let fold_fun bs x =
        let uu____52394 = x  in
        match uu____52394 with
        | (b1,t1,f1) ->
            (match bs with
             | [] -> [([b1], t1, f1)]
             | hd1::tl1 ->
                 let uu____52530 = hd1  in
                 (match uu____52530 with
                  | (b2s,t2,uu____52559) ->
                      (match (t1, t2) with
                       | (FStar_Pervasives_Native.Some
                          typ1,FStar_Pervasives_Native.Some typ2) ->
                           if typ1 = typ2
                           then ((FStar_List.append b2s [b1]), t1, f1) :: tl1
                           else ([b1], t1, f1) :: hd1 :: tl1
                       | uu____52669 -> ([b1], t1, f1) :: bs)))
         in
      let p_collapsed_binder cb =
        let uu____52730 = cb  in
        match uu____52730 with
        | (bs,t,f) ->
            (match t with
             | FStar_Pervasives_Native.None  ->
                 (match bs with
                  | b::[] -> b
                  | uu____52759 -> failwith "Impossible")
             | FStar_Pervasives_Native.Some typ ->
                 (match bs with
                  | [] -> failwith "Impossible"
                  | b::[] -> f b typ
                  | hd1::tl1 ->
                      let uu____52772 =
                        FStar_List.fold_left
                          (fun x  ->
                             fun y  ->
                               let uu____52778 =
                                 FStar_Pprint.op_Hat_Hat FStar_Pprint.space y
                                  in
                               FStar_Pprint.op_Hat_Hat x uu____52778) hd1 tl1
                         in
                      f uu____52772 typ))
         in
      let binders =
        let uu____52796 = accumulate_binders p_Tm e  in
        FStar_List.fold_left fold_fun [] uu____52796  in
      map_rev p_collapsed_binder binders

and (p_tmFormula : FStar_Parser_AST.term -> FStar_Pprint.document) =
  fun e  ->
    let conj =
      let uu____52859 =
        let uu____52860 = str "/\\"  in
        FStar_Pprint.op_Hat_Hat uu____52860 break1  in
      FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____52859  in
    let disj =
      let uu____52863 =
        let uu____52864 = str "\\/"  in
        FStar_Pprint.op_Hat_Hat uu____52864 break1  in
      FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____52863  in
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
        ({ FStar_Ident.idText = "\\/"; FStar_Ident.idRange = uu____52884;_},e1::e2::[])
        ->
        let uu____52890 = p_tmDisjunction e1  in
        let uu____52895 =
          let uu____52900 = p_tmConjunction e2  in [uu____52900]  in
        FStar_List.append uu____52890 uu____52895
    | uu____52909 -> let uu____52910 = p_tmConjunction e  in [uu____52910]

and (p_tmConjunction :
  FStar_Parser_AST.term -> FStar_Pprint.document Prims.list) =
  fun e  ->
    match e.FStar_Parser_AST.tm with
    | FStar_Parser_AST.Op
        ({ FStar_Ident.idText = "/\\"; FStar_Ident.idRange = uu____52920;_},e1::e2::[])
        ->
        let uu____52926 = p_tmConjunction e1  in
        let uu____52929 = let uu____52932 = p_tmTuple e2  in [uu____52932]
           in
        FStar_List.append uu____52926 uu____52929
    | uu____52933 -> let uu____52934 = p_tmTuple e  in [uu____52934]

and (p_tmTuple : FStar_Parser_AST.term -> FStar_Pprint.document) =
  fun e  -> with_comment p_tmTuple' e e.FStar_Parser_AST.range

and (p_tmTuple' : FStar_Parser_AST.term -> FStar_Pprint.document) =
  fun e  ->
    match e.FStar_Parser_AST.tm with
    | FStar_Parser_AST.Construct (lid,args) when
        (is_tuple_constructor lid) && (all_explicit args) ->
        let uu____52951 = FStar_Pprint.op_Hat_Hat FStar_Pprint.comma break1
           in
        FStar_Pprint.separate_map uu____52951
          (fun uu____52959  ->
             match uu____52959 with | (e1,uu____52965) -> p_tmEq e1) args
    | uu____52966 -> p_tmEq e

and (paren_if_gt :
  Prims.int -> Prims.int -> FStar_Pprint.document -> FStar_Pprint.document) =
  fun curr  ->
    fun mine  ->
      fun doc1  ->
        if mine <= curr
        then doc1
        else
          (let uu____52975 =
             let uu____52976 =
               FStar_Pprint.op_Hat_Hat doc1 FStar_Pprint.rparen  in
             FStar_Pprint.op_Hat_Hat FStar_Pprint.lparen uu____52976  in
           FStar_Pprint.group uu____52975)

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
               (let uu____52995 = FStar_Ident.text_of_id op  in
                uu____52995 = "="))
              ||
              (let uu____53000 = FStar_Ident.text_of_id op  in
               uu____53000 = "|>")
            ->
            let op1 = FStar_Ident.text_of_id op  in
            let uu____53006 = levels op1  in
            (match uu____53006 with
             | (left1,mine,right1) ->
                 let uu____53025 =
                   let uu____53026 = FStar_All.pipe_left str op1  in
                   let uu____53028 = p_tmEqWith' p_X left1 e1  in
                   let uu____53029 = p_tmEqWith' p_X right1 e2  in
                   infix0 uu____53026 uu____53028 uu____53029  in
                 paren_if_gt curr mine uu____53025)
        | FStar_Parser_AST.Op
            ({ FStar_Ident.idText = ":=";
               FStar_Ident.idRange = uu____53030;_},e1::e2::[])
            ->
            let uu____53036 =
              let uu____53037 = p_tmEqWith p_X e1  in
              let uu____53038 =
                let uu____53039 =
                  let uu____53040 =
                    let uu____53041 = p_tmEqWith p_X e2  in
                    op_Hat_Slash_Plus_Hat FStar_Pprint.equals uu____53041  in
                  FStar_Pprint.op_Hat_Hat FStar_Pprint.colon uu____53040  in
                FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____53039  in
              FStar_Pprint.op_Hat_Hat uu____53037 uu____53038  in
            FStar_Pprint.group uu____53036
        | FStar_Parser_AST.Op
            ({ FStar_Ident.idText = "-"; FStar_Ident.idRange = uu____53042;_},e1::[])
            ->
            let uu____53047 = levels "-"  in
            (match uu____53047 with
             | (left1,mine,right1) ->
                 let uu____53067 = p_tmEqWith' p_X mine e1  in
                 FStar_Pprint.op_Hat_Slash_Hat FStar_Pprint.minus uu____53067)
        | uu____53068 -> p_tmNoEqWith p_X e

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
              (lid,(e1,uu____53116)::(e2,uu____53118)::[]) when
              (FStar_Ident.lid_equals lid FStar_Parser_Const.cons_lid) &&
                (let uu____53138 = is_list e  in
                 Prims.op_Negation uu____53138)
              ->
              let op = "::"  in
              let uu____53143 = levels op  in
              (match uu____53143 with
               | (left1,mine,right1) ->
                   let uu____53162 =
                     let uu____53163 = str op  in
                     let uu____53164 = p_tmNoEqWith' false p_X left1 e1  in
                     let uu____53166 = p_tmNoEqWith' false p_X right1 e2  in
                     infix0 uu____53163 uu____53164 uu____53166  in
                   paren_if_gt curr mine uu____53162)
          | FStar_Parser_AST.Sum (binders,res) ->
              let op = "&"  in
              let uu____53185 = levels op  in
              (match uu____53185 with
               | (left1,mine,right1) ->
                   let p_dsumfst bt =
                     match bt with
                     | FStar_Util.Inl b ->
                         let uu____53219 = p_binder false b  in
                         let uu____53221 =
                           let uu____53222 =
                             let uu____53223 = str op  in
                             FStar_Pprint.op_Hat_Hat uu____53223 break1  in
                           FStar_Pprint.op_Hat_Hat FStar_Pprint.space
                             uu____53222
                            in
                         FStar_Pprint.op_Hat_Hat uu____53219 uu____53221
                     | FStar_Util.Inr t ->
                         let uu____53225 = p_tmNoEqWith' false p_X left1 t
                            in
                         let uu____53227 =
                           let uu____53228 =
                             let uu____53229 = str op  in
                             FStar_Pprint.op_Hat_Hat uu____53229 break1  in
                           FStar_Pprint.op_Hat_Hat FStar_Pprint.space
                             uu____53228
                            in
                         FStar_Pprint.op_Hat_Hat uu____53225 uu____53227
                      in
                   let uu____53230 =
                     let uu____53231 =
                       FStar_Pprint.concat_map p_dsumfst binders  in
                     let uu____53236 = p_tmNoEqWith' false p_X right1 res  in
                     FStar_Pprint.op_Hat_Hat uu____53231 uu____53236  in
                   paren_if_gt curr mine uu____53230)
          | FStar_Parser_AST.Op
              ({ FStar_Ident.idText = "*";
                 FStar_Ident.idRange = uu____53238;_},e1::e2::[])
              when FStar_ST.op_Bang unfold_tuples ->
              let op = "*"  in
              let uu____53268 = levels op  in
              (match uu____53268 with
               | (left1,mine,right1) ->
                   if inside_tuple
                   then
                     let uu____53288 = str op  in
                     let uu____53289 = p_tmNoEqWith' true p_X left1 e1  in
                     let uu____53291 = p_tmNoEqWith' true p_X right1 e2  in
                     infix0 uu____53288 uu____53289 uu____53291
                   else
                     (let uu____53295 =
                        let uu____53296 = str op  in
                        let uu____53297 = p_tmNoEqWith' true p_X left1 e1  in
                        let uu____53299 = p_tmNoEqWith' true p_X right1 e2
                           in
                        infix0 uu____53296 uu____53297 uu____53299  in
                      paren_if_gt curr mine uu____53295))
          | FStar_Parser_AST.Op (op,e1::e2::[]) when is_operatorInfix34 op ->
              let op1 = FStar_Ident.text_of_id op  in
              let uu____53308 = levels op1  in
              (match uu____53308 with
               | (left1,mine,right1) ->
                   let uu____53327 =
                     let uu____53328 = str op1  in
                     let uu____53329 = p_tmNoEqWith' false p_X left1 e1  in
                     let uu____53331 = p_tmNoEqWith' false p_X right1 e2  in
                     infix0 uu____53328 uu____53329 uu____53331  in
                   paren_if_gt curr mine uu____53327)
          | FStar_Parser_AST.Record (with_opt,record_fields) ->
              let uu____53351 =
                let uu____53352 =
                  default_or_map FStar_Pprint.empty p_with_clause with_opt
                   in
                let uu____53353 =
                  let uu____53354 =
                    FStar_Pprint.op_Hat_Hat FStar_Pprint.semi break1  in
                  separate_map_last uu____53354 p_simpleDef record_fields  in
                FStar_Pprint.op_Hat_Hat uu____53352 uu____53353  in
              braces_with_nesting uu____53351
          | FStar_Parser_AST.Op
              ({ FStar_Ident.idText = "~";
                 FStar_Ident.idRange = uu____53359;_},e1::[])
              ->
              let uu____53364 =
                let uu____53365 = str "~"  in
                let uu____53367 = p_atomicTerm e1  in
                FStar_Pprint.op_Hat_Hat uu____53365 uu____53367  in
              FStar_Pprint.group uu____53364
          | FStar_Parser_AST.Paren p when inside_tuple ->
              (match p.FStar_Parser_AST.tm with
               | FStar_Parser_AST.Op
                   ({ FStar_Ident.idText = "*";
                      FStar_Ident.idRange = uu____53369;_},e1::e2::[])
                   ->
                   let op = "*"  in
                   let uu____53378 = levels op  in
                   (match uu____53378 with
                    | (left1,mine,right1) ->
                        let uu____53397 =
                          let uu____53398 = str op  in
                          let uu____53399 = p_tmNoEqWith' true p_X left1 e1
                             in
                          let uu____53401 = p_tmNoEqWith' true p_X right1 e2
                             in
                          infix0 uu____53398 uu____53399 uu____53401  in
                        paren_if_gt curr mine uu____53397)
               | uu____53403 -> p_X e)
          | uu____53404 -> p_X e

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
        let uu____53411 =
          let uu____53412 = p_lident lid  in
          let uu____53413 =
            let uu____53414 = p_appTerm e1  in
            FStar_Pprint.op_Hat_Slash_Hat FStar_Pprint.colon uu____53414  in
          FStar_Pprint.op_Hat_Slash_Hat uu____53412 uu____53413  in
        FStar_Pprint.group uu____53411
    | FStar_Parser_AST.Refine (b,phi) -> p_refinedBinder b phi
    | uu____53417 -> p_appTerm e

and (p_with_clause : FStar_Parser_AST.term -> FStar_Pprint.document) =
  fun e  ->
    let uu____53419 = p_appTerm e  in
    let uu____53420 =
      let uu____53421 =
        let uu____53422 = str "with"  in
        FStar_Pprint.op_Hat_Hat uu____53422 break1  in
      FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____53421  in
    FStar_Pprint.op_Hat_Hat uu____53419 uu____53420

and (p_refinedBinder :
  FStar_Parser_AST.binder -> FStar_Parser_AST.term -> FStar_Pprint.document)
  =
  fun b  ->
    fun phi  ->
      match b.FStar_Parser_AST.b with
      | FStar_Parser_AST.Annotated (lid,t) ->
          let uu____53428 = p_lident lid  in
          p_refinement b.FStar_Parser_AST.aqual uu____53428 t phi
      | FStar_Parser_AST.TAnnotated uu____53429 ->
          failwith "Is this still used ?"
      | FStar_Parser_AST.Variable uu____53435 ->
          let uu____53436 =
            let uu____53438 = FStar_Parser_AST.binder_to_string b  in
            FStar_Util.format1
              "Imposible : a refined binder ought to be annotated %s"
              uu____53438
             in
          failwith uu____53436
      | FStar_Parser_AST.TVariable uu____53441 ->
          let uu____53442 =
            let uu____53444 = FStar_Parser_AST.binder_to_string b  in
            FStar_Util.format1
              "Imposible : a refined binder ought to be annotated %s"
              uu____53444
             in
          failwith uu____53442
      | FStar_Parser_AST.NoName uu____53447 ->
          let uu____53448 =
            let uu____53450 = FStar_Parser_AST.binder_to_string b  in
            FStar_Util.format1
              "Imposible : a refined binder ought to be annotated %s"
              uu____53450
             in
          failwith uu____53448

and (p_simpleDef :
  Prims.bool ->
    (FStar_Ident.lid * FStar_Parser_AST.term) -> FStar_Pprint.document)
  =
  fun ps  ->
    fun uu____53454  ->
      match uu____53454 with
      | (lid,e) ->
          let uu____53462 =
            let uu____53463 = p_qlident lid  in
            let uu____53464 =
              let uu____53465 = p_noSeqTermAndComment ps false e  in
              FStar_Pprint.op_Hat_Slash_Hat FStar_Pprint.equals uu____53465
               in
            FStar_Pprint.op_Hat_Slash_Hat uu____53463 uu____53464  in
          FStar_Pprint.group uu____53462

and (p_appTerm : FStar_Parser_AST.term -> FStar_Pprint.document) =
  fun e  ->
    match e.FStar_Parser_AST.tm with
    | FStar_Parser_AST.App uu____53468 when is_general_application e ->
        let uu____53475 = head_and_args e  in
        (match uu____53475 with
         | (head1,args) ->
             (match args with
              | e1::e2::[] when
                  (FStar_Pervasives_Native.snd e1) = FStar_Parser_AST.Infix
                  ->
                  let uu____53522 = p_argTerm e1  in
                  let uu____53523 =
                    let uu____53524 =
                      let uu____53525 =
                        let uu____53526 = str "`"  in
                        let uu____53528 =
                          let uu____53529 = p_indexingTerm head1  in
                          let uu____53530 = str "`"  in
                          FStar_Pprint.op_Hat_Hat uu____53529 uu____53530  in
                        FStar_Pprint.op_Hat_Hat uu____53526 uu____53528  in
                      FStar_Pprint.group uu____53525  in
                    let uu____53532 = p_argTerm e2  in
                    FStar_Pprint.op_Hat_Slash_Hat uu____53524 uu____53532  in
                  FStar_Pprint.op_Hat_Slash_Hat uu____53522 uu____53523
              | uu____53533 ->
                  let uu____53540 =
                    let uu____53551 =
                      FStar_ST.op_Bang should_print_fs_typ_app  in
                    if uu____53551
                    then
                      let uu____53585 =
                        FStar_Util.take
                          (fun uu____53609  ->
                             match uu____53609 with
                             | (uu____53615,aq) ->
                                 aq = FStar_Parser_AST.FsTypApp) args
                         in
                      match uu____53585 with
                      | (fs_typ_args,args1) ->
                          let uu____53653 =
                            let uu____53654 = p_indexingTerm head1  in
                            let uu____53655 =
                              let uu____53656 =
                                FStar_Pprint.op_Hat_Hat FStar_Pprint.comma
                                  break1
                                 in
                              soft_surround_map_or_flow (Prims.parse_int "2")
                                (Prims.parse_int "0") FStar_Pprint.empty
                                FStar_Pprint.langle uu____53656
                                FStar_Pprint.rangle p_fsTypArg fs_typ_args
                               in
                            FStar_Pprint.op_Hat_Hat uu____53654 uu____53655
                             in
                          (uu____53653, args1)
                    else
                      (let uu____53671 = p_indexingTerm head1  in
                       (uu____53671, args))
                     in
                  (match uu____53540 with
                   | (head_doc,args1) ->
                       let uu____53692 =
                         let uu____53693 =
                           FStar_Pprint.op_Hat_Hat head_doc
                             FStar_Pprint.space
                            in
                         soft_surround_map_or_flow (Prims.parse_int "2")
                           (Prims.parse_int "0") head_doc uu____53693 break1
                           FStar_Pprint.empty p_argTerm args1
                          in
                       FStar_Pprint.group uu____53692)))
    | FStar_Parser_AST.Construct (lid,args) when
        (is_general_construction e) &&
          (let uu____53715 = is_dtuple_constructor lid  in
           Prims.op_Negation uu____53715)
        ->
        (match args with
         | [] -> p_quident lid
         | arg::[] ->
             let uu____53734 =
               let uu____53735 = p_quident lid  in
               let uu____53736 = p_argTerm arg  in
               FStar_Pprint.op_Hat_Slash_Hat uu____53735 uu____53736  in
             FStar_Pprint.group uu____53734
         | hd1::tl1 ->
             let uu____53753 =
               let uu____53754 =
                 let uu____53755 =
                   let uu____53756 = p_quident lid  in
                   let uu____53757 = p_argTerm hd1  in
                   prefix2 uu____53756 uu____53757  in
                 FStar_Pprint.group uu____53755  in
               let uu____53758 =
                 let uu____53759 =
                   FStar_Pprint.separate_map break1 p_argTerm tl1  in
                 jump2 uu____53759  in
               FStar_Pprint.op_Hat_Hat uu____53754 uu____53758  in
             FStar_Pprint.group uu____53753)
    | uu____53764 -> p_indexingTerm e

and (p_argTerm :
  (FStar_Parser_AST.term * FStar_Parser_AST.imp) -> FStar_Pprint.document) =
  fun arg_imp  ->
    match arg_imp with
    | (u,FStar_Parser_AST.UnivApp ) -> p_universe u
    | (e,FStar_Parser_AST.FsTypApp ) ->
        (FStar_Errors.log_issue e.FStar_Parser_AST.range
           (FStar_Errors.Warning_UnexpectedFsTypApp,
             "Unexpected FsTypApp, output might not be formatted correctly.");
         (let uu____53775 = p_indexingTerm e  in
          FStar_Pprint.surround (Prims.parse_int "2") (Prims.parse_int "1")
            FStar_Pprint.langle uu____53775 FStar_Pprint.rangle))
    | (e,FStar_Parser_AST.Hash ) ->
        let uu____53779 = str "#"  in
        let uu____53781 = p_indexingTerm e  in
        FStar_Pprint.op_Hat_Hat uu____53779 uu____53781
    | (e,FStar_Parser_AST.HashBrace t) ->
        let uu____53784 = str "#["  in
        let uu____53786 =
          let uu____53787 = p_indexingTerm t  in
          let uu____53788 =
            let uu____53789 = str "]"  in
            let uu____53791 = p_indexingTerm e  in
            FStar_Pprint.op_Hat_Hat uu____53789 uu____53791  in
          FStar_Pprint.op_Hat_Hat uu____53787 uu____53788  in
        FStar_Pprint.op_Hat_Hat uu____53784 uu____53786
    | (e,FStar_Parser_AST.Infix ) -> p_indexingTerm e
    | (e,FStar_Parser_AST.Nothing ) -> p_indexingTerm e

and (p_fsTypArg :
  (FStar_Parser_AST.term * FStar_Parser_AST.imp) -> FStar_Pprint.document) =
  fun uu____53794  ->
    match uu____53794 with | (e,uu____53800) -> p_indexingTerm e

and (p_indexingTerm_aux :
  (FStar_Parser_AST.term -> FStar_Pprint.document) ->
    FStar_Parser_AST.term -> FStar_Pprint.document)
  =
  fun exit1  ->
    fun e  ->
      match e.FStar_Parser_AST.tm with
      | FStar_Parser_AST.Op
          ({ FStar_Ident.idText = ".()"; FStar_Ident.idRange = uu____53805;_},e1::e2::[])
          ->
          let uu____53811 =
            let uu____53812 = p_indexingTerm_aux p_atomicTermNotQUident e1
               in
            let uu____53813 =
              let uu____53814 =
                let uu____53815 = p_term false false e2  in
                soft_parens_with_nesting uu____53815  in
              FStar_Pprint.op_Hat_Hat FStar_Pprint.dot uu____53814  in
            FStar_Pprint.op_Hat_Hat uu____53812 uu____53813  in
          FStar_Pprint.group uu____53811
      | FStar_Parser_AST.Op
          ({ FStar_Ident.idText = ".[]"; FStar_Ident.idRange = uu____53818;_},e1::e2::[])
          ->
          let uu____53824 =
            let uu____53825 = p_indexingTerm_aux p_atomicTermNotQUident e1
               in
            let uu____53826 =
              let uu____53827 =
                let uu____53828 = p_term false false e2  in
                soft_brackets_with_nesting uu____53828  in
              FStar_Pprint.op_Hat_Hat FStar_Pprint.dot uu____53827  in
            FStar_Pprint.op_Hat_Hat uu____53825 uu____53826  in
          FStar_Pprint.group uu____53824
      | uu____53831 -> exit1 e

and (p_indexingTerm : FStar_Parser_AST.term -> FStar_Pprint.document) =
  fun e  -> p_indexingTerm_aux p_atomicTerm e

and (p_atomicTerm : FStar_Parser_AST.term -> FStar_Pprint.document) =
  fun e  ->
    match e.FStar_Parser_AST.tm with
    | FStar_Parser_AST.LetOpen (lid,e1) ->
        let uu____53836 = p_quident lid  in
        let uu____53837 =
          let uu____53838 =
            let uu____53839 = p_term false false e1  in
            soft_parens_with_nesting uu____53839  in
          FStar_Pprint.op_Hat_Hat FStar_Pprint.dot uu____53838  in
        FStar_Pprint.op_Hat_Hat uu____53836 uu____53837
    | FStar_Parser_AST.Name lid -> p_quident lid
    | FStar_Parser_AST.Op (op,e1::[]) when is_general_prefix_op op ->
        let uu____53847 =
          let uu____53848 = FStar_Ident.text_of_id op  in str uu____53848  in
        let uu____53850 = p_atomicTerm e1  in
        FStar_Pprint.op_Hat_Hat uu____53847 uu____53850
    | uu____53851 -> p_atomicTermNotQUident e

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
         | uu____53864 -> p_constant c)
    | FStar_Parser_AST.Name lid when
        FStar_Ident.lid_equals lid FStar_Parser_Const.true_lid -> str "True"
    | FStar_Parser_AST.Name lid when
        FStar_Ident.lid_equals lid FStar_Parser_Const.false_lid ->
        str "False"
    | FStar_Parser_AST.Op (op,e1::[]) when is_general_prefix_op op ->
        let uu____53873 =
          let uu____53874 = FStar_Ident.text_of_id op  in str uu____53874  in
        let uu____53876 = p_atomicTermNotQUident e1  in
        FStar_Pprint.op_Hat_Hat uu____53873 uu____53876
    | FStar_Parser_AST.Op (op,[]) ->
        let uu____53880 =
          let uu____53881 =
            let uu____53882 =
              let uu____53883 = FStar_Ident.text_of_id op  in str uu____53883
               in
            let uu____53885 =
              FStar_Pprint.op_Hat_Hat FStar_Pprint.space FStar_Pprint.rparen
               in
            FStar_Pprint.op_Hat_Hat uu____53882 uu____53885  in
          FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____53881  in
        FStar_Pprint.op_Hat_Hat FStar_Pprint.lparen uu____53880
    | FStar_Parser_AST.Construct (lid,args) when is_dtuple_constructor lid ->
        let uu____53900 = all_explicit args  in
        if uu____53900
        then
          let uu____53903 =
            FStar_Pprint.op_Hat_Hat FStar_Pprint.lparen FStar_Pprint.bar  in
          let uu____53904 =
            let uu____53905 =
              FStar_Pprint.op_Hat_Hat FStar_Pprint.comma break1  in
            let uu____53906 = FStar_List.map FStar_Pervasives_Native.fst args
               in
            FStar_Pprint.separate_map uu____53905 p_tmEq uu____53906  in
          let uu____53913 =
            FStar_Pprint.op_Hat_Hat FStar_Pprint.bar FStar_Pprint.rparen  in
          FStar_Pprint.surround (Prims.parse_int "2") (Prims.parse_int "1")
            uu____53903 uu____53904 uu____53913
        else
          (match args with
           | [] -> p_quident lid
           | arg::[] ->
               let uu____53935 =
                 let uu____53936 = p_quident lid  in
                 let uu____53937 = p_argTerm arg  in
                 FStar_Pprint.op_Hat_Slash_Hat uu____53936 uu____53937  in
               FStar_Pprint.group uu____53935
           | hd1::tl1 ->
               let uu____53954 =
                 let uu____53955 =
                   let uu____53956 =
                     let uu____53957 = p_quident lid  in
                     let uu____53958 = p_argTerm hd1  in
                     prefix2 uu____53957 uu____53958  in
                   FStar_Pprint.group uu____53956  in
                 let uu____53959 =
                   let uu____53960 =
                     FStar_Pprint.separate_map break1 p_argTerm tl1  in
                   jump2 uu____53960  in
                 FStar_Pprint.op_Hat_Hat uu____53955 uu____53959  in
               FStar_Pprint.group uu____53954)
    | FStar_Parser_AST.Project (e1,lid) ->
        let uu____53967 =
          let uu____53968 = p_atomicTermNotQUident e1  in
          let uu____53969 =
            let uu____53970 = p_qlident lid  in
            FStar_Pprint.op_Hat_Hat FStar_Pprint.dot uu____53970  in
          FStar_Pprint.prefix (Prims.parse_int "2") (Prims.parse_int "0")
            uu____53968 uu____53969
           in
        FStar_Pprint.group uu____53967
    | uu____53973 -> p_projectionLHS e

and (p_projectionLHS : FStar_Parser_AST.term -> FStar_Pprint.document) =
  fun e  ->
    match e.FStar_Parser_AST.tm with
    | FStar_Parser_AST.Var lid -> p_qlident lid
    | FStar_Parser_AST.Projector (constr_lid,field_lid) ->
        let uu____53978 = p_quident constr_lid  in
        let uu____53979 =
          let uu____53980 =
            let uu____53981 = p_lident field_lid  in
            FStar_Pprint.op_Hat_Hat FStar_Pprint.dot uu____53981  in
          FStar_Pprint.op_Hat_Hat FStar_Pprint.qmark uu____53980  in
        FStar_Pprint.op_Hat_Hat uu____53978 uu____53979
    | FStar_Parser_AST.Discrim constr_lid ->
        let uu____53983 = p_quident constr_lid  in
        FStar_Pprint.op_Hat_Hat uu____53983 FStar_Pprint.qmark
    | FStar_Parser_AST.Paren e1 ->
        let uu____53985 = p_term_sep false false e1  in
        (match uu____53985 with
         | (comm,t) ->
             let doc1 = soft_parens_with_nesting t  in
             if comm = FStar_Pprint.empty
             then doc1
             else
               (let uu____53998 =
                  FStar_Pprint.op_Hat_Hat FStar_Pprint.hardline doc1  in
                FStar_Pprint.op_Hat_Hat comm uu____53998))
    | uu____53999 when is_array e ->
        let es = extract_from_list e  in
        let uu____54003 =
          FStar_Pprint.op_Hat_Hat FStar_Pprint.lbracket FStar_Pprint.bar  in
        let uu____54004 =
          let uu____54005 = FStar_Pprint.op_Hat_Hat FStar_Pprint.semi break1
             in
          separate_map_or_flow_last uu____54005
            (fun ps  -> p_noSeqTermAndComment ps false) es
           in
        let uu____54010 =
          FStar_Pprint.op_Hat_Hat FStar_Pprint.bar FStar_Pprint.rbracket  in
        FStar_Pprint.surround (Prims.parse_int "2") (Prims.parse_int "0")
          uu____54003 uu____54004 uu____54010
    | uu____54013 when is_list e ->
        let uu____54014 =
          let uu____54015 = FStar_Pprint.op_Hat_Hat FStar_Pprint.semi break1
             in
          let uu____54016 = extract_from_list e  in
          separate_map_or_flow_last uu____54015
            (fun ps  -> p_noSeqTermAndComment ps false) uu____54016
           in
        FStar_Pprint.surround (Prims.parse_int "2") (Prims.parse_int "0")
          FStar_Pprint.lbracket uu____54014 FStar_Pprint.rbracket
    | uu____54025 when is_lex_list e ->
        let uu____54026 =
          FStar_Pprint.op_Hat_Hat FStar_Pprint.percent FStar_Pprint.lbracket
           in
        let uu____54027 =
          let uu____54028 = FStar_Pprint.op_Hat_Hat FStar_Pprint.semi break1
             in
          let uu____54029 = extract_from_list e  in
          separate_map_or_flow_last uu____54028
            (fun ps  -> p_noSeqTermAndComment ps false) uu____54029
           in
        FStar_Pprint.surround (Prims.parse_int "2") (Prims.parse_int "1")
          uu____54026 uu____54027 FStar_Pprint.rbracket
    | uu____54038 when is_ref_set e ->
        let es = extract_from_ref_set e  in
        let uu____54042 =
          FStar_Pprint.op_Hat_Hat FStar_Pprint.bang FStar_Pprint.lbrace  in
        let uu____54043 =
          let uu____54044 = FStar_Pprint.op_Hat_Hat FStar_Pprint.comma break1
             in
          separate_map_or_flow uu____54044 p_appTerm es  in
        FStar_Pprint.surround (Prims.parse_int "2") (Prims.parse_int "0")
          uu____54042 uu____54043 FStar_Pprint.rbrace
    | FStar_Parser_AST.Labeled (e1,s,b) ->
        let uu____54054 = str (Prims.op_Hat "(*" (Prims.op_Hat s "*)"))  in
        let uu____54057 = p_term false false e1  in
        FStar_Pprint.op_Hat_Slash_Hat uu____54054 uu____54057
    | FStar_Parser_AST.Op (op,args) when
        let uu____54066 = handleable_op op args  in
        Prims.op_Negation uu____54066 ->
        let uu____54068 =
          let uu____54070 =
            let uu____54072 = FStar_Ident.text_of_id op  in
            let uu____54074 =
              let uu____54076 =
                let uu____54078 =
                  FStar_Util.string_of_int (FStar_List.length args)  in
                Prims.op_Hat uu____54078
                  " arguments couldn't be handled by the pretty printer"
                 in
              Prims.op_Hat " with " uu____54076  in
            Prims.op_Hat uu____54072 uu____54074  in
          Prims.op_Hat "Operation " uu____54070  in
        failwith uu____54068
    | FStar_Parser_AST.Uvar id1 ->
        failwith "Unexpected universe variable out of universe context"
    | FStar_Parser_AST.Wild  ->
        let uu____54085 = p_term false false e  in
        soft_parens_with_nesting uu____54085
    | FStar_Parser_AST.Const uu____54088 ->
        let uu____54089 = p_term false false e  in
        soft_parens_with_nesting uu____54089
    | FStar_Parser_AST.Op uu____54092 ->
        let uu____54099 = p_term false false e  in
        soft_parens_with_nesting uu____54099
    | FStar_Parser_AST.Tvar uu____54102 ->
        let uu____54103 = p_term false false e  in
        soft_parens_with_nesting uu____54103
    | FStar_Parser_AST.Var uu____54106 ->
        let uu____54107 = p_term false false e  in
        soft_parens_with_nesting uu____54107
    | FStar_Parser_AST.Name uu____54110 ->
        let uu____54111 = p_term false false e  in
        soft_parens_with_nesting uu____54111
    | FStar_Parser_AST.Construct uu____54114 ->
        let uu____54125 = p_term false false e  in
        soft_parens_with_nesting uu____54125
    | FStar_Parser_AST.Abs uu____54128 ->
        let uu____54135 = p_term false false e  in
        soft_parens_with_nesting uu____54135
    | FStar_Parser_AST.App uu____54138 ->
        let uu____54145 = p_term false false e  in
        soft_parens_with_nesting uu____54145
    | FStar_Parser_AST.Let uu____54148 ->
        let uu____54169 = p_term false false e  in
        soft_parens_with_nesting uu____54169
    | FStar_Parser_AST.LetOpen uu____54172 ->
        let uu____54177 = p_term false false e  in
        soft_parens_with_nesting uu____54177
    | FStar_Parser_AST.Seq uu____54180 ->
        let uu____54185 = p_term false false e  in
        soft_parens_with_nesting uu____54185
    | FStar_Parser_AST.Bind uu____54188 ->
        let uu____54195 = p_term false false e  in
        soft_parens_with_nesting uu____54195
    | FStar_Parser_AST.If uu____54198 ->
        let uu____54205 = p_term false false e  in
        soft_parens_with_nesting uu____54205
    | FStar_Parser_AST.Match uu____54208 ->
        let uu____54223 = p_term false false e  in
        soft_parens_with_nesting uu____54223
    | FStar_Parser_AST.TryWith uu____54226 ->
        let uu____54241 = p_term false false e  in
        soft_parens_with_nesting uu____54241
    | FStar_Parser_AST.Ascribed uu____54244 ->
        let uu____54253 = p_term false false e  in
        soft_parens_with_nesting uu____54253
    | FStar_Parser_AST.Record uu____54256 ->
        let uu____54269 = p_term false false e  in
        soft_parens_with_nesting uu____54269
    | FStar_Parser_AST.Project uu____54272 ->
        let uu____54277 = p_term false false e  in
        soft_parens_with_nesting uu____54277
    | FStar_Parser_AST.Product uu____54280 ->
        let uu____54287 = p_term false false e  in
        soft_parens_with_nesting uu____54287
    | FStar_Parser_AST.Sum uu____54290 ->
        let uu____54301 = p_term false false e  in
        soft_parens_with_nesting uu____54301
    | FStar_Parser_AST.QForall uu____54304 ->
        let uu____54317 = p_term false false e  in
        soft_parens_with_nesting uu____54317
    | FStar_Parser_AST.QExists uu____54320 ->
        let uu____54333 = p_term false false e  in
        soft_parens_with_nesting uu____54333
    | FStar_Parser_AST.Refine uu____54336 ->
        let uu____54341 = p_term false false e  in
        soft_parens_with_nesting uu____54341
    | FStar_Parser_AST.NamedTyp uu____54344 ->
        let uu____54349 = p_term false false e  in
        soft_parens_with_nesting uu____54349
    | FStar_Parser_AST.Requires uu____54352 ->
        let uu____54360 = p_term false false e  in
        soft_parens_with_nesting uu____54360
    | FStar_Parser_AST.Ensures uu____54363 ->
        let uu____54371 = p_term false false e  in
        soft_parens_with_nesting uu____54371
    | FStar_Parser_AST.Attributes uu____54374 ->
        let uu____54377 = p_term false false e  in
        soft_parens_with_nesting uu____54377
    | FStar_Parser_AST.Quote uu____54380 ->
        let uu____54385 = p_term false false e  in
        soft_parens_with_nesting uu____54385
    | FStar_Parser_AST.VQuote uu____54388 ->
        let uu____54389 = p_term false false e  in
        soft_parens_with_nesting uu____54389
    | FStar_Parser_AST.Antiquote uu____54392 ->
        let uu____54393 = p_term false false e  in
        soft_parens_with_nesting uu____54393
    | FStar_Parser_AST.CalcProof uu____54396 ->
        let uu____54405 = p_term false false e  in
        soft_parens_with_nesting uu____54405

and (p_constant : FStar_Const.sconst -> FStar_Pprint.document) =
  fun uu___339_54408  ->
    match uu___339_54408 with
    | FStar_Const.Const_effect  -> str "Effect"
    | FStar_Const.Const_unit  -> str "()"
    | FStar_Const.Const_bool b -> FStar_Pprint.doc_of_bool b
    | FStar_Const.Const_real r -> str (Prims.op_Hat r "R")
    | FStar_Const.Const_float x -> str (FStar_Util.string_of_float x)
    | FStar_Const.Const_char x -> FStar_Pprint.doc_of_char x
    | FStar_Const.Const_string (s,uu____54420) ->
        let uu____54423 = str (FStar_String.escaped s)  in
        FStar_Pprint.dquotes uu____54423
    | FStar_Const.Const_bytearray (bytes,uu____54425) ->
        let uu____54430 =
          let uu____54431 = str (FStar_Util.string_of_bytes bytes)  in
          FStar_Pprint.dquotes uu____54431  in
        let uu____54432 = str "B"  in
        FStar_Pprint.op_Hat_Hat uu____54430 uu____54432
    | FStar_Const.Const_int (repr,sign_width_opt) ->
        let signedness uu___337_54455 =
          match uu___337_54455 with
          | FStar_Const.Unsigned  -> str "u"
          | FStar_Const.Signed  -> FStar_Pprint.empty  in
        let width uu___338_54462 =
          match uu___338_54462 with
          | FStar_Const.Int8  -> str "y"
          | FStar_Const.Int16  -> str "s"
          | FStar_Const.Int32  -> str "l"
          | FStar_Const.Int64  -> str "L"  in
        let ending =
          default_or_map FStar_Pprint.empty
            (fun uu____54477  ->
               match uu____54477 with
               | (s,w) ->
                   let uu____54484 = signedness s  in
                   let uu____54485 = width w  in
                   FStar_Pprint.op_Hat_Hat uu____54484 uu____54485)
            sign_width_opt
           in
        let uu____54486 = str repr  in
        FStar_Pprint.op_Hat_Hat uu____54486 ending
    | FStar_Const.Const_range_of  -> str "range_of"
    | FStar_Const.Const_set_range_of  -> str "set_range_of"
    | FStar_Const.Const_range r ->
        let uu____54490 = FStar_Range.string_of_range r  in str uu____54490
    | FStar_Const.Const_reify  -> str "reify"
    | FStar_Const.Const_reflect lid ->
        let uu____54494 = p_quident lid  in
        let uu____54495 =
          let uu____54496 =
            let uu____54497 = str "reflect"  in
            FStar_Pprint.op_Hat_Hat FStar_Pprint.dot uu____54497  in
          FStar_Pprint.op_Hat_Hat FStar_Pprint.qmark uu____54496  in
        FStar_Pprint.op_Hat_Hat uu____54494 uu____54495

and (p_universe : FStar_Parser_AST.term -> FStar_Pprint.document) =
  fun u  ->
    let uu____54500 = str "u#"  in
    let uu____54502 = p_atomicUniverse u  in
    FStar_Pprint.op_Hat_Hat uu____54500 uu____54502

and (p_universeFrom : FStar_Parser_AST.term -> FStar_Pprint.document) =
  fun u  ->
    match u.FStar_Parser_AST.tm with
    | FStar_Parser_AST.Op
        ({ FStar_Ident.idText = "+"; FStar_Ident.idRange = uu____54504;_},u1::u2::[])
        ->
        let uu____54510 =
          let uu____54511 = p_universeFrom u1  in
          let uu____54512 =
            let uu____54513 = p_universeFrom u2  in
            FStar_Pprint.op_Hat_Slash_Hat FStar_Pprint.plus uu____54513  in
          FStar_Pprint.op_Hat_Slash_Hat uu____54511 uu____54512  in
        FStar_Pprint.group uu____54510
    | FStar_Parser_AST.App uu____54514 ->
        let uu____54521 = head_and_args u  in
        (match uu____54521 with
         | (head1,args) ->
             (match head1.FStar_Parser_AST.tm with
              | FStar_Parser_AST.Var maybe_max_lid when
                  FStar_Ident.lid_equals maybe_max_lid
                    FStar_Parser_Const.max_lid
                  ->
                  let uu____54547 =
                    let uu____54548 = p_qlident FStar_Parser_Const.max_lid
                       in
                    let uu____54549 =
                      FStar_Pprint.separate_map FStar_Pprint.space
                        (fun uu____54557  ->
                           match uu____54557 with
                           | (u1,uu____54563) -> p_atomicUniverse u1) args
                       in
                    op_Hat_Slash_Plus_Hat uu____54548 uu____54549  in
                  FStar_Pprint.group uu____54547
              | uu____54564 ->
                  let uu____54565 =
                    let uu____54567 = FStar_Parser_AST.term_to_string u  in
                    FStar_Util.format1 "Invalid term in universe context %s"
                      uu____54567
                     in
                  failwith uu____54565))
    | uu____54570 -> p_atomicUniverse u

and (p_atomicUniverse : FStar_Parser_AST.term -> FStar_Pprint.document) =
  fun u  ->
    match u.FStar_Parser_AST.tm with
    | FStar_Parser_AST.Wild  -> FStar_Pprint.underscore
    | FStar_Parser_AST.Const (FStar_Const.Const_int (r,sw)) ->
        p_constant (FStar_Const.Const_int (r, sw))
    | FStar_Parser_AST.Uvar id1 ->
        let uu____54596 = FStar_Ident.text_of_id id1  in str uu____54596
    | FStar_Parser_AST.Paren u1 ->
        let uu____54599 = p_universeFrom u1  in
        soft_parens_with_nesting uu____54599
    | FStar_Parser_AST.Op
        ({ FStar_Ident.idText = "+"; FStar_Ident.idRange = uu____54600;_},uu____54601::uu____54602::[])
        ->
        let uu____54606 = p_universeFrom u  in
        soft_parens_with_nesting uu____54606
    | FStar_Parser_AST.App uu____54607 ->
        let uu____54614 = p_universeFrom u  in
        soft_parens_with_nesting uu____54614
    | uu____54615 ->
        let uu____54616 =
          let uu____54618 = FStar_Parser_AST.term_to_string u  in
          FStar_Util.format1 "Invalid term in universe context %s"
            uu____54618
           in
        failwith uu____54616

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
       | FStar_Parser_AST.Module (uu____54707,decls) ->
           let uu____54713 =
             FStar_All.pipe_right decls (FStar_List.map decl_to_document)  in
           FStar_All.pipe_right uu____54713
             (FStar_Pprint.separate FStar_Pprint.hardline)
       | FStar_Parser_AST.Interface (uu____54722,decls,uu____54724) ->
           let uu____54731 =
             FStar_All.pipe_right decls (FStar_List.map decl_to_document)  in
           FStar_All.pipe_right uu____54731
             (FStar_Pprint.separate FStar_Pprint.hardline)
        in
     FStar_ST.op_Colon_Equals should_print_fs_typ_app false; res)
  
let (comments_to_document :
  (Prims.string * FStar_Range.range) Prims.list -> FStar_Pprint.document) =
  fun comments  ->
    FStar_Pprint.separate_map FStar_Pprint.hardline
      (fun uu____54791  ->
         match uu____54791 with | (comment,range) -> str comment) comments
  
let (extract_decl_range : FStar_Parser_AST.decl -> decl_meta) =
  fun d  ->
    let has_qs =
      match ((d.FStar_Parser_AST.quals), (d.FStar_Parser_AST.d)) with
      | ((FStar_Parser_AST.Assumption )::[],FStar_Parser_AST.Assume
         (id1,uu____54813)) -> false
      | ([],uu____54817) -> false
      | uu____54821 -> true  in
    {
      r = (d.FStar_Parser_AST.drange);
      has_qs;
      has_attrs =
        (Prims.op_Negation (FStar_List.isEmpty d.FStar_Parser_AST.attrs));
      has_fsdoc = (FStar_Util.is_some d.FStar_Parser_AST.doc);
      is_fsdoc =
        (match d.FStar_Parser_AST.d with
         | FStar_Parser_AST.Fsdoc uu____54831 -> true
         | uu____54833 -> false)
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
        | FStar_Parser_AST.Module (uu____54876,decls) -> decls
        | FStar_Parser_AST.Interface (uu____54882,decls,uu____54884) -> decls
         in
      FStar_ST.op_Colon_Equals should_print_fs_typ_app false;
      (match decls with
       | [] -> (FStar_Pprint.empty, comments)
       | d::ds ->
           let uu____54936 =
             match ds with
             | {
                 FStar_Parser_AST.d = FStar_Parser_AST.Pragma
                   (FStar_Parser_AST.LightOff );
                 FStar_Parser_AST.drange = uu____54949;
                 FStar_Parser_AST.doc = uu____54950;
                 FStar_Parser_AST.quals = uu____54951;
                 FStar_Parser_AST.attrs = uu____54952;_}::uu____54953 ->
                 let d0 = FStar_List.hd ds  in
                 let uu____54959 =
                   let uu____54962 =
                     let uu____54965 = FStar_List.tl ds  in d :: uu____54965
                      in
                   d0 :: uu____54962  in
                 (uu____54959, (d0.FStar_Parser_AST.drange))
             | uu____54970 -> ((d :: ds), (d.FStar_Parser_AST.drange))  in
           (match uu____54936 with
            | (decls1,first_range) ->
                (FStar_ST.op_Colon_Equals comment_stack comments;
                 (let initial_comment =
                    let uu____55027 = FStar_Range.start_of_range first_range
                       in
                    place_comments_until_pos (Prims.parse_int "0")
                      (Prims.parse_int "1") uu____55027 dummy_meta
                      FStar_Pprint.empty false true
                     in
                  let doc1 =
                    separate_map_with_comments FStar_Pprint.empty
                      FStar_Pprint.empty p_decl decls1 extract_decl_range
                     in
                  let comments1 = FStar_ST.op_Bang comment_stack  in
                  FStar_ST.op_Colon_Equals comment_stack [];
                  FStar_ST.op_Colon_Equals should_print_fs_typ_app false;
                  (let uu____55136 =
                     FStar_Pprint.op_Hat_Hat initial_comment doc1  in
                   (uu____55136, comments1))))))
  