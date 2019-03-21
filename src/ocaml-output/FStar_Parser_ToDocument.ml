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
            let uu____38987 = let uu____38990 = f x  in uu____38990 :: acc
               in
            aux xs uu____38987
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
            let uu____39057 = f x  in
            (match uu____39057 with
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
          let uu____39113 = f x  in if uu____39113 then all f xs else false
  
let (all_explicit :
  (FStar_Parser_AST.term * FStar_Parser_AST.imp) Prims.list -> Prims.bool) =
  fun args  ->
    FStar_Util.for_all
      (fun uu___324_39146  ->
         match uu___324_39146 with
         | (uu____39152,FStar_Parser_AST.Nothing ) -> true
         | uu____39154 -> false) args
  
let (should_print_fs_typ_app : Prims.bool FStar_ST.ref) =
  FStar_Util.mk_ref false 
let (unfold_tuples : Prims.bool FStar_ST.ref) = FStar_Util.mk_ref true 
let with_fs_typ_app :
  'Auu____39183 'Auu____39184 .
    Prims.bool ->
      ('Auu____39183 -> 'Auu____39184) -> 'Auu____39183 -> 'Auu____39184
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
  'Auu____39294 'Auu____39295 .
    'Auu____39294 ->
      ('Auu____39295 -> 'Auu____39294) ->
        'Auu____39295 FStar_Pervasives_Native.option -> 'Auu____39294
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
  'Auu____39408 .
    FStar_Pprint.document ->
      ('Auu____39408 -> FStar_Pprint.document) ->
        'Auu____39408 Prims.list -> FStar_Pprint.document
  =
  fun sep  ->
    fun f  ->
      fun l  ->
        let uu____39433 =
          let uu____39434 =
            let uu____39435 = FStar_Pprint.op_Hat_Hat sep break1  in
            FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____39435  in
          FStar_Pprint.separate_map uu____39434 f l  in
        FStar_Pprint.group uu____39433
  
let precede_break_separate_map :
  'Auu____39447 .
    FStar_Pprint.document ->
      FStar_Pprint.document ->
        ('Auu____39447 -> FStar_Pprint.document) ->
          'Auu____39447 Prims.list -> FStar_Pprint.document
  =
  fun prec  ->
    fun sep  ->
      fun f  ->
        fun l  ->
          let uu____39477 =
            let uu____39478 = FStar_Pprint.op_Hat_Hat prec FStar_Pprint.space
               in
            let uu____39479 =
              let uu____39480 = FStar_List.hd l  in
              FStar_All.pipe_right uu____39480 f  in
            FStar_Pprint.precede uu____39478 uu____39479  in
          let uu____39481 =
            let uu____39482 = FStar_List.tl l  in
            FStar_Pprint.concat_map
              (fun x  ->
                 let uu____39488 =
                   let uu____39489 =
                     let uu____39490 = f x  in
                     FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____39490
                      in
                   FStar_Pprint.op_Hat_Hat sep uu____39489  in
                 FStar_Pprint.op_Hat_Hat break1 uu____39488) uu____39482
             in
          FStar_Pprint.op_Hat_Hat uu____39477 uu____39481
  
let concat_break_map :
  'Auu____39498 .
    ('Auu____39498 -> FStar_Pprint.document) ->
      'Auu____39498 Prims.list -> FStar_Pprint.document
  =
  fun f  ->
    fun l  ->
      let uu____39518 =
        FStar_Pprint.concat_map
          (fun x  ->
             let uu____39522 = f x  in
             FStar_Pprint.op_Hat_Hat uu____39522 break1) l
         in
      FStar_Pprint.group uu____39518
  
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
    let uu____39585 = str "begin"  in
    let uu____39587 = str "end"  in
    FStar_Pprint.soft_surround (Prims.parse_int "2") (Prims.parse_int "1")
      uu____39585 contents uu____39587
  
let separate_map_last :
  'Auu____39600 .
    FStar_Pprint.document ->
      (Prims.bool -> 'Auu____39600 -> FStar_Pprint.document) ->
        'Auu____39600 Prims.list -> FStar_Pprint.document
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
  'Auu____39652 .
    FStar_Pprint.document ->
      (Prims.bool -> 'Auu____39652 -> FStar_Pprint.document) ->
        'Auu____39652 Prims.list -> FStar_Pprint.document
  =
  fun sep  ->
    fun f  ->
      fun l  ->
        let uu____39684 =
          let uu____39685 =
            let uu____39686 = FStar_Pprint.op_Hat_Hat sep break1  in
            FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____39686  in
          separate_map_last uu____39685 f l  in
        FStar_Pprint.group uu____39684
  
let separate_map_or_flow :
  'Auu____39696 .
    FStar_Pprint.document ->
      ('Auu____39696 -> FStar_Pprint.document) ->
        'Auu____39696 Prims.list -> FStar_Pprint.document
  =
  fun sep  ->
    fun f  ->
      fun l  ->
        if (FStar_List.length l) < (Prims.parse_int "10")
        then FStar_Pprint.separate_map sep f l
        else FStar_Pprint.flow_map sep f l
  
let flow_map_last :
  'Auu____39734 .
    FStar_Pprint.document ->
      (Prims.bool -> 'Auu____39734 -> FStar_Pprint.document) ->
        'Auu____39734 Prims.list -> FStar_Pprint.document
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
  'Auu____39786 .
    FStar_Pprint.document ->
      (Prims.bool -> 'Auu____39786 -> FStar_Pprint.document) ->
        'Auu____39786 Prims.list -> FStar_Pprint.document
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
              let uu____39868 = FStar_Pprint.op_Hat_Slash_Hat doc1 doc3  in
              FStar_Pprint.group uu____39868
            else FStar_Pprint.surround n1 b doc1 doc2 doc3
  
let soft_surround_separate_map :
  'Auu____39890 .
    Prims.int ->
      Prims.int ->
        FStar_Pprint.document ->
          FStar_Pprint.document ->
            FStar_Pprint.document ->
              FStar_Pprint.document ->
                ('Auu____39890 -> FStar_Pprint.document) ->
                  'Auu____39890 Prims.list -> FStar_Pprint.document
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
                    (let uu____39949 = FStar_Pprint.separate_map sep f xs  in
                     FStar_Pprint.soft_surround n1 b opening uu____39949
                       closing)
  
let soft_surround_map_or_flow :
  'Auu____39969 .
    Prims.int ->
      Prims.int ->
        FStar_Pprint.document ->
          FStar_Pprint.document ->
            FStar_Pprint.document ->
              FStar_Pprint.document ->
                ('Auu____39969 -> FStar_Pprint.document) ->
                  'Auu____39969 Prims.list -> FStar_Pprint.document
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
                    (let uu____40028 = separate_map_or_flow sep f xs  in
                     FStar_Pprint.soft_surround n1 b opening uu____40028
                       closing)
  
let (doc_of_fsdoc :
  (Prims.string * (Prims.string * Prims.string) Prims.list) ->
    FStar_Pprint.document)
  =
  fun uu____40047  ->
    match uu____40047 with
    | (comment,keywords) ->
        let uu____40081 =
          let uu____40082 =
            let uu____40085 = str comment  in
            let uu____40086 =
              let uu____40089 =
                let uu____40092 =
                  FStar_Pprint.separate_map FStar_Pprint.comma
                    (fun uu____40103  ->
                       match uu____40103 with
                       | (k,v1) ->
                           let uu____40116 =
                             let uu____40119 = str k  in
                             let uu____40120 =
                               let uu____40123 =
                                 let uu____40126 = str v1  in [uu____40126]
                                  in
                               FStar_Pprint.rarrow :: uu____40123  in
                             uu____40119 :: uu____40120  in
                           FStar_Pprint.concat uu____40116) keywords
                   in
                [uu____40092]  in
              FStar_Pprint.space :: uu____40089  in
            uu____40085 :: uu____40086  in
          FStar_Pprint.concat uu____40082  in
        FStar_Pprint.group uu____40081
  
let (is_unit : FStar_Parser_AST.term -> Prims.bool) =
  fun e  ->
    match e.FStar_Parser_AST.tm with
    | FStar_Parser_AST.Const (FStar_Const.Const_unit ) -> true
    | uu____40136 -> false
  
let (matches_var : FStar_Parser_AST.term -> FStar_Ident.ident -> Prims.bool)
  =
  fun t  ->
    fun x  ->
      match t.FStar_Parser_AST.tm with
      | FStar_Parser_AST.Var y ->
          let uu____40152 = FStar_Ident.text_of_lid y  in
          x.FStar_Ident.idText = uu____40152
      | uu____40155 -> false
  
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
        | FStar_Parser_AST.Construct (lid,uu____40206::(e2,uu____40208)::[])
            -> (FStar_Ident.lid_equals lid cons_lid1) && (aux e2)
        | uu____40231 -> false  in
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
    | FStar_Parser_AST.Construct (uu____40255,[]) -> []
    | FStar_Parser_AST.Construct
        (uu____40266,(e1,FStar_Parser_AST.Nothing )::(e2,FStar_Parser_AST.Nothing
                                                      )::[])
        -> let uu____40287 = extract_from_list e2  in e1 :: uu____40287
    | uu____40290 ->
        let uu____40291 =
          let uu____40293 = FStar_Parser_AST.term_to_string e  in
          FStar_Util.format1 "Not a list %s" uu____40293  in
        failwith uu____40291
  
let (is_array : FStar_Parser_AST.term -> Prims.bool) =
  fun e  ->
    match e.FStar_Parser_AST.tm with
    | FStar_Parser_AST.App
        ({ FStar_Parser_AST.tm = FStar_Parser_AST.Var lid;
           FStar_Parser_AST.range = uu____40307;
           FStar_Parser_AST.level = uu____40308;_},l,FStar_Parser_AST.Nothing
         )
        ->
        (FStar_Ident.lid_equals lid FStar_Parser_Const.array_mk_array_lid) &&
          (is_list l)
    | uu____40310 -> false
  
let rec (is_ref_set : FStar_Parser_AST.term -> Prims.bool) =
  fun e  ->
    match e.FStar_Parser_AST.tm with
    | FStar_Parser_AST.Var maybe_empty_lid ->
        FStar_Ident.lid_equals maybe_empty_lid FStar_Parser_Const.set_empty
    | FStar_Parser_AST.App
        ({ FStar_Parser_AST.tm = FStar_Parser_AST.Var maybe_singleton_lid;
           FStar_Parser_AST.range = uu____40322;
           FStar_Parser_AST.level = uu____40323;_},{
                                                     FStar_Parser_AST.tm =
                                                       FStar_Parser_AST.App
                                                       ({
                                                          FStar_Parser_AST.tm
                                                            =
                                                            FStar_Parser_AST.Var
                                                            maybe_addr_of_lid;
                                                          FStar_Parser_AST.range
                                                            = uu____40325;
                                                          FStar_Parser_AST.level
                                                            = uu____40326;_},e1,FStar_Parser_AST.Nothing
                                                        );
                                                     FStar_Parser_AST.range =
                                                       uu____40328;
                                                     FStar_Parser_AST.level =
                                                       uu____40329;_},FStar_Parser_AST.Nothing
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
                FStar_Parser_AST.range = uu____40331;
                FStar_Parser_AST.level = uu____40332;_},e1,FStar_Parser_AST.Nothing
              );
           FStar_Parser_AST.range = uu____40334;
           FStar_Parser_AST.level = uu____40335;_},e2,FStar_Parser_AST.Nothing
         )
        ->
        ((FStar_Ident.lid_equals maybe_union_lid FStar_Parser_Const.set_union)
           && (is_ref_set e1))
          && (is_ref_set e2)
    | uu____40337 -> false
  
let rec (extract_from_ref_set :
  FStar_Parser_AST.term -> FStar_Parser_AST.term Prims.list) =
  fun e  ->
    match e.FStar_Parser_AST.tm with
    | FStar_Parser_AST.Var uu____40349 -> []
    | FStar_Parser_AST.App
        ({ FStar_Parser_AST.tm = FStar_Parser_AST.Var uu____40350;
           FStar_Parser_AST.range = uu____40351;
           FStar_Parser_AST.level = uu____40352;_},{
                                                     FStar_Parser_AST.tm =
                                                       FStar_Parser_AST.App
                                                       ({
                                                          FStar_Parser_AST.tm
                                                            =
                                                            FStar_Parser_AST.Var
                                                            uu____40353;
                                                          FStar_Parser_AST.range
                                                            = uu____40354;
                                                          FStar_Parser_AST.level
                                                            = uu____40355;_},e1,FStar_Parser_AST.Nothing
                                                        );
                                                     FStar_Parser_AST.range =
                                                       uu____40357;
                                                     FStar_Parser_AST.level =
                                                       uu____40358;_},FStar_Parser_AST.Nothing
         )
        -> [e1]
    | FStar_Parser_AST.App
        ({
           FStar_Parser_AST.tm = FStar_Parser_AST.App
             ({ FStar_Parser_AST.tm = FStar_Parser_AST.Var uu____40359;
                FStar_Parser_AST.range = uu____40360;
                FStar_Parser_AST.level = uu____40361;_},e1,FStar_Parser_AST.Nothing
              );
           FStar_Parser_AST.range = uu____40363;
           FStar_Parser_AST.level = uu____40364;_},e2,FStar_Parser_AST.Nothing
         )
        ->
        let uu____40366 = extract_from_ref_set e1  in
        let uu____40369 = extract_from_ref_set e2  in
        FStar_List.append uu____40366 uu____40369
    | uu____40372 ->
        let uu____40373 =
          let uu____40375 = FStar_Parser_AST.term_to_string e  in
          FStar_Util.format1 "Not a ref set %s" uu____40375  in
        failwith uu____40373
  
let (is_general_application : FStar_Parser_AST.term -> Prims.bool) =
  fun e  ->
    let uu____40387 = (is_array e) || (is_ref_set e)  in
    Prims.op_Negation uu____40387
  
let (is_general_construction : FStar_Parser_AST.term -> Prims.bool) =
  fun e  ->
    let uu____40396 = (is_list e) || (is_lex_list e)  in
    Prims.op_Negation uu____40396
  
let (is_general_prefix_op : FStar_Ident.ident -> Prims.bool) =
  fun op  ->
    let op_starting_char =
      let uu____40407 = FStar_Ident.text_of_id op  in
      FStar_Util.char_at uu____40407 (Prims.parse_int "0")  in
    ((op_starting_char = 33) || (op_starting_char = 63)) ||
      ((op_starting_char = 126) &&
         (let uu____40417 = FStar_Ident.text_of_id op  in uu____40417 <> "~"))
  
let (head_and_args :
  FStar_Parser_AST.term ->
    (FStar_Parser_AST.term * (FStar_Parser_AST.term * FStar_Parser_AST.imp)
      Prims.list))
  =
  fun e  ->
    let rec aux e1 acc =
      match e1.FStar_Parser_AST.tm with
      | FStar_Parser_AST.App (head1,arg,imp) -> aux head1 ((arg, imp) :: acc)
      | uu____40487 -> (e1, acc)  in
    aux e []
  
type associativity =
  | Left 
  | Right 
  | NonAssoc 
let (uu___is_Left : associativity -> Prims.bool) =
  fun projectee  ->
    match projectee with | Left  -> true | uu____40507 -> false
  
let (uu___is_Right : associativity -> Prims.bool) =
  fun projectee  ->
    match projectee with | Right  -> true | uu____40518 -> false
  
let (uu___is_NonAssoc : associativity -> Prims.bool) =
  fun projectee  ->
    match projectee with | NonAssoc  -> true | uu____40529 -> false
  
type token = (FStar_Char.char,Prims.string) FStar_Util.either
type associativity_level = (associativity * token Prims.list)
let (token_to_string :
  (FStar_BaseTypes.char,Prims.string) FStar_Util.either -> Prims.string) =
  fun uu___325_40555  ->
    match uu___325_40555 with
    | FStar_Util.Inl c -> Prims.op_Hat (FStar_Util.string_of_char c) ".*"
    | FStar_Util.Inr s -> s
  
let (matches_token :
  Prims.string ->
    (FStar_Char.char,Prims.string) FStar_Util.either -> Prims.bool)
  =
  fun s  ->
    fun uu___326_40590  ->
      match uu___326_40590 with
      | FStar_Util.Inl c ->
          let uu____40603 = FStar_String.get s (Prims.parse_int "0")  in
          uu____40603 = c
      | FStar_Util.Inr s' -> s = s'
  
let matches_level :
  'Auu____40619 .
    Prims.string ->
      ('Auu____40619 * (FStar_Char.char,Prims.string) FStar_Util.either
        Prims.list) -> Prims.bool
  =
  fun s  ->
    fun uu____40643  ->
      match uu____40643 with
      | (assoc_levels,tokens) ->
          let uu____40675 = FStar_List.tryFind (matches_token s) tokens  in
          uu____40675 <> FStar_Pervasives_Native.None
  
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
  let levels_from_associativity l uu___327_40847 =
    match uu___327_40847 with
    | Left  -> (l, l, (l - (Prims.parse_int "1")))
    | Right  -> ((l - (Prims.parse_int "1")), l, l)
    | NonAssoc  ->
        ((l - (Prims.parse_int "1")), l, (l - (Prims.parse_int "1")))
     in
  FStar_List.mapi
    (fun i  ->
       fun uu____40897  ->
         match uu____40897 with
         | (assoc1,tokens) -> ((levels_from_associativity i assoc1), tokens))
    level_associativity_spec
  
let (assign_levels :
  associativity_level Prims.list ->
    Prims.string -> (Prims.int * Prims.int * Prims.int))
  =
  fun token_associativity_spec  ->
    fun s  ->
      let uu____40972 = FStar_List.tryFind (matches_level s) level_table  in
      match uu____40972 with
      | FStar_Pervasives_Native.Some (assoc_levels,uu____41024) ->
          assoc_levels
      | uu____41062 -> failwith (Prims.op_Hat "Unrecognized operator " s)
  
let max_level :
  'Auu____41095 . ('Auu____41095 * token Prims.list) Prims.list -> Prims.int
  =
  fun l  ->
    let find_level_and_max n1 level =
      let uu____41144 =
        FStar_List.tryFind
          (fun uu____41180  ->
             match uu____41180 with
             | (uu____41197,tokens) ->
                 tokens = (FStar_Pervasives_Native.snd level)) level_table
         in
      match uu____41144 with
      | FStar_Pervasives_Native.Some
          ((uu____41226,l1,uu____41228),uu____41229) -> max n1 l1
      | FStar_Pervasives_Native.None  ->
          let uu____41279 =
            let uu____41281 =
              let uu____41283 =
                FStar_List.map token_to_string
                  (FStar_Pervasives_Native.snd level)
                 in
              FStar_String.concat "," uu____41283  in
            FStar_Util.format1 "Undefined associativity level %s" uu____41281
             in
          failwith uu____41279
       in
    FStar_List.fold_left find_level_and_max (Prims.parse_int "0") l
  
let (levels : Prims.string -> (Prims.int * Prims.int * Prims.int)) =
  fun op  ->
    let uu____41318 = assign_levels level_associativity_spec op  in
    match uu____41318 with
    | (left1,mine,right1) ->
        if op = "*"
        then ((left1 - (Prims.parse_int "1")), mine, right1)
        else (left1, mine, right1)
  
let (operatorInfix0ad12 : associativity_level Prims.list) =
  [opinfix0a; opinfix0b; opinfix0c; opinfix0d; opinfix1; opinfix2] 
let (is_operatorInfix0ad12 : FStar_Ident.ident -> Prims.bool) =
  fun op  ->
    let uu____41377 =
      let uu____41380 =
        let uu____41386 = FStar_Ident.text_of_id op  in
        FStar_All.pipe_left matches_level uu____41386  in
      FStar_List.tryFind uu____41380 operatorInfix0ad12  in
    uu____41377 <> FStar_Pervasives_Native.None
  
let (is_operatorInfix34 : FStar_Ident.ident -> Prims.bool) =
  let opinfix34 = [opinfix3; opinfix4]  in
  fun op  ->
    let uu____41453 =
      let uu____41468 =
        let uu____41486 = FStar_Ident.text_of_id op  in
        FStar_All.pipe_left matches_level uu____41486  in
      FStar_List.tryFind uu____41468 opinfix34  in
    uu____41453 <> FStar_Pervasives_Native.None
  
let (handleable_args_length : FStar_Ident.ident -> Prims.int) =
  fun op  ->
    let op_s = FStar_Ident.text_of_id op  in
    let uu____41552 =
      (is_general_prefix_op op) || (FStar_List.mem op_s ["-"; "~"])  in
    if uu____41552
    then (Prims.parse_int "1")
    else
      (let uu____41565 =
         ((is_operatorInfix0ad12 op) || (is_operatorInfix34 op)) ||
           (FStar_List.mem op_s
              ["<==>"; "==>"; "\\/"; "/\\"; "="; "|>"; ":="; ".()"; ".[]"])
          in
       if uu____41565
       then (Prims.parse_int "2")
       else
         if FStar_List.mem op_s [".()<-"; ".[]<-"]
         then (Prims.parse_int "3")
         else (Prims.parse_int "0"))
  
let handleable_op :
  'Auu____41611 . FStar_Ident.ident -> 'Auu____41611 Prims.list -> Prims.bool
  =
  fun op  ->
    fun args  ->
      match FStar_List.length args with
      | _41627 when _41627 = (Prims.parse_int "0") -> true
      | _41629 when _41629 = (Prims.parse_int "1") ->
          (is_general_prefix_op op) ||
            (let uu____41631 = FStar_Ident.text_of_id op  in
             FStar_List.mem uu____41631 ["-"; "~"])
      | _41639 when _41639 = (Prims.parse_int "2") ->
          ((is_operatorInfix0ad12 op) || (is_operatorInfix34 op)) ||
            (let uu____41641 = FStar_Ident.text_of_id op  in
             FStar_List.mem uu____41641
               ["<==>"; "==>"; "\\/"; "/\\"; "="; "|>"; ":="; ".()"; ".[]"])
      | _41663 when _41663 = (Prims.parse_int "3") ->
          let uu____41664 = FStar_Ident.text_of_id op  in
          FStar_List.mem uu____41664 [".()<-"; ".[]<-"]
      | uu____41672 -> false
  
type annotation_style =
  | Binders of (Prims.int * Prims.int * Prims.bool) 
  | Arrows of (Prims.int * Prims.int) 
let (uu___is_Binders : annotation_style -> Prims.bool) =
  fun projectee  ->
    match projectee with | Binders _0 -> true | uu____41718 -> false
  
let (__proj__Binders__item___0 :
  annotation_style -> (Prims.int * Prims.int * Prims.bool)) =
  fun projectee  -> match projectee with | Binders _0 -> _0 
let (uu___is_Arrows : annotation_style -> Prims.bool) =
  fun projectee  ->
    match projectee with | Arrows _0 -> true | uu____41770 -> false
  
let (__proj__Arrows__item___0 : annotation_style -> (Prims.int * Prims.int))
  = fun projectee  -> match projectee with | Arrows _0 -> _0 
let (all_binders_annot : FStar_Parser_AST.term -> Prims.bool) =
  fun e  ->
    let is_binder_annot b =
      match b.FStar_Parser_AST.b with
      | FStar_Parser_AST.Annotated uu____41812 -> true
      | uu____41818 -> false  in
    let rec all_binders e1 l =
      match e1.FStar_Parser_AST.tm with
      | FStar_Parser_AST.Product (bs,tgt) ->
          let uu____41851 = FStar_List.for_all is_binder_annot bs  in
          if uu____41851
          then all_binders tgt (l + (FStar_List.length bs))
          else (false, (Prims.parse_int "0"))
      | uu____41866 -> (true, (l + (Prims.parse_int "1")))  in
    let uu____41871 = all_binders e (Prims.parse_int "0")  in
    match uu____41871 with
    | (b,l) -> if b && (l > (Prims.parse_int "1")) then true else false
  
type catf =
  FStar_Pprint.document -> FStar_Pprint.document -> FStar_Pprint.document
let (cat_with_colon :
  FStar_Pprint.document -> FStar_Pprint.document -> FStar_Pprint.document) =
  fun x  ->
    fun y  ->
      let uu____41910 = FStar_Pprint.op_Hat_Slash_Hat FStar_Pprint.colon y
         in
      FStar_Pprint.op_Hat_Hat x uu____41910
  
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
  'Auu____42059 .
    ('Auu____42059 -> FStar_Pprint.document) ->
      'Auu____42059 -> FStar_Range.range -> FStar_Pprint.document
  =
  fun printer  ->
    fun tm  ->
      fun tmrange  ->
        let rec comments_before_pos acc print_pos lookahead_pos =
          let uu____42101 = FStar_ST.op_Bang comment_stack  in
          match uu____42101 with
          | [] -> (acc, false)
          | (c,crange)::cs ->
              let comment =
                let uu____42172 = str c  in
                FStar_Pprint.op_Hat_Hat uu____42172 FStar_Pprint.hardline  in
              let uu____42173 = FStar_Range.range_before_pos crange print_pos
                 in
              if uu____42173
              then
                (FStar_ST.op_Colon_Equals comment_stack cs;
                 (let uu____42215 = FStar_Pprint.op_Hat_Hat acc comment  in
                  comments_before_pos uu____42215 print_pos lookahead_pos))
              else
                (let uu____42218 =
                   FStar_Range.range_before_pos crange lookahead_pos  in
                 (acc, uu____42218))
           in
        let uu____42221 =
          let uu____42227 =
            let uu____42228 = FStar_Range.start_of_range tmrange  in
            FStar_Range.end_of_line uu____42228  in
          let uu____42229 = FStar_Range.end_of_range tmrange  in
          comments_before_pos FStar_Pprint.empty uu____42227 uu____42229  in
        match uu____42221 with
        | (comments,has_lookahead) ->
            let printed_e = printer tm  in
            let comments1 =
              if has_lookahead
              then
                let pos = FStar_Range.end_of_range tmrange  in
                let uu____42238 = comments_before_pos comments pos pos  in
                FStar_Pervasives_Native.fst uu____42238
              else comments  in
            if comments1 = FStar_Pprint.empty
            then printed_e
            else
              (let uu____42250 = FStar_Pprint.op_Hat_Hat comments1 printed_e
                  in
               FStar_Pprint.group uu____42250)
  
let with_comment_sep :
  'Auu____42262 'Auu____42263 .
    ('Auu____42262 -> 'Auu____42263) ->
      'Auu____42262 ->
        FStar_Range.range -> (FStar_Pprint.document * 'Auu____42263)
  =
  fun printer  ->
    fun tm  ->
      fun tmrange  ->
        let rec comments_before_pos acc print_pos lookahead_pos =
          let uu____42309 = FStar_ST.op_Bang comment_stack  in
          match uu____42309 with
          | [] -> (acc, false)
          | (c,crange)::cs ->
              let comment = str c  in
              let uu____42380 = FStar_Range.range_before_pos crange print_pos
                 in
              if uu____42380
              then
                (FStar_ST.op_Colon_Equals comment_stack cs;
                 (let uu____42422 =
                    if acc = FStar_Pprint.empty
                    then comment
                    else
                      (let uu____42426 =
                         FStar_Pprint.op_Hat_Hat FStar_Pprint.hardline
                           comment
                          in
                       FStar_Pprint.op_Hat_Hat acc uu____42426)
                     in
                  comments_before_pos uu____42422 print_pos lookahead_pos))
              else
                (let uu____42429 =
                   FStar_Range.range_before_pos crange lookahead_pos  in
                 (acc, uu____42429))
           in
        let uu____42432 =
          let uu____42438 =
            let uu____42439 = FStar_Range.start_of_range tmrange  in
            FStar_Range.end_of_line uu____42439  in
          let uu____42440 = FStar_Range.end_of_range tmrange  in
          comments_before_pos FStar_Pprint.empty uu____42438 uu____42440  in
        match uu____42432 with
        | (comments,has_lookahead) ->
            let printed_e = printer tm  in
            let comments1 =
              if has_lookahead
              then
                let pos = FStar_Range.end_of_range tmrange  in
                let uu____42453 = comments_before_pos comments pos pos  in
                FStar_Pervasives_Native.fst uu____42453
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
                let uu____42506 = FStar_ST.op_Bang comment_stack  in
                match uu____42506 with
                | (comment,crange)::cs when
                    FStar_Range.range_before_pos crange pos ->
                    (FStar_ST.op_Colon_Equals comment_stack cs;
                     (let lnum =
                        let uu____42600 =
                          let uu____42602 =
                            let uu____42604 =
                              FStar_Range.start_of_range crange  in
                            FStar_Range.line_of_pos uu____42604  in
                          uu____42602 - lbegin  in
                        max k uu____42600  in
                      let lnum1 = min (Prims.parse_int "2") lnum  in
                      let doc2 =
                        let uu____42609 =
                          let uu____42610 =
                            FStar_Pprint.repeat lnum1 FStar_Pprint.hardline
                             in
                          let uu____42611 = str comment  in
                          FStar_Pprint.op_Hat_Hat uu____42610 uu____42611  in
                        FStar_Pprint.op_Hat_Hat doc1 uu____42609  in
                      let uu____42612 =
                        let uu____42614 = FStar_Range.end_of_range crange  in
                        FStar_Range.line_of_pos uu____42614  in
                      place_comments_until_pos (Prims.parse_int "1")
                        uu____42612 pos meta_decl doc2 true init1))
                | uu____42617 ->
                    if doc1 = FStar_Pprint.empty
                    then FStar_Pprint.empty
                    else
                      (let lnum =
                         let uu____42630 = FStar_Range.line_of_pos pos  in
                         uu____42630 - lbegin  in
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
                       let uu____42672 =
                         FStar_Pprint.repeat lnum7 FStar_Pprint.hardline  in
                       FStar_Pprint.op_Hat_Hat doc1 uu____42672)
  
let separate_map_with_comments :
  'Auu____42686 .
    FStar_Pprint.document ->
      FStar_Pprint.document ->
        ('Auu____42686 -> FStar_Pprint.document) ->
          'Auu____42686 Prims.list ->
            ('Auu____42686 -> decl_meta) -> FStar_Pprint.document
  =
  fun prefix1  ->
    fun sep  ->
      fun f  ->
        fun xs  ->
          fun extract_meta  ->
            let fold_fun uu____42745 x =
              match uu____42745 with
              | (last_line,doc1) ->
                  let meta_decl = extract_meta x  in
                  let r = meta_decl.r  in
                  let doc2 =
                    let uu____42764 = FStar_Range.start_of_range r  in
                    place_comments_until_pos (Prims.parse_int "1") last_line
                      uu____42764 meta_decl doc1 false false
                     in
                  let uu____42768 =
                    let uu____42770 = FStar_Range.end_of_range r  in
                    FStar_Range.line_of_pos uu____42770  in
                  let uu____42771 =
                    let uu____42772 =
                      let uu____42773 = f x  in
                      FStar_Pprint.op_Hat_Hat sep uu____42773  in
                    FStar_Pprint.op_Hat_Hat doc2 uu____42772  in
                  (uu____42768, uu____42771)
               in
            let uu____42775 =
              let uu____42782 = FStar_List.hd xs  in
              let uu____42783 = FStar_List.tl xs  in
              (uu____42782, uu____42783)  in
            match uu____42775 with
            | (x,xs1) ->
                let init1 =
                  let meta_decl = extract_meta x  in
                  let uu____42801 =
                    let uu____42803 = FStar_Range.end_of_range meta_decl.r
                       in
                    FStar_Range.line_of_pos uu____42803  in
                  let uu____42804 =
                    let uu____42805 = f x  in
                    FStar_Pprint.op_Hat_Hat prefix1 uu____42805  in
                  (uu____42801, uu____42804)  in
                let uu____42807 = FStar_List.fold_left fold_fun init1 xs1  in
                FStar_Pervasives_Native.snd uu____42807
  
let separate_map_with_comments_kw :
  'Auu____42834 'Auu____42835 .
    'Auu____42834 ->
      'Auu____42834 ->
        ('Auu____42834 -> 'Auu____42835 -> FStar_Pprint.document) ->
          'Auu____42835 Prims.list ->
            ('Auu____42835 -> decl_meta) -> FStar_Pprint.document
  =
  fun prefix1  ->
    fun sep  ->
      fun f  ->
        fun xs  ->
          fun extract_meta  ->
            let fold_fun uu____42899 x =
              match uu____42899 with
              | (last_line,doc1) ->
                  let meta_decl = extract_meta x  in
                  let r = meta_decl.r  in
                  let doc2 =
                    let uu____42918 = FStar_Range.start_of_range r  in
                    place_comments_until_pos (Prims.parse_int "1") last_line
                      uu____42918 meta_decl doc1 false false
                     in
                  let uu____42922 =
                    let uu____42924 = FStar_Range.end_of_range r  in
                    FStar_Range.line_of_pos uu____42924  in
                  let uu____42925 =
                    let uu____42926 = f sep x  in
                    FStar_Pprint.op_Hat_Hat doc2 uu____42926  in
                  (uu____42922, uu____42925)
               in
            let uu____42928 =
              let uu____42935 = FStar_List.hd xs  in
              let uu____42936 = FStar_List.tl xs  in
              (uu____42935, uu____42936)  in
            match uu____42928 with
            | (x,xs1) ->
                let init1 =
                  let meta_decl = extract_meta x  in
                  let uu____42954 =
                    let uu____42956 = FStar_Range.end_of_range meta_decl.r
                       in
                    FStar_Range.line_of_pos uu____42956  in
                  let uu____42957 = f prefix1 x  in
                  (uu____42954, uu____42957)  in
                let uu____42959 = FStar_List.fold_left fold_fun init1 xs1  in
                FStar_Pervasives_Native.snd uu____42959
  
let rec (p_decl : FStar_Parser_AST.decl -> FStar_Pprint.document) =
  fun d  ->
    let qualifiers =
      match ((d.FStar_Parser_AST.quals), (d.FStar_Parser_AST.d)) with
      | ((FStar_Parser_AST.Assumption )::[],FStar_Parser_AST.Assume
         (id1,uu____43945)) ->
          let uu____43948 =
            let uu____43950 =
              FStar_Util.char_at id1.FStar_Ident.idText (Prims.parse_int "0")
               in
            FStar_All.pipe_right uu____43950 FStar_Util.is_upper  in
          if uu____43948
          then
            let uu____43956 = p_qualifier FStar_Parser_AST.Assumption  in
            FStar_Pprint.op_Hat_Hat uu____43956 FStar_Pprint.space
          else p_qualifiers d.FStar_Parser_AST.quals
      | uu____43959 -> p_qualifiers d.FStar_Parser_AST.quals  in
    let uu____43966 =
      FStar_Pprint.optional (fun d1  -> p_fsdoc d1) d.FStar_Parser_AST.doc
       in
    let uu____43969 =
      let uu____43970 = p_attributes d.FStar_Parser_AST.attrs  in
      let uu____43971 =
        let uu____43972 = p_rawDecl d  in
        FStar_Pprint.op_Hat_Hat qualifiers uu____43972  in
      FStar_Pprint.op_Hat_Hat uu____43970 uu____43971  in
    FStar_Pprint.op_Hat_Hat uu____43966 uu____43969

and (p_attributes : FStar_Parser_AST.attributes_ -> FStar_Pprint.document) =
  fun attrs  ->
    match attrs with
    | [] -> FStar_Pprint.empty
    | uu____43974 ->
        let uu____43975 =
          let uu____43976 = str "@ "  in
          let uu____43978 =
            let uu____43979 =
              let uu____43980 =
                let uu____43981 =
                  let uu____43982 = FStar_List.map p_atomicTerm attrs  in
                  FStar_Pprint.flow break1 uu____43982  in
                FStar_Pprint.op_Hat_Hat uu____43981 FStar_Pprint.rbracket  in
              FStar_Pprint.align uu____43980  in
            FStar_Pprint.op_Hat_Hat uu____43979 FStar_Pprint.hardline  in
          FStar_Pprint.op_Hat_Hat uu____43976 uu____43978  in
        FStar_Pprint.op_Hat_Hat FStar_Pprint.lbracket uu____43975

and (p_fsdoc : FStar_Parser_AST.fsdoc -> FStar_Pprint.document) =
  fun uu____43985  ->
    match uu____43985 with
    | (doc1,kwd_args) ->
        let kwd_args_doc =
          match kwd_args with
          | [] -> FStar_Pprint.empty
          | kwd_args1 ->
              let process_kwd_arg uu____44033 =
                match uu____44033 with
                | (kwd,arg) ->
                    let uu____44046 = str "@"  in
                    let uu____44048 =
                      let uu____44049 = str kwd  in
                      let uu____44050 =
                        let uu____44051 = str arg  in
                        FStar_Pprint.op_Hat_Hat FStar_Pprint.space
                          uu____44051
                         in
                      FStar_Pprint.op_Hat_Hat uu____44049 uu____44050  in
                    FStar_Pprint.op_Hat_Hat uu____44046 uu____44048
                 in
              let uu____44052 =
                FStar_Pprint.separate_map FStar_Pprint.hardline
                  process_kwd_arg kwd_args1
                 in
              FStar_Pprint.op_Hat_Hat uu____44052 FStar_Pprint.hardline
           in
        let uu____44059 =
          let uu____44060 =
            let uu____44061 =
              let uu____44062 = str doc1  in
              let uu____44063 =
                let uu____44064 =
                  let uu____44065 =
                    FStar_Pprint.op_Hat_Hat FStar_Pprint.rparen
                      FStar_Pprint.hardline
                     in
                  FStar_Pprint.op_Hat_Hat FStar_Pprint.star uu____44065  in
                FStar_Pprint.op_Hat_Hat kwd_args_doc uu____44064  in
              FStar_Pprint.op_Hat_Hat uu____44062 uu____44063  in
            FStar_Pprint.op_Hat_Hat FStar_Pprint.star uu____44061  in
          FStar_Pprint.op_Hat_Hat FStar_Pprint.star uu____44060  in
        FStar_Pprint.op_Hat_Hat FStar_Pprint.lparen uu____44059

and (p_justSig : FStar_Parser_AST.decl -> FStar_Pprint.document) =
  fun d  ->
    match d.FStar_Parser_AST.d with
    | FStar_Parser_AST.Val (lid,t) ->
        let uu____44069 =
          let uu____44070 = str "val"  in
          let uu____44072 =
            let uu____44073 =
              let uu____44074 = p_lident lid  in
              let uu____44075 =
                FStar_Pprint.op_Hat_Hat FStar_Pprint.space FStar_Pprint.colon
                 in
              FStar_Pprint.op_Hat_Hat uu____44074 uu____44075  in
            FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____44073  in
          FStar_Pprint.op_Hat_Hat uu____44070 uu____44072  in
        let uu____44076 = p_typ false false t  in
        FStar_Pprint.op_Hat_Hat uu____44069 uu____44076
    | FStar_Parser_AST.TopLevelLet (uu____44079,lbs) ->
        FStar_Pprint.separate_map FStar_Pprint.hardline
          (fun lb  ->
             let uu____44104 =
               let uu____44105 = str "let"  in p_letlhs uu____44105 lb false
                in
             FStar_Pprint.group uu____44104) lbs
    | uu____44108 -> FStar_Pprint.empty

and (p_list :
  (FStar_Ident.ident -> FStar_Pprint.document) ->
    FStar_Pprint.document ->
      FStar_Ident.ident Prims.list -> FStar_Pprint.document)
  =
  fun f  ->
    fun sep  ->
      fun l  ->
        let rec p_list' uu___328_44123 =
          match uu___328_44123 with
          | [] -> FStar_Pprint.empty
          | x::[] -> f x
          | x::xs ->
              let uu____44131 = f x  in
              let uu____44132 =
                let uu____44133 = p_list' xs  in
                FStar_Pprint.op_Hat_Hat sep uu____44133  in
              FStar_Pprint.op_Hat_Hat uu____44131 uu____44132
           in
        let uu____44134 = str "["  in
        let uu____44136 =
          let uu____44137 = p_list' l  in
          let uu____44138 = str "]"  in
          FStar_Pprint.op_Hat_Hat uu____44137 uu____44138  in
        FStar_Pprint.op_Hat_Hat uu____44134 uu____44136

and (p_rawDecl : FStar_Parser_AST.decl -> FStar_Pprint.document) =
  fun d  ->
    match d.FStar_Parser_AST.d with
    | FStar_Parser_AST.Open uid ->
        let uu____44142 =
          let uu____44143 = str "open"  in
          let uu____44145 = p_quident uid  in
          FStar_Pprint.op_Hat_Slash_Hat uu____44143 uu____44145  in
        FStar_Pprint.group uu____44142
    | FStar_Parser_AST.Include uid ->
        let uu____44147 =
          let uu____44148 = str "include"  in
          let uu____44150 = p_quident uid  in
          FStar_Pprint.op_Hat_Slash_Hat uu____44148 uu____44150  in
        FStar_Pprint.group uu____44147
    | FStar_Parser_AST.Friend uid ->
        let uu____44152 =
          let uu____44153 = str "friend"  in
          let uu____44155 = p_quident uid  in
          FStar_Pprint.op_Hat_Slash_Hat uu____44153 uu____44155  in
        FStar_Pprint.group uu____44152
    | FStar_Parser_AST.ModuleAbbrev (uid1,uid2) ->
        let uu____44158 =
          let uu____44159 = str "module"  in
          let uu____44161 =
            let uu____44162 =
              let uu____44163 = p_uident uid1  in
              let uu____44164 =
                FStar_Pprint.op_Hat_Hat FStar_Pprint.space
                  FStar_Pprint.equals
                 in
              FStar_Pprint.op_Hat_Hat uu____44163 uu____44164  in
            FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____44162  in
          FStar_Pprint.op_Hat_Hat uu____44159 uu____44161  in
        let uu____44165 = p_quident uid2  in
        op_Hat_Slash_Plus_Hat uu____44158 uu____44165
    | FStar_Parser_AST.TopLevelModule uid ->
        let uu____44167 =
          let uu____44168 = str "module"  in
          let uu____44170 =
            let uu____44171 = p_quident uid  in
            FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____44171  in
          FStar_Pprint.op_Hat_Hat uu____44168 uu____44170  in
        FStar_Pprint.group uu____44167
    | FStar_Parser_AST.Tycon
        (true
         ,uu____44172,(FStar_Parser_AST.TyconAbbrev
                       (uid,tpars,FStar_Pervasives_Native.None ,t),FStar_Pervasives_Native.None
                       )::[])
        ->
        let effect_prefix_doc =
          let uu____44209 = str "effect"  in
          let uu____44211 =
            let uu____44212 = p_uident uid  in
            FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____44212  in
          FStar_Pprint.op_Hat_Hat uu____44209 uu____44211  in
        let uu____44213 =
          let uu____44214 = p_typars tpars  in
          FStar_Pprint.surround (Prims.parse_int "2") (Prims.parse_int "1")
            effect_prefix_doc uu____44214 FStar_Pprint.equals
           in
        let uu____44217 = p_typ false false t  in
        op_Hat_Slash_Plus_Hat uu____44213 uu____44217
    | FStar_Parser_AST.Tycon (false ,tc,tcdefs) ->
        let s = if tc then str "class" else str "type"  in
        let uu____44248 =
          let uu____44249 = FStar_List.hd tcdefs  in
          p_fsdocTypeDeclPairs s uu____44249  in
        let uu____44262 =
          let uu____44263 = FStar_List.tl tcdefs  in
          FStar_All.pipe_left
            (FStar_Pprint.concat_map
               (fun x  ->
                  let uu____44301 =
                    let uu____44302 = str "and"  in
                    p_fsdocTypeDeclPairs uu____44302 x  in
                  FStar_Pprint.op_Hat_Hat break1 uu____44301)) uu____44263
           in
        FStar_Pprint.op_Hat_Hat uu____44248 uu____44262
    | FStar_Parser_AST.TopLevelLet (q,lbs) ->
        let let_doc =
          let uu____44319 = str "let"  in
          let uu____44321 = p_letqualifier q  in
          FStar_Pprint.op_Hat_Hat uu____44319 uu____44321  in
        let uu____44322 = str "and"  in
        separate_map_with_comments_kw let_doc uu____44322 p_letbinding lbs
          (fun uu____44332  ->
             match uu____44332 with
             | (p,t) ->
                 let uu____44339 =
                   FStar_Range.union_ranges p.FStar_Parser_AST.prange
                     t.FStar_Parser_AST.range
                    in
                 {
                   r = uu____44339;
                   has_qs = false;
                   has_attrs = false;
                   has_fsdoc = (FStar_Util.is_some d.FStar_Parser_AST.doc);
                   is_fsdoc = false
                 })
    | FStar_Parser_AST.Val (lid,t) ->
        let uu____44345 =
          let uu____44346 = str "val"  in
          let uu____44348 =
            let uu____44349 =
              let uu____44350 = p_lident lid  in
              let uu____44351 = sig_as_binders_if_possible t false  in
              FStar_Pprint.op_Hat_Hat uu____44350 uu____44351  in
            FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____44349  in
          FStar_Pprint.op_Hat_Hat uu____44346 uu____44348  in
        FStar_All.pipe_left FStar_Pprint.group uu____44345
    | FStar_Parser_AST.Assume (id1,t) ->
        let decl_keyword =
          let uu____44356 =
            let uu____44358 =
              FStar_Util.char_at id1.FStar_Ident.idText (Prims.parse_int "0")
               in
            FStar_All.pipe_right uu____44358 FStar_Util.is_upper  in
          if uu____44356
          then FStar_Pprint.empty
          else
            (let uu____44366 = str "val"  in
             FStar_Pprint.op_Hat_Hat uu____44366 FStar_Pprint.space)
           in
        let uu____44368 =
          let uu____44369 = p_ident id1  in
          let uu____44370 =
            let uu____44371 =
              let uu____44372 =
                let uu____44373 = p_typ false false t  in
                FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____44373  in
              FStar_Pprint.op_Hat_Hat FStar_Pprint.colon uu____44372  in
            FStar_Pprint.group uu____44371  in
          FStar_Pprint.op_Hat_Hat uu____44369 uu____44370  in
        FStar_Pprint.op_Hat_Hat decl_keyword uu____44368
    | FStar_Parser_AST.Exception (uid,t_opt) ->
        let uu____44382 = str "exception"  in
        let uu____44384 =
          let uu____44385 =
            let uu____44386 = p_uident uid  in
            let uu____44387 =
              FStar_Pprint.optional
                (fun t  ->
                   let uu____44391 =
                     let uu____44392 = str "of"  in
                     let uu____44394 = p_typ false false t  in
                     op_Hat_Slash_Plus_Hat uu____44392 uu____44394  in
                   FStar_Pprint.op_Hat_Hat break1 uu____44391) t_opt
               in
            FStar_Pprint.op_Hat_Hat uu____44386 uu____44387  in
          FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____44385  in
        FStar_Pprint.op_Hat_Hat uu____44382 uu____44384
    | FStar_Parser_AST.NewEffect ne ->
        let uu____44398 = str "new_effect"  in
        let uu____44400 =
          let uu____44401 = p_newEffect ne  in
          FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____44401  in
        FStar_Pprint.op_Hat_Hat uu____44398 uu____44400
    | FStar_Parser_AST.SubEffect se ->
        let uu____44403 = str "sub_effect"  in
        let uu____44405 =
          let uu____44406 = p_subEffect se  in
          FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____44406  in
        FStar_Pprint.op_Hat_Hat uu____44403 uu____44405
    | FStar_Parser_AST.Pragma p -> p_pragma p
    | FStar_Parser_AST.Fsdoc doc1 -> p_fsdoc doc1
    | FStar_Parser_AST.Main uu____44409 ->
        failwith "*Main declaration* : Is that really still in use ??"
    | FStar_Parser_AST.Tycon (true ,uu____44411,uu____44412) ->
        failwith
          "Effect abbreviation is expected to be defined by an abbreviation"
    | FStar_Parser_AST.Splice (ids,t) ->
        let uu____44440 = str "%splice"  in
        let uu____44442 =
          let uu____44443 =
            let uu____44444 = str ";"  in p_list p_uident uu____44444 ids  in
          let uu____44446 =
            let uu____44447 = p_term false false t  in
            FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____44447  in
          FStar_Pprint.op_Hat_Hat uu____44443 uu____44446  in
        FStar_Pprint.op_Hat_Hat uu____44440 uu____44442

and (p_pragma : FStar_Parser_AST.pragma -> FStar_Pprint.document) =
  fun uu___329_44450  ->
    match uu___329_44450 with
    | FStar_Parser_AST.SetOptions s ->
        let uu____44453 = str "#set-options"  in
        let uu____44455 =
          let uu____44456 =
            let uu____44457 = str s  in FStar_Pprint.dquotes uu____44457  in
          FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____44456  in
        FStar_Pprint.op_Hat_Hat uu____44453 uu____44455
    | FStar_Parser_AST.ResetOptions s_opt ->
        let uu____44462 = str "#reset-options"  in
        let uu____44464 =
          FStar_Pprint.optional
            (fun s  ->
               let uu____44470 =
                 let uu____44471 = str s  in FStar_Pprint.dquotes uu____44471
                  in
               FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____44470) s_opt
           in
        FStar_Pprint.op_Hat_Hat uu____44462 uu____44464
    | FStar_Parser_AST.PushOptions s_opt ->
        let uu____44476 = str "#push-options"  in
        let uu____44478 =
          FStar_Pprint.optional
            (fun s  ->
               let uu____44484 =
                 let uu____44485 = str s  in FStar_Pprint.dquotes uu____44485
                  in
               FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____44484) s_opt
           in
        FStar_Pprint.op_Hat_Hat uu____44476 uu____44478
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
    fun uu____44516  ->
      match uu____44516 with
      | (typedecl,fsdoc_opt) ->
          let uu____44529 = p_typeDecl (kw, fsdoc_opt) typedecl  in
          (match uu____44529 with
           | (comm,decl,body,pre) ->
               if comm = FStar_Pprint.empty
               then
                 let uu____44554 = pre body  in
                 FStar_Pprint.op_Hat_Hat decl uu____44554
               else
                 (let uu____44557 =
                    let uu____44558 =
                      let uu____44559 =
                        let uu____44560 = pre body  in
                        FStar_Pprint.op_Hat_Slash_Hat uu____44560 comm  in
                      FStar_Pprint.op_Hat_Hat decl uu____44559  in
                    let uu____44561 =
                      let uu____44562 =
                        let uu____44563 =
                          let uu____44564 =
                            let uu____44565 =
                              FStar_Pprint.op_Hat_Hat FStar_Pprint.hardline
                                body
                               in
                            FStar_Pprint.op_Hat_Hat comm uu____44565  in
                          FStar_Pprint.op_Hat_Hat FStar_Pprint.hardline
                            uu____44564
                           in
                        FStar_Pprint.nest (Prims.parse_int "2") uu____44563
                         in
                      FStar_Pprint.op_Hat_Hat decl uu____44562  in
                    FStar_Pprint.ifflat uu____44558 uu____44561  in
                  FStar_All.pipe_left FStar_Pprint.group uu____44557))

and (p_typeDecl :
  (FStar_Pprint.document * FStar_Parser_AST.fsdoc
    FStar_Pervasives_Native.option) ->
    FStar_Parser_AST.tycon ->
      (FStar_Pprint.document * FStar_Pprint.document * FStar_Pprint.document
        * (FStar_Pprint.document -> FStar_Pprint.document)))
  =
  fun pre  ->
    fun uu___330_44568  ->
      match uu___330_44568 with
      | FStar_Parser_AST.TyconAbstract (lid,bs,typ_opt) ->
          let uu____44597 = p_typeDeclPrefix pre false lid bs typ_opt  in
          (FStar_Pprint.empty, uu____44597, FStar_Pprint.empty,
            FStar_Pervasives.id)
      | FStar_Parser_AST.TyconAbbrev (lid,bs,typ_opt,t) ->
          let uu____44614 = p_typ_sep false false t  in
          (match uu____44614 with
           | (comm,doc1) ->
               let uu____44634 = p_typeDeclPrefix pre true lid bs typ_opt  in
               (comm, uu____44634, doc1, jump2))
      | FStar_Parser_AST.TyconRecord (lid,bs,typ_opt,record_field_decls) ->
          let p_recordFieldAndComments ps uu____44690 =
            match uu____44690 with
            | (lid1,t,doc_opt) ->
                let uu____44707 =
                  let uu____44712 =
                    FStar_Range.extend_to_end_of_line
                      t.FStar_Parser_AST.range
                     in
                  with_comment_sep (p_recordFieldDecl ps) (lid1, t, doc_opt)
                    uu____44712
                   in
                (match uu____44707 with
                 | (comm,field) ->
                     let sep =
                       if ps then FStar_Pprint.semi else FStar_Pprint.empty
                        in
                     inline_comment_or_above comm field sep)
             in
          let p_fields =
            let uu____44730 =
              separate_map_last FStar_Pprint.hardline
                p_recordFieldAndComments record_field_decls
               in
            braces_with_nesting uu____44730  in
          let uu____44739 = p_typeDeclPrefix pre true lid bs typ_opt  in
          (FStar_Pprint.empty, uu____44739, p_fields,
            ((fun d  -> FStar_Pprint.op_Hat_Hat FStar_Pprint.space d)))
      | FStar_Parser_AST.TyconVariant (lid,bs,typ_opt,ct_decls) ->
          let p_constructorBranchAndComments uu____44806 =
            match uu____44806 with
            | (uid,t_opt,doc_opt,use_of) ->
                let range =
                  let uu____44835 =
                    let uu____44836 =
                      FStar_Util.map_opt t_opt
                        (fun t  -> t.FStar_Parser_AST.range)
                       in
                    FStar_Util.dflt uid.FStar_Ident.idRange uu____44836  in
                  FStar_Range.extend_to_end_of_line uu____44835  in
                let uu____44841 =
                  with_comment_sep p_constructorBranch
                    (uid, t_opt, doc_opt, use_of) range
                   in
                (match uu____44841 with
                 | (comm,ctor) ->
                     inline_comment_or_above comm ctor FStar_Pprint.empty)
             in
          let datacon_doc =
            FStar_Pprint.separate_map FStar_Pprint.hardline
              p_constructorBranchAndComments ct_decls
             in
          let uu____44880 = p_typeDeclPrefix pre true lid bs typ_opt  in
          (FStar_Pprint.empty, uu____44880, datacon_doc, jump2)

and (p_typeDeclPrefix :
  (FStar_Pprint.document * FStar_Parser_AST.fsdoc
    FStar_Pervasives_Native.option) ->
    Prims.bool ->
      FStar_Ident.ident ->
        FStar_Parser_AST.binder Prims.list ->
          FStar_Parser_AST.knd FStar_Pervasives_Native.option ->
            FStar_Pprint.document)
  =
  fun uu____44885  ->
    fun eq1  ->
      fun lid  ->
        fun bs  ->
          fun typ_opt  ->
            match uu____44885 with
            | (kw,fsdoc_opt) ->
                let maybe_with_fsdoc cont =
                  let lid_doc = p_ident lid  in
                  let kw_lid =
                    let uu____44920 =
                      FStar_Pprint.op_Hat_Slash_Hat kw lid_doc  in
                    FStar_Pprint.group uu____44920  in
                  match fsdoc_opt with
                  | FStar_Pervasives_Native.None  -> cont kw_lid
                  | FStar_Pervasives_Native.Some fsdoc ->
                      let uu____44922 =
                        let uu____44925 =
                          let uu____44928 = p_fsdoc fsdoc  in
                          let uu____44929 =
                            let uu____44932 = cont lid_doc  in [uu____44932]
                             in
                          uu____44928 :: uu____44929  in
                        kw :: uu____44925  in
                      FStar_Pprint.separate FStar_Pprint.hardline uu____44922
                   in
                let typ =
                  let maybe_eq =
                    if eq1 then FStar_Pprint.equals else FStar_Pprint.empty
                     in
                  match typ_opt with
                  | FStar_Pervasives_Native.None  -> maybe_eq
                  | FStar_Pervasives_Native.Some t ->
                      let uu____44939 =
                        let uu____44940 =
                          let uu____44941 = p_typ false false t  in
                          FStar_Pprint.op_Hat_Slash_Hat uu____44941 maybe_eq
                           in
                        FStar_Pprint.op_Hat_Hat FStar_Pprint.space
                          uu____44940
                         in
                      FStar_Pprint.op_Hat_Hat FStar_Pprint.colon uu____44939
                   in
                if bs = []
                then maybe_with_fsdoc (fun n1  -> prefix2 n1 typ)
                else
                  (let binders = p_binders_list true bs  in
                   maybe_with_fsdoc
                     (fun n1  ->
                        let uu____44961 =
                          let uu____44962 = FStar_Pprint.flow break1 binders
                             in
                          prefix2 n1 uu____44962  in
                        prefix2 uu____44961 typ))

and (p_recordFieldDecl :
  Prims.bool ->
    (FStar_Ident.ident * FStar_Parser_AST.term * FStar_Parser_AST.fsdoc
      FStar_Pervasives_Native.option) -> FStar_Pprint.document)
  =
  fun ps  ->
    fun uu____44964  ->
      match uu____44964 with
      | (lid,t,doc_opt) ->
          let uu____44981 =
            let uu____44982 = FStar_Pprint.optional p_fsdoc doc_opt  in
            let uu____44983 =
              let uu____44984 = p_lident lid  in
              let uu____44985 =
                let uu____44986 = p_typ ps false t  in
                FStar_Pprint.op_Hat_Hat FStar_Pprint.colon uu____44986  in
              FStar_Pprint.op_Hat_Hat uu____44984 uu____44985  in
            FStar_Pprint.op_Hat_Hat uu____44982 uu____44983  in
          FStar_Pprint.group uu____44981

and (p_constructorBranch :
  (FStar_Ident.ident * FStar_Parser_AST.term FStar_Pervasives_Native.option *
    FStar_Parser_AST.fsdoc FStar_Pervasives_Native.option * Prims.bool) ->
    FStar_Pprint.document)
  =
  fun uu____44988  ->
    match uu____44988 with
    | (uid,t_opt,doc_opt,use_of) ->
        let sep = if use_of then str "of" else FStar_Pprint.colon  in
        let uid_doc =
          let uu____45022 =
            let uu____45023 =
              let uu____45024 = p_uident uid  in
              FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____45024  in
            FStar_Pprint.op_Hat_Hat FStar_Pprint.bar uu____45023  in
          FStar_Pprint.group uu____45022  in
        let uu____45025 = FStar_Pprint.optional p_fsdoc doc_opt  in
        let uu____45026 =
          default_or_map uid_doc
            (fun t  ->
               let uu____45030 =
                 let uu____45031 =
                   let uu____45032 =
                     let uu____45033 =
                       let uu____45034 = p_typ false false t  in
                       FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____45034
                        in
                     FStar_Pprint.op_Hat_Hat sep uu____45033  in
                   FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____45032  in
                 FStar_Pprint.op_Hat_Hat uid_doc uu____45031  in
               FStar_Pprint.group uu____45030) t_opt
           in
        FStar_Pprint.op_Hat_Hat uu____45025 uu____45026

and (p_letlhs :
  FStar_Pprint.document ->
    (FStar_Parser_AST.pattern * FStar_Parser_AST.term) ->
      Prims.bool -> FStar_Pprint.document)
  =
  fun kw  ->
    fun uu____45038  ->
      fun inner_let  ->
        match uu____45038 with
        | (pat,uu____45046) ->
            let uu____45047 =
              match pat.FStar_Parser_AST.pat with
              | FStar_Parser_AST.PatAscribed
                  (pat1,(t,FStar_Pervasives_Native.None )) ->
                  (pat1,
                    (FStar_Pervasives_Native.Some (t, FStar_Pprint.empty)))
              | FStar_Parser_AST.PatAscribed
                  (pat1,(t,FStar_Pervasives_Native.Some tac)) ->
                  let uu____45099 =
                    let uu____45106 =
                      let uu____45111 =
                        let uu____45112 =
                          let uu____45113 =
                            let uu____45114 = str "by"  in
                            let uu____45116 =
                              let uu____45117 = p_atomicTerm tac  in
                              FStar_Pprint.op_Hat_Hat FStar_Pprint.space
                                uu____45117
                               in
                            FStar_Pprint.op_Hat_Hat uu____45114 uu____45116
                             in
                          FStar_Pprint.op_Hat_Hat FStar_Pprint.space
                            uu____45113
                           in
                        FStar_Pprint.group uu____45112  in
                      (t, uu____45111)  in
                    FStar_Pervasives_Native.Some uu____45106  in
                  (pat1, uu____45099)
              | uu____45128 -> (pat, FStar_Pervasives_Native.None)  in
            (match uu____45047 with
             | (pat1,ascr) ->
                 (match pat1.FStar_Parser_AST.pat with
                  | FStar_Parser_AST.PatApp
                      ({
                         FStar_Parser_AST.pat = FStar_Parser_AST.PatVar
                           (lid,uu____45154);
                         FStar_Parser_AST.prange = uu____45155;_},pats)
                      ->
                      let ascr_doc =
                        match ascr with
                        | FStar_Pervasives_Native.Some (t,tac) ->
                            let uu____45172 =
                              sig_as_binders_if_possible t true  in
                            FStar_Pprint.op_Hat_Hat uu____45172 tac
                        | FStar_Pervasives_Native.None  -> FStar_Pprint.empty
                         in
                      let uu____45178 =
                        if inner_let
                        then
                          let uu____45192 = pats_as_binders_if_possible pats
                             in
                          match uu____45192 with
                          | (bs,style) ->
                              ((FStar_List.append bs [ascr_doc]), style)
                        else
                          (let uu____45215 = pats_as_binders_if_possible pats
                              in
                           match uu____45215 with
                           | (bs,style) ->
                               ((FStar_List.append bs [ascr_doc]), style))
                         in
                      (match uu____45178 with
                       | (terms,style) ->
                           let uu____45242 =
                             let uu____45243 =
                               let uu____45244 =
                                 let uu____45245 = p_lident lid  in
                                 let uu____45246 =
                                   format_sig style terms true true  in
                                 FStar_Pprint.op_Hat_Hat uu____45245
                                   uu____45246
                                  in
                               FStar_Pprint.op_Hat_Hat FStar_Pprint.space
                                 uu____45244
                                in
                             FStar_Pprint.op_Hat_Hat kw uu____45243  in
                           FStar_All.pipe_left FStar_Pprint.group uu____45242)
                  | uu____45249 ->
                      let ascr_doc =
                        match ascr with
                        | FStar_Pervasives_Native.Some (t,tac) ->
                            let uu____45257 =
                              let uu____45258 =
                                let uu____45259 =
                                  p_typ_top
                                    (Arrows
                                       ((Prims.parse_int "2"),
                                         (Prims.parse_int "2"))) false false
                                    t
                                   in
                                FStar_Pprint.op_Hat_Hat FStar_Pprint.colon
                                  uu____45259
                                 in
                              FStar_Pprint.group uu____45258  in
                            FStar_Pprint.op_Hat_Hat uu____45257 tac
                        | FStar_Pervasives_Native.None  -> FStar_Pprint.empty
                         in
                      let uu____45270 =
                        let uu____45271 =
                          let uu____45272 =
                            let uu____45273 = p_tuplePattern pat1  in
                            FStar_Pprint.op_Hat_Slash_Hat kw uu____45273  in
                          FStar_Pprint.group uu____45272  in
                        FStar_Pprint.op_Hat_Hat uu____45271 ascr_doc  in
                      FStar_Pprint.group uu____45270))

and (p_letbinding :
  FStar_Pprint.document ->
    (FStar_Parser_AST.pattern * FStar_Parser_AST.term) ->
      FStar_Pprint.document)
  =
  fun kw  ->
    fun uu____45275  ->
      match uu____45275 with
      | (pat,e) ->
          let doc_pat = p_letlhs kw (pat, e) false  in
          let uu____45284 = p_term_sep false false e  in
          (match uu____45284 with
           | (comm,doc_expr) ->
               let doc_expr1 =
                 inline_comment_or_above comm doc_expr FStar_Pprint.empty  in
               let uu____45294 =
                 let uu____45295 =
                   FStar_Pprint.op_Hat_Slash_Hat FStar_Pprint.equals
                     doc_expr1
                    in
                 FStar_Pprint.op_Hat_Slash_Hat doc_pat uu____45295  in
               let uu____45296 =
                 let uu____45297 =
                   let uu____45298 =
                     let uu____45299 =
                       let uu____45300 = jump2 doc_expr1  in
                       FStar_Pprint.op_Hat_Hat FStar_Pprint.equals
                         uu____45300
                        in
                     FStar_Pprint.group uu____45299  in
                   FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____45298  in
                 FStar_Pprint.op_Hat_Hat doc_pat uu____45297  in
               FStar_Pprint.ifflat uu____45294 uu____45296)

and (p_newEffect : FStar_Parser_AST.effect_decl -> FStar_Pprint.document) =
  fun uu___331_45301  ->
    match uu___331_45301 with
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
        let uu____45326 = p_uident uid  in
        let uu____45327 = p_binders true bs  in
        let uu____45329 =
          let uu____45330 = p_simpleTerm false false t  in
          prefix2 FStar_Pprint.equals uu____45330  in
        surround_maybe_empty (Prims.parse_int "2") (Prims.parse_int "1")
          uu____45326 uu____45327 uu____45329

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
          let uu____45345 =
            let uu____45346 =
              let uu____45347 =
                let uu____45348 = p_uident uid  in
                let uu____45349 = p_binders true bs  in
                let uu____45351 =
                  let uu____45352 = p_typ false false t  in
                  prefix2 FStar_Pprint.colon uu____45352  in
                surround_maybe_empty (Prims.parse_int "2")
                  (Prims.parse_int "1") uu____45348 uu____45349 uu____45351
                 in
              FStar_Pprint.group uu____45347  in
            let uu____45357 =
              let uu____45358 = str "with"  in
              let uu____45360 =
                let uu____45361 =
                  let uu____45362 =
                    let uu____45363 =
                      let uu____45364 =
                        let uu____45365 =
                          FStar_Pprint.op_Hat_Hat FStar_Pprint.semi
                            FStar_Pprint.space
                           in
                        FStar_Pprint.op_Hat_Hat FStar_Pprint.hardline
                          uu____45365
                         in
                      separate_map_last uu____45364 p_effectDecl eff_decls
                       in
                    FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____45363
                     in
                  FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____45362  in
                FStar_Pprint.op_Hat_Hat FStar_Pprint.hardline uu____45361  in
              FStar_Pprint.op_Hat_Hat uu____45358 uu____45360  in
            FStar_Pprint.op_Hat_Slash_Hat uu____45346 uu____45357  in
          braces_with_nesting uu____45345

and (p_effectDecl :
  Prims.bool -> FStar_Parser_AST.decl -> FStar_Pprint.document) =
  fun ps  ->
    fun d  ->
      match d.FStar_Parser_AST.d with
      | FStar_Parser_AST.Tycon
          (false
           ,uu____45369,(FStar_Parser_AST.TyconAbbrev
                         (lid,[],FStar_Pervasives_Native.None ,e),FStar_Pervasives_Native.None
                         )::[])
          ->
          let uu____45402 =
            let uu____45403 = p_lident lid  in
            let uu____45404 =
              FStar_Pprint.op_Hat_Hat FStar_Pprint.space FStar_Pprint.equals
               in
            FStar_Pprint.op_Hat_Hat uu____45403 uu____45404  in
          let uu____45405 = p_simpleTerm ps false e  in
          prefix2 uu____45402 uu____45405
      | uu____45407 ->
          let uu____45408 =
            let uu____45410 = FStar_Parser_AST.decl_to_string d  in
            FStar_Util.format1
              "Not a declaration of an effect member... or at least I hope so : %s"
              uu____45410
             in
          failwith uu____45408

and (p_subEffect : FStar_Parser_AST.lift -> FStar_Pprint.document) =
  fun lift  ->
    let lift_op_doc =
      let lifts =
        match lift.FStar_Parser_AST.lift_op with
        | FStar_Parser_AST.NonReifiableLift t -> [("lift_wp", t)]
        | FStar_Parser_AST.ReifiableLift (t1,t2) ->
            [("lift_wp", t1); ("lift", t2)]
        | FStar_Parser_AST.LiftForFree t -> [("lift", t)]  in
      let p_lift ps uu____45493 =
        match uu____45493 with
        | (kwd,t) ->
            let uu____45504 =
              let uu____45505 = str kwd  in
              let uu____45506 =
                FStar_Pprint.op_Hat_Hat FStar_Pprint.space
                  FStar_Pprint.equals
                 in
              FStar_Pprint.op_Hat_Hat uu____45505 uu____45506  in
            let uu____45507 = p_simpleTerm ps false t  in
            prefix2 uu____45504 uu____45507
         in
      separate_break_map_last FStar_Pprint.semi p_lift lifts  in
    let uu____45514 =
      let uu____45515 =
        let uu____45516 = p_quident lift.FStar_Parser_AST.msource  in
        let uu____45517 =
          let uu____45518 = str "~>"  in
          FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____45518  in
        FStar_Pprint.op_Hat_Hat uu____45516 uu____45517  in
      let uu____45520 = p_quident lift.FStar_Parser_AST.mdest  in
      prefix2 uu____45515 uu____45520  in
    let uu____45521 =
      let uu____45522 = braces_with_nesting lift_op_doc  in
      FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____45522  in
    FStar_Pprint.op_Hat_Hat uu____45514 uu____45521

and (p_qualifier : FStar_Parser_AST.qualifier -> FStar_Pprint.document) =
  fun uu___332_45523  ->
    match uu___332_45523 with
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
        let uu____45543 = p_qualifier q  in
        FStar_Pprint.op_Hat_Hat uu____45543 FStar_Pprint.hardline
    | uu____45544 ->
        let uu____45545 =
          let uu____45546 = FStar_List.map p_qualifier qs  in
          FStar_Pprint.flow break1 uu____45546  in
        FStar_Pprint.op_Hat_Hat uu____45545 FStar_Pprint.hardline

and (p_letqualifier :
  FStar_Parser_AST.let_qualifier -> FStar_Pprint.document) =
  fun uu___333_45549  ->
    match uu___333_45549 with
    | FStar_Parser_AST.Rec  ->
        let uu____45550 = str "rec"  in
        FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____45550
    | FStar_Parser_AST.NoLetQualifier  -> FStar_Pprint.empty

and (p_aqual : FStar_Parser_AST.arg_qualifier -> FStar_Pprint.document) =
  fun uu___334_45552  ->
    match uu___334_45552 with
    | FStar_Parser_AST.Implicit  -> str "#"
    | FStar_Parser_AST.Equality  -> str "$"
    | FStar_Parser_AST.Meta t ->
        let t1 =
          match t.FStar_Parser_AST.tm with
          | FStar_Parser_AST.Abs (uu____45557,e) -> e
          | uu____45563 ->
              FStar_Parser_AST.mk_term
                (FStar_Parser_AST.App
                   (t,
                     (FStar_Parser_AST.unit_const t.FStar_Parser_AST.range),
                     FStar_Parser_AST.Nothing)) t.FStar_Parser_AST.range
                FStar_Parser_AST.Expr
           in
        let uu____45564 = str "#["  in
        let uu____45566 =
          let uu____45567 = p_term false false t1  in
          let uu____45570 =
            let uu____45571 = str "]"  in
            FStar_Pprint.op_Hat_Hat uu____45571 break1  in
          FStar_Pprint.op_Hat_Hat uu____45567 uu____45570  in
        FStar_Pprint.op_Hat_Hat uu____45564 uu____45566

and (p_disjunctivePattern :
  FStar_Parser_AST.pattern -> FStar_Pprint.document) =
  fun p  ->
    match p.FStar_Parser_AST.pat with
    | FStar_Parser_AST.PatOr pats ->
        let uu____45577 =
          let uu____45578 =
            let uu____45579 =
              FStar_Pprint.op_Hat_Hat FStar_Pprint.bar FStar_Pprint.space  in
            FStar_Pprint.op_Hat_Hat break1 uu____45579  in
          FStar_Pprint.separate_map uu____45578 p_tuplePattern pats  in
        FStar_Pprint.group uu____45577
    | uu____45580 -> p_tuplePattern p

and (p_tuplePattern : FStar_Parser_AST.pattern -> FStar_Pprint.document) =
  fun p  ->
    match p.FStar_Parser_AST.pat with
    | FStar_Parser_AST.PatTuple (pats,false ) ->
        let uu____45589 =
          let uu____45590 = FStar_Pprint.op_Hat_Hat FStar_Pprint.comma break1
             in
          FStar_Pprint.separate_map uu____45590 p_constructorPattern pats  in
        FStar_Pprint.group uu____45589
    | uu____45591 -> p_constructorPattern p

and (p_constructorPattern :
  FStar_Parser_AST.pattern -> FStar_Pprint.document) =
  fun p  ->
    match p.FStar_Parser_AST.pat with
    | FStar_Parser_AST.PatApp
        ({ FStar_Parser_AST.pat = FStar_Parser_AST.PatName maybe_cons_lid;
           FStar_Parser_AST.prange = uu____45594;_},hd1::tl1::[])
        when
        FStar_Ident.lid_equals maybe_cons_lid FStar_Parser_Const.cons_lid ->
        let uu____45599 =
          FStar_Pprint.op_Hat_Hat FStar_Pprint.colon FStar_Pprint.colon  in
        let uu____45600 = p_constructorPattern hd1  in
        let uu____45601 = p_constructorPattern tl1  in
        infix0 uu____45599 uu____45600 uu____45601
    | FStar_Parser_AST.PatApp
        ({ FStar_Parser_AST.pat = FStar_Parser_AST.PatName uid;
           FStar_Parser_AST.prange = uu____45603;_},pats)
        ->
        let uu____45609 = p_quident uid  in
        let uu____45610 =
          FStar_Pprint.separate_map break1 p_atomicPattern pats  in
        prefix2 uu____45609 uu____45610
    | uu____45611 -> p_atomicPattern p

and (p_atomicPattern : FStar_Parser_AST.pattern -> FStar_Pprint.document) =
  fun p  ->
    match p.FStar_Parser_AST.pat with
    | FStar_Parser_AST.PatAscribed (pat,(t,FStar_Pervasives_Native.None )) ->
        (match ((pat.FStar_Parser_AST.pat), (t.FStar_Parser_AST.tm)) with
         | (FStar_Parser_AST.PatVar (lid,aqual),FStar_Parser_AST.Refine
            ({ FStar_Parser_AST.b = FStar_Parser_AST.Annotated (lid',t1);
               FStar_Parser_AST.brange = uu____45627;
               FStar_Parser_AST.blevel = uu____45628;
               FStar_Parser_AST.aqual = uu____45629;_},phi))
             when lid.FStar_Ident.idText = lid'.FStar_Ident.idText ->
             let uu____45638 =
               let uu____45639 = p_ident lid  in
               p_refinement aqual uu____45639 t1 phi  in
             soft_parens_with_nesting uu____45638
         | (FStar_Parser_AST.PatWild aqual,FStar_Parser_AST.Refine
            ({ FStar_Parser_AST.b = FStar_Parser_AST.NoName t1;
               FStar_Parser_AST.brange = uu____45642;
               FStar_Parser_AST.blevel = uu____45643;
               FStar_Parser_AST.aqual = uu____45644;_},phi))
             ->
             let uu____45650 =
               p_refinement aqual FStar_Pprint.underscore t1 phi  in
             soft_parens_with_nesting uu____45650
         | uu____45651 ->
             let uu____45656 =
               let uu____45657 = p_tuplePattern pat  in
               let uu____45658 =
                 let uu____45659 = p_tmEqNoRefinement t  in
                 FStar_Pprint.op_Hat_Slash_Hat FStar_Pprint.colon uu____45659
                  in
               FStar_Pprint.op_Hat_Hat uu____45657 uu____45658  in
             soft_parens_with_nesting uu____45656)
    | FStar_Parser_AST.PatList pats ->
        let uu____45663 =
          separate_break_map FStar_Pprint.semi p_tuplePattern pats  in
        FStar_Pprint.surround (Prims.parse_int "2") (Prims.parse_int "0")
          FStar_Pprint.lbracket uu____45663 FStar_Pprint.rbracket
    | FStar_Parser_AST.PatRecord pats ->
        let p_recordFieldPat uu____45682 =
          match uu____45682 with
          | (lid,pat) ->
              let uu____45689 = p_qlident lid  in
              let uu____45690 = p_tuplePattern pat  in
              infix2 FStar_Pprint.equals uu____45689 uu____45690
           in
        let uu____45691 =
          separate_break_map FStar_Pprint.semi p_recordFieldPat pats  in
        soft_braces_with_nesting uu____45691
    | FStar_Parser_AST.PatTuple (pats,true ) ->
        let uu____45703 =
          FStar_Pprint.op_Hat_Hat FStar_Pprint.lparen FStar_Pprint.bar  in
        let uu____45704 =
          separate_break_map FStar_Pprint.comma p_constructorPattern pats  in
        let uu____45705 =
          FStar_Pprint.op_Hat_Hat FStar_Pprint.bar FStar_Pprint.rparen  in
        FStar_Pprint.surround (Prims.parse_int "2") (Prims.parse_int "1")
          uu____45703 uu____45704 uu____45705
    | FStar_Parser_AST.PatTvar (tv,arg_qualifier_opt) -> p_tvar tv
    | FStar_Parser_AST.PatOp op ->
        let uu____45716 =
          let uu____45717 =
            let uu____45718 =
              let uu____45719 = FStar_Ident.text_of_id op  in str uu____45719
               in
            let uu____45721 =
              FStar_Pprint.op_Hat_Hat FStar_Pprint.space FStar_Pprint.rparen
               in
            FStar_Pprint.op_Hat_Hat uu____45718 uu____45721  in
          FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____45717  in
        FStar_Pprint.op_Hat_Hat FStar_Pprint.lparen uu____45716
    | FStar_Parser_AST.PatWild aqual ->
        let uu____45725 = FStar_Pprint.optional p_aqual aqual  in
        FStar_Pprint.op_Hat_Hat uu____45725 FStar_Pprint.underscore
    | FStar_Parser_AST.PatConst c -> p_constant c
    | FStar_Parser_AST.PatVar (lid,aqual) ->
        let uu____45733 = FStar_Pprint.optional p_aqual aqual  in
        let uu____45734 = p_lident lid  in
        FStar_Pprint.op_Hat_Hat uu____45733 uu____45734
    | FStar_Parser_AST.PatName uid -> p_quident uid
    | FStar_Parser_AST.PatOr uu____45736 -> failwith "Inner or pattern !"
    | FStar_Parser_AST.PatApp
        ({ FStar_Parser_AST.pat = FStar_Parser_AST.PatName uu____45740;
           FStar_Parser_AST.prange = uu____45741;_},uu____45742)
        ->
        let uu____45747 = p_tuplePattern p  in
        soft_parens_with_nesting uu____45747
    | FStar_Parser_AST.PatTuple (uu____45748,false ) ->
        let uu____45755 = p_tuplePattern p  in
        soft_parens_with_nesting uu____45755
    | uu____45756 ->
        let uu____45757 =
          let uu____45759 = FStar_Parser_AST.pat_to_string p  in
          FStar_Util.format1 "Invalid pattern %s" uu____45759  in
        failwith uu____45757

and (is_typ_tuple : FStar_Parser_AST.term -> Prims.bool) =
  fun e  ->
    match e.FStar_Parser_AST.tm with
    | FStar_Parser_AST.Op
        ({ FStar_Ident.idText = "*"; FStar_Ident.idRange = uu____45764;_},uu____45765)
        -> true
    | uu____45772 -> false

and (is_meta_qualifier :
  FStar_Parser_AST.arg_qualifier FStar_Pervasives_Native.option -> Prims.bool)
  =
  fun aq  ->
    match aq with
    | FStar_Pervasives_Native.Some (FStar_Parser_AST.Meta uu____45778) ->
        true
    | uu____45780 -> false

and (p_binder :
  Prims.bool -> FStar_Parser_AST.binder -> FStar_Pprint.document) =
  fun is_atomic  ->
    fun b  ->
      let uu____45787 = p_binder' is_atomic b  in
      match uu____45787 with
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
          let uu____45824 =
            let uu____45825 =
              FStar_Pprint.optional p_aqual b.FStar_Parser_AST.aqual  in
            let uu____45826 = p_lident lid  in
            FStar_Pprint.op_Hat_Hat uu____45825 uu____45826  in
          (uu____45824, FStar_Pervasives_Native.None, cat_with_colon)
      | FStar_Parser_AST.TVariable lid ->
          let uu____45832 = p_lident lid  in
          (uu____45832, FStar_Pervasives_Native.None, cat_with_colon)
      | FStar_Parser_AST.Annotated (lid,t) ->
          let uu____45839 =
            match t.FStar_Parser_AST.tm with
            | FStar_Parser_AST.Refine
                ({ FStar_Parser_AST.b = FStar_Parser_AST.Annotated (lid',t1);
                   FStar_Parser_AST.brange = uu____45850;
                   FStar_Parser_AST.blevel = uu____45851;
                   FStar_Parser_AST.aqual = uu____45852;_},phi)
                when lid.FStar_Ident.idText = lid'.FStar_Ident.idText ->
                let uu____45857 = p_lident lid  in
                p_refinement' b.FStar_Parser_AST.aqual uu____45857 t1 phi
            | uu____45858 ->
                let t' =
                  let uu____45860 = is_typ_tuple t  in
                  if uu____45860
                  then
                    let uu____45863 = p_tmFormula t  in
                    soft_parens_with_nesting uu____45863
                  else p_tmFormula t  in
                let uu____45866 =
                  let uu____45867 =
                    FStar_Pprint.optional p_aqual b.FStar_Parser_AST.aqual
                     in
                  let uu____45868 = p_lident lid  in
                  FStar_Pprint.op_Hat_Hat uu____45867 uu____45868  in
                (uu____45866, t')
             in
          (match uu____45839 with
           | (b',t') ->
               let catf =
                 let uu____45886 =
                   is_atomic || (is_meta_qualifier b.FStar_Parser_AST.aqual)
                    in
                 if uu____45886
                 then
                   fun x  ->
                     fun y  ->
                       let uu____45893 =
                         let uu____45894 =
                           let uu____45895 = cat_with_colon x y  in
                           FStar_Pprint.op_Hat_Hat uu____45895
                             FStar_Pprint.rparen
                            in
                         FStar_Pprint.op_Hat_Hat FStar_Pprint.lparen
                           uu____45894
                          in
                       FStar_Pprint.group uu____45893
                 else
                   (fun x  ->
                      fun y  ->
                        let uu____45900 = cat_with_colon x y  in
                        FStar_Pprint.group uu____45900)
                  in
               (b', (FStar_Pervasives_Native.Some t'), catf))
      | FStar_Parser_AST.TAnnotated uu____45905 ->
          failwith "Is this still used ?"
      | FStar_Parser_AST.NoName t ->
          (match t.FStar_Parser_AST.tm with
           | FStar_Parser_AST.Refine
               ({ FStar_Parser_AST.b = FStar_Parser_AST.NoName t1;
                  FStar_Parser_AST.brange = uu____45933;
                  FStar_Parser_AST.blevel = uu____45934;
                  FStar_Parser_AST.aqual = uu____45935;_},phi)
               ->
               let uu____45939 =
                 p_refinement' b.FStar_Parser_AST.aqual
                   FStar_Pprint.underscore t1 phi
                  in
               (match uu____45939 with
                | (b',t') ->
                    (b', (FStar_Pervasives_Native.Some t'), cat_with_colon))
           | uu____45960 ->
               if is_atomic
               then
                 let uu____45972 = p_atomicTerm t  in
                 (uu____45972, FStar_Pervasives_Native.None, cat_with_colon)
               else
                 (let uu____45979 = p_appTerm t  in
                  (uu____45979, FStar_Pervasives_Native.None, cat_with_colon)))

and (p_refinement :
  FStar_Parser_AST.arg_qualifier FStar_Pervasives_Native.option ->
    FStar_Pprint.document ->
      FStar_Parser_AST.term -> FStar_Parser_AST.term -> FStar_Pprint.document)
  =
  fun aqual_opt  ->
    fun binder  ->
      fun t  ->
        fun phi  ->
          let uu____45990 = p_refinement' aqual_opt binder t phi  in
          match uu____45990 with | (b,typ) -> cat_with_colon b typ

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
            | FStar_Parser_AST.Construct uu____46006 -> false
            | FStar_Parser_AST.App uu____46018 -> false
            | FStar_Parser_AST.Op uu____46026 -> false
            | uu____46034 -> true  in
          let uu____46036 = p_noSeqTerm false false phi  in
          match uu____46036 with
          | (comm,phi1) ->
              let phi2 =
                if comm = FStar_Pprint.empty
                then phi1
                else
                  (let uu____46053 =
                     FStar_Pprint.op_Hat_Hat FStar_Pprint.hardline phi1  in
                   FStar_Pprint.op_Hat_Hat comm uu____46053)
                 in
              let jump_break =
                if is_t_atomic
                then (Prims.parse_int "0")
                else (Prims.parse_int "1")  in
              let uu____46062 =
                let uu____46063 = FStar_Pprint.optional p_aqual aqual_opt  in
                FStar_Pprint.op_Hat_Hat uu____46063 binder  in
              let uu____46064 =
                let uu____46065 = p_appTerm t  in
                let uu____46066 =
                  let uu____46067 =
                    let uu____46068 =
                      let uu____46069 = soft_braces_with_nesting_tight phi2
                         in
                      let uu____46070 = soft_braces_with_nesting phi2  in
                      FStar_Pprint.ifflat uu____46069 uu____46070  in
                    FStar_Pprint.group uu____46068  in
                  FStar_Pprint.jump (Prims.parse_int "2") jump_break
                    uu____46067
                   in
                FStar_Pprint.op_Hat_Hat uu____46065 uu____46066  in
              (uu____46062, uu____46064)

and (p_binders_list :
  Prims.bool ->
    FStar_Parser_AST.binder Prims.list -> FStar_Pprint.document Prims.list)
  = fun is_atomic  -> fun bs  -> FStar_List.map (p_binder is_atomic) bs

and (p_binders :
  Prims.bool -> FStar_Parser_AST.binder Prims.list -> FStar_Pprint.document)
  =
  fun is_atomic  ->
    fun bs  ->
      let uu____46084 = p_binders_list is_atomic bs  in
      separate_or_flow break1 uu____46084

and (text_of_id_or_underscore : FStar_Ident.ident -> FStar_Pprint.document) =
  fun lid  ->
    let uu____46088 =
      (FStar_Util.starts_with lid.FStar_Ident.idText
         FStar_Ident.reserved_prefix)
        &&
        (let uu____46091 = FStar_Options.print_real_names ()  in
         Prims.op_Negation uu____46091)
       in
    if uu____46088
    then FStar_Pprint.underscore
    else (let uu____46096 = FStar_Ident.text_of_id lid  in str uu____46096)

and (text_of_lid_or_underscore : FStar_Ident.lident -> FStar_Pprint.document)
  =
  fun lid  ->
    let uu____46099 =
      (FStar_Util.starts_with (lid.FStar_Ident.ident).FStar_Ident.idText
         FStar_Ident.reserved_prefix)
        &&
        (let uu____46102 = FStar_Options.print_real_names ()  in
         Prims.op_Negation uu____46102)
       in
    if uu____46099
    then FStar_Pprint.underscore
    else (let uu____46107 = FStar_Ident.text_of_lid lid  in str uu____46107)

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
          let uu____46128 = FStar_Pprint.op_Hat_Hat doc1 sep  in
          FStar_Pprint.group uu____46128
        else
          (let uu____46131 =
             let uu____46132 =
               let uu____46133 =
                 let uu____46134 =
                   let uu____46135 = FStar_Pprint.op_Hat_Hat break1 comm  in
                   FStar_Pprint.op_Hat_Hat sep uu____46135  in
                 FStar_Pprint.op_Hat_Hat doc1 uu____46134  in
               FStar_Pprint.group uu____46133  in
             let uu____46136 =
               let uu____46137 =
                 let uu____46138 = FStar_Pprint.op_Hat_Hat doc1 sep  in
                 FStar_Pprint.op_Hat_Hat FStar_Pprint.hardline uu____46138
                  in
               FStar_Pprint.op_Hat_Hat comm uu____46137  in
             FStar_Pprint.ifflat uu____46132 uu____46136  in
           FStar_All.pipe_left FStar_Pprint.group uu____46131)

and (p_term :
  Prims.bool -> Prims.bool -> FStar_Parser_AST.term -> FStar_Pprint.document)
  =
  fun ps  ->
    fun pb  ->
      fun e  ->
        match e.FStar_Parser_AST.tm with
        | FStar_Parser_AST.Seq (e1,e2) ->
            let uu____46146 = p_noSeqTerm true false e1  in
            (match uu____46146 with
             | (comm,t1) ->
                 let uu____46155 =
                   inline_comment_or_above comm t1 FStar_Pprint.semi  in
                 let uu____46156 =
                   let uu____46157 = p_term ps pb e2  in
                   FStar_Pprint.op_Hat_Hat FStar_Pprint.hardline uu____46157
                    in
                 FStar_Pprint.op_Hat_Hat uu____46155 uu____46156)
        | FStar_Parser_AST.Bind (x,e1,e2) ->
            let uu____46161 =
              let uu____46162 =
                let uu____46163 =
                  let uu____46164 = p_lident x  in
                  let uu____46165 =
                    FStar_Pprint.op_Hat_Hat FStar_Pprint.space
                      FStar_Pprint.long_left_arrow
                     in
                  FStar_Pprint.op_Hat_Hat uu____46164 uu____46165  in
                let uu____46166 =
                  let uu____46167 = p_noSeqTermAndComment true false e1  in
                  let uu____46170 =
                    FStar_Pprint.op_Hat_Hat FStar_Pprint.space
                      FStar_Pprint.semi
                     in
                  FStar_Pprint.op_Hat_Hat uu____46167 uu____46170  in
                op_Hat_Slash_Plus_Hat uu____46163 uu____46166  in
              FStar_Pprint.group uu____46162  in
            let uu____46171 = p_term ps pb e2  in
            FStar_Pprint.op_Hat_Slash_Hat uu____46161 uu____46171
        | uu____46172 ->
            let uu____46173 = p_noSeqTermAndComment ps pb e  in
            FStar_Pprint.group uu____46173

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
            let uu____46185 = p_noSeqTerm true false e1  in
            (match uu____46185 with
             | (comm,t1) ->
                 let uu____46198 =
                   let uu____46199 =
                     let uu____46200 =
                       FStar_Pprint.op_Hat_Hat t1 FStar_Pprint.semi  in
                     FStar_Pprint.group uu____46200  in
                   let uu____46201 =
                     let uu____46202 = p_term ps pb e2  in
                     FStar_Pprint.op_Hat_Hat FStar_Pprint.hardline
                       uu____46202
                      in
                   FStar_Pprint.op_Hat_Hat uu____46199 uu____46201  in
                 (comm, uu____46198))
        | FStar_Parser_AST.Bind (x,e1,e2) ->
            let uu____46206 =
              let uu____46207 =
                let uu____46208 =
                  let uu____46209 =
                    let uu____46210 = p_lident x  in
                    let uu____46211 =
                      FStar_Pprint.op_Hat_Hat FStar_Pprint.space
                        FStar_Pprint.long_left_arrow
                       in
                    FStar_Pprint.op_Hat_Hat uu____46210 uu____46211  in
                  let uu____46212 =
                    let uu____46213 = p_noSeqTermAndComment true false e1  in
                    let uu____46216 =
                      FStar_Pprint.op_Hat_Hat FStar_Pprint.space
                        FStar_Pprint.semi
                       in
                    FStar_Pprint.op_Hat_Hat uu____46213 uu____46216  in
                  op_Hat_Slash_Plus_Hat uu____46209 uu____46212  in
                FStar_Pprint.group uu____46208  in
              let uu____46217 = p_term ps pb e2  in
              FStar_Pprint.op_Hat_Slash_Hat uu____46207 uu____46217  in
            (FStar_Pprint.empty, uu____46206)
        | uu____46218 -> p_noSeqTerm ps pb e

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
            let uu____46238 =
              let uu____46239 = p_tmIff e1  in
              let uu____46240 =
                let uu____46241 =
                  let uu____46242 = p_typ ps pb t  in
                  FStar_Pprint.op_Hat_Slash_Hat FStar_Pprint.colon
                    uu____46242
                   in
                FStar_Pprint.op_Hat_Hat FStar_Pprint.langle uu____46241  in
              FStar_Pprint.op_Hat_Slash_Hat uu____46239 uu____46240  in
            FStar_Pprint.group uu____46238
        | FStar_Parser_AST.Ascribed (e1,t,FStar_Pervasives_Native.Some tac)
            ->
            let uu____46248 =
              let uu____46249 = p_tmIff e1  in
              let uu____46250 =
                let uu____46251 =
                  let uu____46252 =
                    let uu____46253 = p_typ false false t  in
                    let uu____46256 =
                      let uu____46257 = str "by"  in
                      let uu____46259 = p_typ ps pb tac  in
                      FStar_Pprint.op_Hat_Slash_Hat uu____46257 uu____46259
                       in
                    FStar_Pprint.op_Hat_Slash_Hat uu____46253 uu____46256  in
                  FStar_Pprint.op_Hat_Slash_Hat FStar_Pprint.colon
                    uu____46252
                   in
                FStar_Pprint.op_Hat_Hat FStar_Pprint.langle uu____46251  in
              FStar_Pprint.op_Hat_Slash_Hat uu____46249 uu____46250  in
            FStar_Pprint.group uu____46248
        | FStar_Parser_AST.Op
            ({ FStar_Ident.idText = ".()<-";
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
                        soft_parens_with_nesting uu____46274  in
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
        | FStar_Parser_AST.Op
            ({ FStar_Ident.idText = ".[]<-";
               FStar_Ident.idRange = uu____46280;_},e1::e2::e3::[])
            ->
            let uu____46287 =
              let uu____46288 =
                let uu____46289 =
                  let uu____46290 = p_atomicTermNotQUident e1  in
                  let uu____46291 =
                    let uu____46292 =
                      let uu____46293 =
                        let uu____46294 = p_term false false e2  in
                        soft_brackets_with_nesting uu____46294  in
                      let uu____46297 =
                        FStar_Pprint.op_Hat_Hat FStar_Pprint.space
                          FStar_Pprint.larrow
                         in
                      FStar_Pprint.op_Hat_Hat uu____46293 uu____46297  in
                    FStar_Pprint.op_Hat_Hat FStar_Pprint.dot uu____46292  in
                  FStar_Pprint.op_Hat_Hat uu____46290 uu____46291  in
                FStar_Pprint.group uu____46289  in
              let uu____46298 =
                let uu____46299 = p_noSeqTermAndComment ps pb e3  in
                jump2 uu____46299  in
              FStar_Pprint.op_Hat_Hat uu____46288 uu____46298  in
            FStar_Pprint.group uu____46287
        | FStar_Parser_AST.Requires (e1,wtf) ->
            let uu____46309 =
              let uu____46310 = str "requires"  in
              let uu____46312 = p_typ ps pb e1  in
              FStar_Pprint.op_Hat_Slash_Hat uu____46310 uu____46312  in
            FStar_Pprint.group uu____46309
        | FStar_Parser_AST.Ensures (e1,wtf) ->
            let uu____46322 =
              let uu____46323 = str "ensures"  in
              let uu____46325 = p_typ ps pb e1  in
              FStar_Pprint.op_Hat_Slash_Hat uu____46323 uu____46325  in
            FStar_Pprint.group uu____46322
        | FStar_Parser_AST.Attributes es ->
            let uu____46329 =
              let uu____46330 = str "attributes"  in
              let uu____46332 =
                FStar_Pprint.separate_map break1 p_atomicTerm es  in
              FStar_Pprint.op_Hat_Slash_Hat uu____46330 uu____46332  in
            FStar_Pprint.group uu____46329
        | FStar_Parser_AST.If (e1,e2,e3) ->
            if is_unit e3
            then
              let uu____46337 =
                let uu____46338 =
                  let uu____46339 = str "if"  in
                  let uu____46341 = p_noSeqTermAndComment false false e1  in
                  op_Hat_Slash_Plus_Hat uu____46339 uu____46341  in
                let uu____46344 =
                  let uu____46345 = str "then"  in
                  let uu____46347 = p_noSeqTermAndComment ps pb e2  in
                  op_Hat_Slash_Plus_Hat uu____46345 uu____46347  in
                FStar_Pprint.op_Hat_Slash_Hat uu____46338 uu____46344  in
              FStar_Pprint.group uu____46337
            else
              (let e2_doc =
                 match e2.FStar_Parser_AST.tm with
                 | FStar_Parser_AST.If (uu____46351,uu____46352,e31) when
                     is_unit e31 ->
                     let uu____46354 = p_noSeqTermAndComment false false e2
                        in
                     soft_parens_with_nesting uu____46354
                 | uu____46357 -> p_noSeqTermAndComment false false e2  in
               let uu____46360 =
                 let uu____46361 =
                   let uu____46362 = str "if"  in
                   let uu____46364 = p_noSeqTermAndComment false false e1  in
                   op_Hat_Slash_Plus_Hat uu____46362 uu____46364  in
                 let uu____46367 =
                   let uu____46368 =
                     let uu____46369 = str "then"  in
                     op_Hat_Slash_Plus_Hat uu____46369 e2_doc  in
                   let uu____46371 =
                     let uu____46372 = str "else"  in
                     let uu____46374 = p_noSeqTermAndComment ps pb e3  in
                     op_Hat_Slash_Plus_Hat uu____46372 uu____46374  in
                   FStar_Pprint.op_Hat_Slash_Hat uu____46368 uu____46371  in
                 FStar_Pprint.op_Hat_Slash_Hat uu____46361 uu____46367  in
               FStar_Pprint.group uu____46360)
        | FStar_Parser_AST.TryWith (e1,branches) ->
            let uu____46397 =
              let uu____46398 =
                let uu____46399 =
                  let uu____46400 = str "try"  in
                  let uu____46402 = p_noSeqTermAndComment false false e1  in
                  prefix2 uu____46400 uu____46402  in
                let uu____46405 =
                  let uu____46406 = str "with"  in
                  let uu____46408 =
                    separate_map_last FStar_Pprint.hardline p_patternBranch
                      branches
                     in
                  FStar_Pprint.op_Hat_Slash_Hat uu____46406 uu____46408  in
                FStar_Pprint.op_Hat_Slash_Hat uu____46399 uu____46405  in
              FStar_Pprint.group uu____46398  in
            let uu____46417 = paren_if (ps || pb)  in uu____46417 uu____46397
        | FStar_Parser_AST.Match (e1,branches) ->
            let uu____46444 =
              let uu____46445 =
                let uu____46446 =
                  let uu____46447 = str "match"  in
                  let uu____46449 = p_noSeqTermAndComment false false e1  in
                  let uu____46452 = str "with"  in
                  FStar_Pprint.surround (Prims.parse_int "2")
                    (Prims.parse_int "1") uu____46447 uu____46449 uu____46452
                   in
                let uu____46456 =
                  separate_map_last FStar_Pprint.hardline p_patternBranch
                    branches
                   in
                FStar_Pprint.op_Hat_Slash_Hat uu____46446 uu____46456  in
              FStar_Pprint.group uu____46445  in
            let uu____46465 = paren_if (ps || pb)  in uu____46465 uu____46444
        | FStar_Parser_AST.LetOpen (uid,e1) ->
            let uu____46472 =
              let uu____46473 =
                let uu____46474 =
                  let uu____46475 = str "let open"  in
                  let uu____46477 = p_quident uid  in
                  let uu____46478 = str "in"  in
                  FStar_Pprint.surround (Prims.parse_int "2")
                    (Prims.parse_int "1") uu____46475 uu____46477 uu____46478
                   in
                let uu____46482 = p_term false pb e1  in
                FStar_Pprint.op_Hat_Slash_Hat uu____46474 uu____46482  in
              FStar_Pprint.group uu____46473  in
            let uu____46484 = paren_if ps  in uu____46484 uu____46472
        | FStar_Parser_AST.Let (q,lbs,e1) ->
            let p_lb q1 uu____46549 is_last =
              match uu____46549 with
              | (a,(pat,e2)) ->
                  let attrs = p_attrs_opt a  in
                  let doc_let_or_and =
                    match q1 with
                    | FStar_Pervasives_Native.Some (FStar_Parser_AST.Rec ) ->
                        let uu____46583 =
                          let uu____46584 = str "let"  in
                          let uu____46586 = str "rec"  in
                          FStar_Pprint.op_Hat_Slash_Hat uu____46584
                            uu____46586
                           in
                        FStar_Pprint.group uu____46583
                    | FStar_Pervasives_Native.Some
                        (FStar_Parser_AST.NoLetQualifier ) -> str "let"
                    | uu____46589 -> str "and"  in
                  let doc_pat = p_letlhs doc_let_or_and (pat, e2) true  in
                  let uu____46595 = p_term_sep false false e2  in
                  (match uu____46595 with
                   | (comm,doc_expr) ->
                       let doc_expr1 =
                         inline_comment_or_above comm doc_expr
                           FStar_Pprint.empty
                          in
                       let uu____46605 =
                         if is_last
                         then
                           let uu____46607 =
                             FStar_Pprint.flow break1
                               [doc_pat; FStar_Pprint.equals]
                              in
                           let uu____46608 = str "in"  in
                           FStar_Pprint.surround (Prims.parse_int "2")
                             (Prims.parse_int "1") uu____46607 doc_expr1
                             uu____46608
                         else
                           (let uu____46614 =
                              FStar_Pprint.flow break1
                                [doc_pat; FStar_Pprint.equals; doc_expr1]
                               in
                            FStar_Pprint.hang (Prims.parse_int "2")
                              uu____46614)
                          in
                       FStar_Pprint.op_Hat_Hat attrs uu____46605)
               in
            let l = FStar_List.length lbs  in
            let lbs_docs =
              FStar_List.mapi
                (fun i  ->
                   fun lb  ->
                     if i = (Prims.parse_int "0")
                     then
                       let uu____46665 =
                         p_lb (FStar_Pervasives_Native.Some q) lb
                           (i = (l - (Prims.parse_int "1")))
                          in
                       FStar_Pprint.group uu____46665
                     else
                       (let uu____46670 =
                          p_lb FStar_Pervasives_Native.None lb
                            (i = (l - (Prims.parse_int "1")))
                           in
                        FStar_Pprint.group uu____46670)) lbs
               in
            let lbs_doc =
              let uu____46674 = FStar_Pprint.separate break1 lbs_docs  in
              FStar_Pprint.group uu____46674  in
            let uu____46675 =
              let uu____46676 =
                let uu____46677 =
                  let uu____46678 = p_term false pb e1  in
                  FStar_Pprint.op_Hat_Hat FStar_Pprint.hardline uu____46678
                   in
                FStar_Pprint.op_Hat_Hat lbs_doc uu____46677  in
              FStar_Pprint.group uu____46676  in
            let uu____46680 = paren_if ps  in uu____46680 uu____46675
        | FStar_Parser_AST.Abs
            ({ FStar_Parser_AST.pat = FStar_Parser_AST.PatVar (x,typ_opt);
               FStar_Parser_AST.prange = uu____46687;_}::[],{
                                                              FStar_Parser_AST.tm
                                                                =
                                                                FStar_Parser_AST.Match
                                                                (maybe_x,branches);
                                                              FStar_Parser_AST.range
                                                                = uu____46690;
                                                              FStar_Parser_AST.level
                                                                = uu____46691;_})
            when matches_var maybe_x x ->
            let uu____46718 =
              let uu____46719 =
                let uu____46720 = str "function"  in
                let uu____46722 =
                  separate_map_last FStar_Pprint.hardline p_patternBranch
                    branches
                   in
                FStar_Pprint.op_Hat_Slash_Hat uu____46720 uu____46722  in
              FStar_Pprint.group uu____46719  in
            let uu____46731 = paren_if (ps || pb)  in uu____46731 uu____46718
        | FStar_Parser_AST.Quote (e1,FStar_Parser_AST.Dynamic ) ->
            let uu____46737 =
              let uu____46738 = str "quote"  in
              let uu____46740 = p_noSeqTermAndComment ps pb e1  in
              FStar_Pprint.op_Hat_Slash_Hat uu____46738 uu____46740  in
            FStar_Pprint.group uu____46737
        | FStar_Parser_AST.Quote (e1,FStar_Parser_AST.Static ) ->
            let uu____46742 =
              let uu____46743 = str "`"  in
              let uu____46745 = p_noSeqTermAndComment ps pb e1  in
              FStar_Pprint.op_Hat_Hat uu____46743 uu____46745  in
            FStar_Pprint.group uu____46742
        | FStar_Parser_AST.VQuote e1 ->
            let uu____46747 =
              let uu____46748 = str "`%"  in
              let uu____46750 = p_noSeqTermAndComment ps pb e1  in
              FStar_Pprint.op_Hat_Hat uu____46748 uu____46750  in
            FStar_Pprint.group uu____46747
        | FStar_Parser_AST.Antiquote
            {
              FStar_Parser_AST.tm = FStar_Parser_AST.Quote
                (e1,FStar_Parser_AST.Dynamic );
              FStar_Parser_AST.range = uu____46752;
              FStar_Parser_AST.level = uu____46753;_}
            ->
            let uu____46754 =
              let uu____46755 = str "`@"  in
              let uu____46757 = p_noSeqTermAndComment ps pb e1  in
              FStar_Pprint.op_Hat_Hat uu____46755 uu____46757  in
            FStar_Pprint.group uu____46754
        | FStar_Parser_AST.Antiquote e1 ->
            let uu____46759 =
              let uu____46760 = str "`#"  in
              let uu____46762 = p_noSeqTermAndComment ps pb e1  in
              FStar_Pprint.op_Hat_Hat uu____46760 uu____46762  in
            FStar_Pprint.group uu____46759
        | FStar_Parser_AST.CalcProof (rel,init1,steps) ->
            let head1 =
              let uu____46771 = str "calc"  in
              let uu____46773 =
                let uu____46774 =
                  let uu____46775 = p_noSeqTermAndComment false false rel  in
                  let uu____46778 =
                    FStar_Pprint.op_Hat_Hat FStar_Pprint.space
                      FStar_Pprint.lbrace
                     in
                  FStar_Pprint.op_Hat_Hat uu____46775 uu____46778  in
                FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____46774  in
              FStar_Pprint.op_Hat_Hat uu____46771 uu____46773  in
            let bot = FStar_Pprint.rbrace  in
            let uu____46780 =
              FStar_Pprint.op_Hat_Hat FStar_Pprint.hardline bot  in
            let uu____46781 =
              let uu____46782 =
                let uu____46783 =
                  let uu____46784 = p_noSeqTermAndComment false false init1
                     in
                  let uu____46787 =
                    let uu____46788 = str ";"  in
                    let uu____46790 =
                      let uu____46791 =
                        separate_map_last FStar_Pprint.hardline p_calcStep
                          steps
                         in
                      FStar_Pprint.op_Hat_Hat FStar_Pprint.hardline
                        uu____46791
                       in
                    FStar_Pprint.op_Hat_Hat uu____46788 uu____46790  in
                  FStar_Pprint.op_Hat_Hat uu____46784 uu____46787  in
                FStar_Pprint.op_Hat_Hat FStar_Pprint.hardline uu____46783  in
              FStar_All.pipe_left (FStar_Pprint.nest (Prims.parse_int "2"))
                uu____46782
               in
            FStar_Pprint.enclose head1 uu____46780 uu____46781
        | uu____46793 -> p_typ ps pb e

and (p_calcStep :
  Prims.bool -> FStar_Parser_AST.calc_step -> FStar_Pprint.document) =
  fun uu____46794  ->
    fun uu____46795  ->
      match uu____46795 with
      | FStar_Parser_AST.CalcStep (rel,just,next) ->
          let uu____46800 =
            let uu____46801 = p_noSeqTermAndComment false false rel  in
            let uu____46804 =
              let uu____46805 =
                let uu____46806 =
                  let uu____46807 =
                    let uu____46808 = p_noSeqTermAndComment false false just
                       in
                    let uu____46811 =
                      let uu____46812 =
                        let uu____46813 =
                          let uu____46814 =
                            let uu____46815 =
                              p_noSeqTermAndComment false false next  in
                            let uu____46818 = str ";"  in
                            FStar_Pprint.op_Hat_Hat uu____46815 uu____46818
                             in
                          FStar_Pprint.op_Hat_Hat FStar_Pprint.hardline
                            uu____46814
                           in
                        FStar_Pprint.op_Hat_Hat FStar_Pprint.rbrace
                          uu____46813
                         in
                      FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____46812
                       in
                    FStar_Pprint.op_Hat_Hat uu____46808 uu____46811  in
                  FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____46807  in
                FStar_Pprint.op_Hat_Hat FStar_Pprint.lbrace uu____46806  in
              FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____46805  in
            FStar_Pprint.op_Hat_Hat uu____46801 uu____46804  in
          FStar_Pprint.group uu____46800

and (p_attrs_opt :
  FStar_Parser_AST.term Prims.list FStar_Pervasives_Native.option ->
    FStar_Pprint.document)
  =
  fun uu___335_46820  ->
    match uu___335_46820 with
    | FStar_Pervasives_Native.None  -> FStar_Pprint.empty
    | FStar_Pervasives_Native.Some terms ->
        let uu____46832 =
          let uu____46833 = str "[@"  in
          let uu____46835 =
            let uu____46836 =
              FStar_Pprint.separate_map break1 p_atomicTerm terms  in
            let uu____46837 = str "]"  in
            FStar_Pprint.op_Hat_Slash_Hat uu____46836 uu____46837  in
          FStar_Pprint.op_Hat_Slash_Hat uu____46833 uu____46835  in
        FStar_Pprint.group uu____46832

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
                 let uu____46874 =
                   let uu____46875 =
                     let uu____46876 = p_quantifier e  in
                     FStar_Pprint.op_Hat_Hat uu____46876 FStar_Pprint.space
                      in
                   FStar_Pprint.soft_surround (Prims.parse_int "2")
                     (Prims.parse_int "0") uu____46875 binders_doc
                     FStar_Pprint.dot
                    in
                 prefix2 uu____46874 term_doc
             | pats ->
                 let uu____46884 =
                   let uu____46885 =
                     let uu____46886 =
                       let uu____46887 =
                         let uu____46888 = p_quantifier e  in
                         FStar_Pprint.op_Hat_Hat uu____46888
                           FStar_Pprint.space
                          in
                       FStar_Pprint.soft_surround (Prims.parse_int "2")
                         (Prims.parse_int "0") uu____46887 binders_doc
                         FStar_Pprint.dot
                        in
                     let uu____46891 = p_trigger trigger  in
                     prefix2 uu____46886 uu____46891  in
                   FStar_Pprint.group uu____46885  in
                 prefix2 uu____46884 term_doc)
        | FStar_Parser_AST.QExists (bs,trigger,e1) ->
            let binders_doc = p_binders true bs  in
            let term_doc = p_noSeqTermAndComment ps pb e1  in
            (match trigger with
             | [] ->
                 let uu____46912 =
                   let uu____46913 =
                     let uu____46914 = p_quantifier e  in
                     FStar_Pprint.op_Hat_Hat uu____46914 FStar_Pprint.space
                      in
                   FStar_Pprint.soft_surround (Prims.parse_int "2")
                     (Prims.parse_int "0") uu____46913 binders_doc
                     FStar_Pprint.dot
                    in
                 prefix2 uu____46912 term_doc
             | pats ->
                 let uu____46922 =
                   let uu____46923 =
                     let uu____46924 =
                       let uu____46925 =
                         let uu____46926 = p_quantifier e  in
                         FStar_Pprint.op_Hat_Hat uu____46926
                           FStar_Pprint.space
                          in
                       FStar_Pprint.soft_surround (Prims.parse_int "2")
                         (Prims.parse_int "0") uu____46925 binders_doc
                         FStar_Pprint.dot
                        in
                     let uu____46929 = p_trigger trigger  in
                     prefix2 uu____46924 uu____46929  in
                   FStar_Pprint.group uu____46923  in
                 prefix2 uu____46922 term_doc)
        | uu____46930 -> p_simpleTerm ps pb e

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
      let uu____46951 = all_binders_annot t  in
      if uu____46951
      then
        let uu____46954 =
          p_typ_top
            (Binders ((Prims.parse_int "4"), (Prims.parse_int "0"), true))
            false false t
           in
        FStar_Pprint.op_Hat_Hat s uu____46954
      else
        (let uu____46965 =
           let uu____46966 =
             let uu____46967 =
               p_typ_top
                 (Arrows ((Prims.parse_int "2"), (Prims.parse_int "2")))
                 false false t
                in
             FStar_Pprint.op_Hat_Hat s uu____46967  in
           FStar_Pprint.op_Hat_Hat FStar_Pprint.colon uu____46966  in
         FStar_Pprint.group uu____46965)

and (collapse_pats :
  (FStar_Pprint.document * FStar_Pprint.document) Prims.list ->
    FStar_Pprint.document Prims.list)
  =
  fun pats  ->
    let fold_fun bs x =
      let uu____47026 = x  in
      match uu____47026 with
      | (b1,t1) ->
          (match bs with
           | [] -> [([b1], t1)]
           | hd1::tl1 ->
               let uu____47091 = hd1  in
               (match uu____47091 with
                | (b2s,t2) ->
                    if t1 = t2
                    then ((FStar_List.append b2s [b1]), t1) :: tl1
                    else ([b1], t1) :: hd1 :: tl1))
       in
    let p_collapsed_binder cb =
      let uu____47163 = cb  in
      match uu____47163 with
      | (bs,typ) ->
          (match bs with
           | [] -> failwith "Impossible"
           | b::[] -> cat_with_colon b typ
           | hd1::tl1 ->
               let uu____47182 =
                 FStar_List.fold_left
                   (fun x  ->
                      fun y  ->
                        let uu____47188 =
                          FStar_Pprint.op_Hat_Hat FStar_Pprint.space y  in
                        FStar_Pprint.op_Hat_Hat x uu____47188) hd1 tl1
                  in
               cat_with_colon uu____47182 typ)
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
                 FStar_Parser_AST.brange = uu____47267;
                 FStar_Parser_AST.blevel = uu____47268;
                 FStar_Parser_AST.aqual = uu____47269;_},phi))
               when lid.FStar_Ident.idText = lid'.FStar_Ident.idText ->
               let uu____47278 =
                 let uu____47283 = p_ident lid  in
                 p_refinement' aqual uu____47283 t1 phi  in
               FStar_Pervasives_Native.Some uu____47278
           | (FStar_Parser_AST.PatVar (lid,aqual),uu____47290) ->
               let uu____47295 =
                 let uu____47300 =
                   let uu____47301 = FStar_Pprint.optional p_aqual aqual  in
                   let uu____47302 = p_ident lid  in
                   FStar_Pprint.op_Hat_Hat uu____47301 uu____47302  in
                 let uu____47303 = p_tmEqNoRefinement t  in
                 (uu____47300, uu____47303)  in
               FStar_Pervasives_Native.Some uu____47295
           | uu____47308 -> FStar_Pervasives_Native.None)
      | uu____47317 -> FStar_Pervasives_Native.None  in
    let all_unbound p =
      match p.FStar_Parser_AST.pat with
      | FStar_Parser_AST.PatAscribed uu____47330 -> false
      | uu____47342 -> true  in
    let uu____47344 = map_if_all all_binders pats  in
    match uu____47344 with
    | FStar_Pervasives_Native.Some bs ->
        let uu____47376 = collapse_pats bs  in
        (uu____47376,
          (Binders ((Prims.parse_int "4"), (Prims.parse_int "0"), true)))
    | FStar_Pervasives_Native.None  ->
        let uu____47393 = FStar_List.map p_atomicPattern pats  in
        (uu____47393,
          (Binders ((Prims.parse_int "4"), (Prims.parse_int "0"), false)))

and (p_quantifier : FStar_Parser_AST.term -> FStar_Pprint.document) =
  fun e  ->
    match e.FStar_Parser_AST.tm with
    | FStar_Parser_AST.QForall uu____47405 -> str "forall"
    | FStar_Parser_AST.QExists uu____47419 -> str "exists"
    | uu____47433 ->
        failwith "Imposible : p_quantifier called on a non-quantifier term"

and (p_trigger :
  FStar_Parser_AST.term Prims.list Prims.list -> FStar_Pprint.document) =
  fun uu___336_47435  ->
    match uu___336_47435 with
    | [] -> FStar_Pprint.empty
    | pats ->
        let uu____47447 =
          let uu____47448 =
            let uu____47449 =
              let uu____47450 = str "pattern"  in
              let uu____47452 =
                let uu____47453 =
                  let uu____47454 = p_disjunctivePats pats  in
                  FStar_Pprint.jump (Prims.parse_int "2")
                    (Prims.parse_int "0") uu____47454
                   in
                FStar_Pprint.op_Hat_Hat uu____47453 FStar_Pprint.rbrace  in
              FStar_Pprint.op_Hat_Slash_Hat uu____47450 uu____47452  in
            FStar_Pprint.op_Hat_Hat FStar_Pprint.colon uu____47449  in
          FStar_Pprint.op_Hat_Hat FStar_Pprint.lbrace uu____47448  in
        FStar_Pprint.group uu____47447

and (p_disjunctivePats :
  FStar_Parser_AST.term Prims.list Prims.list -> FStar_Pprint.document) =
  fun pats  ->
    let uu____47462 = str "\\/"  in
    FStar_Pprint.separate_map uu____47462 p_conjunctivePats pats

and (p_conjunctivePats :
  FStar_Parser_AST.term Prims.list -> FStar_Pprint.document) =
  fun pats  ->
    let uu____47469 =
      let uu____47470 = FStar_Pprint.op_Hat_Hat FStar_Pprint.semi break1  in
      FStar_Pprint.separate_map uu____47470 p_appTerm pats  in
    FStar_Pprint.group uu____47469

and (p_simpleTerm :
  Prims.bool -> Prims.bool -> FStar_Parser_AST.term -> FStar_Pprint.document)
  =
  fun ps  ->
    fun pb  ->
      fun e  ->
        match e.FStar_Parser_AST.tm with
        | FStar_Parser_AST.Abs (pats,e1) ->
            let uu____47482 = p_term_sep false pb e1  in
            (match uu____47482 with
             | (comm,doc1) ->
                 let prefix1 =
                   let uu____47491 = str "fun"  in
                   let uu____47493 =
                     let uu____47494 =
                       FStar_Pprint.separate_map break1 p_atomicPattern pats
                        in
                     FStar_Pprint.op_Hat_Slash_Hat uu____47494
                       FStar_Pprint.rarrow
                      in
                   op_Hat_Slash_Plus_Hat uu____47491 uu____47493  in
                 let uu____47495 =
                   if comm <> FStar_Pprint.empty
                   then
                     let uu____47497 =
                       let uu____47498 =
                         let uu____47499 =
                           FStar_Pprint.op_Hat_Hat FStar_Pprint.hardline doc1
                            in
                         FStar_Pprint.op_Hat_Hat comm uu____47499  in
                       FStar_Pprint.op_Hat_Hat FStar_Pprint.hardline
                         uu____47498
                        in
                     FStar_Pprint.op_Hat_Hat prefix1 uu____47497
                   else
                     (let uu____47502 = op_Hat_Slash_Plus_Hat prefix1 doc1
                         in
                      FStar_Pprint.group uu____47502)
                    in
                 let uu____47503 = paren_if ps  in uu____47503 uu____47495)
        | uu____47508 -> p_tmIff e

and (p_maybeFocusArrow : Prims.bool -> FStar_Pprint.document) =
  fun b  -> if b then str "~>" else FStar_Pprint.rarrow

and (p_patternBranch :
  Prims.bool ->
    (FStar_Parser_AST.pattern * FStar_Parser_AST.term
      FStar_Pervasives_Native.option * FStar_Parser_AST.term) ->
      FStar_Pprint.document)
  =
  fun pb  ->
    fun uu____47516  ->
      match uu____47516 with
      | (pat,when_opt,e) ->
          let one_pattern_branch p =
            let branch =
              match when_opt with
              | FStar_Pervasives_Native.None  ->
                  let uu____47540 =
                    let uu____47541 =
                      let uu____47542 =
                        let uu____47543 = p_tuplePattern p  in
                        let uu____47544 =
                          FStar_Pprint.op_Hat_Hat FStar_Pprint.space
                            FStar_Pprint.rarrow
                           in
                        FStar_Pprint.op_Hat_Hat uu____47543 uu____47544  in
                      FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____47542
                       in
                    FStar_Pprint.op_Hat_Hat FStar_Pprint.bar uu____47541  in
                  FStar_Pprint.group uu____47540
              | FStar_Pervasives_Native.Some f ->
                  let uu____47546 =
                    let uu____47547 =
                      let uu____47548 =
                        let uu____47549 =
                          let uu____47550 =
                            let uu____47551 = p_tuplePattern p  in
                            let uu____47552 = str "when"  in
                            FStar_Pprint.op_Hat_Slash_Hat uu____47551
                              uu____47552
                             in
                          FStar_Pprint.group uu____47550  in
                        let uu____47554 =
                          let uu____47555 =
                            let uu____47558 = p_tmFormula f  in
                            [uu____47558; FStar_Pprint.rarrow]  in
                          FStar_Pprint.flow break1 uu____47555  in
                        FStar_Pprint.op_Hat_Slash_Hat uu____47549 uu____47554
                         in
                      FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____47548
                       in
                    FStar_Pprint.op_Hat_Hat FStar_Pprint.bar uu____47547  in
                  FStar_Pprint.hang (Prims.parse_int "2") uu____47546
               in
            let uu____47560 = p_term_sep false pb e  in
            match uu____47560 with
            | (comm,doc1) ->
                if pb
                then
                  (if comm = FStar_Pprint.empty
                   then
                     let uu____47570 = op_Hat_Slash_Plus_Hat branch doc1  in
                     FStar_Pprint.group uu____47570
                   else
                     (let uu____47573 =
                        let uu____47574 =
                          let uu____47575 =
                            let uu____47576 =
                              let uu____47577 =
                                FStar_Pprint.op_Hat_Hat break1 comm  in
                              FStar_Pprint.op_Hat_Hat doc1 uu____47577  in
                            op_Hat_Slash_Plus_Hat branch uu____47576  in
                          FStar_Pprint.group uu____47575  in
                        let uu____47578 =
                          let uu____47579 =
                            let uu____47580 =
                              inline_comment_or_above comm doc1
                                FStar_Pprint.empty
                               in
                            jump2 uu____47580  in
                          FStar_Pprint.op_Hat_Hat branch uu____47579  in
                        FStar_Pprint.ifflat uu____47574 uu____47578  in
                      FStar_Pprint.group uu____47573))
                else
                  if comm <> FStar_Pprint.empty
                  then
                    (let uu____47584 =
                       let uu____47585 =
                         FStar_Pprint.op_Hat_Hat FStar_Pprint.hardline doc1
                          in
                       FStar_Pprint.op_Hat_Hat comm uu____47585  in
                     op_Hat_Slash_Plus_Hat branch uu____47584)
                  else op_Hat_Slash_Plus_Hat branch doc1
             in
          (match pat.FStar_Parser_AST.pat with
           | FStar_Parser_AST.PatOr pats ->
               (match FStar_List.rev pats with
                | hd1::tl1 ->
                    let last_pat_branch = one_pattern_branch hd1  in
                    let uu____47596 =
                      let uu____47597 =
                        let uu____47598 =
                          let uu____47599 =
                            let uu____47600 =
                              let uu____47601 =
                                FStar_Pprint.op_Hat_Hat FStar_Pprint.bar
                                  FStar_Pprint.space
                                 in
                              FStar_Pprint.op_Hat_Hat break1 uu____47601  in
                            FStar_Pprint.separate_map uu____47600
                              p_tuplePattern (FStar_List.rev tl1)
                             in
                          FStar_Pprint.op_Hat_Slash_Hat uu____47599
                            last_pat_branch
                           in
                        FStar_Pprint.op_Hat_Hat FStar_Pprint.space
                          uu____47598
                         in
                      FStar_Pprint.op_Hat_Hat FStar_Pprint.bar uu____47597
                       in
                    FStar_Pprint.group uu____47596
                | [] ->
                    failwith "Impossible: disjunctive pattern can't be empty")
           | uu____47603 -> one_pattern_branch pat)

and (p_tmIff : FStar_Parser_AST.term -> FStar_Pprint.document) =
  fun e  ->
    match e.FStar_Parser_AST.tm with
    | FStar_Parser_AST.Op
        ({ FStar_Ident.idText = "<==>"; FStar_Ident.idRange = uu____47605;_},e1::e2::[])
        ->
        let uu____47611 = str "<==>"  in
        let uu____47613 = p_tmImplies e1  in
        let uu____47614 = p_tmIff e2  in
        infix0 uu____47611 uu____47613 uu____47614
    | uu____47615 -> p_tmImplies e

and (p_tmImplies : FStar_Parser_AST.term -> FStar_Pprint.document) =
  fun e  ->
    match e.FStar_Parser_AST.tm with
    | FStar_Parser_AST.Op
        ({ FStar_Ident.idText = "==>"; FStar_Ident.idRange = uu____47617;_},e1::e2::[])
        ->
        let uu____47623 = str "==>"  in
        let uu____47625 =
          p_tmArrow (Arrows ((Prims.parse_int "2"), (Prims.parse_int "2")))
            false p_tmFormula e1
           in
        let uu____47631 = p_tmImplies e2  in
        infix0 uu____47623 uu____47625 uu____47631
    | uu____47632 ->
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
          let uu____47646 =
            FStar_List.splitAt
              ((FStar_List.length terms) - (Prims.parse_int "1")) terms
             in
          match uu____47646 with
          | (terms',last1) ->
              let uu____47666 =
                match style with
                | Arrows (n1,ln) ->
                    let uu____47701 =
                      let uu____47702 =
                        FStar_Pprint.op_Hat_Hat FStar_Pprint.rarrow break1
                         in
                      FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____47702
                       in
                    let uu____47703 =
                      FStar_Pprint.op_Hat_Hat FStar_Pprint.rarrow
                        FStar_Pprint.space
                       in
                    (n1, ln, terms', uu____47701, uu____47703)
                | Binders (n1,ln,parens1) ->
                    let uu____47717 =
                      if parens1
                      then FStar_List.map soft_parens_with_nesting terms'
                      else terms'  in
                    let uu____47725 =
                      FStar_Pprint.op_Hat_Hat FStar_Pprint.colon
                        FStar_Pprint.space
                       in
                    (n1, ln, uu____47717, break1, uu____47725)
                 in
              (match uu____47666 with
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
                    | _47758 when _47758 = (Prims.parse_int "1") ->
                        FStar_List.hd terms
                    | uu____47759 ->
                        let uu____47760 =
                          let uu____47761 =
                            let uu____47762 =
                              let uu____47763 =
                                FStar_Pprint.separate sep terms'1  in
                              let uu____47764 =
                                let uu____47765 =
                                  FStar_Pprint.op_Hat_Hat last_op1 last2  in
                                FStar_Pprint.op_Hat_Hat one_line_space
                                  uu____47765
                                 in
                              FStar_Pprint.op_Hat_Hat uu____47763 uu____47764
                               in
                            FStar_Pprint.op_Hat_Hat fs uu____47762  in
                          let uu____47766 =
                            let uu____47767 =
                              let uu____47768 =
                                let uu____47769 =
                                  let uu____47770 =
                                    FStar_Pprint.separate sep terms'1  in
                                  FStar_Pprint.op_Hat_Hat fs uu____47770  in
                                let uu____47771 =
                                  let uu____47772 =
                                    let uu____47773 =
                                      let uu____47774 =
                                        FStar_Pprint.op_Hat_Hat sep
                                          single_line_arg_indent
                                         in
                                      let uu____47775 =
                                        FStar_List.map
                                          (fun x  ->
                                             let uu____47781 =
                                               FStar_Pprint.hang
                                                 (Prims.parse_int "2") x
                                                in
                                             FStar_Pprint.align uu____47781)
                                          terms'1
                                         in
                                      FStar_Pprint.separate uu____47774
                                        uu____47775
                                       in
                                    FStar_Pprint.op_Hat_Hat
                                      single_line_arg_indent uu____47773
                                     in
                                  jump2 uu____47772  in
                                FStar_Pprint.ifflat uu____47769 uu____47771
                                 in
                              FStar_Pprint.group uu____47768  in
                            let uu____47783 =
                              let uu____47784 =
                                let uu____47785 =
                                  FStar_Pprint.op_Hat_Hat last_op1 last2  in
                                FStar_Pprint.hang last_n uu____47785  in
                              FStar_Pprint.align uu____47784  in
                            FStar_Pprint.prefix n1 (Prims.parse_int "1")
                              uu____47767 uu____47783
                             in
                          FStar_Pprint.ifflat uu____47761 uu____47766  in
                        FStar_Pprint.group uu____47760))

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
            | Arrows uu____47799 -> p_tmArrow' p_Tm e
            | Binders uu____47806 -> collapse_binders p_Tm e  in
          format_sig style terms false flat_space

and (p_tmArrow' :
  (FStar_Parser_AST.term -> FStar_Pprint.document) ->
    FStar_Parser_AST.term -> FStar_Pprint.document Prims.list)
  =
  fun p_Tm  ->
    fun e  ->
      match e.FStar_Parser_AST.tm with
      | FStar_Parser_AST.Product (bs,tgt) ->
          let uu____47829 = FStar_List.map (fun b  -> p_binder false b) bs
             in
          let uu____47835 = p_tmArrow' p_Tm tgt  in
          FStar_List.append uu____47829 uu____47835
      | uu____47838 -> let uu____47839 = p_Tm e  in [uu____47839]

and (collapse_binders :
  (FStar_Parser_AST.term -> FStar_Pprint.document) ->
    FStar_Parser_AST.term -> FStar_Pprint.document Prims.list)
  =
  fun p_Tm  ->
    fun e  ->
      let rec accumulate_binders p_Tm1 e1 =
        match e1.FStar_Parser_AST.tm with
        | FStar_Parser_AST.Product (bs,tgt) ->
            let uu____47892 = FStar_List.map (fun b  -> p_binder' false b) bs
               in
            let uu____47918 = accumulate_binders p_Tm1 tgt  in
            FStar_List.append uu____47892 uu____47918
        | uu____47941 ->
            let uu____47942 =
              let uu____47953 = p_Tm1 e1  in
              (uu____47953, FStar_Pervasives_Native.None, cat_with_colon)  in
            [uu____47942]
         in
      let fold_fun bs x =
        let uu____48051 = x  in
        match uu____48051 with
        | (b1,t1,f1) ->
            (match bs with
             | [] -> [([b1], t1, f1)]
             | hd1::tl1 ->
                 let uu____48183 = hd1  in
                 (match uu____48183 with
                  | (b2s,t2,uu____48212) ->
                      (match (t1, t2) with
                       | (FStar_Pervasives_Native.Some
                          typ1,FStar_Pervasives_Native.Some typ2) ->
                           if typ1 = typ2
                           then ((FStar_List.append b2s [b1]), t1, f1) :: tl1
                           else ([b1], t1, f1) :: hd1 :: tl1
                       | uu____48314 -> ([b1], t1, f1) :: bs)))
         in
      let p_collapsed_binder cb =
        let uu____48371 = cb  in
        match uu____48371 with
        | (bs,t,f) ->
            (match t with
             | FStar_Pervasives_Native.None  ->
                 (match bs with
                  | b::[] -> b
                  | uu____48400 -> failwith "Impossible")
             | FStar_Pervasives_Native.Some typ ->
                 (match bs with
                  | [] -> failwith "Impossible"
                  | b::[] -> f b typ
                  | hd1::tl1 ->
                      let uu____48411 =
                        FStar_List.fold_left
                          (fun x  ->
                             fun y  ->
                               let uu____48417 =
                                 FStar_Pprint.op_Hat_Hat FStar_Pprint.space y
                                  in
                               FStar_Pprint.op_Hat_Hat x uu____48417) hd1 tl1
                         in
                      f uu____48411 typ))
         in
      let binders =
        let uu____48433 = accumulate_binders p_Tm e  in
        FStar_List.fold_left fold_fun [] uu____48433  in
      map_rev p_collapsed_binder binders

and (p_tmFormula : FStar_Parser_AST.term -> FStar_Pprint.document) =
  fun e  ->
    let conj =
      let uu____48496 =
        let uu____48497 = str "/\\"  in
        FStar_Pprint.op_Hat_Hat uu____48497 break1  in
      FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____48496  in
    let disj =
      let uu____48500 =
        let uu____48501 = str "\\/"  in
        FStar_Pprint.op_Hat_Hat uu____48501 break1  in
      FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____48500  in
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
        ({ FStar_Ident.idText = "\\/"; FStar_Ident.idRange = uu____48521;_},e1::e2::[])
        ->
        let uu____48527 = p_tmDisjunction e1  in
        let uu____48532 =
          let uu____48537 = p_tmConjunction e2  in [uu____48537]  in
        FStar_List.append uu____48527 uu____48532
    | uu____48546 -> let uu____48547 = p_tmConjunction e  in [uu____48547]

and (p_tmConjunction :
  FStar_Parser_AST.term -> FStar_Pprint.document Prims.list) =
  fun e  ->
    match e.FStar_Parser_AST.tm with
    | FStar_Parser_AST.Op
        ({ FStar_Ident.idText = "/\\"; FStar_Ident.idRange = uu____48557;_},e1::e2::[])
        ->
        let uu____48563 = p_tmConjunction e1  in
        let uu____48566 = let uu____48569 = p_tmTuple e2  in [uu____48569]
           in
        FStar_List.append uu____48563 uu____48566
    | uu____48570 -> let uu____48571 = p_tmTuple e  in [uu____48571]

and (p_tmTuple : FStar_Parser_AST.term -> FStar_Pprint.document) =
  fun e  -> with_comment p_tmTuple' e e.FStar_Parser_AST.range

and (p_tmTuple' : FStar_Parser_AST.term -> FStar_Pprint.document) =
  fun e  ->
    match e.FStar_Parser_AST.tm with
    | FStar_Parser_AST.Construct (lid,args) when
        (is_tuple_constructor lid) && (all_explicit args) ->
        let uu____48588 = FStar_Pprint.op_Hat_Hat FStar_Pprint.comma break1
           in
        FStar_Pprint.separate_map uu____48588
          (fun uu____48596  ->
             match uu____48596 with | (e1,uu____48602) -> p_tmEq e1) args
    | uu____48603 -> p_tmEq e

and (paren_if_gt :
  Prims.int -> Prims.int -> FStar_Pprint.document -> FStar_Pprint.document) =
  fun curr  ->
    fun mine  ->
      fun doc1  ->
        if mine <= curr
        then doc1
        else
          (let uu____48612 =
             let uu____48613 =
               FStar_Pprint.op_Hat_Hat doc1 FStar_Pprint.rparen  in
             FStar_Pprint.op_Hat_Hat FStar_Pprint.lparen uu____48613  in
           FStar_Pprint.group uu____48612)

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
               (let uu____48632 = FStar_Ident.text_of_id op  in
                uu____48632 = "="))
              ||
              (let uu____48637 = FStar_Ident.text_of_id op  in
               uu____48637 = "|>")
            ->
            let op1 = FStar_Ident.text_of_id op  in
            let uu____48643 = levels op1  in
            (match uu____48643 with
             | (left1,mine,right1) ->
                 let uu____48662 =
                   let uu____48663 = FStar_All.pipe_left str op1  in
                   let uu____48665 = p_tmEqWith' p_X left1 e1  in
                   let uu____48666 = p_tmEqWith' p_X right1 e2  in
                   infix0 uu____48663 uu____48665 uu____48666  in
                 paren_if_gt curr mine uu____48662)
        | FStar_Parser_AST.Op
            ({ FStar_Ident.idText = ":=";
               FStar_Ident.idRange = uu____48667;_},e1::e2::[])
            ->
            let uu____48673 =
              let uu____48674 = p_tmEqWith p_X e1  in
              let uu____48675 =
                let uu____48676 =
                  let uu____48677 =
                    let uu____48678 = p_tmEqWith p_X e2  in
                    op_Hat_Slash_Plus_Hat FStar_Pprint.equals uu____48678  in
                  FStar_Pprint.op_Hat_Hat FStar_Pprint.colon uu____48677  in
                FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____48676  in
              FStar_Pprint.op_Hat_Hat uu____48674 uu____48675  in
            FStar_Pprint.group uu____48673
        | FStar_Parser_AST.Op
            ({ FStar_Ident.idText = "-"; FStar_Ident.idRange = uu____48679;_},e1::[])
            ->
            let uu____48684 = levels "-"  in
            (match uu____48684 with
             | (left1,mine,right1) ->
                 let uu____48704 = p_tmEqWith' p_X mine e1  in
                 FStar_Pprint.op_Hat_Slash_Hat FStar_Pprint.minus uu____48704)
        | uu____48705 -> p_tmNoEqWith p_X e

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
              (lid,(e1,uu____48753)::(e2,uu____48755)::[]) when
              (FStar_Ident.lid_equals lid FStar_Parser_Const.cons_lid) &&
                (let uu____48775 = is_list e  in
                 Prims.op_Negation uu____48775)
              ->
              let op = "::"  in
              let uu____48780 = levels op  in
              (match uu____48780 with
               | (left1,mine,right1) ->
                   let uu____48799 =
                     let uu____48800 = str op  in
                     let uu____48801 = p_tmNoEqWith' false p_X left1 e1  in
                     let uu____48803 = p_tmNoEqWith' false p_X right1 e2  in
                     infix0 uu____48800 uu____48801 uu____48803  in
                   paren_if_gt curr mine uu____48799)
          | FStar_Parser_AST.Sum (binders,res) ->
              let op = "&"  in
              let uu____48822 = levels op  in
              (match uu____48822 with
               | (left1,mine,right1) ->
                   let p_dsumfst bt =
                     match bt with
                     | FStar_Util.Inl b ->
                         let uu____48856 = p_binder false b  in
                         let uu____48858 =
                           let uu____48859 =
                             let uu____48860 = str op  in
                             FStar_Pprint.op_Hat_Hat uu____48860 break1  in
                           FStar_Pprint.op_Hat_Hat FStar_Pprint.space
                             uu____48859
                            in
                         FStar_Pprint.op_Hat_Hat uu____48856 uu____48858
                     | FStar_Util.Inr t ->
                         let uu____48862 = p_tmNoEqWith' false p_X left1 t
                            in
                         let uu____48864 =
                           let uu____48865 =
                             let uu____48866 = str op  in
                             FStar_Pprint.op_Hat_Hat uu____48866 break1  in
                           FStar_Pprint.op_Hat_Hat FStar_Pprint.space
                             uu____48865
                            in
                         FStar_Pprint.op_Hat_Hat uu____48862 uu____48864
                      in
                   let uu____48867 =
                     let uu____48868 =
                       FStar_Pprint.concat_map p_dsumfst binders  in
                     let uu____48873 = p_tmNoEqWith' false p_X right1 res  in
                     FStar_Pprint.op_Hat_Hat uu____48868 uu____48873  in
                   paren_if_gt curr mine uu____48867)
          | FStar_Parser_AST.Op
              ({ FStar_Ident.idText = "*";
                 FStar_Ident.idRange = uu____48875;_},e1::e2::[])
              when FStar_ST.op_Bang unfold_tuples ->
              let op = "*"  in
              let uu____48905 = levels op  in
              (match uu____48905 with
               | (left1,mine,right1) ->
                   if inside_tuple
                   then
                     let uu____48925 = str op  in
                     let uu____48926 = p_tmNoEqWith' true p_X left1 e1  in
                     let uu____48928 = p_tmNoEqWith' true p_X right1 e2  in
                     infix0 uu____48925 uu____48926 uu____48928
                   else
                     (let uu____48932 =
                        let uu____48933 = str op  in
                        let uu____48934 = p_tmNoEqWith' true p_X left1 e1  in
                        let uu____48936 = p_tmNoEqWith' true p_X right1 e2
                           in
                        infix0 uu____48933 uu____48934 uu____48936  in
                      paren_if_gt curr mine uu____48932))
          | FStar_Parser_AST.Op (op,e1::e2::[]) when is_operatorInfix34 op ->
              let op1 = FStar_Ident.text_of_id op  in
              let uu____48945 = levels op1  in
              (match uu____48945 with
               | (left1,mine,right1) ->
                   let uu____48964 =
                     let uu____48965 = str op1  in
                     let uu____48966 = p_tmNoEqWith' false p_X left1 e1  in
                     let uu____48968 = p_tmNoEqWith' false p_X right1 e2  in
                     infix0 uu____48965 uu____48966 uu____48968  in
                   paren_if_gt curr mine uu____48964)
          | FStar_Parser_AST.Record (with_opt,record_fields) ->
              let uu____48988 =
                let uu____48989 =
                  default_or_map FStar_Pprint.empty p_with_clause with_opt
                   in
                let uu____48990 =
                  let uu____48991 =
                    FStar_Pprint.op_Hat_Hat FStar_Pprint.semi break1  in
                  separate_map_last uu____48991 p_simpleDef record_fields  in
                FStar_Pprint.op_Hat_Hat uu____48989 uu____48990  in
              braces_with_nesting uu____48988
          | FStar_Parser_AST.Op
              ({ FStar_Ident.idText = "~";
                 FStar_Ident.idRange = uu____48996;_},e1::[])
              ->
              let uu____49001 =
                let uu____49002 = str "~"  in
                let uu____49004 = p_atomicTerm e1  in
                FStar_Pprint.op_Hat_Hat uu____49002 uu____49004  in
              FStar_Pprint.group uu____49001
          | FStar_Parser_AST.Paren p when inside_tuple ->
              (match p.FStar_Parser_AST.tm with
               | FStar_Parser_AST.Op
                   ({ FStar_Ident.idText = "*";
                      FStar_Ident.idRange = uu____49006;_},e1::e2::[])
                   ->
                   let op = "*"  in
                   let uu____49015 = levels op  in
                   (match uu____49015 with
                    | (left1,mine,right1) ->
                        let uu____49034 =
                          let uu____49035 = str op  in
                          let uu____49036 = p_tmNoEqWith' true p_X left1 e1
                             in
                          let uu____49038 = p_tmNoEqWith' true p_X right1 e2
                             in
                          infix0 uu____49035 uu____49036 uu____49038  in
                        paren_if_gt curr mine uu____49034)
               | uu____49040 -> p_X e)
          | uu____49041 -> p_X e

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
        let uu____49048 =
          let uu____49049 = p_lident lid  in
          let uu____49050 =
            let uu____49051 = p_appTerm e1  in
            FStar_Pprint.op_Hat_Slash_Hat FStar_Pprint.colon uu____49051  in
          FStar_Pprint.op_Hat_Slash_Hat uu____49049 uu____49050  in
        FStar_Pprint.group uu____49048
    | FStar_Parser_AST.Refine (b,phi) -> p_refinedBinder b phi
    | uu____49054 -> p_appTerm e

and (p_with_clause : FStar_Parser_AST.term -> FStar_Pprint.document) =
  fun e  ->
    let uu____49056 = p_appTerm e  in
    let uu____49057 =
      let uu____49058 =
        let uu____49059 = str "with"  in
        FStar_Pprint.op_Hat_Hat uu____49059 break1  in
      FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____49058  in
    FStar_Pprint.op_Hat_Hat uu____49056 uu____49057

and (p_refinedBinder :
  FStar_Parser_AST.binder -> FStar_Parser_AST.term -> FStar_Pprint.document)
  =
  fun b  ->
    fun phi  ->
      match b.FStar_Parser_AST.b with
      | FStar_Parser_AST.Annotated (lid,t) ->
          let uu____49065 = p_lident lid  in
          p_refinement b.FStar_Parser_AST.aqual uu____49065 t phi
      | FStar_Parser_AST.TAnnotated uu____49066 ->
          failwith "Is this still used ?"
      | FStar_Parser_AST.Variable uu____49072 ->
          let uu____49073 =
            let uu____49075 = FStar_Parser_AST.binder_to_string b  in
            FStar_Util.format1
              "Imposible : a refined binder ought to be annotated %s"
              uu____49075
             in
          failwith uu____49073
      | FStar_Parser_AST.TVariable uu____49078 ->
          let uu____49079 =
            let uu____49081 = FStar_Parser_AST.binder_to_string b  in
            FStar_Util.format1
              "Imposible : a refined binder ought to be annotated %s"
              uu____49081
             in
          failwith uu____49079
      | FStar_Parser_AST.NoName uu____49084 ->
          let uu____49085 =
            let uu____49087 = FStar_Parser_AST.binder_to_string b  in
            FStar_Util.format1
              "Imposible : a refined binder ought to be annotated %s"
              uu____49087
             in
          failwith uu____49085

and (p_simpleDef :
  Prims.bool ->
    (FStar_Ident.lid * FStar_Parser_AST.term) -> FStar_Pprint.document)
  =
  fun ps  ->
    fun uu____49091  ->
      match uu____49091 with
      | (lid,e) ->
          let uu____49099 =
            let uu____49100 = p_qlident lid  in
            let uu____49101 =
              let uu____49102 = p_noSeqTermAndComment ps false e  in
              FStar_Pprint.op_Hat_Slash_Hat FStar_Pprint.equals uu____49102
               in
            FStar_Pprint.op_Hat_Slash_Hat uu____49100 uu____49101  in
          FStar_Pprint.group uu____49099

and (p_appTerm : FStar_Parser_AST.term -> FStar_Pprint.document) =
  fun e  ->
    match e.FStar_Parser_AST.tm with
    | FStar_Parser_AST.App uu____49105 when is_general_application e ->
        let uu____49112 = head_and_args e  in
        (match uu____49112 with
         | (head1,args) ->
             (match args with
              | e1::e2::[] when
                  (FStar_Pervasives_Native.snd e1) = FStar_Parser_AST.Infix
                  ->
                  let uu____49159 = p_argTerm e1  in
                  let uu____49160 =
                    let uu____49161 =
                      let uu____49162 =
                        let uu____49163 = str "`"  in
                        let uu____49165 =
                          let uu____49166 = p_indexingTerm head1  in
                          let uu____49167 = str "`"  in
                          FStar_Pprint.op_Hat_Hat uu____49166 uu____49167  in
                        FStar_Pprint.op_Hat_Hat uu____49163 uu____49165  in
                      FStar_Pprint.group uu____49162  in
                    let uu____49169 = p_argTerm e2  in
                    FStar_Pprint.op_Hat_Slash_Hat uu____49161 uu____49169  in
                  FStar_Pprint.op_Hat_Slash_Hat uu____49159 uu____49160
              | uu____49170 ->
                  let uu____49177 =
                    let uu____49188 =
                      FStar_ST.op_Bang should_print_fs_typ_app  in
                    if uu____49188
                    then
                      let uu____49222 =
                        FStar_Util.take
                          (fun uu____49246  ->
                             match uu____49246 with
                             | (uu____49252,aq) ->
                                 aq = FStar_Parser_AST.FsTypApp) args
                         in
                      match uu____49222 with
                      | (fs_typ_args,args1) ->
                          let uu____49290 =
                            let uu____49291 = p_indexingTerm head1  in
                            let uu____49292 =
                              let uu____49293 =
                                FStar_Pprint.op_Hat_Hat FStar_Pprint.comma
                                  break1
                                 in
                              soft_surround_map_or_flow (Prims.parse_int "2")
                                (Prims.parse_int "0") FStar_Pprint.empty
                                FStar_Pprint.langle uu____49293
                                FStar_Pprint.rangle p_fsTypArg fs_typ_args
                               in
                            FStar_Pprint.op_Hat_Hat uu____49291 uu____49292
                             in
                          (uu____49290, args1)
                    else
                      (let uu____49308 = p_indexingTerm head1  in
                       (uu____49308, args))
                     in
                  (match uu____49177 with
                   | (head_doc,args1) ->
                       let uu____49329 =
                         let uu____49330 =
                           FStar_Pprint.op_Hat_Hat head_doc
                             FStar_Pprint.space
                            in
                         soft_surround_map_or_flow (Prims.parse_int "2")
                           (Prims.parse_int "0") head_doc uu____49330 break1
                           FStar_Pprint.empty p_argTerm args1
                          in
                       FStar_Pprint.group uu____49329)))
    | FStar_Parser_AST.Construct (lid,args) when
        (is_general_construction e) &&
          (let uu____49352 = is_dtuple_constructor lid  in
           Prims.op_Negation uu____49352)
        ->
        (match args with
         | [] -> p_quident lid
         | arg::[] ->
             let uu____49371 =
               let uu____49372 = p_quident lid  in
               let uu____49373 = p_argTerm arg  in
               FStar_Pprint.op_Hat_Slash_Hat uu____49372 uu____49373  in
             FStar_Pprint.group uu____49371
         | hd1::tl1 ->
             let uu____49390 =
               let uu____49391 =
                 let uu____49392 =
                   let uu____49393 = p_quident lid  in
                   let uu____49394 = p_argTerm hd1  in
                   prefix2 uu____49393 uu____49394  in
                 FStar_Pprint.group uu____49392  in
               let uu____49395 =
                 let uu____49396 =
                   FStar_Pprint.separate_map break1 p_argTerm tl1  in
                 jump2 uu____49396  in
               FStar_Pprint.op_Hat_Hat uu____49391 uu____49395  in
             FStar_Pprint.group uu____49390)
    | uu____49401 -> p_indexingTerm e

and (p_argTerm :
  (FStar_Parser_AST.term * FStar_Parser_AST.imp) -> FStar_Pprint.document) =
  fun arg_imp  ->
    match arg_imp with
    | (u,FStar_Parser_AST.UnivApp ) -> p_universe u
    | (e,FStar_Parser_AST.FsTypApp ) ->
        (FStar_Errors.log_issue e.FStar_Parser_AST.range
           (FStar_Errors.Warning_UnexpectedFsTypApp,
             "Unexpected FsTypApp, output might not be formatted correctly.");
         (let uu____49412 = p_indexingTerm e  in
          FStar_Pprint.surround (Prims.parse_int "2") (Prims.parse_int "1")
            FStar_Pprint.langle uu____49412 FStar_Pprint.rangle))
    | (e,FStar_Parser_AST.Hash ) ->
        let uu____49416 = str "#"  in
        let uu____49418 = p_indexingTerm e  in
        FStar_Pprint.op_Hat_Hat uu____49416 uu____49418
    | (e,FStar_Parser_AST.HashBrace t) ->
        let uu____49421 = str "#["  in
        let uu____49423 =
          let uu____49424 = p_indexingTerm t  in
          let uu____49425 =
            let uu____49426 = str "]"  in
            let uu____49428 = p_indexingTerm e  in
            FStar_Pprint.op_Hat_Hat uu____49426 uu____49428  in
          FStar_Pprint.op_Hat_Hat uu____49424 uu____49425  in
        FStar_Pprint.op_Hat_Hat uu____49421 uu____49423
    | (e,FStar_Parser_AST.Infix ) -> p_indexingTerm e
    | (e,FStar_Parser_AST.Nothing ) -> p_indexingTerm e

and (p_fsTypArg :
  (FStar_Parser_AST.term * FStar_Parser_AST.imp) -> FStar_Pprint.document) =
  fun uu____49431  ->
    match uu____49431 with | (e,uu____49437) -> p_indexingTerm e

and (p_indexingTerm_aux :
  (FStar_Parser_AST.term -> FStar_Pprint.document) ->
    FStar_Parser_AST.term -> FStar_Pprint.document)
  =
  fun exit1  ->
    fun e  ->
      match e.FStar_Parser_AST.tm with
      | FStar_Parser_AST.Op
          ({ FStar_Ident.idText = ".()"; FStar_Ident.idRange = uu____49442;_},e1::e2::[])
          ->
          let uu____49448 =
            let uu____49449 = p_indexingTerm_aux p_atomicTermNotQUident e1
               in
            let uu____49450 =
              let uu____49451 =
                let uu____49452 = p_term false false e2  in
                soft_parens_with_nesting uu____49452  in
              FStar_Pprint.op_Hat_Hat FStar_Pprint.dot uu____49451  in
            FStar_Pprint.op_Hat_Hat uu____49449 uu____49450  in
          FStar_Pprint.group uu____49448
      | FStar_Parser_AST.Op
          ({ FStar_Ident.idText = ".[]"; FStar_Ident.idRange = uu____49455;_},e1::e2::[])
          ->
          let uu____49461 =
            let uu____49462 = p_indexingTerm_aux p_atomicTermNotQUident e1
               in
            let uu____49463 =
              let uu____49464 =
                let uu____49465 = p_term false false e2  in
                soft_brackets_with_nesting uu____49465  in
              FStar_Pprint.op_Hat_Hat FStar_Pprint.dot uu____49464  in
            FStar_Pprint.op_Hat_Hat uu____49462 uu____49463  in
          FStar_Pprint.group uu____49461
      | uu____49468 -> exit1 e

and (p_indexingTerm : FStar_Parser_AST.term -> FStar_Pprint.document) =
  fun e  -> p_indexingTerm_aux p_atomicTerm e

and (p_atomicTerm : FStar_Parser_AST.term -> FStar_Pprint.document) =
  fun e  ->
    match e.FStar_Parser_AST.tm with
    | FStar_Parser_AST.LetOpen (lid,e1) ->
        let uu____49473 = p_quident lid  in
        let uu____49474 =
          let uu____49475 =
            let uu____49476 = p_term false false e1  in
            soft_parens_with_nesting uu____49476  in
          FStar_Pprint.op_Hat_Hat FStar_Pprint.dot uu____49475  in
        FStar_Pprint.op_Hat_Hat uu____49473 uu____49474
    | FStar_Parser_AST.Name lid -> p_quident lid
    | FStar_Parser_AST.Op (op,e1::[]) when is_general_prefix_op op ->
        let uu____49484 =
          let uu____49485 = FStar_Ident.text_of_id op  in str uu____49485  in
        let uu____49487 = p_atomicTerm e1  in
        FStar_Pprint.op_Hat_Hat uu____49484 uu____49487
    | uu____49488 -> p_atomicTermNotQUident e

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
         | uu____49501 -> p_constant c)
    | FStar_Parser_AST.Name lid when
        FStar_Ident.lid_equals lid FStar_Parser_Const.true_lid -> str "True"
    | FStar_Parser_AST.Name lid when
        FStar_Ident.lid_equals lid FStar_Parser_Const.false_lid ->
        str "False"
    | FStar_Parser_AST.Op (op,e1::[]) when is_general_prefix_op op ->
        let uu____49510 =
          let uu____49511 = FStar_Ident.text_of_id op  in str uu____49511  in
        let uu____49513 = p_atomicTermNotQUident e1  in
        FStar_Pprint.op_Hat_Hat uu____49510 uu____49513
    | FStar_Parser_AST.Op (op,[]) ->
        let uu____49517 =
          let uu____49518 =
            let uu____49519 =
              let uu____49520 = FStar_Ident.text_of_id op  in str uu____49520
               in
            let uu____49522 =
              FStar_Pprint.op_Hat_Hat FStar_Pprint.space FStar_Pprint.rparen
               in
            FStar_Pprint.op_Hat_Hat uu____49519 uu____49522  in
          FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____49518  in
        FStar_Pprint.op_Hat_Hat FStar_Pprint.lparen uu____49517
    | FStar_Parser_AST.Construct (lid,args) when is_dtuple_constructor lid ->
        let uu____49537 = all_explicit args  in
        if uu____49537
        then
          let uu____49540 =
            FStar_Pprint.op_Hat_Hat FStar_Pprint.lparen FStar_Pprint.bar  in
          let uu____49541 =
            let uu____49542 =
              FStar_Pprint.op_Hat_Hat FStar_Pprint.comma break1  in
            let uu____49543 = FStar_List.map FStar_Pervasives_Native.fst args
               in
            FStar_Pprint.separate_map uu____49542 p_tmEq uu____49543  in
          let uu____49550 =
            FStar_Pprint.op_Hat_Hat FStar_Pprint.bar FStar_Pprint.rparen  in
          FStar_Pprint.surround (Prims.parse_int "2") (Prims.parse_int "1")
            uu____49540 uu____49541 uu____49550
        else
          (match args with
           | [] -> p_quident lid
           | arg::[] ->
               let uu____49572 =
                 let uu____49573 = p_quident lid  in
                 let uu____49574 = p_argTerm arg  in
                 FStar_Pprint.op_Hat_Slash_Hat uu____49573 uu____49574  in
               FStar_Pprint.group uu____49572
           | hd1::tl1 ->
               let uu____49591 =
                 let uu____49592 =
                   let uu____49593 =
                     let uu____49594 = p_quident lid  in
                     let uu____49595 = p_argTerm hd1  in
                     prefix2 uu____49594 uu____49595  in
                   FStar_Pprint.group uu____49593  in
                 let uu____49596 =
                   let uu____49597 =
                     FStar_Pprint.separate_map break1 p_argTerm tl1  in
                   jump2 uu____49597  in
                 FStar_Pprint.op_Hat_Hat uu____49592 uu____49596  in
               FStar_Pprint.group uu____49591)
    | FStar_Parser_AST.Project (e1,lid) ->
        let uu____49604 =
          let uu____49605 = p_atomicTermNotQUident e1  in
          let uu____49606 =
            let uu____49607 = p_qlident lid  in
            FStar_Pprint.op_Hat_Hat FStar_Pprint.dot uu____49607  in
          FStar_Pprint.prefix (Prims.parse_int "2") (Prims.parse_int "0")
            uu____49605 uu____49606
           in
        FStar_Pprint.group uu____49604
    | uu____49610 -> p_projectionLHS e

and (p_projectionLHS : FStar_Parser_AST.term -> FStar_Pprint.document) =
  fun e  ->
    match e.FStar_Parser_AST.tm with
    | FStar_Parser_AST.Var lid -> p_qlident lid
    | FStar_Parser_AST.Projector (constr_lid,field_lid) ->
        let uu____49615 = p_quident constr_lid  in
        let uu____49616 =
          let uu____49617 =
            let uu____49618 = p_lident field_lid  in
            FStar_Pprint.op_Hat_Hat FStar_Pprint.dot uu____49618  in
          FStar_Pprint.op_Hat_Hat FStar_Pprint.qmark uu____49617  in
        FStar_Pprint.op_Hat_Hat uu____49615 uu____49616
    | FStar_Parser_AST.Discrim constr_lid ->
        let uu____49620 = p_quident constr_lid  in
        FStar_Pprint.op_Hat_Hat uu____49620 FStar_Pprint.qmark
    | FStar_Parser_AST.Paren e1 ->
        let uu____49622 = p_term_sep false false e1  in
        (match uu____49622 with
         | (comm,t) ->
             let doc1 = soft_parens_with_nesting t  in
             if comm = FStar_Pprint.empty
             then doc1
             else
               (let uu____49635 =
                  FStar_Pprint.op_Hat_Hat FStar_Pprint.hardline doc1  in
                FStar_Pprint.op_Hat_Hat comm uu____49635))
    | uu____49636 when is_array e ->
        let es = extract_from_list e  in
        let uu____49640 =
          FStar_Pprint.op_Hat_Hat FStar_Pprint.lbracket FStar_Pprint.bar  in
        let uu____49641 =
          let uu____49642 = FStar_Pprint.op_Hat_Hat FStar_Pprint.semi break1
             in
          separate_map_or_flow_last uu____49642
            (fun ps  -> p_noSeqTermAndComment ps false) es
           in
        let uu____49647 =
          FStar_Pprint.op_Hat_Hat FStar_Pprint.bar FStar_Pprint.rbracket  in
        FStar_Pprint.surround (Prims.parse_int "2") (Prims.parse_int "0")
          uu____49640 uu____49641 uu____49647
    | uu____49650 when is_list e ->
        let uu____49651 =
          let uu____49652 = FStar_Pprint.op_Hat_Hat FStar_Pprint.semi break1
             in
          let uu____49653 = extract_from_list e  in
          separate_map_or_flow_last uu____49652
            (fun ps  -> p_noSeqTermAndComment ps false) uu____49653
           in
        FStar_Pprint.surround (Prims.parse_int "2") (Prims.parse_int "0")
          FStar_Pprint.lbracket uu____49651 FStar_Pprint.rbracket
    | uu____49662 when is_lex_list e ->
        let uu____49663 =
          FStar_Pprint.op_Hat_Hat FStar_Pprint.percent FStar_Pprint.lbracket
           in
        let uu____49664 =
          let uu____49665 = FStar_Pprint.op_Hat_Hat FStar_Pprint.semi break1
             in
          let uu____49666 = extract_from_list e  in
          separate_map_or_flow_last uu____49665
            (fun ps  -> p_noSeqTermAndComment ps false) uu____49666
           in
        FStar_Pprint.surround (Prims.parse_int "2") (Prims.parse_int "1")
          uu____49663 uu____49664 FStar_Pprint.rbracket
    | uu____49675 when is_ref_set e ->
        let es = extract_from_ref_set e  in
        let uu____49679 =
          FStar_Pprint.op_Hat_Hat FStar_Pprint.bang FStar_Pprint.lbrace  in
        let uu____49680 =
          let uu____49681 = FStar_Pprint.op_Hat_Hat FStar_Pprint.comma break1
             in
          separate_map_or_flow uu____49681 p_appTerm es  in
        FStar_Pprint.surround (Prims.parse_int "2") (Prims.parse_int "0")
          uu____49679 uu____49680 FStar_Pprint.rbrace
    | FStar_Parser_AST.Labeled (e1,s,b) ->
        let uu____49691 = str (Prims.op_Hat "(*" (Prims.op_Hat s "*)"))  in
        let uu____49694 = p_term false false e1  in
        FStar_Pprint.op_Hat_Slash_Hat uu____49691 uu____49694
    | FStar_Parser_AST.Op (op,args) when
        let uu____49703 = handleable_op op args  in
        Prims.op_Negation uu____49703 ->
        let uu____49705 =
          let uu____49707 =
            let uu____49709 = FStar_Ident.text_of_id op  in
            let uu____49711 =
              let uu____49713 =
                let uu____49715 =
                  FStar_Util.string_of_int (FStar_List.length args)  in
                Prims.op_Hat uu____49715
                  " arguments couldn't be handled by the pretty printer"
                 in
              Prims.op_Hat " with " uu____49713  in
            Prims.op_Hat uu____49709 uu____49711  in
          Prims.op_Hat "Operation " uu____49707  in
        failwith uu____49705
    | FStar_Parser_AST.Uvar id1 ->
        failwith "Unexpected universe variable out of universe context"
    | FStar_Parser_AST.Wild  ->
        let uu____49722 = p_term false false e  in
        soft_parens_with_nesting uu____49722
    | FStar_Parser_AST.Const uu____49725 ->
        let uu____49726 = p_term false false e  in
        soft_parens_with_nesting uu____49726
    | FStar_Parser_AST.Op uu____49729 ->
        let uu____49736 = p_term false false e  in
        soft_parens_with_nesting uu____49736
    | FStar_Parser_AST.Tvar uu____49739 ->
        let uu____49740 = p_term false false e  in
        soft_parens_with_nesting uu____49740
    | FStar_Parser_AST.Var uu____49743 ->
        let uu____49744 = p_term false false e  in
        soft_parens_with_nesting uu____49744
    | FStar_Parser_AST.Name uu____49747 ->
        let uu____49748 = p_term false false e  in
        soft_parens_with_nesting uu____49748
    | FStar_Parser_AST.Construct uu____49751 ->
        let uu____49762 = p_term false false e  in
        soft_parens_with_nesting uu____49762
    | FStar_Parser_AST.Abs uu____49765 ->
        let uu____49772 = p_term false false e  in
        soft_parens_with_nesting uu____49772
    | FStar_Parser_AST.App uu____49775 ->
        let uu____49782 = p_term false false e  in
        soft_parens_with_nesting uu____49782
    | FStar_Parser_AST.Let uu____49785 ->
        let uu____49806 = p_term false false e  in
        soft_parens_with_nesting uu____49806
    | FStar_Parser_AST.LetOpen uu____49809 ->
        let uu____49814 = p_term false false e  in
        soft_parens_with_nesting uu____49814
    | FStar_Parser_AST.Seq uu____49817 ->
        let uu____49822 = p_term false false e  in
        soft_parens_with_nesting uu____49822
    | FStar_Parser_AST.Bind uu____49825 ->
        let uu____49832 = p_term false false e  in
        soft_parens_with_nesting uu____49832
    | FStar_Parser_AST.If uu____49835 ->
        let uu____49842 = p_term false false e  in
        soft_parens_with_nesting uu____49842
    | FStar_Parser_AST.Match uu____49845 ->
        let uu____49860 = p_term false false e  in
        soft_parens_with_nesting uu____49860
    | FStar_Parser_AST.TryWith uu____49863 ->
        let uu____49878 = p_term false false e  in
        soft_parens_with_nesting uu____49878
    | FStar_Parser_AST.Ascribed uu____49881 ->
        let uu____49890 = p_term false false e  in
        soft_parens_with_nesting uu____49890
    | FStar_Parser_AST.Record uu____49893 ->
        let uu____49906 = p_term false false e  in
        soft_parens_with_nesting uu____49906
    | FStar_Parser_AST.Project uu____49909 ->
        let uu____49914 = p_term false false e  in
        soft_parens_with_nesting uu____49914
    | FStar_Parser_AST.Product uu____49917 ->
        let uu____49924 = p_term false false e  in
        soft_parens_with_nesting uu____49924
    | FStar_Parser_AST.Sum uu____49927 ->
        let uu____49938 = p_term false false e  in
        soft_parens_with_nesting uu____49938
    | FStar_Parser_AST.QForall uu____49941 ->
        let uu____49954 = p_term false false e  in
        soft_parens_with_nesting uu____49954
    | FStar_Parser_AST.QExists uu____49957 ->
        let uu____49970 = p_term false false e  in
        soft_parens_with_nesting uu____49970
    | FStar_Parser_AST.Refine uu____49973 ->
        let uu____49978 = p_term false false e  in
        soft_parens_with_nesting uu____49978
    | FStar_Parser_AST.NamedTyp uu____49981 ->
        let uu____49986 = p_term false false e  in
        soft_parens_with_nesting uu____49986
    | FStar_Parser_AST.Requires uu____49989 ->
        let uu____49997 = p_term false false e  in
        soft_parens_with_nesting uu____49997
    | FStar_Parser_AST.Ensures uu____50000 ->
        let uu____50008 = p_term false false e  in
        soft_parens_with_nesting uu____50008
    | FStar_Parser_AST.Attributes uu____50011 ->
        let uu____50014 = p_term false false e  in
        soft_parens_with_nesting uu____50014
    | FStar_Parser_AST.Quote uu____50017 ->
        let uu____50022 = p_term false false e  in
        soft_parens_with_nesting uu____50022
    | FStar_Parser_AST.VQuote uu____50025 ->
        let uu____50026 = p_term false false e  in
        soft_parens_with_nesting uu____50026
    | FStar_Parser_AST.Antiquote uu____50029 ->
        let uu____50030 = p_term false false e  in
        soft_parens_with_nesting uu____50030
    | FStar_Parser_AST.CalcProof uu____50033 ->
        let uu____50042 = p_term false false e  in
        soft_parens_with_nesting uu____50042

and (p_constant : FStar_Const.sconst -> FStar_Pprint.document) =
  fun uu___339_50045  ->
    match uu___339_50045 with
    | FStar_Const.Const_effect  -> str "Effect"
    | FStar_Const.Const_unit  -> str "()"
    | FStar_Const.Const_bool b -> FStar_Pprint.doc_of_bool b
    | FStar_Const.Const_real r -> str (Prims.op_Hat r "R")
    | FStar_Const.Const_float x -> str (FStar_Util.string_of_float x)
    | FStar_Const.Const_char x -> FStar_Pprint.doc_of_char x
    | FStar_Const.Const_string (s,uu____50057) ->
        let uu____50060 = str (FStar_String.escaped s)  in
        FStar_Pprint.dquotes uu____50060
    | FStar_Const.Const_bytearray (bytes,uu____50062) ->
        let uu____50067 =
          let uu____50068 = str (FStar_Util.string_of_bytes bytes)  in
          FStar_Pprint.dquotes uu____50068  in
        let uu____50069 = str "B"  in
        FStar_Pprint.op_Hat_Hat uu____50067 uu____50069
    | FStar_Const.Const_int (repr,sign_width_opt) ->
        let signedness uu___337_50092 =
          match uu___337_50092 with
          | FStar_Const.Unsigned  -> str "u"
          | FStar_Const.Signed  -> FStar_Pprint.empty  in
        let width uu___338_50099 =
          match uu___338_50099 with
          | FStar_Const.Int8  -> str "y"
          | FStar_Const.Int16  -> str "s"
          | FStar_Const.Int32  -> str "l"
          | FStar_Const.Int64  -> str "L"  in
        let ending =
          default_or_map FStar_Pprint.empty
            (fun uu____50114  ->
               match uu____50114 with
               | (s,w) ->
                   let uu____50121 = signedness s  in
                   let uu____50122 = width w  in
                   FStar_Pprint.op_Hat_Hat uu____50121 uu____50122)
            sign_width_opt
           in
        let uu____50123 = str repr  in
        FStar_Pprint.op_Hat_Hat uu____50123 ending
    | FStar_Const.Const_range_of  -> str "range_of"
    | FStar_Const.Const_set_range_of  -> str "set_range_of"
    | FStar_Const.Const_range r ->
        let uu____50127 = FStar_Range.string_of_range r  in str uu____50127
    | FStar_Const.Const_reify  -> str "reify"
    | FStar_Const.Const_reflect lid ->
        let uu____50131 = p_quident lid  in
        let uu____50132 =
          let uu____50133 =
            let uu____50134 = str "reflect"  in
            FStar_Pprint.op_Hat_Hat FStar_Pprint.dot uu____50134  in
          FStar_Pprint.op_Hat_Hat FStar_Pprint.qmark uu____50133  in
        FStar_Pprint.op_Hat_Hat uu____50131 uu____50132

and (p_universe : FStar_Parser_AST.term -> FStar_Pprint.document) =
  fun u  ->
    let uu____50137 = str "u#"  in
    let uu____50139 = p_atomicUniverse u  in
    FStar_Pprint.op_Hat_Hat uu____50137 uu____50139

and (p_universeFrom : FStar_Parser_AST.term -> FStar_Pprint.document) =
  fun u  ->
    match u.FStar_Parser_AST.tm with
    | FStar_Parser_AST.Op
        ({ FStar_Ident.idText = "+"; FStar_Ident.idRange = uu____50141;_},u1::u2::[])
        ->
        let uu____50147 =
          let uu____50148 = p_universeFrom u1  in
          let uu____50149 =
            let uu____50150 = p_universeFrom u2  in
            FStar_Pprint.op_Hat_Slash_Hat FStar_Pprint.plus uu____50150  in
          FStar_Pprint.op_Hat_Slash_Hat uu____50148 uu____50149  in
        FStar_Pprint.group uu____50147
    | FStar_Parser_AST.App uu____50151 ->
        let uu____50158 = head_and_args u  in
        (match uu____50158 with
         | (head1,args) ->
             (match head1.FStar_Parser_AST.tm with
              | FStar_Parser_AST.Var maybe_max_lid when
                  FStar_Ident.lid_equals maybe_max_lid
                    FStar_Parser_Const.max_lid
                  ->
                  let uu____50184 =
                    let uu____50185 = p_qlident FStar_Parser_Const.max_lid
                       in
                    let uu____50186 =
                      FStar_Pprint.separate_map FStar_Pprint.space
                        (fun uu____50194  ->
                           match uu____50194 with
                           | (u1,uu____50200) -> p_atomicUniverse u1) args
                       in
                    op_Hat_Slash_Plus_Hat uu____50185 uu____50186  in
                  FStar_Pprint.group uu____50184
              | uu____50201 ->
                  let uu____50202 =
                    let uu____50204 = FStar_Parser_AST.term_to_string u  in
                    FStar_Util.format1 "Invalid term in universe context %s"
                      uu____50204
                     in
                  failwith uu____50202))
    | uu____50207 -> p_atomicUniverse u

and (p_atomicUniverse : FStar_Parser_AST.term -> FStar_Pprint.document) =
  fun u  ->
    match u.FStar_Parser_AST.tm with
    | FStar_Parser_AST.Wild  -> FStar_Pprint.underscore
    | FStar_Parser_AST.Const (FStar_Const.Const_int (r,sw)) ->
        p_constant (FStar_Const.Const_int (r, sw))
    | FStar_Parser_AST.Uvar id1 ->
        let uu____50233 = FStar_Ident.text_of_id id1  in str uu____50233
    | FStar_Parser_AST.Paren u1 ->
        let uu____50236 = p_universeFrom u1  in
        soft_parens_with_nesting uu____50236
    | FStar_Parser_AST.Op
        ({ FStar_Ident.idText = "+"; FStar_Ident.idRange = uu____50237;_},uu____50238::uu____50239::[])
        ->
        let uu____50243 = p_universeFrom u  in
        soft_parens_with_nesting uu____50243
    | FStar_Parser_AST.App uu____50244 ->
        let uu____50251 = p_universeFrom u  in
        soft_parens_with_nesting uu____50251
    | uu____50252 ->
        let uu____50253 =
          let uu____50255 = FStar_Parser_AST.term_to_string u  in
          FStar_Util.format1 "Invalid term in universe context %s"
            uu____50255
           in
        failwith uu____50253

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
       | FStar_Parser_AST.Module (uu____50344,decls) ->
           let uu____50350 =
             FStar_All.pipe_right decls (FStar_List.map decl_to_document)  in
           FStar_All.pipe_right uu____50350
             (FStar_Pprint.separate FStar_Pprint.hardline)
       | FStar_Parser_AST.Interface (uu____50359,decls,uu____50361) ->
           let uu____50368 =
             FStar_All.pipe_right decls (FStar_List.map decl_to_document)  in
           FStar_All.pipe_right uu____50368
             (FStar_Pprint.separate FStar_Pprint.hardline)
        in
     FStar_ST.op_Colon_Equals should_print_fs_typ_app false; res)
  
let (comments_to_document :
  (Prims.string * FStar_Range.range) Prims.list -> FStar_Pprint.document) =
  fun comments  ->
    FStar_Pprint.separate_map FStar_Pprint.hardline
      (fun uu____50428  ->
         match uu____50428 with | (comment,range) -> str comment) comments
  
let (extract_decl_range : FStar_Parser_AST.decl -> decl_meta) =
  fun d  ->
    let has_qs =
      match ((d.FStar_Parser_AST.quals), (d.FStar_Parser_AST.d)) with
      | ((FStar_Parser_AST.Assumption )::[],FStar_Parser_AST.Assume
         (id1,uu____50450)) -> false
      | ([],uu____50454) -> false
      | uu____50458 -> true  in
    {
      r = (d.FStar_Parser_AST.drange);
      has_qs;
      has_attrs =
        (Prims.op_Negation (FStar_List.isEmpty d.FStar_Parser_AST.attrs));
      has_fsdoc = (FStar_Util.is_some d.FStar_Parser_AST.doc);
      is_fsdoc =
        (match d.FStar_Parser_AST.d with
         | FStar_Parser_AST.Fsdoc uu____50468 -> true
         | uu____50470 -> false)
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
        | FStar_Parser_AST.Module (uu____50513,decls) -> decls
        | FStar_Parser_AST.Interface (uu____50519,decls,uu____50521) -> decls
         in
      FStar_ST.op_Colon_Equals should_print_fs_typ_app false;
      (match decls with
       | [] -> (FStar_Pprint.empty, comments)
       | d::ds ->
           let uu____50573 =
             match ds with
             | {
                 FStar_Parser_AST.d = FStar_Parser_AST.Pragma
                   (FStar_Parser_AST.LightOff );
                 FStar_Parser_AST.drange = uu____50586;
                 FStar_Parser_AST.doc = uu____50587;
                 FStar_Parser_AST.quals = uu____50588;
                 FStar_Parser_AST.attrs = uu____50589;_}::uu____50590 ->
                 let d0 = FStar_List.hd ds  in
                 let uu____50596 =
                   let uu____50599 =
                     let uu____50602 = FStar_List.tl ds  in d :: uu____50602
                      in
                   d0 :: uu____50599  in
                 (uu____50596, (d0.FStar_Parser_AST.drange))
             | uu____50607 -> ((d :: ds), (d.FStar_Parser_AST.drange))  in
           (match uu____50573 with
            | (decls1,first_range) ->
                (FStar_ST.op_Colon_Equals comment_stack comments;
                 (let initial_comment =
                    let uu____50664 = FStar_Range.start_of_range first_range
                       in
                    place_comments_until_pos (Prims.parse_int "0")
                      (Prims.parse_int "1") uu____50664 dummy_meta
                      FStar_Pprint.empty false true
                     in
                  let doc1 =
                    separate_map_with_comments FStar_Pprint.empty
                      FStar_Pprint.empty p_decl decls1 extract_decl_range
                     in
                  let comments1 = FStar_ST.op_Bang comment_stack  in
                  FStar_ST.op_Colon_Equals comment_stack [];
                  FStar_ST.op_Colon_Equals should_print_fs_typ_app false;
                  (let uu____50773 =
                     FStar_Pprint.op_Hat_Hat initial_comment doc1  in
                   (uu____50773, comments1))))))
  