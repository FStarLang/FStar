open Prims
let (maybe_unthunk : FStar_Parser_AST.term -> FStar_Parser_AST.term) =
  fun t ->
    match t.FStar_Parser_AST.tm with
    | FStar_Parser_AST.Abs (uu____8::[], body) -> body
    | uu____12 -> t
let (min : Prims.int -> Prims.int -> Prims.int) =
  fun x -> fun y -> if x > y then y else x
let (max : Prims.int -> Prims.int -> Prims.int) =
  fun x -> fun y -> if x > y then x else y
let map_rev : 'a 'b . ('a -> 'b) -> 'a Prims.list -> 'b Prims.list =
  fun f ->
    fun l ->
      let rec aux l1 acc =
        match l1 with
        | [] -> acc
        | x::xs ->
            let uu____112 = let uu____115 = f x in uu____115 :: acc in
            aux xs uu____112 in
      aux l []
let map_if_all :
  'a 'b .
    ('a -> 'b FStar_Pervasives_Native.option) ->
      'a Prims.list -> 'b Prims.list FStar_Pervasives_Native.option
  =
  fun f ->
    fun l ->
      let rec aux l1 acc =
        match l1 with
        | [] -> acc
        | x::xs ->
            let uu____181 = f x in
            (match uu____181 with
             | FStar_Pervasives_Native.Some r -> aux xs (r :: acc)
             | FStar_Pervasives_Native.None -> []) in
      let r = aux l [] in
      if (FStar_List.length l) = (FStar_List.length r)
      then FStar_Pervasives_Native.Some r
      else FStar_Pervasives_Native.None
let rec all : 'a . ('a -> Prims.bool) -> 'a Prims.list -> Prims.bool =
  fun f ->
    fun l ->
      match l with
      | [] -> true
      | x::xs -> let uu____237 = f x in if uu____237 then all f xs else false
let (all1_explicit :
  (FStar_Parser_AST.term * FStar_Parser_AST.imp) Prims.list -> Prims.bool) =
  fun args ->
    (Prims.op_Negation (FStar_List.isEmpty args)) &&
      (FStar_Util.for_all
         (fun uu___0_274 ->
            match uu___0_274 with
            | (uu____280, FStar_Parser_AST.Nothing) -> true
            | uu____282 -> false) args)
let (should_print_fs_typ_app : Prims.bool FStar_ST.ref) =
  FStar_Util.mk_ref false
let (unfold_tuples : Prims.bool FStar_ST.ref) = FStar_Util.mk_ref true
let with_fs_typ_app :
  'uuuuuu311 'uuuuuu312 .
    Prims.bool -> ('uuuuuu311 -> 'uuuuuu312) -> 'uuuuuu311 -> 'uuuuuu312
  =
  fun b ->
    fun printer ->
      fun t ->
        let b0 = FStar_ST.op_Bang should_print_fs_typ_app in
        FStar_ST.op_Colon_Equals should_print_fs_typ_app b;
        (let res = printer t in
         FStar_ST.op_Colon_Equals should_print_fs_typ_app b0; res)
let (str : Prims.string -> FStar_Pprint.document) =
  fun s -> FStar_Pprint.doc_of_string s
let default_or_map :
  'uuuuuu422 'uuuuuu423 .
    'uuuuuu422 ->
      ('uuuuuu423 -> 'uuuuuu422) ->
        'uuuuuu423 FStar_Pervasives_Native.option -> 'uuuuuu422
  =
  fun n ->
    fun f ->
      fun x ->
        match x with
        | FStar_Pervasives_Native.None -> n
        | FStar_Pervasives_Native.Some x' -> f x'
let (prefix2 :
  FStar_Pprint.document -> FStar_Pprint.document -> FStar_Pprint.document) =
  fun prefix_ ->
    fun body ->
      FStar_Pprint.prefix (Prims.of_int (2)) Prims.int_one prefix_ body
let (prefix2_nonempty :
  FStar_Pprint.document -> FStar_Pprint.document -> FStar_Pprint.document) =
  fun prefix_ ->
    fun body ->
      if body = FStar_Pprint.empty then prefix_ else prefix2 prefix_ body
let (op_Hat_Slash_Plus_Hat :
  FStar_Pprint.document -> FStar_Pprint.document -> FStar_Pprint.document) =
  fun prefix_ -> fun body -> prefix2 prefix_ body
let (jump2 : FStar_Pprint.document -> FStar_Pprint.document) =
  fun body -> FStar_Pprint.jump (Prims.of_int (2)) Prims.int_one body
let (infix2 :
  FStar_Pprint.document ->
    FStar_Pprint.document -> FStar_Pprint.document -> FStar_Pprint.document)
  = FStar_Pprint.infix (Prims.of_int (2)) Prims.int_one
let (infix0 :
  FStar_Pprint.document ->
    FStar_Pprint.document -> FStar_Pprint.document -> FStar_Pprint.document)
  = FStar_Pprint.infix Prims.int_zero Prims.int_one
let (break1 : FStar_Pprint.document) = FStar_Pprint.break_ Prims.int_one
let separate_break_map :
  'uuuuuu536 .
    FStar_Pprint.document ->
      ('uuuuuu536 -> FStar_Pprint.document) ->
        'uuuuuu536 Prims.list -> FStar_Pprint.document
  =
  fun sep ->
    fun f ->
      fun l ->
        let uu____561 =
          let uu____562 =
            let uu____563 = FStar_Pprint.op_Hat_Hat sep break1 in
            FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____563 in
          FStar_Pprint.separate_map uu____562 f l in
        FStar_Pprint.group uu____561
let precede_break_separate_map :
  'uuuuuu575 .
    FStar_Pprint.document ->
      FStar_Pprint.document ->
        ('uuuuuu575 -> FStar_Pprint.document) ->
          'uuuuuu575 Prims.list -> FStar_Pprint.document
  =
  fun prec ->
    fun sep ->
      fun f ->
        fun l ->
          let uu____605 =
            let uu____606 = FStar_Pprint.op_Hat_Hat prec FStar_Pprint.space in
            let uu____607 =
              let uu____608 = FStar_List.hd l in
              FStar_All.pipe_right uu____608 f in
            FStar_Pprint.precede uu____606 uu____607 in
          let uu____609 =
            let uu____610 = FStar_List.tl l in
            FStar_Pprint.concat_map
              (fun x ->
                 let uu____616 =
                   let uu____617 =
                     let uu____618 = f x in
                     FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____618 in
                   FStar_Pprint.op_Hat_Hat sep uu____617 in
                 FStar_Pprint.op_Hat_Hat break1 uu____616) uu____610 in
          FStar_Pprint.op_Hat_Hat uu____605 uu____609
let concat_break_map :
  'uuuuuu626 .
    ('uuuuuu626 -> FStar_Pprint.document) ->
      'uuuuuu626 Prims.list -> FStar_Pprint.document
  =
  fun f ->
    fun l ->
      let uu____646 =
        FStar_Pprint.concat_map
          (fun x ->
             let uu____650 = f x in FStar_Pprint.op_Hat_Hat uu____650 break1)
          l in
      FStar_Pprint.group uu____646
let (parens_with_nesting : FStar_Pprint.document -> FStar_Pprint.document) =
  fun contents ->
    FStar_Pprint.surround (Prims.of_int (2)) Prims.int_zero
      FStar_Pprint.lparen contents FStar_Pprint.rparen
let (soft_parens_with_nesting :
  FStar_Pprint.document -> FStar_Pprint.document) =
  fun contents ->
    FStar_Pprint.soft_surround (Prims.of_int (2)) Prims.int_zero
      FStar_Pprint.lparen contents FStar_Pprint.rparen
let (braces_with_nesting : FStar_Pprint.document -> FStar_Pprint.document) =
  fun contents ->
    FStar_Pprint.surround (Prims.of_int (2)) Prims.int_one
      FStar_Pprint.lbrace contents FStar_Pprint.rbrace
let (soft_braces_with_nesting :
  FStar_Pprint.document -> FStar_Pprint.document) =
  fun contents ->
    FStar_Pprint.soft_surround (Prims.of_int (2)) Prims.int_one
      FStar_Pprint.lbrace contents FStar_Pprint.rbrace
let (soft_braces_with_nesting_tight :
  FStar_Pprint.document -> FStar_Pprint.document) =
  fun contents ->
    FStar_Pprint.soft_surround (Prims.of_int (2)) Prims.int_zero
      FStar_Pprint.lbrace contents FStar_Pprint.rbrace
let (brackets_with_nesting : FStar_Pprint.document -> FStar_Pprint.document)
  =
  fun contents ->
    FStar_Pprint.surround (Prims.of_int (2)) Prims.int_one
      FStar_Pprint.lbracket contents FStar_Pprint.rbracket
let (soft_brackets_with_nesting :
  FStar_Pprint.document -> FStar_Pprint.document) =
  fun contents ->
    FStar_Pprint.soft_surround (Prims.of_int (2)) Prims.int_one
      FStar_Pprint.lbracket contents FStar_Pprint.rbracket
let (soft_begin_end_with_nesting :
  FStar_Pprint.document -> FStar_Pprint.document) =
  fun contents ->
    let uu____713 = str "begin" in
    let uu____715 = str "end" in
    FStar_Pprint.soft_surround (Prims.of_int (2)) Prims.int_one uu____713
      contents uu____715
let separate_map_last :
  'uuuuuu728 .
    FStar_Pprint.document ->
      (Prims.bool -> 'uuuuuu728 -> FStar_Pprint.document) ->
        'uuuuuu728 Prims.list -> FStar_Pprint.document
  =
  fun sep ->
    fun f ->
      fun es ->
        let l = FStar_List.length es in
        let es1 =
          FStar_List.mapi (fun i -> fun e -> f (i <> (l - Prims.int_one)) e)
            es in
        FStar_Pprint.separate sep es1
let separate_break_map_last :
  'uuuuuu780 .
    FStar_Pprint.document ->
      (Prims.bool -> 'uuuuuu780 -> FStar_Pprint.document) ->
        'uuuuuu780 Prims.list -> FStar_Pprint.document
  =
  fun sep ->
    fun f ->
      fun l ->
        let uu____812 =
          let uu____813 =
            let uu____814 = FStar_Pprint.op_Hat_Hat sep break1 in
            FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____814 in
          separate_map_last uu____813 f l in
        FStar_Pprint.group uu____812
let separate_map_or_flow :
  'uuuuuu824 .
    FStar_Pprint.document ->
      ('uuuuuu824 -> FStar_Pprint.document) ->
        'uuuuuu824 Prims.list -> FStar_Pprint.document
  =
  fun sep ->
    fun f ->
      fun l ->
        if (FStar_List.length l) < (Prims.of_int (10))
        then FStar_Pprint.separate_map sep f l
        else FStar_Pprint.flow_map sep f l
let flow_map_last :
  'uuuuuu862 .
    FStar_Pprint.document ->
      (Prims.bool -> 'uuuuuu862 -> FStar_Pprint.document) ->
        'uuuuuu862 Prims.list -> FStar_Pprint.document
  =
  fun sep ->
    fun f ->
      fun es ->
        let l = FStar_List.length es in
        let es1 =
          FStar_List.mapi (fun i -> fun e -> f (i <> (l - Prims.int_one)) e)
            es in
        FStar_Pprint.flow sep es1
let separate_map_or_flow_last :
  'uuuuuu914 .
    FStar_Pprint.document ->
      (Prims.bool -> 'uuuuuu914 -> FStar_Pprint.document) ->
        'uuuuuu914 Prims.list -> FStar_Pprint.document
  =
  fun sep ->
    fun f ->
      fun l ->
        if (FStar_List.length l) < (Prims.of_int (10))
        then separate_map_last sep f l
        else flow_map_last sep f l
let (separate_or_flow :
  FStar_Pprint.document ->
    FStar_Pprint.document Prims.list -> FStar_Pprint.document)
  = fun sep -> fun l -> separate_map_or_flow sep FStar_Pervasives.id l
let (surround_maybe_empty :
  Prims.int ->
    Prims.int ->
      FStar_Pprint.document ->
        FStar_Pprint.document ->
          FStar_Pprint.document -> FStar_Pprint.document)
  =
  fun n ->
    fun b ->
      fun doc1 ->
        fun doc2 ->
          fun doc3 ->
            if doc2 = FStar_Pprint.empty
            then
              let uu____996 = FStar_Pprint.op_Hat_Slash_Hat doc1 doc3 in
              FStar_Pprint.group uu____996
            else FStar_Pprint.surround n b doc1 doc2 doc3
let soft_surround_separate_map :
  'uuuuuu1018 .
    Prims.int ->
      Prims.int ->
        FStar_Pprint.document ->
          FStar_Pprint.document ->
            FStar_Pprint.document ->
              FStar_Pprint.document ->
                ('uuuuuu1018 -> FStar_Pprint.document) ->
                  'uuuuuu1018 Prims.list -> FStar_Pprint.document
  =
  fun n ->
    fun b ->
      fun void_ ->
        fun opening ->
          fun sep ->
            fun closing ->
              fun f ->
                fun xs ->
                  if xs = []
                  then void_
                  else
                    (let uu____1077 = FStar_Pprint.separate_map sep f xs in
                     FStar_Pprint.soft_surround n b opening uu____1077
                       closing)
let soft_surround_map_or_flow :
  'uuuuuu1097 .
    Prims.int ->
      Prims.int ->
        FStar_Pprint.document ->
          FStar_Pprint.document ->
            FStar_Pprint.document ->
              FStar_Pprint.document ->
                ('uuuuuu1097 -> FStar_Pprint.document) ->
                  'uuuuuu1097 Prims.list -> FStar_Pprint.document
  =
  fun n ->
    fun b ->
      fun void_ ->
        fun opening ->
          fun sep ->
            fun closing ->
              fun f ->
                fun xs ->
                  if xs = []
                  then void_
                  else
                    (let uu____1156 = separate_map_or_flow sep f xs in
                     FStar_Pprint.soft_surround n b opening uu____1156
                       closing)
let (is_unit : FStar_Parser_AST.term -> Prims.bool) =
  fun e ->
    match e.FStar_Parser_AST.tm with
    | FStar_Parser_AST.Const (FStar_Const.Const_unit) -> true
    | uu____1166 -> false
let (matches_var : FStar_Parser_AST.term -> FStar_Ident.ident -> Prims.bool)
  =
  fun t ->
    fun x ->
      match t.FStar_Parser_AST.tm with
      | FStar_Parser_AST.Var y ->
          let uu____1182 = FStar_Ident.string_of_id x in
          let uu____1184 = FStar_Ident.string_of_lid y in
          uu____1182 = uu____1184
      | uu____1187 -> false
let (is_tuple_constructor : FStar_Ident.lident -> Prims.bool) =
  FStar_Parser_Const.is_tuple_data_lid'
let (is_dtuple_constructor : FStar_Ident.lident -> Prims.bool) =
  FStar_Parser_Const.is_dtuple_data_lid'
let (is_list_structure :
  FStar_Ident.lident ->
    FStar_Ident.lident -> FStar_Parser_AST.term -> Prims.bool)
  =
  fun cons_lid ->
    fun nil_lid ->
      let rec aux e =
        match e.FStar_Parser_AST.tm with
        | FStar_Parser_AST.Construct (lid, []) ->
            FStar_Ident.lid_equals lid nil_lid
        | FStar_Parser_AST.Construct (lid, uu____1238::(e2, uu____1240)::[])
            -> (FStar_Ident.lid_equals lid cons_lid) && (aux e2)
        | uu____1263 -> false in
      aux
let (is_list : FStar_Parser_AST.term -> Prims.bool) =
  is_list_structure FStar_Parser_Const.cons_lid FStar_Parser_Const.nil_lid
let (is_lex_list : FStar_Parser_AST.term -> Prims.bool) =
  is_list_structure FStar_Parser_Const.lexcons_lid
    FStar_Parser_Const.lextop_lid
let rec (extract_from_list :
  FStar_Parser_AST.term -> FStar_Parser_AST.term Prims.list) =
  fun e ->
    match e.FStar_Parser_AST.tm with
    | FStar_Parser_AST.Construct (uu____1287, []) -> []
    | FStar_Parser_AST.Construct
        (uu____1298,
         (e1, FStar_Parser_AST.Nothing)::(e2, FStar_Parser_AST.Nothing)::[])
        -> let uu____1319 = extract_from_list e2 in e1 :: uu____1319
    | uu____1322 ->
        let uu____1323 =
          let uu____1325 = FStar_Parser_AST.term_to_string e in
          FStar_Util.format1 "Not a list %s" uu____1325 in
        failwith uu____1323
let (is_array : FStar_Parser_AST.term -> Prims.bool) =
  fun e ->
    match e.FStar_Parser_AST.tm with
    | FStar_Parser_AST.App
        ({ FStar_Parser_AST.tm = FStar_Parser_AST.Var lid;
           FStar_Parser_AST.range = uu____1339;
           FStar_Parser_AST.level = uu____1340;_},
         l, FStar_Parser_AST.Nothing)
        ->
        (FStar_Ident.lid_equals lid FStar_Parser_Const.array_of_list_lid) &&
          (is_list l)
    | uu____1342 -> false
let rec (is_ref_set : FStar_Parser_AST.term -> Prims.bool) =
  fun e ->
    match e.FStar_Parser_AST.tm with
    | FStar_Parser_AST.Var maybe_empty_lid ->
        FStar_Ident.lid_equals maybe_empty_lid FStar_Parser_Const.set_empty
    | FStar_Parser_AST.App
        ({ FStar_Parser_AST.tm = FStar_Parser_AST.Var maybe_singleton_lid;
           FStar_Parser_AST.range = uu____1354;
           FStar_Parser_AST.level = uu____1355;_},
         {
           FStar_Parser_AST.tm = FStar_Parser_AST.App
             ({ FStar_Parser_AST.tm = FStar_Parser_AST.Var maybe_addr_of_lid;
                FStar_Parser_AST.range = uu____1357;
                FStar_Parser_AST.level = uu____1358;_},
              e1, FStar_Parser_AST.Nothing);
           FStar_Parser_AST.range = uu____1360;
           FStar_Parser_AST.level = uu____1361;_},
         FStar_Parser_AST.Nothing)
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
                FStar_Parser_AST.range = uu____1363;
                FStar_Parser_AST.level = uu____1364;_},
              e1, FStar_Parser_AST.Nothing);
           FStar_Parser_AST.range = uu____1366;
           FStar_Parser_AST.level = uu____1367;_},
         e2, FStar_Parser_AST.Nothing)
        ->
        ((FStar_Ident.lid_equals maybe_union_lid FStar_Parser_Const.set_union)
           && (is_ref_set e1))
          && (is_ref_set e2)
    | uu____1369 -> false
let rec (extract_from_ref_set :
  FStar_Parser_AST.term -> FStar_Parser_AST.term Prims.list) =
  fun e ->
    match e.FStar_Parser_AST.tm with
    | FStar_Parser_AST.Var uu____1381 -> []
    | FStar_Parser_AST.App
        ({ FStar_Parser_AST.tm = FStar_Parser_AST.Var uu____1382;
           FStar_Parser_AST.range = uu____1383;
           FStar_Parser_AST.level = uu____1384;_},
         {
           FStar_Parser_AST.tm = FStar_Parser_AST.App
             ({ FStar_Parser_AST.tm = FStar_Parser_AST.Var uu____1385;
                FStar_Parser_AST.range = uu____1386;
                FStar_Parser_AST.level = uu____1387;_},
              e1, FStar_Parser_AST.Nothing);
           FStar_Parser_AST.range = uu____1389;
           FStar_Parser_AST.level = uu____1390;_},
         FStar_Parser_AST.Nothing)
        -> [e1]
    | FStar_Parser_AST.App
        ({
           FStar_Parser_AST.tm = FStar_Parser_AST.App
             ({ FStar_Parser_AST.tm = FStar_Parser_AST.Var uu____1391;
                FStar_Parser_AST.range = uu____1392;
                FStar_Parser_AST.level = uu____1393;_},
              e1, FStar_Parser_AST.Nothing);
           FStar_Parser_AST.range = uu____1395;
           FStar_Parser_AST.level = uu____1396;_},
         e2, FStar_Parser_AST.Nothing)
        ->
        let uu____1398 = extract_from_ref_set e1 in
        let uu____1401 = extract_from_ref_set e2 in
        FStar_List.append uu____1398 uu____1401
    | uu____1404 ->
        let uu____1405 =
          let uu____1407 = FStar_Parser_AST.term_to_string e in
          FStar_Util.format1 "Not a ref set %s" uu____1407 in
        failwith uu____1405
let (is_general_application : FStar_Parser_AST.term -> Prims.bool) =
  fun e ->
    let uu____1419 = (is_array e) || (is_ref_set e) in
    Prims.op_Negation uu____1419
let (is_general_construction : FStar_Parser_AST.term -> Prims.bool) =
  fun e ->
    let uu____1428 = (is_list e) || (is_lex_list e) in
    Prims.op_Negation uu____1428
let (is_general_prefix_op : FStar_Ident.ident -> Prims.bool) =
  fun op ->
    let op_starting_char =
      let uu____1439 = FStar_Ident.string_of_id op in
      FStar_Util.char_at uu____1439 Prims.int_zero in
    ((op_starting_char = 33) || (op_starting_char = 63)) ||
      ((op_starting_char = 126) &&
         (let uu____1449 = FStar_Ident.string_of_id op in uu____1449 <> "~"))
let (head_and_args :
  FStar_Parser_AST.term ->
    (FStar_Parser_AST.term * (FStar_Parser_AST.term * FStar_Parser_AST.imp)
      Prims.list))
  =
  fun e ->
    let rec aux e1 acc =
      match e1.FStar_Parser_AST.tm with
      | FStar_Parser_AST.App (head, arg, imp) -> aux head ((arg, imp) :: acc)
      | uu____1519 -> (e1, acc) in
    aux e []
type associativity =
  | Left 
  | Right 
  | NonAssoc 
let (uu___is_Left : associativity -> Prims.bool) =
  fun projectee -> match projectee with | Left -> true | uu____1539 -> false
let (uu___is_Right : associativity -> Prims.bool) =
  fun projectee -> match projectee with | Right -> true | uu____1550 -> false
let (uu___is_NonAssoc : associativity -> Prims.bool) =
  fun projectee ->
    match projectee with | NonAssoc -> true | uu____1561 -> false
type token = (FStar_Char.char, Prims.string) FStar_Util.either
type associativity_level = (associativity * token Prims.list)
let (token_to_string :
  (FStar_BaseTypes.char, Prims.string) FStar_Util.either -> Prims.string) =
  fun uu___1_1587 ->
    match uu___1_1587 with
    | FStar_Util.Inl c -> Prims.op_Hat (FStar_Util.string_of_char c) ".*"
    | FStar_Util.Inr s -> s
let (matches_token :
  Prims.string ->
    (FStar_Char.char, Prims.string) FStar_Util.either -> Prims.bool)
  =
  fun s ->
    fun uu___2_1622 ->
      match uu___2_1622 with
      | FStar_Util.Inl c ->
          let uu____1635 = FStar_String.get s Prims.int_zero in
          uu____1635 = c
      | FStar_Util.Inr s' -> s = s'
let matches_level :
  'uuuuuu1651 .
    Prims.string ->
      ('uuuuuu1651 * (FStar_Char.char, Prims.string) FStar_Util.either
        Prims.list) -> Prims.bool
  =
  fun s ->
    fun uu____1675 ->
      match uu____1675 with
      | (assoc_levels, tokens) ->
          let uu____1707 = FStar_List.tryFind (matches_token s) tokens in
          uu____1707 <> FStar_Pervasives_Native.None
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
  let levels_from_associativity l uu___3_1879 =
    match uu___3_1879 with
    | Left -> (l, l, (l - Prims.int_one))
    | Right -> ((l - Prims.int_one), l, l)
    | NonAssoc -> ((l - Prims.int_one), l, (l - Prims.int_one)) in
  FStar_List.mapi
    (fun i ->
       fun uu____1929 ->
         match uu____1929 with
         | (assoc, tokens) -> ((levels_from_associativity i assoc), tokens))
    level_associativity_spec
let (assign_levels :
  associativity_level Prims.list ->
    Prims.string -> (Prims.int * Prims.int * Prims.int))
  =
  fun token_associativity_spec ->
    fun s ->
      let uu____2004 = FStar_List.tryFind (matches_level s) level_table in
      match uu____2004 with
      | FStar_Pervasives_Native.Some (assoc_levels, uu____2056) ->
          assoc_levels
      | uu____2094 -> failwith (Prims.op_Hat "Unrecognized operator " s)
let max_level :
  'uuuuuu2127 . ('uuuuuu2127 * token Prims.list) Prims.list -> Prims.int =
  fun l ->
    let find_level_and_max n level =
      let uu____2176 =
        FStar_List.tryFind
          (fun uu____2212 ->
             match uu____2212 with
             | (uu____2229, tokens) ->
                 tokens = (FStar_Pervasives_Native.snd level)) level_table in
      match uu____2176 with
      | FStar_Pervasives_Native.Some
          ((uu____2258, l1, uu____2260), uu____2261) -> max n l1
      | FStar_Pervasives_Native.None ->
          let uu____2311 =
            let uu____2313 =
              let uu____2315 =
                FStar_List.map token_to_string
                  (FStar_Pervasives_Native.snd level) in
              FStar_String.concat "," uu____2315 in
            FStar_Util.format1 "Undefined associativity level %s" uu____2313 in
          failwith uu____2311 in
    FStar_List.fold_left find_level_and_max Prims.int_zero l
let (levels : Prims.string -> (Prims.int * Prims.int * Prims.int)) =
  fun op ->
    let uu____2350 = assign_levels level_associativity_spec op in
    match uu____2350 with
    | (left, mine, right) ->
        if op = "*"
        then ((left - Prims.int_one), mine, right)
        else (left, mine, right)
let (operatorInfix0ad12 : associativity_level Prims.list) =
  [opinfix0a; opinfix0b; opinfix0c; opinfix0d; opinfix1; opinfix2]
let (is_operatorInfix0ad12 : FStar_Ident.ident -> Prims.bool) =
  fun op ->
    let uu____2409 =
      let uu____2412 =
        let uu____2418 = FStar_Ident.string_of_id op in
        FStar_All.pipe_left matches_level uu____2418 in
      FStar_List.tryFind uu____2412 operatorInfix0ad12 in
    uu____2409 <> FStar_Pervasives_Native.None
let (is_operatorInfix34 : FStar_Ident.ident -> Prims.bool) =
  let opinfix34 = [opinfix3; opinfix4] in
  fun op ->
    let uu____2485 =
      let uu____2500 =
        let uu____2518 = FStar_Ident.string_of_id op in
        FStar_All.pipe_left matches_level uu____2518 in
      FStar_List.tryFind uu____2500 opinfix34 in
    uu____2485 <> FStar_Pervasives_Native.None
let (handleable_args_length : FStar_Ident.ident -> Prims.int) =
  fun op ->
    let op_s = FStar_Ident.string_of_id op in
    let uu____2584 =
      (is_general_prefix_op op) || (FStar_List.mem op_s ["-"; "~"]) in
    if uu____2584
    then Prims.int_one
    else
      (let uu____2597 =
         ((is_operatorInfix0ad12 op) || (is_operatorInfix34 op)) ||
           (FStar_List.mem op_s
              ["<==>"; "==>"; "\\/"; "/\\"; "="; "|>"; ":="; ".()"; ".[]"]) in
       if uu____2597
       then (Prims.of_int (2))
       else
         if FStar_List.mem op_s [".()<-"; ".[]<-"]
         then (Prims.of_int (3))
         else Prims.int_zero)
let handleable_op :
  'uuuuuu2643 . FStar_Ident.ident -> 'uuuuuu2643 Prims.list -> Prims.bool =
  fun op ->
    fun args ->
      match FStar_List.length args with
      | uu____2659 when uu____2659 = Prims.int_zero -> true
      | uu____2661 when uu____2661 = Prims.int_one ->
          (is_general_prefix_op op) ||
            (let uu____2663 = FStar_Ident.string_of_id op in
             FStar_List.mem uu____2663 ["-"; "~"])
      | uu____2671 when uu____2671 = (Prims.of_int (2)) ->
          ((is_operatorInfix0ad12 op) || (is_operatorInfix34 op)) ||
            (let uu____2673 = FStar_Ident.string_of_id op in
             FStar_List.mem uu____2673
               ["<==>"; "==>"; "\\/"; "/\\"; "="; "|>"; ":="; ".()"; ".[]"])
      | uu____2695 when uu____2695 = (Prims.of_int (3)) ->
          let uu____2696 = FStar_Ident.string_of_id op in
          FStar_List.mem uu____2696 [".()<-"; ".[]<-"]
      | uu____2704 -> false
type annotation_style =
  | Binders of (Prims.int * Prims.int * Prims.bool) 
  | Arrows of (Prims.int * Prims.int) 
let (uu___is_Binders : annotation_style -> Prims.bool) =
  fun projectee ->
    match projectee with | Binders _0 -> true | uu____2750 -> false
let (__proj__Binders__item___0 :
  annotation_style -> (Prims.int * Prims.int * Prims.bool)) =
  fun projectee -> match projectee with | Binders _0 -> _0
let (uu___is_Arrows : annotation_style -> Prims.bool) =
  fun projectee ->
    match projectee with | Arrows _0 -> true | uu____2802 -> false
let (__proj__Arrows__item___0 : annotation_style -> (Prims.int * Prims.int))
  = fun projectee -> match projectee with | Arrows _0 -> _0
let (all_binders_annot : FStar_Parser_AST.term -> Prims.bool) =
  fun e ->
    let is_binder_annot b =
      match b.FStar_Parser_AST.b with
      | FStar_Parser_AST.Annotated uu____2844 -> true
      | uu____2850 -> false in
    let rec all_binders e1 l =
      match e1.FStar_Parser_AST.tm with
      | FStar_Parser_AST.Product (bs, tgt) ->
          let uu____2883 = FStar_List.for_all is_binder_annot bs in
          if uu____2883
          then all_binders tgt (l + (FStar_List.length bs))
          else (false, Prims.int_zero)
      | uu____2898 -> (true, (l + Prims.int_one)) in
    let uu____2903 = all_binders e Prims.int_zero in
    match uu____2903 with
    | (b, l) -> if b && (l > Prims.int_one) then true else false
type catf =
  FStar_Pprint.document -> FStar_Pprint.document -> FStar_Pprint.document
let (cat_with_colon :
  FStar_Pprint.document -> FStar_Pprint.document -> FStar_Pprint.document) =
  fun x ->
    fun y ->
      let uu____2942 = FStar_Pprint.op_Hat_Slash_Hat FStar_Pprint.colon y in
      FStar_Pprint.op_Hat_Hat x uu____2942
let (comment_stack :
  (Prims.string * FStar_Range.range) Prims.list FStar_ST.ref) =
  FStar_Util.mk_ref []
type decl_meta =
  {
  r: FStar_Range.range ;
  has_qs: Prims.bool ;
  has_attrs: Prims.bool }
let (__proj__Mkdecl_meta__item__r : decl_meta -> FStar_Range.range) =
  fun projectee -> match projectee with | { r; has_qs; has_attrs;_} -> r
let (__proj__Mkdecl_meta__item__has_qs : decl_meta -> Prims.bool) =
  fun projectee -> match projectee with | { r; has_qs; has_attrs;_} -> has_qs
let (__proj__Mkdecl_meta__item__has_attrs : decl_meta -> Prims.bool) =
  fun projectee ->
    match projectee with | { r; has_qs; has_attrs;_} -> has_attrs
let (dummy_meta : decl_meta) =
  { r = FStar_Range.dummyRange; has_qs = false; has_attrs = false }
let with_comment :
  'uuuuuu3031 .
    ('uuuuuu3031 -> FStar_Pprint.document) ->
      'uuuuuu3031 -> FStar_Range.range -> FStar_Pprint.document
  =
  fun printer ->
    fun tm ->
      fun tmrange ->
        let rec comments_before_pos acc print_pos lookahead_pos =
          let uu____3073 = FStar_ST.op_Bang comment_stack in
          match uu____3073 with
          | [] -> (acc, false)
          | (c, crange)::cs ->
              let comment =
                let uu____3144 = str c in
                FStar_Pprint.op_Hat_Hat uu____3144 FStar_Pprint.hardline in
              let uu____3145 = FStar_Range.range_before_pos crange print_pos in
              if uu____3145
              then
                (FStar_ST.op_Colon_Equals comment_stack cs;
                 (let uu____3187 = FStar_Pprint.op_Hat_Hat acc comment in
                  comments_before_pos uu____3187 print_pos lookahead_pos))
              else
                (let uu____3190 =
                   FStar_Range.range_before_pos crange lookahead_pos in
                 (acc, uu____3190)) in
        let uu____3193 =
          let uu____3199 =
            let uu____3200 = FStar_Range.start_of_range tmrange in
            FStar_Range.end_of_line uu____3200 in
          let uu____3201 = FStar_Range.end_of_range tmrange in
          comments_before_pos FStar_Pprint.empty uu____3199 uu____3201 in
        match uu____3193 with
        | (comments, has_lookahead) ->
            let printed_e = printer tm in
            let comments1 =
              if has_lookahead
              then
                let pos = FStar_Range.end_of_range tmrange in
                let uu____3210 = comments_before_pos comments pos pos in
                FStar_Pervasives_Native.fst uu____3210
              else comments in
            if comments1 = FStar_Pprint.empty
            then printed_e
            else
              (let uu____3222 = FStar_Pprint.op_Hat_Hat comments1 printed_e in
               FStar_Pprint.group uu____3222)
let with_comment_sep :
  'uuuuuu3234 'uuuuuu3235 .
    ('uuuuuu3234 -> 'uuuuuu3235) ->
      'uuuuuu3234 ->
        FStar_Range.range -> (FStar_Pprint.document * 'uuuuuu3235)
  =
  fun printer ->
    fun tm ->
      fun tmrange ->
        let rec comments_before_pos acc print_pos lookahead_pos =
          let uu____3281 = FStar_ST.op_Bang comment_stack in
          match uu____3281 with
          | [] -> (acc, false)
          | (c, crange)::cs ->
              let comment = str c in
              let uu____3352 = FStar_Range.range_before_pos crange print_pos in
              if uu____3352
              then
                (FStar_ST.op_Colon_Equals comment_stack cs;
                 (let uu____3394 =
                    if acc = FStar_Pprint.empty
                    then comment
                    else
                      (let uu____3398 =
                         FStar_Pprint.op_Hat_Hat FStar_Pprint.hardline
                           comment in
                       FStar_Pprint.op_Hat_Hat acc uu____3398) in
                  comments_before_pos uu____3394 print_pos lookahead_pos))
              else
                (let uu____3401 =
                   FStar_Range.range_before_pos crange lookahead_pos in
                 (acc, uu____3401)) in
        let uu____3404 =
          let uu____3410 =
            let uu____3411 = FStar_Range.start_of_range tmrange in
            FStar_Range.end_of_line uu____3411 in
          let uu____3412 = FStar_Range.end_of_range tmrange in
          comments_before_pos FStar_Pprint.empty uu____3410 uu____3412 in
        match uu____3404 with
        | (comments, has_lookahead) ->
            let printed_e = printer tm in
            let comments1 =
              if has_lookahead
              then
                let pos = FStar_Range.end_of_range tmrange in
                let uu____3425 = comments_before_pos comments pos pos in
                FStar_Pervasives_Native.fst uu____3425
              else comments in
            (comments1, printed_e)
let rec (place_comments_until_pos :
  Prims.int ->
    Prims.int ->
      FStar_Range.pos ->
        decl_meta ->
          FStar_Pprint.document ->
            Prims.bool -> Prims.bool -> FStar_Pprint.document)
  =
  fun k ->
    fun lbegin ->
      fun pos ->
        fun meta_decl ->
          fun doc ->
            fun r ->
              fun init ->
                let uu____3478 = FStar_ST.op_Bang comment_stack in
                match uu____3478 with
                | (comment, crange)::cs when
                    FStar_Range.range_before_pos crange pos ->
                    (FStar_ST.op_Colon_Equals comment_stack cs;
                     (let lnum =
                        let uu____3572 =
                          let uu____3574 =
                            let uu____3576 =
                              FStar_Range.start_of_range crange in
                            FStar_Range.line_of_pos uu____3576 in
                          uu____3574 - lbegin in
                        max k uu____3572 in
                      let lnum1 = min (Prims.of_int (2)) lnum in
                      let doc1 =
                        let uu____3581 =
                          let uu____3582 =
                            FStar_Pprint.repeat lnum1 FStar_Pprint.hardline in
                          let uu____3583 = str comment in
                          FStar_Pprint.op_Hat_Hat uu____3582 uu____3583 in
                        FStar_Pprint.op_Hat_Hat doc uu____3581 in
                      let uu____3584 =
                        let uu____3586 = FStar_Range.end_of_range crange in
                        FStar_Range.line_of_pos uu____3586 in
                      place_comments_until_pos Prims.int_one uu____3584 pos
                        meta_decl doc1 true init))
                | uu____3589 ->
                    if doc = FStar_Pprint.empty
                    then FStar_Pprint.empty
                    else
                      (let lnum =
                         let uu____3602 = FStar_Range.line_of_pos pos in
                         uu____3602 - lbegin in
                       let lnum1 = min (Prims.of_int (3)) lnum in
                       let lnum2 =
                         if meta_decl.has_qs || meta_decl.has_attrs
                         then lnum1 - Prims.int_one
                         else lnum1 in
                       let lnum3 = max k lnum2 in
                       let lnum4 =
                         if meta_decl.has_qs && meta_decl.has_attrs
                         then (Prims.of_int (2))
                         else lnum3 in
                       let lnum5 = if init then (Prims.of_int (2)) else lnum4 in
                       let uu____3630 =
                         FStar_Pprint.repeat lnum5 FStar_Pprint.hardline in
                       FStar_Pprint.op_Hat_Hat doc uu____3630)
let separate_map_with_comments :
  'uuuuuu3644 .
    FStar_Pprint.document ->
      FStar_Pprint.document ->
        ('uuuuuu3644 -> FStar_Pprint.document) ->
          'uuuuuu3644 Prims.list ->
            ('uuuuuu3644 -> decl_meta) -> FStar_Pprint.document
  =
  fun prefix ->
    fun sep ->
      fun f ->
        fun xs ->
          fun extract_meta ->
            let fold_fun uu____3703 x =
              match uu____3703 with
              | (last_line, doc) ->
                  let meta_decl = extract_meta x in
                  let r = meta_decl.r in
                  let doc1 =
                    let uu____3722 = FStar_Range.start_of_range r in
                    place_comments_until_pos Prims.int_one last_line
                      uu____3722 meta_decl doc false false in
                  let uu____3726 =
                    let uu____3728 = FStar_Range.end_of_range r in
                    FStar_Range.line_of_pos uu____3728 in
                  let uu____3729 =
                    let uu____3730 =
                      let uu____3731 = f x in
                      FStar_Pprint.op_Hat_Hat sep uu____3731 in
                    FStar_Pprint.op_Hat_Hat doc1 uu____3730 in
                  (uu____3726, uu____3729) in
            let uu____3733 =
              let uu____3740 = FStar_List.hd xs in
              let uu____3741 = FStar_List.tl xs in (uu____3740, uu____3741) in
            match uu____3733 with
            | (x, xs1) ->
                let init =
                  let meta_decl = extract_meta x in
                  let uu____3759 =
                    let uu____3761 = FStar_Range.end_of_range meta_decl.r in
                    FStar_Range.line_of_pos uu____3761 in
                  let uu____3762 =
                    let uu____3763 = f x in
                    FStar_Pprint.op_Hat_Hat prefix uu____3763 in
                  (uu____3759, uu____3762) in
                let uu____3765 = FStar_List.fold_left fold_fun init xs1 in
                FStar_Pervasives_Native.snd uu____3765
let separate_map_with_comments_kw :
  'uuuuuu3792 'uuuuuu3793 .
    'uuuuuu3792 ->
      'uuuuuu3792 ->
        ('uuuuuu3792 -> 'uuuuuu3793 -> FStar_Pprint.document) ->
          'uuuuuu3793 Prims.list ->
            ('uuuuuu3793 -> decl_meta) -> FStar_Pprint.document
  =
  fun prefix ->
    fun sep ->
      fun f ->
        fun xs ->
          fun extract_meta ->
            let fold_fun uu____3857 x =
              match uu____3857 with
              | (last_line, doc) ->
                  let meta_decl = extract_meta x in
                  let r = meta_decl.r in
                  let doc1 =
                    let uu____3876 = FStar_Range.start_of_range r in
                    place_comments_until_pos Prims.int_one last_line
                      uu____3876 meta_decl doc false false in
                  let uu____3880 =
                    let uu____3882 = FStar_Range.end_of_range r in
                    FStar_Range.line_of_pos uu____3882 in
                  let uu____3883 =
                    let uu____3884 = f sep x in
                    FStar_Pprint.op_Hat_Hat doc1 uu____3884 in
                  (uu____3880, uu____3883) in
            let uu____3886 =
              let uu____3893 = FStar_List.hd xs in
              let uu____3894 = FStar_List.tl xs in (uu____3893, uu____3894) in
            match uu____3886 with
            | (x, xs1) ->
                let init =
                  let meta_decl = extract_meta x in
                  let uu____3912 =
                    let uu____3914 = FStar_Range.end_of_range meta_decl.r in
                    FStar_Range.line_of_pos uu____3914 in
                  let uu____3915 = f prefix x in (uu____3912, uu____3915) in
                let uu____3917 = FStar_List.fold_left fold_fun init xs1 in
                FStar_Pervasives_Native.snd uu____3917
let rec (p_decl : FStar_Parser_AST.decl -> FStar_Pprint.document) =
  fun d ->
    let qualifiers =
      match ((d.FStar_Parser_AST.quals), (d.FStar_Parser_AST.d)) with
      | ((FStar_Parser_AST.Assumption)::[], FStar_Parser_AST.Assume
         (id, uu____4873)) ->
          let uu____4876 =
            let uu____4878 =
              let uu____4880 = FStar_Ident.string_of_id id in
              FStar_Util.char_at uu____4880 Prims.int_zero in
            FStar_All.pipe_right uu____4878 FStar_Util.is_upper in
          if uu____4876
          then
            let uu____4886 = p_qualifier FStar_Parser_AST.Assumption in
            FStar_Pprint.op_Hat_Hat uu____4886 FStar_Pprint.space
          else p_qualifiers d.FStar_Parser_AST.quals
      | uu____4889 -> p_qualifiers d.FStar_Parser_AST.quals in
    let uu____4896 = p_attributes d.FStar_Parser_AST.attrs in
    let uu____4897 =
      let uu____4898 = p_rawDecl d in
      FStar_Pprint.op_Hat_Hat qualifiers uu____4898 in
    FStar_Pprint.op_Hat_Hat uu____4896 uu____4897
and (p_attributes : FStar_Parser_AST.attributes_ -> FStar_Pprint.document) =
  fun attrs ->
    match attrs with
    | [] -> FStar_Pprint.empty
    | uu____4900 ->
        let uu____4901 =
          let uu____4902 = str "@@ " in
          let uu____4904 =
            let uu____4905 =
              let uu____4906 =
                let uu____4907 =
                  let uu____4908 = str "; " in
                  let uu____4910 =
                    FStar_List.map (p_noSeqTermAndComment false false) attrs in
                  FStar_Pprint.flow uu____4908 uu____4910 in
                FStar_Pprint.op_Hat_Hat uu____4907 FStar_Pprint.rbracket in
              FStar_Pprint.align uu____4906 in
            FStar_Pprint.op_Hat_Hat uu____4905 FStar_Pprint.hardline in
          FStar_Pprint.op_Hat_Hat uu____4902 uu____4904 in
        FStar_Pprint.op_Hat_Hat FStar_Pprint.lbracket uu____4901
and (p_justSig : FStar_Parser_AST.decl -> FStar_Pprint.document) =
  fun d ->
    match d.FStar_Parser_AST.d with
    | FStar_Parser_AST.Val (lid, t) ->
        let uu____4918 =
          let uu____4919 = str "val" in
          let uu____4921 =
            let uu____4922 =
              let uu____4923 = p_lident lid in
              let uu____4924 =
                FStar_Pprint.op_Hat_Hat FStar_Pprint.space FStar_Pprint.colon in
              FStar_Pprint.op_Hat_Hat uu____4923 uu____4924 in
            FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____4922 in
          FStar_Pprint.op_Hat_Hat uu____4919 uu____4921 in
        let uu____4925 = p_typ false false t in
        FStar_Pprint.op_Hat_Hat uu____4918 uu____4925
    | FStar_Parser_AST.TopLevelLet (uu____4928, lbs) ->
        FStar_Pprint.separate_map FStar_Pprint.hardline
          (fun lb ->
             let uu____4953 =
               let uu____4954 = str "let" in p_letlhs uu____4954 lb false in
             FStar_Pprint.group uu____4953) lbs
    | uu____4957 -> FStar_Pprint.empty
and (p_list :
  (FStar_Ident.ident -> FStar_Pprint.document) ->
    FStar_Pprint.document ->
      FStar_Ident.ident Prims.list -> FStar_Pprint.document)
  =
  fun f ->
    fun sep ->
      fun l ->
        let rec p_list' uu___4_4972 =
          match uu___4_4972 with
          | [] -> FStar_Pprint.empty
          | x::[] -> f x
          | x::xs ->
              let uu____4980 = f x in
              let uu____4981 =
                let uu____4982 = p_list' xs in
                FStar_Pprint.op_Hat_Hat sep uu____4982 in
              FStar_Pprint.op_Hat_Hat uu____4980 uu____4981 in
        let uu____4983 = str "[" in
        let uu____4985 =
          let uu____4986 = p_list' l in
          let uu____4987 = str "]" in
          FStar_Pprint.op_Hat_Hat uu____4986 uu____4987 in
        FStar_Pprint.op_Hat_Hat uu____4983 uu____4985
and (p_rawDecl : FStar_Parser_AST.decl -> FStar_Pprint.document) =
  fun d ->
    match d.FStar_Parser_AST.d with
    | FStar_Parser_AST.Open uid ->
        let uu____4991 =
          let uu____4992 = str "open" in
          let uu____4994 = p_quident uid in
          FStar_Pprint.op_Hat_Slash_Hat uu____4992 uu____4994 in
        FStar_Pprint.group uu____4991
    | FStar_Parser_AST.Include uid ->
        let uu____4996 =
          let uu____4997 = str "include" in
          let uu____4999 = p_quident uid in
          FStar_Pprint.op_Hat_Slash_Hat uu____4997 uu____4999 in
        FStar_Pprint.group uu____4996
    | FStar_Parser_AST.Friend uid ->
        let uu____5001 =
          let uu____5002 = str "friend" in
          let uu____5004 = p_quident uid in
          FStar_Pprint.op_Hat_Slash_Hat uu____5002 uu____5004 in
        FStar_Pprint.group uu____5001
    | FStar_Parser_AST.ModuleAbbrev (uid1, uid2) ->
        let uu____5007 =
          let uu____5008 = str "module" in
          let uu____5010 =
            let uu____5011 =
              let uu____5012 = p_uident uid1 in
              let uu____5013 =
                FStar_Pprint.op_Hat_Hat FStar_Pprint.space
                  FStar_Pprint.equals in
              FStar_Pprint.op_Hat_Hat uu____5012 uu____5013 in
            FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____5011 in
          FStar_Pprint.op_Hat_Hat uu____5008 uu____5010 in
        let uu____5014 = p_quident uid2 in
        op_Hat_Slash_Plus_Hat uu____5007 uu____5014
    | FStar_Parser_AST.TopLevelModule uid ->
        let uu____5016 =
          let uu____5017 = str "module" in
          let uu____5019 =
            let uu____5020 = p_quident uid in
            FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____5020 in
          FStar_Pprint.op_Hat_Hat uu____5017 uu____5019 in
        FStar_Pprint.group uu____5016
    | FStar_Parser_AST.Tycon
        (true, uu____5021, (FStar_Parser_AST.TyconAbbrev
         (uid, tpars, FStar_Pervasives_Native.None, t))::[])
        ->
        let effect_prefix_doc =
          let uu____5038 = str "effect" in
          let uu____5040 =
            let uu____5041 = p_uident uid in
            FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____5041 in
          FStar_Pprint.op_Hat_Hat uu____5038 uu____5040 in
        let uu____5042 =
          let uu____5043 = p_typars tpars in
          FStar_Pprint.surround (Prims.of_int (2)) Prims.int_one
            effect_prefix_doc uu____5043 FStar_Pprint.equals in
        let uu____5046 = p_typ false false t in
        op_Hat_Slash_Plus_Hat uu____5042 uu____5046
    | FStar_Parser_AST.Tycon (false, tc, tcdefs) ->
        let s = if tc then str "class" else str "type" in
        let uu____5065 =
          let uu____5066 = FStar_List.hd tcdefs in
          p_typeDeclWithKw s uu____5066 in
        let uu____5067 =
          let uu____5068 = FStar_List.tl tcdefs in
          FStar_All.pipe_left
            (FStar_Pprint.concat_map
               (fun x ->
                  let uu____5076 =
                    let uu____5077 = str "and" in
                    p_typeDeclWithKw uu____5077 x in
                  FStar_Pprint.op_Hat_Hat break1 uu____5076)) uu____5068 in
        FStar_Pprint.op_Hat_Hat uu____5065 uu____5067
    | FStar_Parser_AST.TopLevelLet (q, lbs) ->
        let let_doc =
          let uu____5094 = str "let" in
          let uu____5096 = p_letqualifier q in
          FStar_Pprint.op_Hat_Hat uu____5094 uu____5096 in
        let uu____5097 = str "and" in
        separate_map_with_comments_kw let_doc uu____5097 p_letbinding lbs
          (fun uu____5107 ->
             match uu____5107 with
             | (p, t) ->
                 let uu____5114 =
                   FStar_Range.union_ranges p.FStar_Parser_AST.prange
                     t.FStar_Parser_AST.range in
                 { r = uu____5114; has_qs = false; has_attrs = false })
    | FStar_Parser_AST.Val (lid, t) ->
        let uu____5119 =
          let uu____5120 = str "val" in
          let uu____5122 =
            let uu____5123 =
              let uu____5124 = p_lident lid in
              let uu____5125 = sig_as_binders_if_possible t false in
              FStar_Pprint.op_Hat_Hat uu____5124 uu____5125 in
            FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____5123 in
          FStar_Pprint.op_Hat_Hat uu____5120 uu____5122 in
        FStar_All.pipe_left FStar_Pprint.group uu____5119
    | FStar_Parser_AST.Assume (id, t) ->
        let decl_keyword =
          let uu____5130 =
            let uu____5132 =
              let uu____5134 = FStar_Ident.string_of_id id in
              FStar_Util.char_at uu____5134 Prims.int_zero in
            FStar_All.pipe_right uu____5132 FStar_Util.is_upper in
          if uu____5130
          then FStar_Pprint.empty
          else
            (let uu____5142 = str "val" in
             FStar_Pprint.op_Hat_Hat uu____5142 FStar_Pprint.space) in
        let uu____5144 =
          let uu____5145 = p_ident id in
          let uu____5146 =
            let uu____5147 =
              let uu____5148 =
                let uu____5149 = p_typ false false t in
                FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____5149 in
              FStar_Pprint.op_Hat_Hat FStar_Pprint.colon uu____5148 in
            FStar_Pprint.group uu____5147 in
          FStar_Pprint.op_Hat_Hat uu____5145 uu____5146 in
        FStar_Pprint.op_Hat_Hat decl_keyword uu____5144
    | FStar_Parser_AST.Exception (uid, t_opt) ->
        let uu____5158 = str "exception" in
        let uu____5160 =
          let uu____5161 =
            let uu____5162 = p_uident uid in
            let uu____5163 =
              FStar_Pprint.optional
                (fun t ->
                   let uu____5167 =
                     let uu____5168 = str "of" in
                     let uu____5170 = p_typ false false t in
                     op_Hat_Slash_Plus_Hat uu____5168 uu____5170 in
                   FStar_Pprint.op_Hat_Hat break1 uu____5167) t_opt in
            FStar_Pprint.op_Hat_Hat uu____5162 uu____5163 in
          FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____5161 in
        FStar_Pprint.op_Hat_Hat uu____5158 uu____5160
    | FStar_Parser_AST.NewEffect ne ->
        let uu____5174 = str "new_effect" in
        let uu____5176 =
          let uu____5177 = p_newEffect ne in
          FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____5177 in
        FStar_Pprint.op_Hat_Hat uu____5174 uu____5176
    | FStar_Parser_AST.SubEffect se ->
        let uu____5179 = str "sub_effect" in
        let uu____5181 =
          let uu____5182 = p_subEffect se in
          FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____5182 in
        FStar_Pprint.op_Hat_Hat uu____5179 uu____5181
    | FStar_Parser_AST.LayeredEffect ne ->
        let uu____5184 = str "layered_effect" in
        let uu____5186 =
          let uu____5187 = p_newEffect ne in
          FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____5187 in
        FStar_Pprint.op_Hat_Hat uu____5184 uu____5186
    | FStar_Parser_AST.Polymonadic_bind (l1, l2, l3, t) ->
        let uu____5192 = str "polymonadic_bind" in
        let uu____5194 =
          let uu____5195 =
            let uu____5196 = p_quident l1 in
            let uu____5197 =
              let uu____5198 =
                let uu____5199 =
                  let uu____5200 = p_quident l2 in
                  let uu____5201 =
                    let uu____5202 =
                      let uu____5203 = str "|>" in
                      let uu____5205 =
                        let uu____5206 = p_quident l3 in
                        let uu____5207 =
                          let uu____5208 = p_simpleTerm false false t in
                          FStar_Pprint.op_Hat_Hat FStar_Pprint.equals
                            uu____5208 in
                        FStar_Pprint.op_Hat_Hat uu____5206 uu____5207 in
                      FStar_Pprint.op_Hat_Hat uu____5203 uu____5205 in
                    FStar_Pprint.op_Hat_Hat FStar_Pprint.rparen uu____5202 in
                  FStar_Pprint.op_Hat_Hat uu____5200 uu____5201 in
                FStar_Pprint.op_Hat_Hat break1 uu____5199 in
              FStar_Pprint.op_Hat_Hat FStar_Pprint.comma uu____5198 in
            FStar_Pprint.op_Hat_Hat uu____5196 uu____5197 in
          FStar_Pprint.op_Hat_Hat FStar_Pprint.lparen uu____5195 in
        FStar_Pprint.op_Hat_Hat uu____5192 uu____5194
    | FStar_Parser_AST.Pragma p -> p_pragma p
    | FStar_Parser_AST.Tycon (true, uu____5212, uu____5213) ->
        failwith
          "Effect abbreviation is expected to be defined by an abbreviation"
    | FStar_Parser_AST.Splice (ids, t) ->
        let uu____5229 = str "%splice" in
        let uu____5231 =
          let uu____5232 =
            let uu____5233 = str ";" in p_list p_uident uu____5233 ids in
          let uu____5235 =
            let uu____5236 = p_term false false t in
            FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____5236 in
          FStar_Pprint.op_Hat_Hat uu____5232 uu____5235 in
        FStar_Pprint.op_Hat_Hat uu____5229 uu____5231
and (p_pragma : FStar_Parser_AST.pragma -> FStar_Pprint.document) =
  fun uu___5_5239 ->
    match uu___5_5239 with
    | FStar_Parser_AST.SetOptions s ->
        let uu____5242 = str "#set-options" in
        let uu____5244 =
          let uu____5245 =
            let uu____5246 = str s in FStar_Pprint.dquotes uu____5246 in
          FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____5245 in
        FStar_Pprint.op_Hat_Hat uu____5242 uu____5244
    | FStar_Parser_AST.ResetOptions s_opt ->
        let uu____5251 = str "#reset-options" in
        let uu____5253 =
          FStar_Pprint.optional
            (fun s ->
               let uu____5259 =
                 let uu____5260 = str s in FStar_Pprint.dquotes uu____5260 in
               FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____5259) s_opt in
        FStar_Pprint.op_Hat_Hat uu____5251 uu____5253
    | FStar_Parser_AST.PushOptions s_opt ->
        let uu____5265 = str "#push-options" in
        let uu____5267 =
          FStar_Pprint.optional
            (fun s ->
               let uu____5273 =
                 let uu____5274 = str s in FStar_Pprint.dquotes uu____5274 in
               FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____5273) s_opt in
        FStar_Pprint.op_Hat_Hat uu____5265 uu____5267
    | FStar_Parser_AST.PopOptions -> str "#pop-options"
    | FStar_Parser_AST.RestartSolver -> str "#restart-solver"
    | FStar_Parser_AST.LightOff ->
        (FStar_ST.op_Colon_Equals should_print_fs_typ_app true;
         str "#light \"off\"")
and (p_typars : FStar_Parser_AST.binder Prims.list -> FStar_Pprint.document)
  = fun bs -> p_binders true bs
and (p_typeDeclWithKw :
  FStar_Pprint.document -> FStar_Parser_AST.tycon -> FStar_Pprint.document) =
  fun kw ->
    fun typedecl ->
      let uu____5307 = p_typeDecl kw typedecl in
      match uu____5307 with
      | (comm, decl, body, pre) ->
          if comm = FStar_Pprint.empty
          then
            let uu____5330 = pre body in
            FStar_Pprint.op_Hat_Hat decl uu____5330
          else
            (let uu____5333 =
               let uu____5334 =
                 let uu____5335 =
                   let uu____5336 = pre body in
                   FStar_Pprint.op_Hat_Slash_Hat uu____5336 comm in
                 FStar_Pprint.op_Hat_Hat decl uu____5335 in
               let uu____5337 =
                 let uu____5338 =
                   let uu____5339 =
                     let uu____5340 =
                       let uu____5341 =
                         FStar_Pprint.op_Hat_Hat FStar_Pprint.hardline body in
                       FStar_Pprint.op_Hat_Hat comm uu____5341 in
                     FStar_Pprint.op_Hat_Hat FStar_Pprint.hardline uu____5340 in
                   FStar_Pprint.nest (Prims.of_int (2)) uu____5339 in
                 FStar_Pprint.op_Hat_Hat decl uu____5338 in
               FStar_Pprint.ifflat uu____5334 uu____5337 in
             FStar_All.pipe_left FStar_Pprint.group uu____5333)
and (p_typeDecl :
  FStar_Pprint.document ->
    FStar_Parser_AST.tycon ->
      (FStar_Pprint.document * FStar_Pprint.document * FStar_Pprint.document
        * (FStar_Pprint.document -> FStar_Pprint.document)))
  =
  fun pre ->
    fun uu___6_5344 ->
      match uu___6_5344 with
      | FStar_Parser_AST.TyconAbstract (lid, bs, typ_opt) ->
          let uu____5367 = p_typeDeclPrefix pre false lid bs typ_opt in
          (FStar_Pprint.empty, uu____5367, FStar_Pprint.empty,
            FStar_Pervasives.id)
      | FStar_Parser_AST.TyconAbbrev (lid, bs, typ_opt, t) ->
          let uu____5384 = p_typ_sep false false t in
          (match uu____5384 with
           | (comm, doc) ->
               let uu____5404 = p_typeDeclPrefix pre true lid bs typ_opt in
               (comm, uu____5404, doc, jump2))
      | FStar_Parser_AST.TyconRecord (lid, bs, typ_opt, record_field_decls)
          ->
          let p_recordField ps uu____5448 =
            match uu____5448 with
            | (lid1, t) ->
                let uu____5456 =
                  let uu____5461 =
                    FStar_Range.extend_to_end_of_line
                      t.FStar_Parser_AST.range in
                  with_comment_sep (p_recordFieldDecl ps) (lid1, t)
                    uu____5461 in
                (match uu____5456 with
                 | (comm, field) ->
                     let sep =
                       if ps then FStar_Pprint.semi else FStar_Pprint.empty in
                     inline_comment_or_above comm field sep) in
          let p_fields =
            let uu____5473 =
              separate_map_last FStar_Pprint.hardline p_recordField
                record_field_decls in
            braces_with_nesting uu____5473 in
          let uu____5478 = p_typeDeclPrefix pre true lid bs typ_opt in
          (FStar_Pprint.empty, uu____5478, p_fields,
            ((fun d -> FStar_Pprint.op_Hat_Hat FStar_Pprint.space d)))
      | FStar_Parser_AST.TyconVariant (lid, bs, typ_opt, ct_decls) ->
          let p_constructorBranchAndComments uu____5533 =
            match uu____5533 with
            | (uid, t_opt, use_of) ->
                let range =
                  let uu____5553 =
                    let uu____5554 = FStar_Ident.range_of_id uid in
                    let uu____5555 =
                      FStar_Util.map_opt t_opt
                        (fun t -> t.FStar_Parser_AST.range) in
                    FStar_Util.dflt uu____5554 uu____5555 in
                  FStar_Range.extend_to_end_of_line uu____5553 in
                let uu____5560 =
                  with_comment_sep p_constructorBranch (uid, t_opt, use_of)
                    range in
                (match uu____5560 with
                 | (comm, ctor) ->
                     inline_comment_or_above comm ctor FStar_Pprint.empty) in
          let datacon_doc =
            FStar_Pprint.separate_map FStar_Pprint.hardline
              p_constructorBranchAndComments ct_decls in
          let uu____5589 = p_typeDeclPrefix pre true lid bs typ_opt in
          (FStar_Pprint.empty, uu____5589, datacon_doc, jump2)
and (p_typeDeclPrefix :
  FStar_Pprint.document ->
    Prims.bool ->
      FStar_Ident.ident ->
        FStar_Parser_AST.binder Prims.list ->
          FStar_Parser_AST.knd FStar_Pervasives_Native.option ->
            FStar_Pprint.document)
  =
  fun kw ->
    fun eq ->
      fun lid ->
        fun bs ->
          fun typ_opt ->
            let with_kw cont =
              let lid_doc = p_ident lid in
              let kw_lid =
                let uu____5617 = FStar_Pprint.op_Hat_Slash_Hat kw lid_doc in
                FStar_Pprint.group uu____5617 in
              cont kw_lid in
            let typ =
              let maybe_eq =
                if eq then FStar_Pprint.equals else FStar_Pprint.empty in
              match typ_opt with
              | FStar_Pervasives_Native.None -> maybe_eq
              | FStar_Pervasives_Native.Some t ->
                  let uu____5624 =
                    let uu____5625 =
                      let uu____5626 = p_typ false false t in
                      FStar_Pprint.op_Hat_Slash_Hat uu____5626 maybe_eq in
                    FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____5625 in
                  FStar_Pprint.op_Hat_Hat FStar_Pprint.colon uu____5624 in
            if bs = []
            then with_kw (fun n -> prefix2 n typ)
            else
              (let binders = p_binders_list true bs in
               with_kw
                 (fun n ->
                    let uu____5646 =
                      let uu____5647 = FStar_Pprint.flow break1 binders in
                      prefix2 n uu____5647 in
                    prefix2 uu____5646 typ))
and (p_recordFieldDecl :
  Prims.bool ->
    (FStar_Ident.ident * FStar_Parser_AST.term) -> FStar_Pprint.document)
  =
  fun ps ->
    fun uu____5649 ->
      match uu____5649 with
      | (lid, t) ->
          let uu____5657 =
            let uu____5658 = p_lident lid in
            let uu____5659 =
              let uu____5660 = p_typ ps false t in
              FStar_Pprint.op_Hat_Hat FStar_Pprint.colon uu____5660 in
            FStar_Pprint.op_Hat_Hat uu____5658 uu____5659 in
          FStar_Pprint.group uu____5657
and (p_constructorBranch :
  (FStar_Ident.ident * FStar_Parser_AST.term FStar_Pervasives_Native.option *
    Prims.bool) -> FStar_Pprint.document)
  =
  fun uu____5662 ->
    match uu____5662 with
    | (uid, t_opt, use_of) ->
        let sep = if use_of then str "of" else FStar_Pprint.colon in
        let uid_doc =
          let uu____5687 =
            let uu____5688 =
              let uu____5689 = p_uident uid in
              FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____5689 in
            FStar_Pprint.op_Hat_Hat FStar_Pprint.bar uu____5688 in
          FStar_Pprint.group uu____5687 in
        default_or_map uid_doc
          (fun t ->
             let uu____5693 =
               let uu____5694 =
                 let uu____5695 =
                   let uu____5696 =
                     let uu____5697 = p_typ false false t in
                     FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____5697 in
                   FStar_Pprint.op_Hat_Hat sep uu____5696 in
                 FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____5695 in
               FStar_Pprint.op_Hat_Hat uid_doc uu____5694 in
             FStar_Pprint.group uu____5693) t_opt
and (p_letlhs :
  FStar_Pprint.document ->
    (FStar_Parser_AST.pattern * FStar_Parser_AST.term) ->
      Prims.bool -> FStar_Pprint.document)
  =
  fun kw ->
    fun uu____5701 ->
      fun inner_let ->
        match uu____5701 with
        | (pat, uu____5709) ->
            let uu____5710 =
              match pat.FStar_Parser_AST.pat with
              | FStar_Parser_AST.PatAscribed
                  (pat1, (t, FStar_Pervasives_Native.None)) ->
                  (pat1,
                    (FStar_Pervasives_Native.Some (t, FStar_Pprint.empty)))
              | FStar_Parser_AST.PatAscribed
                  (pat1, (t, FStar_Pervasives_Native.Some tac)) ->
                  let uu____5762 =
                    let uu____5769 =
                      let uu____5774 =
                        let uu____5775 =
                          let uu____5776 =
                            let uu____5777 = str "by" in
                            let uu____5779 =
                              let uu____5780 =
                                p_atomicTerm (maybe_unthunk tac) in
                              FStar_Pprint.op_Hat_Hat FStar_Pprint.space
                                uu____5780 in
                            FStar_Pprint.op_Hat_Hat uu____5777 uu____5779 in
                          FStar_Pprint.op_Hat_Hat FStar_Pprint.space
                            uu____5776 in
                        FStar_Pprint.group uu____5775 in
                      (t, uu____5774) in
                    FStar_Pervasives_Native.Some uu____5769 in
                  (pat1, uu____5762)
              | uu____5791 -> (pat, FStar_Pervasives_Native.None) in
            (match uu____5710 with
             | (pat1, ascr) ->
                 (match pat1.FStar_Parser_AST.pat with
                  | FStar_Parser_AST.PatApp
                      ({
                         FStar_Parser_AST.pat = FStar_Parser_AST.PatVar
                           (lid, uu____5817);
                         FStar_Parser_AST.prange = uu____5818;_},
                       pats)
                      ->
                      let ascr_doc =
                        match ascr with
                        | FStar_Pervasives_Native.Some (t, tac) ->
                            let uu____5835 =
                              sig_as_binders_if_possible t true in
                            FStar_Pprint.op_Hat_Hat uu____5835 tac
                        | FStar_Pervasives_Native.None -> FStar_Pprint.empty in
                      let uu____5841 =
                        if inner_let
                        then
                          let uu____5855 = pats_as_binders_if_possible pats in
                          match uu____5855 with
                          | (bs, style) ->
                              ((FStar_List.append bs [ascr_doc]), style)
                        else
                          (let uu____5878 = pats_as_binders_if_possible pats in
                           match uu____5878 with
                           | (bs, style) ->
                               ((FStar_List.append bs [ascr_doc]), style)) in
                      (match uu____5841 with
                       | (terms, style) ->
                           let uu____5905 =
                             let uu____5906 =
                               let uu____5907 =
                                 let uu____5908 = p_lident lid in
                                 let uu____5909 =
                                   format_sig style terms true true in
                                 FStar_Pprint.op_Hat_Hat uu____5908
                                   uu____5909 in
                               FStar_Pprint.op_Hat_Hat FStar_Pprint.space
                                 uu____5907 in
                             FStar_Pprint.op_Hat_Hat kw uu____5906 in
                           FStar_All.pipe_left FStar_Pprint.group uu____5905)
                  | uu____5912 ->
                      let ascr_doc =
                        match ascr with
                        | FStar_Pervasives_Native.Some (t, tac) ->
                            let uu____5920 =
                              let uu____5921 =
                                let uu____5922 =
                                  p_typ_top
                                    (Arrows
                                       ((Prims.of_int (2)),
                                         (Prims.of_int (2)))) false false t in
                                FStar_Pprint.op_Hat_Hat FStar_Pprint.colon
                                  uu____5922 in
                              FStar_Pprint.group uu____5921 in
                            FStar_Pprint.op_Hat_Hat uu____5920 tac
                        | FStar_Pervasives_Native.None -> FStar_Pprint.empty in
                      let uu____5933 =
                        let uu____5934 =
                          let uu____5935 =
                            let uu____5936 = p_tuplePattern pat1 in
                            FStar_Pprint.op_Hat_Slash_Hat kw uu____5936 in
                          FStar_Pprint.group uu____5935 in
                        FStar_Pprint.op_Hat_Hat uu____5934 ascr_doc in
                      FStar_Pprint.group uu____5933))
and (p_letbinding :
  FStar_Pprint.document ->
    (FStar_Parser_AST.pattern * FStar_Parser_AST.term) ->
      FStar_Pprint.document)
  =
  fun kw ->
    fun uu____5938 ->
      match uu____5938 with
      | (pat, e) ->
          let doc_pat = p_letlhs kw (pat, e) false in
          let uu____5947 = p_term_sep false false e in
          (match uu____5947 with
           | (comm, doc_expr) ->
               let doc_expr1 =
                 inline_comment_or_above comm doc_expr FStar_Pprint.empty in
               let uu____5957 =
                 let uu____5958 =
                   FStar_Pprint.op_Hat_Slash_Hat FStar_Pprint.equals
                     doc_expr1 in
                 FStar_Pprint.op_Hat_Slash_Hat doc_pat uu____5958 in
               let uu____5959 =
                 let uu____5960 =
                   let uu____5961 =
                     let uu____5962 =
                       let uu____5963 = jump2 doc_expr1 in
                       FStar_Pprint.op_Hat_Hat FStar_Pprint.equals uu____5963 in
                     FStar_Pprint.group uu____5962 in
                   FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____5961 in
                 FStar_Pprint.op_Hat_Hat doc_pat uu____5960 in
               FStar_Pprint.ifflat uu____5957 uu____5959)
and (p_newEffect : FStar_Parser_AST.effect_decl -> FStar_Pprint.document) =
  fun uu___7_5964 ->
    match uu___7_5964 with
    | FStar_Parser_AST.RedefineEffect (lid, bs, t) ->
        p_effectRedefinition lid bs t
    | FStar_Parser_AST.DefineEffect (lid, bs, t, eff_decls) ->
        p_effectDefinition lid bs t eff_decls
and (p_effectRedefinition :
  FStar_Ident.ident ->
    FStar_Parser_AST.binder Prims.list ->
      FStar_Parser_AST.term -> FStar_Pprint.document)
  =
  fun uid ->
    fun bs ->
      fun t ->
        let uu____5989 = p_uident uid in
        let uu____5990 = p_binders true bs in
        let uu____5992 =
          let uu____5993 = p_simpleTerm false false t in
          prefix2 FStar_Pprint.equals uu____5993 in
        surround_maybe_empty (Prims.of_int (2)) Prims.int_one uu____5989
          uu____5990 uu____5992
and (p_effectDefinition :
  FStar_Ident.ident ->
    FStar_Parser_AST.binder Prims.list ->
      FStar_Parser_AST.term ->
        FStar_Parser_AST.decl Prims.list -> FStar_Pprint.document)
  =
  fun uid ->
    fun bs ->
      fun t ->
        fun eff_decls ->
          let binders = p_binders true bs in
          let uu____6008 =
            let uu____6009 =
              let uu____6010 =
                let uu____6011 = p_uident uid in
                let uu____6012 = p_binders true bs in
                let uu____6014 =
                  let uu____6015 = p_typ false false t in
                  prefix2 FStar_Pprint.colon uu____6015 in
                surround_maybe_empty (Prims.of_int (2)) Prims.int_one
                  uu____6011 uu____6012 uu____6014 in
              FStar_Pprint.group uu____6010 in
            let uu____6020 =
              let uu____6021 = str "with" in
              let uu____6023 =
                let uu____6024 =
                  let uu____6025 =
                    let uu____6026 =
                      let uu____6027 =
                        let uu____6028 =
                          FStar_Pprint.op_Hat_Hat FStar_Pprint.semi
                            FStar_Pprint.space in
                        FStar_Pprint.op_Hat_Hat FStar_Pprint.hardline
                          uu____6028 in
                      separate_map_last uu____6027 p_effectDecl eff_decls in
                    FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____6026 in
                  FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____6025 in
                FStar_Pprint.op_Hat_Hat FStar_Pprint.hardline uu____6024 in
              FStar_Pprint.op_Hat_Hat uu____6021 uu____6023 in
            FStar_Pprint.op_Hat_Slash_Hat uu____6009 uu____6020 in
          braces_with_nesting uu____6008
and (p_effectDecl :
  Prims.bool -> FStar_Parser_AST.decl -> FStar_Pprint.document) =
  fun ps ->
    fun d ->
      match d.FStar_Parser_AST.d with
      | FStar_Parser_AST.Tycon
          (false, uu____6032, (FStar_Parser_AST.TyconAbbrev
           (lid, [], FStar_Pervasives_Native.None, e))::[])
          ->
          let uu____6045 =
            let uu____6046 = p_lident lid in
            let uu____6047 =
              FStar_Pprint.op_Hat_Hat FStar_Pprint.space FStar_Pprint.equals in
            FStar_Pprint.op_Hat_Hat uu____6046 uu____6047 in
          let uu____6048 = p_simpleTerm ps false e in
          prefix2 uu____6045 uu____6048
      | uu____6050 ->
          let uu____6051 =
            let uu____6053 = FStar_Parser_AST.decl_to_string d in
            FStar_Util.format1
              "Not a declaration of an effect member... or at least I hope so : %s"
              uu____6053 in
          failwith uu____6051
and (p_subEffect : FStar_Parser_AST.lift -> FStar_Pprint.document) =
  fun lift ->
    let lift_op_doc =
      let lifts =
        match lift.FStar_Parser_AST.lift_op with
        | FStar_Parser_AST.NonReifiableLift t -> [("lift_wp", t)]
        | FStar_Parser_AST.ReifiableLift (t1, t2) ->
            [("lift_wp", t1); ("lift", t2)]
        | FStar_Parser_AST.LiftForFree t -> [("lift", t)] in
      let p_lift ps uu____6136 =
        match uu____6136 with
        | (kwd, t) ->
            let uu____6147 =
              let uu____6148 = str kwd in
              let uu____6149 =
                FStar_Pprint.op_Hat_Hat FStar_Pprint.space
                  FStar_Pprint.equals in
              FStar_Pprint.op_Hat_Hat uu____6148 uu____6149 in
            let uu____6150 = p_simpleTerm ps false t in
            prefix2 uu____6147 uu____6150 in
      separate_break_map_last FStar_Pprint.semi p_lift lifts in
    let uu____6157 =
      let uu____6158 =
        let uu____6159 = p_quident lift.FStar_Parser_AST.msource in
        let uu____6160 =
          let uu____6161 = str "~>" in
          FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____6161 in
        FStar_Pprint.op_Hat_Hat uu____6159 uu____6160 in
      let uu____6163 = p_quident lift.FStar_Parser_AST.mdest in
      prefix2 uu____6158 uu____6163 in
    let uu____6164 =
      let uu____6165 = braces_with_nesting lift_op_doc in
      FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____6165 in
    FStar_Pprint.op_Hat_Hat uu____6157 uu____6164
and (p_qualifier : FStar_Parser_AST.qualifier -> FStar_Pprint.document) =
  fun uu___8_6166 ->
    match uu___8_6166 with
    | FStar_Parser_AST.Private -> str "private"
    | FStar_Parser_AST.Abstract -> str "abstract"
    | FStar_Parser_AST.Noeq -> str "noeq"
    | FStar_Parser_AST.Unopteq -> str "unopteq"
    | FStar_Parser_AST.Assumption -> str "assume"
    | FStar_Parser_AST.DefaultEffect -> str "default"
    | FStar_Parser_AST.TotalEffect -> str "total"
    | FStar_Parser_AST.Effect_qual -> FStar_Pprint.empty
    | FStar_Parser_AST.New -> str "new"
    | FStar_Parser_AST.Inline -> str "inline"
    | FStar_Parser_AST.Visible -> FStar_Pprint.empty
    | FStar_Parser_AST.Unfold_for_unification_and_vcgen -> str "unfold"
    | FStar_Parser_AST.Inline_for_extraction -> str "inline_for_extraction"
    | FStar_Parser_AST.Irreducible -> str "irreducible"
    | FStar_Parser_AST.NoExtract -> str "noextract"
    | FStar_Parser_AST.Reifiable -> str "reifiable"
    | FStar_Parser_AST.Reflectable -> str "reflectable"
    | FStar_Parser_AST.Opaque -> str "opaque"
    | FStar_Parser_AST.Logic -> str "logic"
and (p_qualifiers : FStar_Parser_AST.qualifiers -> FStar_Pprint.document) =
  fun qs ->
    match qs with
    | [] -> FStar_Pprint.empty
    | q::[] ->
        let uu____6186 = p_qualifier q in
        FStar_Pprint.op_Hat_Hat uu____6186 FStar_Pprint.hardline
    | uu____6187 ->
        let uu____6188 =
          let uu____6189 = FStar_List.map p_qualifier qs in
          FStar_Pprint.flow break1 uu____6189 in
        FStar_Pprint.op_Hat_Hat uu____6188 FStar_Pprint.hardline
and (p_letqualifier :
  FStar_Parser_AST.let_qualifier -> FStar_Pprint.document) =
  fun uu___9_6192 ->
    match uu___9_6192 with
    | FStar_Parser_AST.Rec ->
        let uu____6193 = str "rec" in
        FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____6193
    | FStar_Parser_AST.NoLetQualifier -> FStar_Pprint.empty
and (p_aqual : FStar_Parser_AST.arg_qualifier -> FStar_Pprint.document) =
  fun uu___10_6195 ->
    match uu___10_6195 with
    | FStar_Parser_AST.Implicit -> str "#"
    | FStar_Parser_AST.Equality -> str "$"
    | FStar_Parser_AST.Meta (FStar_Parser_AST.Arg_qualifier_meta_tac t) ->
        let t1 =
          match t.FStar_Parser_AST.tm with
          | FStar_Parser_AST.Abs (uu____6200, e) -> e
          | uu____6206 ->
              FStar_Parser_AST.mk_term
                (FStar_Parser_AST.App
                   (t,
                     (FStar_Parser_AST.unit_const t.FStar_Parser_AST.range),
                     FStar_Parser_AST.Nothing)) t.FStar_Parser_AST.range
                FStar_Parser_AST.Expr in
        let uu____6207 = str "#[" in
        let uu____6209 =
          let uu____6210 = p_term false false t1 in
          let uu____6213 =
            let uu____6214 = str "]" in
            FStar_Pprint.op_Hat_Hat uu____6214 break1 in
          FStar_Pprint.op_Hat_Hat uu____6210 uu____6213 in
        FStar_Pprint.op_Hat_Hat uu____6207 uu____6209
    | FStar_Parser_AST.Meta (FStar_Parser_AST.Arg_qualifier_meta_attr t) ->
        let uu____6217 = str "#[@" in
        let uu____6219 =
          let uu____6220 = p_term false false t in
          let uu____6223 =
            let uu____6224 = str "]" in
            FStar_Pprint.op_Hat_Hat uu____6224 break1 in
          FStar_Pprint.op_Hat_Hat uu____6220 uu____6223 in
        FStar_Pprint.op_Hat_Hat uu____6217 uu____6219
and (p_disjunctivePattern :
  FStar_Parser_AST.pattern -> FStar_Pprint.document) =
  fun p ->
    match p.FStar_Parser_AST.pat with
    | FStar_Parser_AST.PatOr pats ->
        let uu____6230 =
          let uu____6231 =
            let uu____6232 =
              FStar_Pprint.op_Hat_Hat FStar_Pprint.bar FStar_Pprint.space in
            FStar_Pprint.op_Hat_Hat break1 uu____6232 in
          FStar_Pprint.separate_map uu____6231 p_tuplePattern pats in
        FStar_Pprint.group uu____6230
    | uu____6233 -> p_tuplePattern p
and (p_tuplePattern : FStar_Parser_AST.pattern -> FStar_Pprint.document) =
  fun p ->
    match p.FStar_Parser_AST.pat with
    | FStar_Parser_AST.PatTuple (pats, false) ->
        let uu____6242 =
          let uu____6243 = FStar_Pprint.op_Hat_Hat FStar_Pprint.comma break1 in
          FStar_Pprint.separate_map uu____6243 p_constructorPattern pats in
        FStar_Pprint.group uu____6242
    | uu____6244 -> p_constructorPattern p
and (p_constructorPattern :
  FStar_Parser_AST.pattern -> FStar_Pprint.document) =
  fun p ->
    match p.FStar_Parser_AST.pat with
    | FStar_Parser_AST.PatApp
        ({ FStar_Parser_AST.pat = FStar_Parser_AST.PatName maybe_cons_lid;
           FStar_Parser_AST.prange = uu____6247;_},
         hd::tl::[])
        when
        FStar_Ident.lid_equals maybe_cons_lid FStar_Parser_Const.cons_lid ->
        let uu____6252 =
          FStar_Pprint.op_Hat_Hat FStar_Pprint.colon FStar_Pprint.colon in
        let uu____6253 = p_constructorPattern hd in
        let uu____6254 = p_constructorPattern tl in
        infix0 uu____6252 uu____6253 uu____6254
    | FStar_Parser_AST.PatApp
        ({ FStar_Parser_AST.pat = FStar_Parser_AST.PatName uid;
           FStar_Parser_AST.prange = uu____6256;_},
         pats)
        ->
        let uu____6262 = p_quident uid in
        let uu____6263 =
          FStar_Pprint.separate_map break1 p_atomicPattern pats in
        prefix2 uu____6262 uu____6263
    | uu____6264 -> p_atomicPattern p
and (p_atomicPattern : FStar_Parser_AST.pattern -> FStar_Pprint.document) =
  fun p ->
    match p.FStar_Parser_AST.pat with
    | FStar_Parser_AST.PatAscribed (pat, (t, FStar_Pervasives_Native.None))
        ->
        (match ((pat.FStar_Parser_AST.pat), (t.FStar_Parser_AST.tm)) with
         | (FStar_Parser_AST.PatVar (lid, aqual), FStar_Parser_AST.Refine
            ({ FStar_Parser_AST.b = FStar_Parser_AST.Annotated (lid', t1);
               FStar_Parser_AST.brange = uu____6280;
               FStar_Parser_AST.blevel = uu____6281;
               FStar_Parser_AST.aqual = uu____6282;_},
             phi)) when
             let uu____6290 = FStar_Ident.string_of_id lid in
             let uu____6292 = FStar_Ident.string_of_id lid' in
             uu____6290 = uu____6292 ->
             let uu____6295 =
               let uu____6296 = p_ident lid in
               p_refinement aqual uu____6296 t1 phi in
             soft_parens_with_nesting uu____6295
         | (FStar_Parser_AST.PatWild aqual, FStar_Parser_AST.Refine
            ({ FStar_Parser_AST.b = FStar_Parser_AST.NoName t1;
               FStar_Parser_AST.brange = uu____6299;
               FStar_Parser_AST.blevel = uu____6300;
               FStar_Parser_AST.aqual = uu____6301;_},
             phi)) ->
             let uu____6307 =
               p_refinement aqual FStar_Pprint.underscore t1 phi in
             soft_parens_with_nesting uu____6307
         | uu____6308 ->
             let uu____6313 =
               let uu____6314 = p_tuplePattern pat in
               let uu____6315 =
                 let uu____6316 = p_tmEqNoRefinement t in
                 FStar_Pprint.op_Hat_Slash_Hat FStar_Pprint.colon uu____6316 in
               FStar_Pprint.op_Hat_Hat uu____6314 uu____6315 in
             soft_parens_with_nesting uu____6313)
    | FStar_Parser_AST.PatList pats ->
        let uu____6320 =
          separate_break_map FStar_Pprint.semi p_tuplePattern pats in
        FStar_Pprint.surround (Prims.of_int (2)) Prims.int_zero
          FStar_Pprint.lbracket uu____6320 FStar_Pprint.rbracket
    | FStar_Parser_AST.PatRecord pats ->
        let p_recordFieldPat uu____6339 =
          match uu____6339 with
          | (lid, pat) ->
              let uu____6346 = p_qlident lid in
              let uu____6347 = p_tuplePattern pat in
              infix2 FStar_Pprint.equals uu____6346 uu____6347 in
        let uu____6348 =
          separate_break_map FStar_Pprint.semi p_recordFieldPat pats in
        soft_braces_with_nesting uu____6348
    | FStar_Parser_AST.PatTuple (pats, true) ->
        let uu____6360 =
          FStar_Pprint.op_Hat_Hat FStar_Pprint.lparen FStar_Pprint.bar in
        let uu____6361 =
          separate_break_map FStar_Pprint.comma p_constructorPattern pats in
        let uu____6362 =
          FStar_Pprint.op_Hat_Hat FStar_Pprint.bar FStar_Pprint.rparen in
        FStar_Pprint.surround (Prims.of_int (2)) Prims.int_one uu____6360
          uu____6361 uu____6362
    | FStar_Parser_AST.PatTvar (tv, arg_qualifier_opt) -> p_tvar tv
    | FStar_Parser_AST.PatOp op ->
        let uu____6373 =
          let uu____6374 =
            let uu____6375 =
              let uu____6376 = FStar_Ident.string_of_id op in str uu____6376 in
            let uu____6378 =
              FStar_Pprint.op_Hat_Hat FStar_Pprint.space FStar_Pprint.rparen in
            FStar_Pprint.op_Hat_Hat uu____6375 uu____6378 in
          FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____6374 in
        FStar_Pprint.op_Hat_Hat FStar_Pprint.lparen uu____6373
    | FStar_Parser_AST.PatWild aqual ->
        let uu____6382 = FStar_Pprint.optional p_aqual aqual in
        FStar_Pprint.op_Hat_Hat uu____6382 FStar_Pprint.underscore
    | FStar_Parser_AST.PatConst c -> p_constant c
    | FStar_Parser_AST.PatVar (lid, aqual) ->
        let uu____6390 = FStar_Pprint.optional p_aqual aqual in
        let uu____6391 = p_lident lid in
        FStar_Pprint.op_Hat_Hat uu____6390 uu____6391
    | FStar_Parser_AST.PatName uid -> p_quident uid
    | FStar_Parser_AST.PatOr uu____6393 -> failwith "Inner or pattern !"
    | FStar_Parser_AST.PatApp
        ({ FStar_Parser_AST.pat = FStar_Parser_AST.PatName uu____6397;
           FStar_Parser_AST.prange = uu____6398;_},
         uu____6399)
        ->
        let uu____6404 = p_tuplePattern p in
        soft_parens_with_nesting uu____6404
    | FStar_Parser_AST.PatTuple (uu____6405, false) ->
        let uu____6412 = p_tuplePattern p in
        soft_parens_with_nesting uu____6412
    | uu____6413 ->
        let uu____6414 =
          let uu____6416 = FStar_Parser_AST.pat_to_string p in
          FStar_Util.format1 "Invalid pattern %s" uu____6416 in
        failwith uu____6414
and (is_typ_tuple : FStar_Parser_AST.term -> Prims.bool) =
  fun e ->
    match e.FStar_Parser_AST.tm with
    | FStar_Parser_AST.Op (id, uu____6422) when
        let uu____6427 = FStar_Ident.string_of_id id in uu____6427 = "*" ->
        true
    | uu____6432 -> false
and (is_meta_qualifier :
  FStar_Parser_AST.arg_qualifier FStar_Pervasives_Native.option -> Prims.bool)
  =
  fun aq ->
    match aq with
    | FStar_Pervasives_Native.Some (FStar_Parser_AST.Meta uu____6438) -> true
    | uu____6440 -> false
and (p_binder :
  Prims.bool -> FStar_Parser_AST.binder -> FStar_Pprint.document) =
  fun is_atomic ->
    fun b ->
      let uu____6447 = p_binder' is_atomic b in
      match uu____6447 with
      | (b', t', catf1) ->
          (match t' with
           | FStar_Pervasives_Native.Some typ -> catf1 b' typ
           | FStar_Pervasives_Native.None -> b')
and (p_binder' :
  Prims.bool ->
    FStar_Parser_AST.binder ->
      (FStar_Pprint.document * FStar_Pprint.document
        FStar_Pervasives_Native.option * catf))
  =
  fun is_atomic ->
    fun b ->
      match b.FStar_Parser_AST.b with
      | FStar_Parser_AST.Variable lid ->
          let uu____6484 =
            let uu____6485 =
              FStar_Pprint.optional p_aqual b.FStar_Parser_AST.aqual in
            let uu____6486 = p_lident lid in
            FStar_Pprint.op_Hat_Hat uu____6485 uu____6486 in
          (uu____6484, FStar_Pervasives_Native.None, cat_with_colon)
      | FStar_Parser_AST.TVariable lid ->
          let uu____6492 = p_lident lid in
          (uu____6492, FStar_Pervasives_Native.None, cat_with_colon)
      | FStar_Parser_AST.Annotated (lid, t) ->
          let uu____6499 =
            match t.FStar_Parser_AST.tm with
            | FStar_Parser_AST.Refine
                ({
                   FStar_Parser_AST.b = FStar_Parser_AST.Annotated (lid', t1);
                   FStar_Parser_AST.brange = uu____6510;
                   FStar_Parser_AST.blevel = uu____6511;
                   FStar_Parser_AST.aqual = uu____6512;_},
                 phi)
                when
                let uu____6516 = FStar_Ident.string_of_id lid in
                let uu____6518 = FStar_Ident.string_of_id lid' in
                uu____6516 = uu____6518 ->
                let uu____6521 = p_lident lid in
                p_refinement' b.FStar_Parser_AST.aqual uu____6521 t1 phi
            | uu____6522 ->
                let t' =
                  let uu____6524 = is_typ_tuple t in
                  if uu____6524
                  then
                    let uu____6527 = p_tmFormula t in
                    soft_parens_with_nesting uu____6527
                  else p_tmFormula t in
                let uu____6530 =
                  let uu____6531 =
                    FStar_Pprint.optional p_aqual b.FStar_Parser_AST.aqual in
                  let uu____6532 = p_lident lid in
                  FStar_Pprint.op_Hat_Hat uu____6531 uu____6532 in
                (uu____6530, t') in
          (match uu____6499 with
           | (b', t') ->
               let catf1 =
                 let uu____6550 =
                   is_atomic || (is_meta_qualifier b.FStar_Parser_AST.aqual) in
                 if uu____6550
                 then
                   fun x ->
                     fun y ->
                       let uu____6557 =
                         let uu____6558 =
                           let uu____6559 = cat_with_colon x y in
                           FStar_Pprint.op_Hat_Hat uu____6559
                             FStar_Pprint.rparen in
                         FStar_Pprint.op_Hat_Hat FStar_Pprint.lparen
                           uu____6558 in
                       FStar_Pprint.group uu____6557
                 else
                   (fun x ->
                      fun y ->
                        let uu____6564 = cat_with_colon x y in
                        FStar_Pprint.group uu____6564) in
               (b', (FStar_Pervasives_Native.Some t'), catf1))
      | FStar_Parser_AST.TAnnotated uu____6569 ->
          failwith "Is this still used ?"
      | FStar_Parser_AST.NoName t ->
          (match t.FStar_Parser_AST.tm with
           | FStar_Parser_AST.Refine
               ({ FStar_Parser_AST.b = FStar_Parser_AST.NoName t1;
                  FStar_Parser_AST.brange = uu____6597;
                  FStar_Parser_AST.blevel = uu____6598;
                  FStar_Parser_AST.aqual = uu____6599;_},
                phi)
               ->
               let uu____6603 =
                 p_refinement' b.FStar_Parser_AST.aqual
                   FStar_Pprint.underscore t1 phi in
               (match uu____6603 with
                | (b', t') ->
                    (b', (FStar_Pervasives_Native.Some t'), cat_with_colon))
           | uu____6624 ->
               if is_atomic
               then
                 let uu____6636 = p_atomicTerm t in
                 (uu____6636, FStar_Pervasives_Native.None, cat_with_colon)
               else
                 (let uu____6643 = p_appTerm t in
                  (uu____6643, FStar_Pervasives_Native.None, cat_with_colon)))
and (p_refinement :
  FStar_Parser_AST.arg_qualifier FStar_Pervasives_Native.option ->
    FStar_Pprint.document ->
      FStar_Parser_AST.term -> FStar_Parser_AST.term -> FStar_Pprint.document)
  =
  fun aqual_opt ->
    fun binder ->
      fun t ->
        fun phi ->
          let uu____6654 = p_refinement' aqual_opt binder t phi in
          match uu____6654 with | (b, typ) -> cat_with_colon b typ
and (p_refinement' :
  FStar_Parser_AST.arg_qualifier FStar_Pervasives_Native.option ->
    FStar_Pprint.document ->
      FStar_Parser_AST.term ->
        FStar_Parser_AST.term ->
          (FStar_Pprint.document * FStar_Pprint.document))
  =
  fun aqual_opt ->
    fun binder ->
      fun t ->
        fun phi ->
          let is_t_atomic =
            match t.FStar_Parser_AST.tm with
            | FStar_Parser_AST.Construct uu____6670 -> false
            | FStar_Parser_AST.App uu____6682 -> false
            | FStar_Parser_AST.Op uu____6690 -> false
            | uu____6698 -> true in
          let uu____6700 = p_noSeqTerm false false phi in
          match uu____6700 with
          | (comm, phi1) ->
              let phi2 =
                if comm = FStar_Pprint.empty
                then phi1
                else
                  (let uu____6717 =
                     FStar_Pprint.op_Hat_Hat FStar_Pprint.hardline phi1 in
                   FStar_Pprint.op_Hat_Hat comm uu____6717) in
              let jump_break =
                if is_t_atomic then Prims.int_zero else Prims.int_one in
              let uu____6726 =
                let uu____6727 = FStar_Pprint.optional p_aqual aqual_opt in
                FStar_Pprint.op_Hat_Hat uu____6727 binder in
              let uu____6728 =
                let uu____6729 = p_appTerm t in
                let uu____6730 =
                  let uu____6731 =
                    let uu____6732 =
                      let uu____6733 = soft_braces_with_nesting_tight phi2 in
                      let uu____6734 = soft_braces_with_nesting phi2 in
                      FStar_Pprint.ifflat uu____6733 uu____6734 in
                    FStar_Pprint.group uu____6732 in
                  FStar_Pprint.jump (Prims.of_int (2)) jump_break uu____6731 in
                FStar_Pprint.op_Hat_Hat uu____6729 uu____6730 in
              (uu____6726, uu____6728)
and (p_binders_list :
  Prims.bool ->
    FStar_Parser_AST.binder Prims.list -> FStar_Pprint.document Prims.list)
  = fun is_atomic -> fun bs -> FStar_List.map (p_binder is_atomic) bs
and (p_binders :
  Prims.bool -> FStar_Parser_AST.binder Prims.list -> FStar_Pprint.document)
  =
  fun is_atomic ->
    fun bs ->
      let uu____6748 = p_binders_list is_atomic bs in
      separate_or_flow break1 uu____6748
and (string_of_id_or_underscore : FStar_Ident.ident -> FStar_Pprint.document)
  =
  fun lid ->
    let uu____6752 =
      (let uu____6756 = FStar_Ident.string_of_id lid in
       FStar_Util.starts_with uu____6756 FStar_Ident.reserved_prefix) &&
        (let uu____6759 = FStar_Options.print_real_names () in
         Prims.op_Negation uu____6759) in
    if uu____6752
    then FStar_Pprint.underscore
    else (let uu____6764 = FStar_Ident.string_of_id lid in str uu____6764)
and (text_of_lid_or_underscore : FStar_Ident.lident -> FStar_Pprint.document)
  =
  fun lid ->
    let uu____6767 =
      (let uu____6771 =
         let uu____6773 = FStar_Ident.ident_of_lid lid in
         FStar_Ident.string_of_id uu____6773 in
       FStar_Util.starts_with uu____6771 FStar_Ident.reserved_prefix) &&
        (let uu____6775 = FStar_Options.print_real_names () in
         Prims.op_Negation uu____6775) in
    if uu____6767
    then FStar_Pprint.underscore
    else (let uu____6780 = FStar_Ident.string_of_lid lid in str uu____6780)
and (p_qlident : FStar_Ident.lid -> FStar_Pprint.document) =
  fun lid -> text_of_lid_or_underscore lid
and (p_quident : FStar_Ident.lid -> FStar_Pprint.document) =
  fun lid -> text_of_lid_or_underscore lid
and (p_ident : FStar_Ident.ident -> FStar_Pprint.document) =
  fun lid -> string_of_id_or_underscore lid
and (p_lident : FStar_Ident.ident -> FStar_Pprint.document) =
  fun lid -> string_of_id_or_underscore lid
and (p_uident : FStar_Ident.ident -> FStar_Pprint.document) =
  fun lid -> string_of_id_or_underscore lid
and (p_tvar : FStar_Ident.ident -> FStar_Pprint.document) =
  fun lid -> string_of_id_or_underscore lid
and (paren_if : Prims.bool -> FStar_Pprint.document -> FStar_Pprint.document)
  = fun b -> if b then soft_parens_with_nesting else (fun x -> x)
and (inline_comment_or_above :
  FStar_Pprint.document ->
    FStar_Pprint.document -> FStar_Pprint.document -> FStar_Pprint.document)
  =
  fun comm ->
    fun doc ->
      fun sep ->
        if comm = FStar_Pprint.empty
        then
          let uu____6801 = FStar_Pprint.op_Hat_Hat doc sep in
          FStar_Pprint.group uu____6801
        else
          (let uu____6804 =
             let uu____6805 =
               let uu____6806 =
                 let uu____6807 =
                   let uu____6808 = FStar_Pprint.op_Hat_Hat break1 comm in
                   FStar_Pprint.op_Hat_Hat sep uu____6808 in
                 FStar_Pprint.op_Hat_Hat doc uu____6807 in
               FStar_Pprint.group uu____6806 in
             let uu____6809 =
               let uu____6810 =
                 let uu____6811 = FStar_Pprint.op_Hat_Hat doc sep in
                 FStar_Pprint.op_Hat_Hat FStar_Pprint.hardline uu____6811 in
               FStar_Pprint.op_Hat_Hat comm uu____6810 in
             FStar_Pprint.ifflat uu____6805 uu____6809 in
           FStar_All.pipe_left FStar_Pprint.group uu____6804)
and (p_term :
  Prims.bool -> Prims.bool -> FStar_Parser_AST.term -> FStar_Pprint.document)
  =
  fun ps ->
    fun pb ->
      fun e ->
        match e.FStar_Parser_AST.tm with
        | FStar_Parser_AST.Seq (e1, e2) ->
            let uu____6819 = p_noSeqTerm true false e1 in
            (match uu____6819 with
             | (comm, t1) ->
                 let uu____6828 =
                   inline_comment_or_above comm t1 FStar_Pprint.semi in
                 let uu____6829 =
                   let uu____6830 = p_term ps pb e2 in
                   FStar_Pprint.op_Hat_Hat FStar_Pprint.hardline uu____6830 in
                 FStar_Pprint.op_Hat_Hat uu____6828 uu____6829)
        | FStar_Parser_AST.Bind (x, e1, e2) ->
            let uu____6834 =
              let uu____6835 =
                let uu____6836 =
                  let uu____6837 = p_lident x in
                  let uu____6838 =
                    FStar_Pprint.op_Hat_Hat FStar_Pprint.space
                      FStar_Pprint.long_left_arrow in
                  FStar_Pprint.op_Hat_Hat uu____6837 uu____6838 in
                let uu____6839 =
                  let uu____6840 = p_noSeqTermAndComment true false e1 in
                  let uu____6843 =
                    FStar_Pprint.op_Hat_Hat FStar_Pprint.space
                      FStar_Pprint.semi in
                  FStar_Pprint.op_Hat_Hat uu____6840 uu____6843 in
                op_Hat_Slash_Plus_Hat uu____6836 uu____6839 in
              FStar_Pprint.group uu____6835 in
            let uu____6844 = p_term ps pb e2 in
            FStar_Pprint.op_Hat_Slash_Hat uu____6834 uu____6844
        | uu____6845 ->
            let uu____6846 = p_noSeqTermAndComment ps pb e in
            FStar_Pprint.group uu____6846
and (p_term_sep :
  Prims.bool ->
    Prims.bool ->
      FStar_Parser_AST.term ->
        (FStar_Pprint.document * FStar_Pprint.document))
  =
  fun ps ->
    fun pb ->
      fun e ->
        match e.FStar_Parser_AST.tm with
        | FStar_Parser_AST.Seq (e1, e2) ->
            let uu____6858 = p_noSeqTerm true false e1 in
            (match uu____6858 with
             | (comm, t1) ->
                 let uu____6871 =
                   let uu____6872 =
                     let uu____6873 =
                       FStar_Pprint.op_Hat_Hat t1 FStar_Pprint.semi in
                     FStar_Pprint.group uu____6873 in
                   let uu____6874 =
                     let uu____6875 = p_term ps pb e2 in
                     FStar_Pprint.op_Hat_Hat FStar_Pprint.hardline uu____6875 in
                   FStar_Pprint.op_Hat_Hat uu____6872 uu____6874 in
                 (comm, uu____6871))
        | FStar_Parser_AST.Bind (x, e1, e2) ->
            let uu____6879 =
              let uu____6880 =
                let uu____6881 =
                  let uu____6882 =
                    let uu____6883 = p_lident x in
                    let uu____6884 =
                      FStar_Pprint.op_Hat_Hat FStar_Pprint.space
                        FStar_Pprint.long_left_arrow in
                    FStar_Pprint.op_Hat_Hat uu____6883 uu____6884 in
                  let uu____6885 =
                    let uu____6886 = p_noSeqTermAndComment true false e1 in
                    let uu____6889 =
                      FStar_Pprint.op_Hat_Hat FStar_Pprint.space
                        FStar_Pprint.semi in
                    FStar_Pprint.op_Hat_Hat uu____6886 uu____6889 in
                  op_Hat_Slash_Plus_Hat uu____6882 uu____6885 in
                FStar_Pprint.group uu____6881 in
              let uu____6890 = p_term ps pb e2 in
              FStar_Pprint.op_Hat_Slash_Hat uu____6880 uu____6890 in
            (FStar_Pprint.empty, uu____6879)
        | uu____6891 -> p_noSeqTerm ps pb e
and (p_noSeqTerm :
  Prims.bool ->
    Prims.bool ->
      FStar_Parser_AST.term ->
        (FStar_Pprint.document * FStar_Pprint.document))
  =
  fun ps ->
    fun pb ->
      fun e ->
        with_comment_sep (p_noSeqTerm' ps pb) e e.FStar_Parser_AST.range
and (p_noSeqTermAndComment :
  Prims.bool -> Prims.bool -> FStar_Parser_AST.term -> FStar_Pprint.document)
  =
  fun ps ->
    fun pb ->
      fun e -> with_comment (p_noSeqTerm' ps pb) e e.FStar_Parser_AST.range
and (p_noSeqTerm' :
  Prims.bool -> Prims.bool -> FStar_Parser_AST.term -> FStar_Pprint.document)
  =
  fun ps ->
    fun pb ->
      fun e ->
        match e.FStar_Parser_AST.tm with
        | FStar_Parser_AST.Ascribed (e1, t, FStar_Pervasives_Native.None) ->
            let uu____6911 =
              let uu____6912 = p_tmIff e1 in
              let uu____6913 =
                let uu____6914 =
                  let uu____6915 = p_typ ps pb t in
                  FStar_Pprint.op_Hat_Slash_Hat FStar_Pprint.colon uu____6915 in
                FStar_Pprint.op_Hat_Hat FStar_Pprint.langle uu____6914 in
              FStar_Pprint.op_Hat_Slash_Hat uu____6912 uu____6913 in
            FStar_Pprint.group uu____6911
        | FStar_Parser_AST.Ascribed (e1, t, FStar_Pervasives_Native.Some tac)
            ->
            let uu____6921 =
              let uu____6922 = p_tmIff e1 in
              let uu____6923 =
                let uu____6924 =
                  let uu____6925 =
                    let uu____6926 = p_typ false false t in
                    let uu____6929 =
                      let uu____6930 = str "by" in
                      let uu____6932 = p_typ ps pb (maybe_unthunk tac) in
                      FStar_Pprint.op_Hat_Slash_Hat uu____6930 uu____6932 in
                    FStar_Pprint.op_Hat_Slash_Hat uu____6926 uu____6929 in
                  FStar_Pprint.op_Hat_Slash_Hat FStar_Pprint.colon uu____6925 in
                FStar_Pprint.op_Hat_Hat FStar_Pprint.langle uu____6924 in
              FStar_Pprint.op_Hat_Slash_Hat uu____6922 uu____6923 in
            FStar_Pprint.group uu____6921
        | FStar_Parser_AST.Op (id, e1::e2::e3::[]) when
            let uu____6939 = FStar_Ident.string_of_id id in
            uu____6939 = ".()<-" ->
            let uu____6943 =
              let uu____6944 =
                let uu____6945 =
                  let uu____6946 = p_atomicTermNotQUident e1 in
                  let uu____6947 =
                    let uu____6948 =
                      let uu____6949 =
                        let uu____6950 = p_term false false e2 in
                        soft_parens_with_nesting uu____6950 in
                      let uu____6953 =
                        FStar_Pprint.op_Hat_Hat FStar_Pprint.space
                          FStar_Pprint.larrow in
                      FStar_Pprint.op_Hat_Hat uu____6949 uu____6953 in
                    FStar_Pprint.op_Hat_Hat FStar_Pprint.dot uu____6948 in
                  FStar_Pprint.op_Hat_Hat uu____6946 uu____6947 in
                FStar_Pprint.group uu____6945 in
              let uu____6954 =
                let uu____6955 = p_noSeqTermAndComment ps pb e3 in
                jump2 uu____6955 in
              FStar_Pprint.op_Hat_Hat uu____6944 uu____6954 in
            FStar_Pprint.group uu____6943
        | FStar_Parser_AST.Op (id, e1::e2::e3::[]) when
            let uu____6962 = FStar_Ident.string_of_id id in
            uu____6962 = ".[]<-" ->
            let uu____6966 =
              let uu____6967 =
                let uu____6968 =
                  let uu____6969 = p_atomicTermNotQUident e1 in
                  let uu____6970 =
                    let uu____6971 =
                      let uu____6972 =
                        let uu____6973 = p_term false false e2 in
                        soft_brackets_with_nesting uu____6973 in
                      let uu____6976 =
                        FStar_Pprint.op_Hat_Hat FStar_Pprint.space
                          FStar_Pprint.larrow in
                      FStar_Pprint.op_Hat_Hat uu____6972 uu____6976 in
                    FStar_Pprint.op_Hat_Hat FStar_Pprint.dot uu____6971 in
                  FStar_Pprint.op_Hat_Hat uu____6969 uu____6970 in
                FStar_Pprint.group uu____6968 in
              let uu____6977 =
                let uu____6978 = p_noSeqTermAndComment ps pb e3 in
                jump2 uu____6978 in
              FStar_Pprint.op_Hat_Hat uu____6967 uu____6977 in
            FStar_Pprint.group uu____6966
        | FStar_Parser_AST.Requires (e1, wtf) ->
            let uu____6988 =
              let uu____6989 = str "requires" in
              let uu____6991 = p_typ ps pb e1 in
              FStar_Pprint.op_Hat_Slash_Hat uu____6989 uu____6991 in
            FStar_Pprint.group uu____6988
        | FStar_Parser_AST.Ensures (e1, wtf) ->
            let uu____7001 =
              let uu____7002 = str "ensures" in
              let uu____7004 = p_typ ps pb e1 in
              FStar_Pprint.op_Hat_Slash_Hat uu____7002 uu____7004 in
            FStar_Pprint.group uu____7001
        | FStar_Parser_AST.Attributes es ->
            let uu____7008 =
              let uu____7009 = str "attributes" in
              let uu____7011 =
                FStar_Pprint.separate_map break1 p_atomicTerm es in
              FStar_Pprint.op_Hat_Slash_Hat uu____7009 uu____7011 in
            FStar_Pprint.group uu____7008
        | FStar_Parser_AST.If (e1, e2, e3) ->
            if is_unit e3
            then
              let uu____7016 =
                let uu____7017 =
                  let uu____7018 = str "if" in
                  let uu____7020 = p_noSeqTermAndComment false false e1 in
                  op_Hat_Slash_Plus_Hat uu____7018 uu____7020 in
                let uu____7023 =
                  let uu____7024 = str "then" in
                  let uu____7026 = p_noSeqTermAndComment ps pb e2 in
                  op_Hat_Slash_Plus_Hat uu____7024 uu____7026 in
                FStar_Pprint.op_Hat_Slash_Hat uu____7017 uu____7023 in
              FStar_Pprint.group uu____7016
            else
              (let e2_doc =
                 match e2.FStar_Parser_AST.tm with
                 | FStar_Parser_AST.If (uu____7030, uu____7031, e31) when
                     is_unit e31 ->
                     let uu____7033 = p_noSeqTermAndComment false false e2 in
                     soft_parens_with_nesting uu____7033
                 | uu____7036 -> p_noSeqTermAndComment false false e2 in
               let uu____7039 =
                 let uu____7040 =
                   let uu____7041 = str "if" in
                   let uu____7043 = p_noSeqTermAndComment false false e1 in
                   op_Hat_Slash_Plus_Hat uu____7041 uu____7043 in
                 let uu____7046 =
                   let uu____7047 =
                     let uu____7048 = str "then" in
                     op_Hat_Slash_Plus_Hat uu____7048 e2_doc in
                   let uu____7050 =
                     let uu____7051 = str "else" in
                     let uu____7053 = p_noSeqTermAndComment ps pb e3 in
                     op_Hat_Slash_Plus_Hat uu____7051 uu____7053 in
                   FStar_Pprint.op_Hat_Slash_Hat uu____7047 uu____7050 in
                 FStar_Pprint.op_Hat_Slash_Hat uu____7040 uu____7046 in
               FStar_Pprint.group uu____7039)
        | FStar_Parser_AST.TryWith (e1, branches) ->
            let uu____7076 =
              let uu____7077 =
                let uu____7078 =
                  let uu____7079 = str "try" in
                  let uu____7081 = p_noSeqTermAndComment false false e1 in
                  prefix2 uu____7079 uu____7081 in
                let uu____7084 =
                  let uu____7085 = str "with" in
                  let uu____7087 =
                    separate_map_last FStar_Pprint.hardline p_patternBranch
                      branches in
                  FStar_Pprint.op_Hat_Slash_Hat uu____7085 uu____7087 in
                FStar_Pprint.op_Hat_Slash_Hat uu____7078 uu____7084 in
              FStar_Pprint.group uu____7077 in
            let uu____7096 = paren_if (ps || pb) in uu____7096 uu____7076
        | FStar_Parser_AST.Match (e1, branches) ->
            let uu____7123 =
              let uu____7124 =
                let uu____7125 =
                  let uu____7126 = str "match" in
                  let uu____7128 = p_noSeqTermAndComment false false e1 in
                  let uu____7131 = str "with" in
                  FStar_Pprint.surround (Prims.of_int (2)) Prims.int_one
                    uu____7126 uu____7128 uu____7131 in
                let uu____7135 =
                  separate_map_last FStar_Pprint.hardline p_patternBranch
                    branches in
                FStar_Pprint.op_Hat_Slash_Hat uu____7125 uu____7135 in
              FStar_Pprint.group uu____7124 in
            let uu____7144 = paren_if (ps || pb) in uu____7144 uu____7123
        | FStar_Parser_AST.LetOpen (uid, e1) ->
            let uu____7151 =
              let uu____7152 =
                let uu____7153 =
                  let uu____7154 = str "let open" in
                  let uu____7156 = p_quident uid in
                  let uu____7157 = str "in" in
                  FStar_Pprint.surround (Prims.of_int (2)) Prims.int_one
                    uu____7154 uu____7156 uu____7157 in
                let uu____7161 = p_term false pb e1 in
                FStar_Pprint.op_Hat_Slash_Hat uu____7153 uu____7161 in
              FStar_Pprint.group uu____7152 in
            let uu____7163 = paren_if ps in uu____7163 uu____7151
        | FStar_Parser_AST.Let (q, lbs, e1) ->
            let p_lb q1 uu____7228 is_last =
              match uu____7228 with
              | (a, (pat, e2)) ->
                  let attrs = p_attrs_opt a in
                  let doc_let_or_and =
                    match q1 with
                    | FStar_Pervasives_Native.Some (FStar_Parser_AST.Rec) ->
                        let uu____7262 =
                          let uu____7263 = str "let" in
                          let uu____7265 = str "rec" in
                          FStar_Pprint.op_Hat_Slash_Hat uu____7263 uu____7265 in
                        FStar_Pprint.group uu____7262
                    | FStar_Pervasives_Native.Some
                        (FStar_Parser_AST.NoLetQualifier) -> str "let"
                    | uu____7268 -> str "and" in
                  let doc_pat = p_letlhs doc_let_or_and (pat, e2) true in
                  let uu____7274 = p_term_sep false false e2 in
                  (match uu____7274 with
                   | (comm, doc_expr) ->
                       let doc_expr1 =
                         inline_comment_or_above comm doc_expr
                           FStar_Pprint.empty in
                       let uu____7284 =
                         if is_last
                         then
                           let uu____7286 =
                             FStar_Pprint.flow break1
                               [doc_pat; FStar_Pprint.equals] in
                           let uu____7287 = str "in" in
                           FStar_Pprint.surround (Prims.of_int (2))
                             Prims.int_one uu____7286 doc_expr1 uu____7287
                         else
                           (let uu____7293 =
                              FStar_Pprint.flow break1
                                [doc_pat; FStar_Pprint.equals; doc_expr1] in
                            FStar_Pprint.hang (Prims.of_int (2)) uu____7293) in
                       FStar_Pprint.op_Hat_Hat attrs uu____7284) in
            let l = FStar_List.length lbs in
            let lbs_docs =
              FStar_List.mapi
                (fun i ->
                   fun lb ->
                     if i = Prims.int_zero
                     then
                       let uu____7344 =
                         p_lb (FStar_Pervasives_Native.Some q) lb
                           (i = (l - Prims.int_one)) in
                       FStar_Pprint.group uu____7344
                     else
                       (let uu____7349 =
                          p_lb FStar_Pervasives_Native.None lb
                            (i = (l - Prims.int_one)) in
                        FStar_Pprint.group uu____7349)) lbs in
            let lbs_doc =
              let uu____7353 = FStar_Pprint.separate break1 lbs_docs in
              FStar_Pprint.group uu____7353 in
            let uu____7354 =
              let uu____7355 =
                let uu____7356 =
                  let uu____7357 = p_term false pb e1 in
                  FStar_Pprint.op_Hat_Hat FStar_Pprint.hardline uu____7357 in
                FStar_Pprint.op_Hat_Hat lbs_doc uu____7356 in
              FStar_Pprint.group uu____7355 in
            let uu____7359 = paren_if ps in uu____7359 uu____7354
        | FStar_Parser_AST.Abs
            ({ FStar_Parser_AST.pat = FStar_Parser_AST.PatVar (x, typ_opt);
               FStar_Parser_AST.prange = uu____7366;_}::[],
             {
               FStar_Parser_AST.tm = FStar_Parser_AST.Match
                 (maybe_x, branches);
               FStar_Parser_AST.range = uu____7369;
               FStar_Parser_AST.level = uu____7370;_})
            when matches_var maybe_x x ->
            let uu____7397 =
              let uu____7398 =
                let uu____7399 = str "function" in
                let uu____7401 =
                  separate_map_last FStar_Pprint.hardline p_patternBranch
                    branches in
                FStar_Pprint.op_Hat_Slash_Hat uu____7399 uu____7401 in
              FStar_Pprint.group uu____7398 in
            let uu____7410 = paren_if (ps || pb) in uu____7410 uu____7397
        | FStar_Parser_AST.Quote (e1, FStar_Parser_AST.Dynamic) ->
            let uu____7416 =
              let uu____7417 = str "quote" in
              let uu____7419 = p_noSeqTermAndComment ps pb e1 in
              FStar_Pprint.op_Hat_Slash_Hat uu____7417 uu____7419 in
            FStar_Pprint.group uu____7416
        | FStar_Parser_AST.Quote (e1, FStar_Parser_AST.Static) ->
            let uu____7421 =
              let uu____7422 = str "`" in
              let uu____7424 = p_noSeqTermAndComment ps pb e1 in
              FStar_Pprint.op_Hat_Hat uu____7422 uu____7424 in
            FStar_Pprint.group uu____7421
        | FStar_Parser_AST.VQuote e1 ->
            let uu____7426 =
              let uu____7427 = str "`%" in
              let uu____7429 = p_noSeqTermAndComment ps pb e1 in
              FStar_Pprint.op_Hat_Hat uu____7427 uu____7429 in
            FStar_Pprint.group uu____7426
        | FStar_Parser_AST.Antiquote
            {
              FStar_Parser_AST.tm = FStar_Parser_AST.Quote
                (e1, FStar_Parser_AST.Dynamic);
              FStar_Parser_AST.range = uu____7431;
              FStar_Parser_AST.level = uu____7432;_}
            ->
            let uu____7433 =
              let uu____7434 = str "`@" in
              let uu____7436 = p_noSeqTermAndComment ps pb e1 in
              FStar_Pprint.op_Hat_Hat uu____7434 uu____7436 in
            FStar_Pprint.group uu____7433
        | FStar_Parser_AST.Antiquote e1 ->
            let uu____7438 =
              let uu____7439 = str "`#" in
              let uu____7441 = p_noSeqTermAndComment ps pb e1 in
              FStar_Pprint.op_Hat_Hat uu____7439 uu____7441 in
            FStar_Pprint.group uu____7438
        | FStar_Parser_AST.CalcProof (rel, init, steps) ->
            let head =
              let uu____7450 = str "calc" in
              let uu____7452 =
                let uu____7453 =
                  let uu____7454 = p_noSeqTermAndComment false false rel in
                  let uu____7457 =
                    FStar_Pprint.op_Hat_Hat FStar_Pprint.space
                      FStar_Pprint.lbrace in
                  FStar_Pprint.op_Hat_Hat uu____7454 uu____7457 in
                FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____7453 in
              FStar_Pprint.op_Hat_Hat uu____7450 uu____7452 in
            let bot = FStar_Pprint.rbrace in
            let uu____7459 =
              FStar_Pprint.op_Hat_Hat FStar_Pprint.hardline bot in
            let uu____7460 =
              let uu____7461 =
                let uu____7462 =
                  let uu____7463 = p_noSeqTermAndComment false false init in
                  let uu____7466 =
                    let uu____7467 = str ";" in
                    let uu____7469 =
                      let uu____7470 =
                        separate_map_last FStar_Pprint.hardline p_calcStep
                          steps in
                      FStar_Pprint.op_Hat_Hat FStar_Pprint.hardline
                        uu____7470 in
                    FStar_Pprint.op_Hat_Hat uu____7467 uu____7469 in
                  FStar_Pprint.op_Hat_Hat uu____7463 uu____7466 in
                FStar_Pprint.op_Hat_Hat FStar_Pprint.hardline uu____7462 in
              FStar_All.pipe_left (FStar_Pprint.nest (Prims.of_int (2)))
                uu____7461 in
            FStar_Pprint.enclose head uu____7459 uu____7460
        | uu____7472 -> p_typ ps pb e
and (p_calcStep :
  Prims.bool -> FStar_Parser_AST.calc_step -> FStar_Pprint.document) =
  fun uu____7473 ->
    fun uu____7474 ->
      match uu____7474 with
      | FStar_Parser_AST.CalcStep (rel, just, next) ->
          let uu____7479 =
            let uu____7480 = p_noSeqTermAndComment false false rel in
            let uu____7483 =
              let uu____7484 =
                let uu____7485 =
                  let uu____7486 =
                    let uu____7487 = p_noSeqTermAndComment false false just in
                    let uu____7490 =
                      let uu____7491 =
                        let uu____7492 =
                          let uu____7493 =
                            let uu____7494 =
                              p_noSeqTermAndComment false false next in
                            let uu____7497 = str ";" in
                            FStar_Pprint.op_Hat_Hat uu____7494 uu____7497 in
                          FStar_Pprint.op_Hat_Hat FStar_Pprint.hardline
                            uu____7493 in
                        FStar_Pprint.op_Hat_Hat FStar_Pprint.rbrace
                          uu____7492 in
                      FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____7491 in
                    FStar_Pprint.op_Hat_Hat uu____7487 uu____7490 in
                  FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____7486 in
                FStar_Pprint.op_Hat_Hat FStar_Pprint.lbrace uu____7485 in
              FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____7484 in
            FStar_Pprint.op_Hat_Hat uu____7480 uu____7483 in
          FStar_Pprint.group uu____7479
and (p_attrs_opt :
  FStar_Parser_AST.term Prims.list FStar_Pervasives_Native.option ->
    FStar_Pprint.document)
  =
  fun uu___11_7499 ->
    match uu___11_7499 with
    | FStar_Pervasives_Native.None -> FStar_Pprint.empty
    | FStar_Pervasives_Native.Some terms ->
        let uu____7511 =
          let uu____7512 = str "[@@" in
          let uu____7514 =
            let uu____7515 =
              let uu____7516 = str "; " in
              FStar_Pprint.separate_map uu____7516
                (p_noSeqTermAndComment false false) terms in
            let uu____7520 = str "]" in
            FStar_Pprint.op_Hat_Slash_Hat uu____7515 uu____7520 in
          FStar_Pprint.op_Hat_Slash_Hat uu____7512 uu____7514 in
        FStar_Pprint.group uu____7511
and (p_typ :
  Prims.bool -> Prims.bool -> FStar_Parser_AST.term -> FStar_Pprint.document)
  =
  fun ps ->
    fun pb -> fun e -> with_comment (p_typ' ps pb) e e.FStar_Parser_AST.range
and (p_typ_sep :
  Prims.bool ->
    Prims.bool ->
      FStar_Parser_AST.term ->
        (FStar_Pprint.document * FStar_Pprint.document))
  =
  fun ps ->
    fun pb ->
      fun e -> with_comment_sep (p_typ' ps pb) e e.FStar_Parser_AST.range
and (p_typ' :
  Prims.bool -> Prims.bool -> FStar_Parser_AST.term -> FStar_Pprint.document)
  =
  fun ps ->
    fun pb ->
      fun e ->
        match e.FStar_Parser_AST.tm with
        | FStar_Parser_AST.QForall (bs, (uu____7538, trigger), e1) ->
            let binders_doc = p_binders true bs in
            let term_doc = p_noSeqTermAndComment ps pb e1 in
            (match trigger with
             | [] ->
                 let uu____7572 =
                   let uu____7573 =
                     let uu____7574 = p_quantifier e in
                     FStar_Pprint.op_Hat_Hat uu____7574 FStar_Pprint.space in
                   FStar_Pprint.soft_surround (Prims.of_int (2))
                     Prims.int_zero uu____7573 binders_doc FStar_Pprint.dot in
                 prefix2 uu____7572 term_doc
             | pats ->
                 let uu____7582 =
                   let uu____7583 =
                     let uu____7584 =
                       let uu____7585 =
                         let uu____7586 = p_quantifier e in
                         FStar_Pprint.op_Hat_Hat uu____7586
                           FStar_Pprint.space in
                       FStar_Pprint.soft_surround (Prims.of_int (2))
                         Prims.int_zero uu____7585 binders_doc
                         FStar_Pprint.dot in
                     let uu____7589 = p_trigger trigger in
                     prefix2 uu____7584 uu____7589 in
                   FStar_Pprint.group uu____7583 in
                 prefix2 uu____7582 term_doc)
        | FStar_Parser_AST.QExists (bs, (uu____7591, trigger), e1) ->
            let binders_doc = p_binders true bs in
            let term_doc = p_noSeqTermAndComment ps pb e1 in
            (match trigger with
             | [] ->
                 let uu____7625 =
                   let uu____7626 =
                     let uu____7627 = p_quantifier e in
                     FStar_Pprint.op_Hat_Hat uu____7627 FStar_Pprint.space in
                   FStar_Pprint.soft_surround (Prims.of_int (2))
                     Prims.int_zero uu____7626 binders_doc FStar_Pprint.dot in
                 prefix2 uu____7625 term_doc
             | pats ->
                 let uu____7635 =
                   let uu____7636 =
                     let uu____7637 =
                       let uu____7638 =
                         let uu____7639 = p_quantifier e in
                         FStar_Pprint.op_Hat_Hat uu____7639
                           FStar_Pprint.space in
                       FStar_Pprint.soft_surround (Prims.of_int (2))
                         Prims.int_zero uu____7638 binders_doc
                         FStar_Pprint.dot in
                     let uu____7642 = p_trigger trigger in
                     prefix2 uu____7637 uu____7642 in
                   FStar_Pprint.group uu____7636 in
                 prefix2 uu____7635 term_doc)
        | uu____7643 -> p_simpleTerm ps pb e
and (p_typ_top :
  annotation_style ->
    Prims.bool ->
      Prims.bool -> FStar_Parser_AST.term -> FStar_Pprint.document)
  =
  fun style ->
    fun ps ->
      fun pb ->
        fun e ->
          with_comment (p_typ_top' style ps pb) e e.FStar_Parser_AST.range
and (p_typ_top' :
  annotation_style ->
    Prims.bool ->
      Prims.bool -> FStar_Parser_AST.term -> FStar_Pprint.document)
  =
  fun style ->
    fun ps -> fun pb -> fun e -> p_tmArrow style true p_tmFormula e
and (sig_as_binders_if_possible :
  FStar_Parser_AST.term -> Prims.bool -> FStar_Pprint.document) =
  fun t ->
    fun extra_space ->
      let s = if extra_space then FStar_Pprint.space else FStar_Pprint.empty in
      let uu____7664 = all_binders_annot t in
      if uu____7664
      then
        let uu____7667 =
          p_typ_top (Binders ((Prims.of_int (4)), Prims.int_zero, true))
            false false t in
        FStar_Pprint.op_Hat_Hat s uu____7667
      else
        (let uu____7678 =
           let uu____7679 =
             let uu____7680 =
               p_typ_top (Arrows ((Prims.of_int (2)), (Prims.of_int (2))))
                 false false t in
             FStar_Pprint.op_Hat_Hat s uu____7680 in
           FStar_Pprint.op_Hat_Hat FStar_Pprint.colon uu____7679 in
         FStar_Pprint.group uu____7678)
and (collapse_pats :
  (FStar_Pprint.document * FStar_Pprint.document) Prims.list ->
    FStar_Pprint.document Prims.list)
  =
  fun pats ->
    let fold_fun bs x =
      let uu____7739 = x in
      match uu____7739 with
      | (b1, t1) ->
          (match bs with
           | [] -> [([b1], t1)]
           | hd::tl ->
               let uu____7804 = hd in
               (match uu____7804 with
                | (b2s, t2) ->
                    if t1 = t2
                    then ((FStar_List.append b2s [b1]), t1) :: tl
                    else ([b1], t1) :: hd :: tl)) in
    let p_collapsed_binder cb =
      let uu____7876 = cb in
      match uu____7876 with
      | (bs, typ) ->
          (match bs with
           | [] -> failwith "Impossible"
           | b::[] -> cat_with_colon b typ
           | hd::tl ->
               let uu____7895 =
                 FStar_List.fold_left
                   (fun x ->
                      fun y ->
                        let uu____7901 =
                          FStar_Pprint.op_Hat_Hat FStar_Pprint.space y in
                        FStar_Pprint.op_Hat_Hat x uu____7901) hd tl in
               cat_with_colon uu____7895 typ) in
    let binders = FStar_List.fold_left fold_fun [] (FStar_List.rev pats) in
    map_rev p_collapsed_binder binders
and (pats_as_binders_if_possible :
  FStar_Parser_AST.pattern Prims.list ->
    (FStar_Pprint.document Prims.list * annotation_style))
  =
  fun pats ->
    let all_binders p =
      match p.FStar_Parser_AST.pat with
      | FStar_Parser_AST.PatAscribed (pat, (t, FStar_Pervasives_Native.None))
          ->
          (match ((pat.FStar_Parser_AST.pat), (t.FStar_Parser_AST.tm)) with
           | (FStar_Parser_AST.PatVar (lid, aqual), FStar_Parser_AST.Refine
              ({ FStar_Parser_AST.b = FStar_Parser_AST.Annotated (lid', t1);
                 FStar_Parser_AST.brange = uu____7980;
                 FStar_Parser_AST.blevel = uu____7981;
                 FStar_Parser_AST.aqual = uu____7982;_},
               phi)) when
               let uu____7990 = FStar_Ident.string_of_id lid in
               let uu____7992 = FStar_Ident.string_of_id lid' in
               uu____7990 = uu____7992 ->
               let uu____7995 =
                 let uu____8000 = p_ident lid in
                 p_refinement' aqual uu____8000 t1 phi in
               FStar_Pervasives_Native.Some uu____7995
           | (FStar_Parser_AST.PatVar (lid, aqual), uu____8007) ->
               let uu____8012 =
                 let uu____8017 =
                   let uu____8018 = FStar_Pprint.optional p_aqual aqual in
                   let uu____8019 = p_ident lid in
                   FStar_Pprint.op_Hat_Hat uu____8018 uu____8019 in
                 let uu____8020 = p_tmEqNoRefinement t in
                 (uu____8017, uu____8020) in
               FStar_Pervasives_Native.Some uu____8012
           | uu____8025 -> FStar_Pervasives_Native.None)
      | uu____8034 -> FStar_Pervasives_Native.None in
    let all_unbound p =
      match p.FStar_Parser_AST.pat with
      | FStar_Parser_AST.PatAscribed uu____8047 -> false
      | uu____8059 -> true in
    let uu____8061 = map_if_all all_binders pats in
    match uu____8061 with
    | FStar_Pervasives_Native.Some bs ->
        let uu____8093 = collapse_pats bs in
        (uu____8093, (Binders ((Prims.of_int (4)), Prims.int_zero, true)))
    | FStar_Pervasives_Native.None ->
        let uu____8110 = FStar_List.map p_atomicPattern pats in
        (uu____8110, (Binders ((Prims.of_int (4)), Prims.int_zero, false)))
and (p_quantifier : FStar_Parser_AST.term -> FStar_Pprint.document) =
  fun e ->
    match e.FStar_Parser_AST.tm with
    | FStar_Parser_AST.QForall uu____8122 -> str "forall"
    | FStar_Parser_AST.QExists uu____8142 -> str "exists"
    | uu____8162 ->
        failwith "Imposible : p_quantifier called on a non-quantifier term"
and (p_trigger :
  FStar_Parser_AST.term Prims.list Prims.list -> FStar_Pprint.document) =
  fun uu___12_8164 ->
    match uu___12_8164 with
    | [] -> FStar_Pprint.empty
    | pats ->
        let uu____8176 =
          let uu____8177 =
            let uu____8178 =
              let uu____8179 = str "pattern" in
              let uu____8181 =
                let uu____8182 =
                  let uu____8183 = p_disjunctivePats pats in
                  FStar_Pprint.jump (Prims.of_int (2)) Prims.int_zero
                    uu____8183 in
                FStar_Pprint.op_Hat_Hat uu____8182 FStar_Pprint.rbrace in
              FStar_Pprint.op_Hat_Slash_Hat uu____8179 uu____8181 in
            FStar_Pprint.op_Hat_Hat FStar_Pprint.colon uu____8178 in
          FStar_Pprint.op_Hat_Hat FStar_Pprint.lbrace uu____8177 in
        FStar_Pprint.group uu____8176
and (p_disjunctivePats :
  FStar_Parser_AST.term Prims.list Prims.list -> FStar_Pprint.document) =
  fun pats ->
    let uu____8191 = str "\\/" in
    FStar_Pprint.separate_map uu____8191 p_conjunctivePats pats
and (p_conjunctivePats :
  FStar_Parser_AST.term Prims.list -> FStar_Pprint.document) =
  fun pats ->
    let uu____8198 =
      let uu____8199 = FStar_Pprint.op_Hat_Hat FStar_Pprint.semi break1 in
      FStar_Pprint.separate_map uu____8199 p_appTerm pats in
    FStar_Pprint.group uu____8198
and (p_simpleTerm :
  Prims.bool -> Prims.bool -> FStar_Parser_AST.term -> FStar_Pprint.document)
  =
  fun ps ->
    fun pb ->
      fun e ->
        match e.FStar_Parser_AST.tm with
        | FStar_Parser_AST.Abs (pats, e1) ->
            let uu____8211 = p_term_sep false pb e1 in
            (match uu____8211 with
             | (comm, doc) ->
                 let prefix =
                   let uu____8220 = str "fun" in
                   let uu____8222 =
                     let uu____8223 =
                       FStar_Pprint.separate_map break1 p_atomicPattern pats in
                     FStar_Pprint.op_Hat_Slash_Hat uu____8223
                       FStar_Pprint.rarrow in
                   op_Hat_Slash_Plus_Hat uu____8220 uu____8222 in
                 let uu____8224 =
                   if comm <> FStar_Pprint.empty
                   then
                     let uu____8226 =
                       let uu____8227 =
                         let uu____8228 =
                           FStar_Pprint.op_Hat_Hat FStar_Pprint.hardline doc in
                         FStar_Pprint.op_Hat_Hat comm uu____8228 in
                       FStar_Pprint.op_Hat_Hat FStar_Pprint.hardline
                         uu____8227 in
                     FStar_Pprint.op_Hat_Hat prefix uu____8226
                   else
                     (let uu____8231 = op_Hat_Slash_Plus_Hat prefix doc in
                      FStar_Pprint.group uu____8231) in
                 let uu____8232 = paren_if ps in uu____8232 uu____8224)
        | uu____8237 -> p_tmIff e
and (p_maybeFocusArrow : Prims.bool -> FStar_Pprint.document) =
  fun b -> if b then str "~>" else FStar_Pprint.rarrow
and (p_patternBranch :
  Prims.bool ->
    (FStar_Parser_AST.pattern * FStar_Parser_AST.term
      FStar_Pervasives_Native.option * FStar_Parser_AST.term) ->
      FStar_Pprint.document)
  =
  fun pb ->
    fun uu____8245 ->
      match uu____8245 with
      | (pat, when_opt, e) ->
          let one_pattern_branch p =
            let branch =
              match when_opt with
              | FStar_Pervasives_Native.None ->
                  let uu____8269 =
                    let uu____8270 =
                      let uu____8271 =
                        let uu____8272 = p_tuplePattern p in
                        let uu____8273 =
                          FStar_Pprint.op_Hat_Hat FStar_Pprint.space
                            FStar_Pprint.rarrow in
                        FStar_Pprint.op_Hat_Hat uu____8272 uu____8273 in
                      FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____8271 in
                    FStar_Pprint.op_Hat_Hat FStar_Pprint.bar uu____8270 in
                  FStar_Pprint.group uu____8269
              | FStar_Pervasives_Native.Some f ->
                  let uu____8275 =
                    let uu____8276 =
                      let uu____8277 =
                        let uu____8278 =
                          let uu____8279 =
                            let uu____8280 = p_tuplePattern p in
                            let uu____8281 = str "when" in
                            FStar_Pprint.op_Hat_Slash_Hat uu____8280
                              uu____8281 in
                          FStar_Pprint.group uu____8279 in
                        let uu____8283 =
                          let uu____8284 =
                            let uu____8287 = p_tmFormula f in
                            [uu____8287; FStar_Pprint.rarrow] in
                          FStar_Pprint.flow break1 uu____8284 in
                        FStar_Pprint.op_Hat_Slash_Hat uu____8278 uu____8283 in
                      FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____8277 in
                    FStar_Pprint.op_Hat_Hat FStar_Pprint.bar uu____8276 in
                  FStar_Pprint.hang (Prims.of_int (2)) uu____8275 in
            let uu____8289 = p_term_sep false pb e in
            match uu____8289 with
            | (comm, doc) ->
                if pb
                then
                  (if comm = FStar_Pprint.empty
                   then
                     let uu____8299 = op_Hat_Slash_Plus_Hat branch doc in
                     FStar_Pprint.group uu____8299
                   else
                     (let uu____8302 =
                        let uu____8303 =
                          let uu____8304 =
                            let uu____8305 =
                              let uu____8306 =
                                FStar_Pprint.op_Hat_Hat break1 comm in
                              FStar_Pprint.op_Hat_Hat doc uu____8306 in
                            op_Hat_Slash_Plus_Hat branch uu____8305 in
                          FStar_Pprint.group uu____8304 in
                        let uu____8307 =
                          let uu____8308 =
                            let uu____8309 =
                              inline_comment_or_above comm doc
                                FStar_Pprint.empty in
                            jump2 uu____8309 in
                          FStar_Pprint.op_Hat_Hat branch uu____8308 in
                        FStar_Pprint.ifflat uu____8303 uu____8307 in
                      FStar_Pprint.group uu____8302))
                else
                  if comm <> FStar_Pprint.empty
                  then
                    (let uu____8313 =
                       let uu____8314 =
                         FStar_Pprint.op_Hat_Hat FStar_Pprint.hardline doc in
                       FStar_Pprint.op_Hat_Hat comm uu____8314 in
                     op_Hat_Slash_Plus_Hat branch uu____8313)
                  else op_Hat_Slash_Plus_Hat branch doc in
          (match pat.FStar_Parser_AST.pat with
           | FStar_Parser_AST.PatOr pats ->
               (match FStar_List.rev pats with
                | hd::tl ->
                    let last_pat_branch = one_pattern_branch hd in
                    let uu____8325 =
                      let uu____8326 =
                        let uu____8327 =
                          let uu____8328 =
                            let uu____8329 =
                              let uu____8330 =
                                FStar_Pprint.op_Hat_Hat FStar_Pprint.bar
                                  FStar_Pprint.space in
                              FStar_Pprint.op_Hat_Hat break1 uu____8330 in
                            FStar_Pprint.separate_map uu____8329
                              p_tuplePattern (FStar_List.rev tl) in
                          FStar_Pprint.op_Hat_Slash_Hat uu____8328
                            last_pat_branch in
                        FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____8327 in
                      FStar_Pprint.op_Hat_Hat FStar_Pprint.bar uu____8326 in
                    FStar_Pprint.group uu____8325
                | [] ->
                    failwith "Impossible: disjunctive pattern can't be empty")
           | uu____8332 -> one_pattern_branch pat)
and (p_tmIff : FStar_Parser_AST.term -> FStar_Pprint.document) =
  fun e ->
    match e.FStar_Parser_AST.tm with
    | FStar_Parser_AST.Op (id, e1::e2::[]) when
        let uu____8339 = FStar_Ident.string_of_id id in uu____8339 = "<==>"
        ->
        let uu____8343 = str "<==>" in
        let uu____8345 = p_tmImplies e1 in
        let uu____8346 = p_tmIff e2 in
        infix0 uu____8343 uu____8345 uu____8346
    | uu____8347 -> p_tmImplies e
and (p_tmImplies : FStar_Parser_AST.term -> FStar_Pprint.document) =
  fun e ->
    match e.FStar_Parser_AST.tm with
    | FStar_Parser_AST.Op (id, e1::e2::[]) when
        let uu____8354 = FStar_Ident.string_of_id id in uu____8354 = "==>" ->
        let uu____8358 = str "==>" in
        let uu____8360 =
          p_tmArrow (Arrows ((Prims.of_int (2)), (Prims.of_int (2)))) false
            p_tmFormula e1 in
        let uu____8366 = p_tmImplies e2 in
        infix0 uu____8358 uu____8360 uu____8366
    | uu____8367 ->
        p_tmArrow (Arrows ((Prims.of_int (2)), (Prims.of_int (2)))) false
          p_tmFormula e
and (format_sig :
  annotation_style ->
    FStar_Pprint.document Prims.list ->
      Prims.bool -> Prims.bool -> FStar_Pprint.document)
  =
  fun style ->
    fun terms ->
      fun no_last_op ->
        fun flat_space ->
          let uu____8381 =
            FStar_List.splitAt ((FStar_List.length terms) - Prims.int_one)
              terms in
          match uu____8381 with
          | (terms', last) ->
              let uu____8401 =
                match style with
                | Arrows (n, ln) ->
                    let uu____8436 =
                      let uu____8437 =
                        FStar_Pprint.op_Hat_Hat FStar_Pprint.rarrow break1 in
                      FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____8437 in
                    let uu____8438 =
                      FStar_Pprint.op_Hat_Hat FStar_Pprint.rarrow
                        FStar_Pprint.space in
                    (n, ln, terms', uu____8436, uu____8438)
                | Binders (n, ln, parens) ->
                    let uu____8452 =
                      if parens
                      then FStar_List.map soft_parens_with_nesting terms'
                      else terms' in
                    let uu____8460 =
                      FStar_Pprint.op_Hat_Hat FStar_Pprint.colon
                        FStar_Pprint.space in
                    (n, ln, uu____8452, break1, uu____8460) in
              (match uu____8401 with
               | (n, last_n, terms'1, sep, last_op) ->
                   let last1 = FStar_List.hd last in
                   let last_op1 =
                     if
                       ((FStar_List.length terms) > Prims.int_one) &&
                         (Prims.op_Negation no_last_op)
                     then last_op
                     else FStar_Pprint.empty in
                   let one_line_space =
                     if
                       (Prims.op_Negation (last1 = FStar_Pprint.empty)) ||
                         (Prims.op_Negation no_last_op)
                     then FStar_Pprint.space
                     else FStar_Pprint.empty in
                   let single_line_arg_indent =
                     FStar_Pprint.repeat n FStar_Pprint.space in
                   let fs =
                     if flat_space
                     then FStar_Pprint.space
                     else FStar_Pprint.empty in
                   (match FStar_List.length terms with
                    | uu____8493 when uu____8493 = Prims.int_one ->
                        FStar_List.hd terms
                    | uu____8494 ->
                        let uu____8495 =
                          let uu____8496 =
                            let uu____8497 =
                              let uu____8498 =
                                FStar_Pprint.separate sep terms'1 in
                              let uu____8499 =
                                let uu____8500 =
                                  FStar_Pprint.op_Hat_Hat last_op1 last1 in
                                FStar_Pprint.op_Hat_Hat one_line_space
                                  uu____8500 in
                              FStar_Pprint.op_Hat_Hat uu____8498 uu____8499 in
                            FStar_Pprint.op_Hat_Hat fs uu____8497 in
                          let uu____8501 =
                            let uu____8502 =
                              let uu____8503 =
                                let uu____8504 =
                                  let uu____8505 =
                                    FStar_Pprint.separate sep terms'1 in
                                  FStar_Pprint.op_Hat_Hat fs uu____8505 in
                                let uu____8506 =
                                  let uu____8507 =
                                    let uu____8508 =
                                      let uu____8509 =
                                        FStar_Pprint.op_Hat_Hat sep
                                          single_line_arg_indent in
                                      let uu____8510 =
                                        FStar_List.map
                                          (fun x ->
                                             let uu____8516 =
                                               FStar_Pprint.hang
                                                 (Prims.of_int (2)) x in
                                             FStar_Pprint.align uu____8516)
                                          terms'1 in
                                      FStar_Pprint.separate uu____8509
                                        uu____8510 in
                                    FStar_Pprint.op_Hat_Hat
                                      single_line_arg_indent uu____8508 in
                                  jump2 uu____8507 in
                                FStar_Pprint.ifflat uu____8504 uu____8506 in
                              FStar_Pprint.group uu____8503 in
                            let uu____8518 =
                              let uu____8519 =
                                let uu____8520 =
                                  FStar_Pprint.op_Hat_Hat last_op1 last1 in
                                FStar_Pprint.hang last_n uu____8520 in
                              FStar_Pprint.align uu____8519 in
                            FStar_Pprint.prefix n Prims.int_one uu____8502
                              uu____8518 in
                          FStar_Pprint.ifflat uu____8496 uu____8501 in
                        FStar_Pprint.group uu____8495))
and (p_tmArrow :
  annotation_style ->
    Prims.bool ->
      (FStar_Parser_AST.term -> FStar_Pprint.document) ->
        FStar_Parser_AST.term -> FStar_Pprint.document)
  =
  fun style ->
    fun flat_space ->
      fun p_Tm ->
        fun e ->
          let terms =
            match style with
            | Arrows uu____8534 -> p_tmArrow' p_Tm e
            | Binders uu____8541 -> collapse_binders p_Tm e in
          format_sig style terms false flat_space
and (p_tmArrow' :
  (FStar_Parser_AST.term -> FStar_Pprint.document) ->
    FStar_Parser_AST.term -> FStar_Pprint.document Prims.list)
  =
  fun p_Tm ->
    fun e ->
      match e.FStar_Parser_AST.tm with
      | FStar_Parser_AST.Product (bs, tgt) ->
          let uu____8564 = FStar_List.map (fun b -> p_binder false b) bs in
          let uu____8570 = p_tmArrow' p_Tm tgt in
          FStar_List.append uu____8564 uu____8570
      | uu____8573 -> let uu____8574 = p_Tm e in [uu____8574]
and (collapse_binders :
  (FStar_Parser_AST.term -> FStar_Pprint.document) ->
    FStar_Parser_AST.term -> FStar_Pprint.document Prims.list)
  =
  fun p_Tm ->
    fun e ->
      let rec accumulate_binders p_Tm1 e1 =
        match e1.FStar_Parser_AST.tm with
        | FStar_Parser_AST.Product (bs, tgt) ->
            let uu____8627 = FStar_List.map (fun b -> p_binder' false b) bs in
            let uu____8653 = accumulate_binders p_Tm1 tgt in
            FStar_List.append uu____8627 uu____8653
        | uu____8676 ->
            let uu____8677 =
              let uu____8688 = p_Tm1 e1 in
              (uu____8688, FStar_Pervasives_Native.None, cat_with_colon) in
            [uu____8677] in
      let fold_fun bs x =
        let uu____8786 = x in
        match uu____8786 with
        | (b1, t1, f1) ->
            (match bs with
             | [] -> [([b1], t1, f1)]
             | hd::tl ->
                 let uu____8918 = hd in
                 (match uu____8918 with
                  | (b2s, t2, uu____8947) ->
                      (match (t1, t2) with
                       | (FStar_Pervasives_Native.Some typ1,
                          FStar_Pervasives_Native.Some typ2) ->
                           if typ1 = typ2
                           then ((FStar_List.append b2s [b1]), t1, f1) :: tl
                           else ([b1], t1, f1) :: hd :: tl
                       | uu____9049 -> ([b1], t1, f1) :: bs))) in
      let p_collapsed_binder cb =
        let uu____9106 = cb in
        match uu____9106 with
        | (bs, t, f) ->
            (match t with
             | FStar_Pervasives_Native.None ->
                 (match bs with
                  | b::[] -> b
                  | uu____9135 -> failwith "Impossible")
             | FStar_Pervasives_Native.Some typ ->
                 (match bs with
                  | [] -> failwith "Impossible"
                  | b::[] -> f b typ
                  | hd::tl ->
                      let uu____9146 =
                        FStar_List.fold_left
                          (fun x ->
                             fun y ->
                               let uu____9152 =
                                 FStar_Pprint.op_Hat_Hat FStar_Pprint.space y in
                               FStar_Pprint.op_Hat_Hat x uu____9152) hd tl in
                      f uu____9146 typ)) in
      let binders =
        let uu____9168 = accumulate_binders p_Tm e in
        FStar_List.fold_left fold_fun [] uu____9168 in
      map_rev p_collapsed_binder binders
and (p_tmFormula : FStar_Parser_AST.term -> FStar_Pprint.document) =
  fun e ->
    let conj =
      let uu____9231 =
        let uu____9232 = str "/\\" in
        FStar_Pprint.op_Hat_Hat uu____9232 break1 in
      FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____9231 in
    let disj =
      let uu____9235 =
        let uu____9236 = str "\\/" in
        FStar_Pprint.op_Hat_Hat uu____9236 break1 in
      FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____9235 in
    let formula = p_tmDisjunction e in
    FStar_Pprint.flow_map disj
      (fun d -> FStar_Pprint.flow_map conj (fun x -> FStar_Pprint.group x) d)
      formula
and (p_tmDisjunction :
  FStar_Parser_AST.term -> FStar_Pprint.document Prims.list Prims.list) =
  fun e ->
    match e.FStar_Parser_AST.tm with
    | FStar_Parser_AST.Op (id, e1::e2::[]) when
        let uu____9261 = FStar_Ident.string_of_id id in uu____9261 = "\\/" ->
        let uu____9265 = p_tmDisjunction e1 in
        let uu____9270 = let uu____9275 = p_tmConjunction e2 in [uu____9275] in
        FStar_List.append uu____9265 uu____9270
    | uu____9284 -> let uu____9285 = p_tmConjunction e in [uu____9285]
and (p_tmConjunction :
  FStar_Parser_AST.term -> FStar_Pprint.document Prims.list) =
  fun e ->
    match e.FStar_Parser_AST.tm with
    | FStar_Parser_AST.Op (id, e1::e2::[]) when
        let uu____9300 = FStar_Ident.string_of_id id in uu____9300 = "/\\" ->
        let uu____9304 = p_tmConjunction e1 in
        let uu____9307 = let uu____9310 = p_tmTuple e2 in [uu____9310] in
        FStar_List.append uu____9304 uu____9307
    | uu____9311 -> let uu____9312 = p_tmTuple e in [uu____9312]
and (p_tmTuple : FStar_Parser_AST.term -> FStar_Pprint.document) =
  fun e -> with_comment p_tmTuple' e e.FStar_Parser_AST.range
and (p_tmTuple' : FStar_Parser_AST.term -> FStar_Pprint.document) =
  fun e ->
    match e.FStar_Parser_AST.tm with
    | FStar_Parser_AST.Construct (lid, args) when
        (is_tuple_constructor lid) && (all1_explicit args) ->
        let uu____9329 = FStar_Pprint.op_Hat_Hat FStar_Pprint.comma break1 in
        FStar_Pprint.separate_map uu____9329
          (fun uu____9337 ->
             match uu____9337 with | (e1, uu____9343) -> p_tmEq e1) args
    | uu____9344 -> p_tmEq e
and (paren_if_gt :
  Prims.int -> Prims.int -> FStar_Pprint.document -> FStar_Pprint.document) =
  fun curr ->
    fun mine ->
      fun doc ->
        if mine <= curr
        then doc
        else
          (let uu____9353 =
             let uu____9354 = FStar_Pprint.op_Hat_Hat doc FStar_Pprint.rparen in
             FStar_Pprint.op_Hat_Hat FStar_Pprint.lparen uu____9354 in
           FStar_Pprint.group uu____9353)
and (p_tmEqWith :
  (FStar_Parser_AST.term -> FStar_Pprint.document) ->
    FStar_Parser_AST.term -> FStar_Pprint.document)
  =
  fun p_X ->
    fun e ->
      let n =
        max_level
          (FStar_List.append [colon_equals; pipe_right] operatorInfix0ad12) in
      p_tmEqWith' p_X n e
and (p_tmEqWith' :
  (FStar_Parser_AST.term -> FStar_Pprint.document) ->
    Prims.int -> FStar_Parser_AST.term -> FStar_Pprint.document)
  =
  fun p_X ->
    fun curr ->
      fun e ->
        match e.FStar_Parser_AST.tm with
        | FStar_Parser_AST.Op (op, e1::e2::[]) when
            (let uu____9374 =
               (let uu____9378 = FStar_Ident.string_of_id op in
                uu____9378 = "==>") ||
                 (let uu____9383 = FStar_Ident.string_of_id op in
                  uu____9383 = "<==>") in
             Prims.op_Negation uu____9374) &&
              (((is_operatorInfix0ad12 op) ||
                  (let uu____9388 = FStar_Ident.string_of_id op in
                   uu____9388 = "="))
                 ||
                 (let uu____9393 = FStar_Ident.string_of_id op in
                  uu____9393 = "|>"))
            ->
            let op1 = FStar_Ident.string_of_id op in
            let uu____9399 = levels op1 in
            (match uu____9399 with
             | (left, mine, right) ->
                 let uu____9418 =
                   let uu____9419 = FStar_All.pipe_left str op1 in
                   let uu____9421 = p_tmEqWith' p_X left e1 in
                   let uu____9422 = p_tmEqWith' p_X right e2 in
                   infix0 uu____9419 uu____9421 uu____9422 in
                 paren_if_gt curr mine uu____9418)
        | FStar_Parser_AST.Op (id, e1::e2::[]) when
            let uu____9428 = FStar_Ident.string_of_id id in uu____9428 = ":="
            ->
            let uu____9432 =
              let uu____9433 = p_tmEqWith p_X e1 in
              let uu____9434 =
                let uu____9435 =
                  let uu____9436 =
                    let uu____9437 = p_tmEqWith p_X e2 in
                    op_Hat_Slash_Plus_Hat FStar_Pprint.equals uu____9437 in
                  FStar_Pprint.op_Hat_Hat FStar_Pprint.colon uu____9436 in
                FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____9435 in
              FStar_Pprint.op_Hat_Hat uu____9433 uu____9434 in
            FStar_Pprint.group uu____9432
        | FStar_Parser_AST.Op (id, e1::[]) when
            let uu____9442 = FStar_Ident.string_of_id id in uu____9442 = "-"
            ->
            let uu____9446 = levels "-" in
            (match uu____9446 with
             | (left, mine, right) ->
                 let uu____9466 = p_tmEqWith' p_X mine e1 in
                 FStar_Pprint.op_Hat_Slash_Hat FStar_Pprint.minus uu____9466)
        | uu____9467 -> p_tmNoEqWith p_X e
and (p_tmNoEqWith :
  (FStar_Parser_AST.term -> FStar_Pprint.document) ->
    FStar_Parser_AST.term -> FStar_Pprint.document)
  =
  fun p_X ->
    fun e ->
      let n = max_level [colon_colon; amp; opinfix3; opinfix4] in
      p_tmNoEqWith' false p_X n e
and (p_tmNoEqWith' :
  Prims.bool ->
    (FStar_Parser_AST.term -> FStar_Pprint.document) ->
      Prims.int -> FStar_Parser_AST.term -> FStar_Pprint.document)
  =
  fun inside_tuple ->
    fun p_X ->
      fun curr ->
        fun e ->
          match e.FStar_Parser_AST.tm with
          | FStar_Parser_AST.Construct
              (lid, (e1, uu____9515)::(e2, uu____9517)::[]) when
              (FStar_Ident.lid_equals lid FStar_Parser_Const.cons_lid) &&
                (let uu____9537 = is_list e in Prims.op_Negation uu____9537)
              ->
              let op = "::" in
              let uu____9542 = levels op in
              (match uu____9542 with
               | (left, mine, right) ->
                   let uu____9561 =
                     let uu____9562 = str op in
                     let uu____9563 = p_tmNoEqWith' false p_X left e1 in
                     let uu____9565 = p_tmNoEqWith' false p_X right e2 in
                     infix0 uu____9562 uu____9563 uu____9565 in
                   paren_if_gt curr mine uu____9561)
          | FStar_Parser_AST.Sum (binders, res) ->
              let op = "&" in
              let uu____9584 = levels op in
              (match uu____9584 with
               | (left, mine, right) ->
                   let p_dsumfst bt =
                     match bt with
                     | FStar_Util.Inl b ->
                         let uu____9618 = p_binder false b in
                         let uu____9620 =
                           let uu____9621 =
                             let uu____9622 = str op in
                             FStar_Pprint.op_Hat_Hat uu____9622 break1 in
                           FStar_Pprint.op_Hat_Hat FStar_Pprint.space
                             uu____9621 in
                         FStar_Pprint.op_Hat_Hat uu____9618 uu____9620
                     | FStar_Util.Inr t ->
                         let uu____9624 = p_tmNoEqWith' false p_X left t in
                         let uu____9626 =
                           let uu____9627 =
                             let uu____9628 = str op in
                             FStar_Pprint.op_Hat_Hat uu____9628 break1 in
                           FStar_Pprint.op_Hat_Hat FStar_Pprint.space
                             uu____9627 in
                         FStar_Pprint.op_Hat_Hat uu____9624 uu____9626 in
                   let uu____9629 =
                     let uu____9630 =
                       FStar_Pprint.concat_map p_dsumfst binders in
                     let uu____9635 = p_tmNoEqWith' false p_X right res in
                     FStar_Pprint.op_Hat_Hat uu____9630 uu____9635 in
                   paren_if_gt curr mine uu____9629)
          | FStar_Parser_AST.Op (id, e1::e2::[]) when
              (let uu____9644 = FStar_Ident.string_of_id id in
               uu____9644 = "*") && (FStar_ST.op_Bang unfold_tuples)
              ->
              let op = "*" in
              let uu____9672 = levels op in
              (match uu____9672 with
               | (left, mine, right) ->
                   if inside_tuple
                   then
                     let uu____9692 = str op in
                     let uu____9693 = p_tmNoEqWith' true p_X left e1 in
                     let uu____9695 = p_tmNoEqWith' true p_X right e2 in
                     infix0 uu____9692 uu____9693 uu____9695
                   else
                     (let uu____9699 =
                        let uu____9700 = str op in
                        let uu____9701 = p_tmNoEqWith' true p_X left e1 in
                        let uu____9703 = p_tmNoEqWith' true p_X right e2 in
                        infix0 uu____9700 uu____9701 uu____9703 in
                      paren_if_gt curr mine uu____9699))
          | FStar_Parser_AST.Op (op, e1::e2::[]) when is_operatorInfix34 op
              ->
              let op1 = FStar_Ident.string_of_id op in
              let uu____9712 = levels op1 in
              (match uu____9712 with
               | (left, mine, right) ->
                   let uu____9731 =
                     let uu____9732 = str op1 in
                     let uu____9733 = p_tmNoEqWith' false p_X left e1 in
                     let uu____9735 = p_tmNoEqWith' false p_X right e2 in
                     infix0 uu____9732 uu____9733 uu____9735 in
                   paren_if_gt curr mine uu____9731)
          | FStar_Parser_AST.Record (with_opt, record_fields) ->
              let uu____9755 =
                let uu____9756 =
                  default_or_map FStar_Pprint.empty p_with_clause with_opt in
                let uu____9757 =
                  let uu____9758 =
                    FStar_Pprint.op_Hat_Hat FStar_Pprint.semi break1 in
                  separate_map_last uu____9758 p_simpleDef record_fields in
                FStar_Pprint.op_Hat_Hat uu____9756 uu____9757 in
              braces_with_nesting uu____9755
          | FStar_Parser_AST.Op (id, e1::[]) when
              let uu____9767 = FStar_Ident.string_of_id id in
              uu____9767 = "~" ->
              let uu____9771 =
                let uu____9772 = str "~" in
                let uu____9774 = p_atomicTerm e1 in
                FStar_Pprint.op_Hat_Hat uu____9772 uu____9774 in
              FStar_Pprint.group uu____9771
          | FStar_Parser_AST.Paren p when inside_tuple ->
              (match p.FStar_Parser_AST.tm with
               | FStar_Parser_AST.Op (id, e1::e2::[]) when
                   let uu____9781 = FStar_Ident.string_of_id id in
                   uu____9781 = "*" ->
                   let op = "*" in
                   let uu____9788 = levels op in
                   (match uu____9788 with
                    | (left, mine, right) ->
                        let uu____9807 =
                          let uu____9808 = str op in
                          let uu____9809 = p_tmNoEqWith' true p_X left e1 in
                          let uu____9811 = p_tmNoEqWith' true p_X right e2 in
                          infix0 uu____9808 uu____9809 uu____9811 in
                        paren_if_gt curr mine uu____9807)
               | uu____9813 -> p_X e)
          | uu____9814 -> p_X e
and (p_tmEqNoRefinement : FStar_Parser_AST.term -> FStar_Pprint.document) =
  fun e -> p_tmEqWith p_appTerm e
and (p_tmEq : FStar_Parser_AST.term -> FStar_Pprint.document) =
  fun e -> p_tmEqWith p_tmRefinement e
and (p_tmNoEq : FStar_Parser_AST.term -> FStar_Pprint.document) =
  fun e -> p_tmNoEqWith p_tmRefinement e
and (p_tmRefinement : FStar_Parser_AST.term -> FStar_Pprint.document) =
  fun e ->
    match e.FStar_Parser_AST.tm with
    | FStar_Parser_AST.NamedTyp (lid, e1) ->
        let uu____9821 =
          let uu____9822 = p_lident lid in
          let uu____9823 =
            let uu____9824 = p_appTerm e1 in
            FStar_Pprint.op_Hat_Slash_Hat FStar_Pprint.colon uu____9824 in
          FStar_Pprint.op_Hat_Slash_Hat uu____9822 uu____9823 in
        FStar_Pprint.group uu____9821
    | FStar_Parser_AST.Refine (b, phi) -> p_refinedBinder b phi
    | uu____9827 -> p_appTerm e
and (p_with_clause : FStar_Parser_AST.term -> FStar_Pprint.document) =
  fun e ->
    let uu____9829 = p_appTerm e in
    let uu____9830 =
      let uu____9831 =
        let uu____9832 = str "with" in
        FStar_Pprint.op_Hat_Hat uu____9832 break1 in
      FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____9831 in
    FStar_Pprint.op_Hat_Hat uu____9829 uu____9830
and (p_refinedBinder :
  FStar_Parser_AST.binder -> FStar_Parser_AST.term -> FStar_Pprint.document)
  =
  fun b ->
    fun phi ->
      match b.FStar_Parser_AST.b with
      | FStar_Parser_AST.Annotated (lid, t) ->
          let uu____9838 = p_lident lid in
          p_refinement b.FStar_Parser_AST.aqual uu____9838 t phi
      | FStar_Parser_AST.TAnnotated uu____9839 ->
          failwith "Is this still used ?"
      | FStar_Parser_AST.Variable uu____9845 ->
          let uu____9846 =
            let uu____9848 = FStar_Parser_AST.binder_to_string b in
            FStar_Util.format1
              "Imposible : a refined binder ought to be annotated %s"
              uu____9848 in
          failwith uu____9846
      | FStar_Parser_AST.TVariable uu____9851 ->
          let uu____9852 =
            let uu____9854 = FStar_Parser_AST.binder_to_string b in
            FStar_Util.format1
              "Imposible : a refined binder ought to be annotated %s"
              uu____9854 in
          failwith uu____9852
      | FStar_Parser_AST.NoName uu____9857 ->
          let uu____9858 =
            let uu____9860 = FStar_Parser_AST.binder_to_string b in
            FStar_Util.format1
              "Imposible : a refined binder ought to be annotated %s"
              uu____9860 in
          failwith uu____9858
and (p_simpleDef :
  Prims.bool ->
    (FStar_Ident.lid * FStar_Parser_AST.term) -> FStar_Pprint.document)
  =
  fun ps ->
    fun uu____9864 ->
      match uu____9864 with
      | (lid, e) ->
          let uu____9872 =
            let uu____9873 = p_qlident lid in
            let uu____9874 =
              let uu____9875 = p_noSeqTermAndComment ps false e in
              FStar_Pprint.op_Hat_Slash_Hat FStar_Pprint.equals uu____9875 in
            FStar_Pprint.op_Hat_Slash_Hat uu____9873 uu____9874 in
          FStar_Pprint.group uu____9872
and (p_appTerm : FStar_Parser_AST.term -> FStar_Pprint.document) =
  fun e ->
    match e.FStar_Parser_AST.tm with
    | FStar_Parser_AST.App uu____9878 when is_general_application e ->
        let uu____9885 = head_and_args e in
        (match uu____9885 with
         | (head, args) ->
             (match args with
              | e1::e2::[] when
                  (FStar_Pervasives_Native.snd e1) = FStar_Parser_AST.Infix
                  ->
                  let uu____9932 = p_argTerm e1 in
                  let uu____9933 =
                    let uu____9934 =
                      let uu____9935 =
                        let uu____9936 = str "`" in
                        let uu____9938 =
                          let uu____9939 = p_indexingTerm head in
                          let uu____9940 = str "`" in
                          FStar_Pprint.op_Hat_Hat uu____9939 uu____9940 in
                        FStar_Pprint.op_Hat_Hat uu____9936 uu____9938 in
                      FStar_Pprint.group uu____9935 in
                    let uu____9942 = p_argTerm e2 in
                    FStar_Pprint.op_Hat_Slash_Hat uu____9934 uu____9942 in
                  FStar_Pprint.op_Hat_Slash_Hat uu____9932 uu____9933
              | uu____9943 ->
                  let uu____9950 =
                    let uu____9961 = FStar_ST.op_Bang should_print_fs_typ_app in
                    if uu____9961
                    then
                      let uu____9995 =
                        FStar_Util.take
                          (fun uu____10019 ->
                             match uu____10019 with
                             | (uu____10025, aq) ->
                                 aq = FStar_Parser_AST.FsTypApp) args in
                      match uu____9995 with
                      | (fs_typ_args, args1) ->
                          let uu____10063 =
                            let uu____10064 = p_indexingTerm head in
                            let uu____10065 =
                              let uu____10066 =
                                FStar_Pprint.op_Hat_Hat FStar_Pprint.comma
                                  break1 in
                              soft_surround_map_or_flow (Prims.of_int (2))
                                Prims.int_zero FStar_Pprint.empty
                                FStar_Pprint.langle uu____10066
                                FStar_Pprint.rangle p_fsTypArg fs_typ_args in
                            FStar_Pprint.op_Hat_Hat uu____10064 uu____10065 in
                          (uu____10063, args1)
                    else
                      (let uu____10081 = p_indexingTerm head in
                       (uu____10081, args)) in
                  (match uu____9950 with
                   | (head_doc, args1) ->
                       let uu____10102 =
                         let uu____10103 =
                           FStar_Pprint.op_Hat_Hat head_doc
                             FStar_Pprint.space in
                         soft_surround_map_or_flow (Prims.of_int (2))
                           Prims.int_zero head_doc uu____10103 break1
                           FStar_Pprint.empty p_argTerm args1 in
                       FStar_Pprint.group uu____10102)))
    | FStar_Parser_AST.Construct (lid, args) when
        (is_general_construction e) &&
          (let uu____10125 =
             (is_dtuple_constructor lid) && (all1_explicit args) in
           Prims.op_Negation uu____10125)
        ->
        (match args with
         | [] -> p_quident lid
         | arg::[] ->
             let uu____10144 =
               let uu____10145 = p_quident lid in
               let uu____10146 = p_argTerm arg in
               FStar_Pprint.op_Hat_Slash_Hat uu____10145 uu____10146 in
             FStar_Pprint.group uu____10144
         | hd::tl ->
             let uu____10163 =
               let uu____10164 =
                 let uu____10165 =
                   let uu____10166 = p_quident lid in
                   let uu____10167 = p_argTerm hd in
                   prefix2 uu____10166 uu____10167 in
                 FStar_Pprint.group uu____10165 in
               let uu____10168 =
                 let uu____10169 =
                   FStar_Pprint.separate_map break1 p_argTerm tl in
                 jump2 uu____10169 in
               FStar_Pprint.op_Hat_Hat uu____10164 uu____10168 in
             FStar_Pprint.group uu____10163)
    | uu____10174 -> p_indexingTerm e
and (p_argTerm :
  (FStar_Parser_AST.term * FStar_Parser_AST.imp) -> FStar_Pprint.document) =
  fun arg_imp ->
    match arg_imp with
    | (u, FStar_Parser_AST.UnivApp) -> p_universe u
    | (e, FStar_Parser_AST.FsTypApp) ->
        (FStar_Errors.log_issue e.FStar_Parser_AST.range
           (FStar_Errors.Warning_UnexpectedFsTypApp,
             "Unexpected FsTypApp, output might not be formatted correctly.");
         (let uu____10185 = p_indexingTerm e in
          FStar_Pprint.surround (Prims.of_int (2)) Prims.int_one
            FStar_Pprint.langle uu____10185 FStar_Pprint.rangle))
    | (e, FStar_Parser_AST.Hash) ->
        let uu____10189 = str "#" in
        let uu____10191 = p_indexingTerm e in
        FStar_Pprint.op_Hat_Hat uu____10189 uu____10191
    | (e, FStar_Parser_AST.HashBrace t) ->
        let uu____10194 = str "#[" in
        let uu____10196 =
          let uu____10197 = p_indexingTerm t in
          let uu____10198 =
            let uu____10199 = str "]" in
            let uu____10201 = p_indexingTerm e in
            FStar_Pprint.op_Hat_Hat uu____10199 uu____10201 in
          FStar_Pprint.op_Hat_Hat uu____10197 uu____10198 in
        FStar_Pprint.op_Hat_Hat uu____10194 uu____10196
    | (e, FStar_Parser_AST.Infix) -> p_indexingTerm e
    | (e, FStar_Parser_AST.Nothing) -> p_indexingTerm e
and (p_fsTypArg :
  (FStar_Parser_AST.term * FStar_Parser_AST.imp) -> FStar_Pprint.document) =
  fun uu____10204 ->
    match uu____10204 with | (e, uu____10210) -> p_indexingTerm e
and (p_indexingTerm_aux :
  (FStar_Parser_AST.term -> FStar_Pprint.document) ->
    FStar_Parser_AST.term -> FStar_Pprint.document)
  =
  fun exit ->
    fun e ->
      match e.FStar_Parser_AST.tm with
      | FStar_Parser_AST.Op (id, e1::e2::[]) when
          let uu____10220 = FStar_Ident.string_of_id id in
          uu____10220 = ".()" ->
          let uu____10224 =
            let uu____10225 = p_indexingTerm_aux p_atomicTermNotQUident e1 in
            let uu____10226 =
              let uu____10227 =
                let uu____10228 = p_term false false e2 in
                soft_parens_with_nesting uu____10228 in
              FStar_Pprint.op_Hat_Hat FStar_Pprint.dot uu____10227 in
            FStar_Pprint.op_Hat_Hat uu____10225 uu____10226 in
          FStar_Pprint.group uu____10224
      | FStar_Parser_AST.Op (id, e1::e2::[]) when
          let uu____10236 = FStar_Ident.string_of_id id in
          uu____10236 = ".[]" ->
          let uu____10240 =
            let uu____10241 = p_indexingTerm_aux p_atomicTermNotQUident e1 in
            let uu____10242 =
              let uu____10243 =
                let uu____10244 = p_term false false e2 in
                soft_brackets_with_nesting uu____10244 in
              FStar_Pprint.op_Hat_Hat FStar_Pprint.dot uu____10243 in
            FStar_Pprint.op_Hat_Hat uu____10241 uu____10242 in
          FStar_Pprint.group uu____10240
      | uu____10247 -> exit e
and (p_indexingTerm : FStar_Parser_AST.term -> FStar_Pprint.document) =
  fun e -> p_indexingTerm_aux p_atomicTerm e
and (p_atomicTerm : FStar_Parser_AST.term -> FStar_Pprint.document) =
  fun e ->
    match e.FStar_Parser_AST.tm with
    | FStar_Parser_AST.LetOpen (lid, e1) ->
        let uu____10252 = p_quident lid in
        let uu____10253 =
          let uu____10254 =
            let uu____10255 = p_term false false e1 in
            soft_parens_with_nesting uu____10255 in
          FStar_Pprint.op_Hat_Hat FStar_Pprint.dot uu____10254 in
        FStar_Pprint.op_Hat_Hat uu____10252 uu____10253
    | FStar_Parser_AST.Name lid -> p_quident lid
    | FStar_Parser_AST.Op (op, e1::[]) when is_general_prefix_op op ->
        let uu____10263 =
          let uu____10264 = FStar_Ident.string_of_id op in str uu____10264 in
        let uu____10266 = p_atomicTerm e1 in
        FStar_Pprint.op_Hat_Hat uu____10263 uu____10266
    | uu____10267 -> p_atomicTermNotQUident e
and (p_atomicTermNotQUident : FStar_Parser_AST.term -> FStar_Pprint.document)
  =
  fun e ->
    match e.FStar_Parser_AST.tm with
    | FStar_Parser_AST.Wild -> FStar_Pprint.underscore
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
         | uu____10280 -> p_constant c)
    | FStar_Parser_AST.Name lid when
        FStar_Ident.lid_equals lid FStar_Parser_Const.true_lid -> str "True"
    | FStar_Parser_AST.Name lid when
        FStar_Ident.lid_equals lid FStar_Parser_Const.false_lid ->
        str "False"
    | FStar_Parser_AST.Op (op, e1::[]) when is_general_prefix_op op ->
        let uu____10289 =
          let uu____10290 = FStar_Ident.string_of_id op in str uu____10290 in
        let uu____10292 = p_atomicTermNotQUident e1 in
        FStar_Pprint.op_Hat_Hat uu____10289 uu____10292
    | FStar_Parser_AST.Op (op, []) ->
        let uu____10296 =
          let uu____10297 =
            let uu____10298 =
              let uu____10299 = FStar_Ident.string_of_id op in
              str uu____10299 in
            let uu____10301 =
              FStar_Pprint.op_Hat_Hat FStar_Pprint.space FStar_Pprint.rparen in
            FStar_Pprint.op_Hat_Hat uu____10298 uu____10301 in
          FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____10297 in
        FStar_Pprint.op_Hat_Hat FStar_Pprint.lparen uu____10296
    | FStar_Parser_AST.Construct (lid, args) when
        (is_dtuple_constructor lid) && (all1_explicit args) ->
        let uu____10316 =
          FStar_Pprint.op_Hat_Hat FStar_Pprint.lparen FStar_Pprint.bar in
        let uu____10317 =
          let uu____10318 = FStar_Pprint.op_Hat_Hat FStar_Pprint.comma break1 in
          FStar_Pprint.separate_map uu____10318
            (fun uu____10326 ->
               match uu____10326 with | (e1, uu____10332) -> p_tmEq e1) args in
        let uu____10333 =
          FStar_Pprint.op_Hat_Hat FStar_Pprint.bar FStar_Pprint.rparen in
        FStar_Pprint.surround (Prims.of_int (2)) Prims.int_one uu____10316
          uu____10317 uu____10333
    | FStar_Parser_AST.Project (e1, lid) ->
        let uu____10338 =
          let uu____10339 = p_atomicTermNotQUident e1 in
          let uu____10340 =
            let uu____10341 = p_qlident lid in
            FStar_Pprint.op_Hat_Hat FStar_Pprint.dot uu____10341 in
          FStar_Pprint.prefix (Prims.of_int (2)) Prims.int_zero uu____10339
            uu____10340 in
        FStar_Pprint.group uu____10338
    | uu____10344 -> p_projectionLHS e
and (p_projectionLHS : FStar_Parser_AST.term -> FStar_Pprint.document) =
  fun e ->
    match e.FStar_Parser_AST.tm with
    | FStar_Parser_AST.Var lid -> p_qlident lid
    | FStar_Parser_AST.Projector (constr_lid, field_lid) ->
        let uu____10349 = p_quident constr_lid in
        let uu____10350 =
          let uu____10351 =
            let uu____10352 = p_lident field_lid in
            FStar_Pprint.op_Hat_Hat FStar_Pprint.dot uu____10352 in
          FStar_Pprint.op_Hat_Hat FStar_Pprint.qmark uu____10351 in
        FStar_Pprint.op_Hat_Hat uu____10349 uu____10350
    | FStar_Parser_AST.Discrim constr_lid ->
        let uu____10354 = p_quident constr_lid in
        FStar_Pprint.op_Hat_Hat uu____10354 FStar_Pprint.qmark
    | FStar_Parser_AST.Paren e1 ->
        let uu____10356 = p_term_sep false false e1 in
        (match uu____10356 with
         | (comm, t) ->
             let doc = soft_parens_with_nesting t in
             if comm = FStar_Pprint.empty
             then doc
             else
               (let uu____10369 =
                  FStar_Pprint.op_Hat_Hat FStar_Pprint.hardline doc in
                FStar_Pprint.op_Hat_Hat comm uu____10369))
    | uu____10370 when is_array e ->
        let es = extract_from_list e in
        let uu____10374 =
          FStar_Pprint.op_Hat_Hat FStar_Pprint.lbracket FStar_Pprint.bar in
        let uu____10375 =
          let uu____10376 = FStar_Pprint.op_Hat_Hat FStar_Pprint.semi break1 in
          separate_map_or_flow_last uu____10376
            (fun ps -> p_noSeqTermAndComment ps false) es in
        let uu____10381 =
          FStar_Pprint.op_Hat_Hat FStar_Pprint.bar FStar_Pprint.rbracket in
        FStar_Pprint.surround (Prims.of_int (2)) Prims.int_zero uu____10374
          uu____10375 uu____10381
    | uu____10384 when is_list e ->
        let uu____10385 =
          let uu____10386 = FStar_Pprint.op_Hat_Hat FStar_Pprint.semi break1 in
          let uu____10387 = extract_from_list e in
          separate_map_or_flow_last uu____10386
            (fun ps -> p_noSeqTermAndComment ps false) uu____10387 in
        FStar_Pprint.surround (Prims.of_int (2)) Prims.int_zero
          FStar_Pprint.lbracket uu____10385 FStar_Pprint.rbracket
    | uu____10396 when is_lex_list e ->
        let uu____10397 =
          FStar_Pprint.op_Hat_Hat FStar_Pprint.percent FStar_Pprint.lbracket in
        let uu____10398 =
          let uu____10399 = FStar_Pprint.op_Hat_Hat FStar_Pprint.semi break1 in
          let uu____10400 = extract_from_list e in
          separate_map_or_flow_last uu____10399
            (fun ps -> p_noSeqTermAndComment ps false) uu____10400 in
        FStar_Pprint.surround (Prims.of_int (2)) Prims.int_one uu____10397
          uu____10398 FStar_Pprint.rbracket
    | uu____10409 when is_ref_set e ->
        let es = extract_from_ref_set e in
        let uu____10413 =
          FStar_Pprint.op_Hat_Hat FStar_Pprint.bang FStar_Pprint.lbrace in
        let uu____10414 =
          let uu____10415 = FStar_Pprint.op_Hat_Hat FStar_Pprint.comma break1 in
          separate_map_or_flow uu____10415 p_appTerm es in
        FStar_Pprint.surround (Prims.of_int (2)) Prims.int_zero uu____10413
          uu____10414 FStar_Pprint.rbrace
    | FStar_Parser_AST.Labeled (e1, s, b) ->
        let uu____10425 = str (Prims.op_Hat "(*" (Prims.op_Hat s "*)")) in
        let uu____10428 = p_term false false e1 in
        FStar_Pprint.op_Hat_Slash_Hat uu____10425 uu____10428
    | FStar_Parser_AST.Op (op, args) when
        let uu____10437 = handleable_op op args in
        Prims.op_Negation uu____10437 ->
        let uu____10439 =
          let uu____10441 =
            let uu____10443 = FStar_Ident.string_of_id op in
            let uu____10445 =
              let uu____10447 =
                let uu____10449 =
                  FStar_Util.string_of_int (FStar_List.length args) in
                Prims.op_Hat uu____10449
                  " arguments couldn't be handled by the pretty printer" in
              Prims.op_Hat " with " uu____10447 in
            Prims.op_Hat uu____10443 uu____10445 in
          Prims.op_Hat "Operation " uu____10441 in
        failwith uu____10439
    | FStar_Parser_AST.Uvar id ->
        failwith "Unexpected universe variable out of universe context"
    | FStar_Parser_AST.Wild ->
        let uu____10456 = p_term false false e in
        soft_parens_with_nesting uu____10456
    | FStar_Parser_AST.Const uu____10459 ->
        let uu____10460 = p_term false false e in
        soft_parens_with_nesting uu____10460
    | FStar_Parser_AST.Op uu____10463 ->
        let uu____10470 = p_term false false e in
        soft_parens_with_nesting uu____10470
    | FStar_Parser_AST.Tvar uu____10473 ->
        let uu____10474 = p_term false false e in
        soft_parens_with_nesting uu____10474
    | FStar_Parser_AST.Var uu____10477 ->
        let uu____10478 = p_term false false e in
        soft_parens_with_nesting uu____10478
    | FStar_Parser_AST.Name uu____10481 ->
        let uu____10482 = p_term false false e in
        soft_parens_with_nesting uu____10482
    | FStar_Parser_AST.Construct uu____10485 ->
        let uu____10496 = p_term false false e in
        soft_parens_with_nesting uu____10496
    | FStar_Parser_AST.Abs uu____10499 ->
        let uu____10506 = p_term false false e in
        soft_parens_with_nesting uu____10506
    | FStar_Parser_AST.App uu____10509 ->
        let uu____10516 = p_term false false e in
        soft_parens_with_nesting uu____10516
    | FStar_Parser_AST.Let uu____10519 ->
        let uu____10540 = p_term false false e in
        soft_parens_with_nesting uu____10540
    | FStar_Parser_AST.LetOpen uu____10543 ->
        let uu____10548 = p_term false false e in
        soft_parens_with_nesting uu____10548
    | FStar_Parser_AST.Seq uu____10551 ->
        let uu____10556 = p_term false false e in
        soft_parens_with_nesting uu____10556
    | FStar_Parser_AST.Bind uu____10559 ->
        let uu____10566 = p_term false false e in
        soft_parens_with_nesting uu____10566
    | FStar_Parser_AST.If uu____10569 ->
        let uu____10576 = p_term false false e in
        soft_parens_with_nesting uu____10576
    | FStar_Parser_AST.Match uu____10579 ->
        let uu____10594 = p_term false false e in
        soft_parens_with_nesting uu____10594
    | FStar_Parser_AST.TryWith uu____10597 ->
        let uu____10612 = p_term false false e in
        soft_parens_with_nesting uu____10612
    | FStar_Parser_AST.Ascribed uu____10615 ->
        let uu____10624 = p_term false false e in
        soft_parens_with_nesting uu____10624
    | FStar_Parser_AST.Record uu____10627 ->
        let uu____10640 = p_term false false e in
        soft_parens_with_nesting uu____10640
    | FStar_Parser_AST.Project uu____10643 ->
        let uu____10648 = p_term false false e in
        soft_parens_with_nesting uu____10648
    | FStar_Parser_AST.Product uu____10651 ->
        let uu____10658 = p_term false false e in
        soft_parens_with_nesting uu____10658
    | FStar_Parser_AST.Sum uu____10661 ->
        let uu____10672 = p_term false false e in
        soft_parens_with_nesting uu____10672
    | FStar_Parser_AST.QForall uu____10675 ->
        let uu____10694 = p_term false false e in
        soft_parens_with_nesting uu____10694
    | FStar_Parser_AST.QExists uu____10697 ->
        let uu____10716 = p_term false false e in
        soft_parens_with_nesting uu____10716
    | FStar_Parser_AST.Refine uu____10719 ->
        let uu____10724 = p_term false false e in
        soft_parens_with_nesting uu____10724
    | FStar_Parser_AST.NamedTyp uu____10727 ->
        let uu____10732 = p_term false false e in
        soft_parens_with_nesting uu____10732
    | FStar_Parser_AST.Requires uu____10735 ->
        let uu____10743 = p_term false false e in
        soft_parens_with_nesting uu____10743
    | FStar_Parser_AST.Ensures uu____10746 ->
        let uu____10754 = p_term false false e in
        soft_parens_with_nesting uu____10754
    | FStar_Parser_AST.Attributes uu____10757 ->
        let uu____10760 = p_term false false e in
        soft_parens_with_nesting uu____10760
    | FStar_Parser_AST.Quote uu____10763 ->
        let uu____10768 = p_term false false e in
        soft_parens_with_nesting uu____10768
    | FStar_Parser_AST.VQuote uu____10771 ->
        let uu____10772 = p_term false false e in
        soft_parens_with_nesting uu____10772
    | FStar_Parser_AST.Antiquote uu____10775 ->
        let uu____10776 = p_term false false e in
        soft_parens_with_nesting uu____10776
    | FStar_Parser_AST.CalcProof uu____10779 ->
        let uu____10788 = p_term false false e in
        soft_parens_with_nesting uu____10788
and (p_constant : FStar_Const.sconst -> FStar_Pprint.document) =
  fun uu___15_10791 ->
    match uu___15_10791 with
    | FStar_Const.Const_effect -> str "Effect"
    | FStar_Const.Const_unit -> str "()"
    | FStar_Const.Const_bool b -> FStar_Pprint.doc_of_bool b
    | FStar_Const.Const_real r -> str (Prims.op_Hat r "R")
    | FStar_Const.Const_float x -> str (FStar_Util.string_of_float x)
    | FStar_Const.Const_char x -> FStar_Pprint.doc_of_char x
    | FStar_Const.Const_string (s, uu____10803) ->
        let uu____10806 = str (FStar_String.escaped s) in
        FStar_Pprint.dquotes uu____10806
    | FStar_Const.Const_bytearray (bytes, uu____10808) ->
        let uu____10815 =
          let uu____10816 = str (FStar_Util.string_of_bytes bytes) in
          FStar_Pprint.dquotes uu____10816 in
        let uu____10817 = str "B" in
        FStar_Pprint.op_Hat_Hat uu____10815 uu____10817
    | FStar_Const.Const_int (repr, sign_width_opt) ->
        let signedness uu___13_10840 =
          match uu___13_10840 with
          | FStar_Const.Unsigned -> str "u"
          | FStar_Const.Signed -> FStar_Pprint.empty in
        let width uu___14_10847 =
          match uu___14_10847 with
          | FStar_Const.Int8 -> str "y"
          | FStar_Const.Int16 -> str "s"
          | FStar_Const.Int32 -> str "l"
          | FStar_Const.Int64 -> str "L" in
        let ending =
          default_or_map FStar_Pprint.empty
            (fun uu____10862 ->
               match uu____10862 with
               | (s, w) ->
                   let uu____10869 = signedness s in
                   let uu____10870 = width w in
                   FStar_Pprint.op_Hat_Hat uu____10869 uu____10870)
            sign_width_opt in
        let uu____10871 = str repr in
        FStar_Pprint.op_Hat_Hat uu____10871 ending
    | FStar_Const.Const_range_of -> str "range_of"
    | FStar_Const.Const_set_range_of -> str "set_range_of"
    | FStar_Const.Const_range r ->
        let uu____10875 = FStar_Range.string_of_range r in str uu____10875
    | FStar_Const.Const_reify -> str "reify"
    | FStar_Const.Const_reflect lid ->
        let uu____10879 = p_quident lid in
        let uu____10880 =
          let uu____10881 =
            let uu____10882 = str "reflect" in
            FStar_Pprint.op_Hat_Hat FStar_Pprint.dot uu____10882 in
          FStar_Pprint.op_Hat_Hat FStar_Pprint.qmark uu____10881 in
        FStar_Pprint.op_Hat_Hat uu____10879 uu____10880
and (p_universe : FStar_Parser_AST.term -> FStar_Pprint.document) =
  fun u ->
    let uu____10885 = str "u#" in
    let uu____10887 = p_atomicUniverse u in
    FStar_Pprint.op_Hat_Hat uu____10885 uu____10887
and (p_universeFrom : FStar_Parser_AST.term -> FStar_Pprint.document) =
  fun u ->
    match u.FStar_Parser_AST.tm with
    | FStar_Parser_AST.Op (id, u1::u2::[]) when
        let uu____10894 = FStar_Ident.string_of_id id in uu____10894 = "+" ->
        let uu____10898 =
          let uu____10899 = p_universeFrom u1 in
          let uu____10900 =
            let uu____10901 = p_universeFrom u2 in
            FStar_Pprint.op_Hat_Slash_Hat FStar_Pprint.plus uu____10901 in
          FStar_Pprint.op_Hat_Slash_Hat uu____10899 uu____10900 in
        FStar_Pprint.group uu____10898
    | FStar_Parser_AST.App uu____10902 ->
        let uu____10909 = head_and_args u in
        (match uu____10909 with
         | (head, args) ->
             (match head.FStar_Parser_AST.tm with
              | FStar_Parser_AST.Var maybe_max_lid when
                  FStar_Ident.lid_equals maybe_max_lid
                    FStar_Parser_Const.max_lid
                  ->
                  let uu____10935 =
                    let uu____10936 = p_qlident FStar_Parser_Const.max_lid in
                    let uu____10937 =
                      FStar_Pprint.separate_map FStar_Pprint.space
                        (fun uu____10945 ->
                           match uu____10945 with
                           | (u1, uu____10951) -> p_atomicUniverse u1) args in
                    op_Hat_Slash_Plus_Hat uu____10936 uu____10937 in
                  FStar_Pprint.group uu____10935
              | uu____10952 ->
                  let uu____10953 =
                    let uu____10955 = FStar_Parser_AST.term_to_string u in
                    FStar_Util.format1 "Invalid term in universe context %s"
                      uu____10955 in
                  failwith uu____10953))
    | uu____10958 -> p_atomicUniverse u
and (p_atomicUniverse : FStar_Parser_AST.term -> FStar_Pprint.document) =
  fun u ->
    match u.FStar_Parser_AST.tm with
    | FStar_Parser_AST.Wild -> FStar_Pprint.underscore
    | FStar_Parser_AST.Const (FStar_Const.Const_int (r, sw)) ->
        p_constant (FStar_Const.Const_int (r, sw))
    | FStar_Parser_AST.Uvar id ->
        let uu____10984 = FStar_Ident.string_of_id id in str uu____10984
    | FStar_Parser_AST.Paren u1 ->
        let uu____10987 = p_universeFrom u1 in
        soft_parens_with_nesting uu____10987
    | FStar_Parser_AST.App uu____10988 ->
        let uu____10995 = p_universeFrom u in
        soft_parens_with_nesting uu____10995
    | FStar_Parser_AST.Op (id, uu____10997::uu____10998::[]) when
        let uu____11001 = FStar_Ident.string_of_id id in uu____11001 = "+" ->
        let uu____11005 = p_universeFrom u in
        soft_parens_with_nesting uu____11005
    | uu____11006 ->
        let uu____11007 =
          let uu____11009 = FStar_Parser_AST.term_to_string u in
          FStar_Util.format1 "Invalid term in universe context %s"
            uu____11009 in
        failwith uu____11007
let (term_to_document : FStar_Parser_AST.term -> FStar_Pprint.document) =
  fun e -> FStar_ST.op_Colon_Equals unfold_tuples false; p_term false false e
let (signature_to_document : FStar_Parser_AST.decl -> FStar_Pprint.document)
  = fun e -> p_justSig e
let (decl_to_document : FStar_Parser_AST.decl -> FStar_Pprint.document) =
  fun e -> p_decl e
let (pat_to_document : FStar_Parser_AST.pattern -> FStar_Pprint.document) =
  fun p -> p_disjunctivePattern p
let (binder_to_document : FStar_Parser_AST.binder -> FStar_Pprint.document) =
  fun b -> p_binder true b
let (modul_to_document : FStar_Parser_AST.modul -> FStar_Pprint.document) =
  fun m ->
    FStar_ST.op_Colon_Equals should_print_fs_typ_app false;
    (let res =
       match m with
       | FStar_Parser_AST.Module (uu____11098, decls) ->
           let uu____11104 =
             FStar_All.pipe_right decls (FStar_List.map decl_to_document) in
           FStar_All.pipe_right uu____11104
             (FStar_Pprint.separate FStar_Pprint.hardline)
       | FStar_Parser_AST.Interface (uu____11113, decls, uu____11115) ->
           let uu____11122 =
             FStar_All.pipe_right decls (FStar_List.map decl_to_document) in
           FStar_All.pipe_right uu____11122
             (FStar_Pprint.separate FStar_Pprint.hardline) in
     FStar_ST.op_Colon_Equals should_print_fs_typ_app false; res)
let (comments_to_document :
  (Prims.string * FStar_Range.range) Prims.list -> FStar_Pprint.document) =
  fun comments ->
    FStar_Pprint.separate_map FStar_Pprint.hardline
      (fun uu____11182 ->
         match uu____11182 with | (comment, range) -> str comment) comments
let (extract_decl_range : FStar_Parser_AST.decl -> decl_meta) =
  fun d ->
    let has_qs =
      match ((d.FStar_Parser_AST.quals), (d.FStar_Parser_AST.d)) with
      | ((FStar_Parser_AST.Assumption)::[], FStar_Parser_AST.Assume
         (id, uu____11204)) -> false
      | ([], uu____11208) -> false
      | uu____11212 -> true in
    {
      r = (d.FStar_Parser_AST.drange);
      has_qs;
      has_attrs =
        (Prims.op_Negation (FStar_List.isEmpty d.FStar_Parser_AST.attrs))
    }
let (modul_with_comments_to_document :
  FStar_Parser_AST.modul ->
    (Prims.string * FStar_Range.range) Prims.list ->
      (FStar_Pprint.document * (Prims.string * FStar_Range.range) Prims.list))
  =
  fun m ->
    fun comments ->
      let decls =
        match m with
        | FStar_Parser_AST.Module (uu____11261, decls) -> decls
        | FStar_Parser_AST.Interface (uu____11267, decls, uu____11269) ->
            decls in
      FStar_ST.op_Colon_Equals should_print_fs_typ_app false;
      (match decls with
       | [] -> (FStar_Pprint.empty, comments)
       | d::ds ->
           let uu____11321 =
             match ds with
             | {
                 FStar_Parser_AST.d = FStar_Parser_AST.Pragma
                   (FStar_Parser_AST.LightOff);
                 FStar_Parser_AST.drange = uu____11334;
                 FStar_Parser_AST.quals = uu____11335;
                 FStar_Parser_AST.attrs = uu____11336;_}::uu____11337 ->
                 let d0 = FStar_List.hd ds in
                 let uu____11341 =
                   let uu____11344 =
                     let uu____11347 = FStar_List.tl ds in d :: uu____11347 in
                   d0 :: uu____11344 in
                 (uu____11341, (d0.FStar_Parser_AST.drange))
             | uu____11352 -> ((d :: ds), (d.FStar_Parser_AST.drange)) in
           (match uu____11321 with
            | (decls1, first_range) ->
                (FStar_ST.op_Colon_Equals comment_stack comments;
                 (let initial_comment =
                    let uu____11409 = FStar_Range.start_of_range first_range in
                    place_comments_until_pos Prims.int_zero Prims.int_one
                      uu____11409 dummy_meta FStar_Pprint.empty false true in
                  let doc =
                    separate_map_with_comments FStar_Pprint.empty
                      FStar_Pprint.empty p_decl decls1 extract_decl_range in
                  let comments1 = FStar_ST.op_Bang comment_stack in
                  FStar_ST.op_Colon_Equals comment_stack [];
                  FStar_ST.op_Colon_Equals should_print_fs_typ_app false;
                  (let uu____11518 =
                     FStar_Pprint.op_Hat_Hat initial_comment doc in
                   (uu____11518, comments1))))))