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
            let uu____93 = let uu____96 = f x in uu____96 :: acc in
            aux xs uu____93 in
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
            let uu____161 = f x in
            (match uu____161 with
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
      | x::xs -> let uu____210 = f x in if uu____210 then all f xs else false
let (all1_explicit :
  (FStar_Parser_AST.term * FStar_Parser_AST.imp) Prims.list -> Prims.bool) =
  fun args ->
    (Prims.op_Negation (FStar_List.isEmpty args)) &&
      (FStar_Util.for_all
         (fun uu___0_239 ->
            match uu___0_239 with
            | (uu____244, FStar_Parser_AST.Nothing) -> true
            | uu____245 -> false) args)
let (should_print_fs_typ_app : Prims.bool FStar_ST.ref) =
  FStar_Util.mk_ref false
let (unfold_tuples : Prims.bool FStar_ST.ref) = FStar_Util.mk_ref true
let with_fs_typ_app :
  'uuuuuu264 'uuuuuu265 .
    Prims.bool -> ('uuuuuu264 -> 'uuuuuu265) -> 'uuuuuu264 -> 'uuuuuu265
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
  'uuuuuu323 'uuuuuu324 .
    'uuuuuu323 ->
      ('uuuuuu324 -> 'uuuuuu323) ->
        'uuuuuu324 FStar_Pervasives_Native.option -> 'uuuuuu323
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
  'uuuuuu418 .
    FStar_Pprint.document ->
      ('uuuuuu418 -> FStar_Pprint.document) ->
        'uuuuuu418 Prims.list -> FStar_Pprint.document
  =
  fun sep ->
    fun f ->
      fun l ->
        let uu____443 =
          let uu____444 =
            let uu____445 = FStar_Pprint.op_Hat_Hat sep break1 in
            FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____445 in
          FStar_Pprint.separate_map uu____444 f l in
        FStar_Pprint.group uu____443
let precede_break_separate_map :
  'uuuuuu456 .
    FStar_Pprint.document ->
      FStar_Pprint.document ->
        ('uuuuuu456 -> FStar_Pprint.document) ->
          'uuuuuu456 Prims.list -> FStar_Pprint.document
  =
  fun prec ->
    fun sep ->
      fun f ->
        fun l ->
          let uu____486 =
            let uu____487 = FStar_Pprint.op_Hat_Hat prec FStar_Pprint.space in
            let uu____488 =
              let uu____489 = FStar_List.hd l in
              FStar_All.pipe_right uu____489 f in
            FStar_Pprint.precede uu____487 uu____488 in
          let uu____490 =
            let uu____491 = FStar_List.tl l in
            FStar_Pprint.concat_map
              (fun x ->
                 let uu____497 =
                   let uu____498 =
                     let uu____499 = f x in
                     FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____499 in
                   FStar_Pprint.op_Hat_Hat sep uu____498 in
                 FStar_Pprint.op_Hat_Hat break1 uu____497) uu____491 in
          FStar_Pprint.op_Hat_Hat uu____486 uu____490
let concat_break_map :
  'uuuuuu506 .
    ('uuuuuu506 -> FStar_Pprint.document) ->
      'uuuuuu506 Prims.list -> FStar_Pprint.document
  =
  fun f ->
    fun l ->
      let uu____526 =
        FStar_Pprint.concat_map
          (fun x ->
             let uu____530 = f x in FStar_Pprint.op_Hat_Hat uu____530 break1)
          l in
      FStar_Pprint.group uu____526
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
    let uu____571 = str "begin" in
    let uu____572 = str "end" in
    FStar_Pprint.soft_surround (Prims.of_int (2)) Prims.int_one uu____571
      contents uu____572
let separate_map_last :
  'uuuuuu581 .
    FStar_Pprint.document ->
      (Prims.bool -> 'uuuuuu581 -> FStar_Pprint.document) ->
        'uuuuuu581 Prims.list -> FStar_Pprint.document
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
  'uuuuuu627 .
    FStar_Pprint.document ->
      (Prims.bool -> 'uuuuuu627 -> FStar_Pprint.document) ->
        'uuuuuu627 Prims.list -> FStar_Pprint.document
  =
  fun sep ->
    fun f ->
      fun l ->
        let uu____657 =
          let uu____658 =
            let uu____659 = FStar_Pprint.op_Hat_Hat sep break1 in
            FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____659 in
          separate_map_last uu____658 f l in
        FStar_Pprint.group uu____657
let separate_map_or_flow :
  'uuuuuu668 .
    FStar_Pprint.document ->
      ('uuuuuu668 -> FStar_Pprint.document) ->
        'uuuuuu668 Prims.list -> FStar_Pprint.document
  =
  fun sep ->
    fun f ->
      fun l ->
        if (FStar_List.length l) < (Prims.of_int (10))
        then FStar_Pprint.separate_map sep f l
        else FStar_Pprint.flow_map sep f l
let flow_map_last :
  'uuuuuu702 .
    FStar_Pprint.document ->
      (Prims.bool -> 'uuuuuu702 -> FStar_Pprint.document) ->
        'uuuuuu702 Prims.list -> FStar_Pprint.document
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
  'uuuuuu748 .
    FStar_Pprint.document ->
      (Prims.bool -> 'uuuuuu748 -> FStar_Pprint.document) ->
        'uuuuuu748 Prims.list -> FStar_Pprint.document
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
              let uu____818 = FStar_Pprint.op_Hat_Slash_Hat doc1 doc3 in
              FStar_Pprint.group uu____818
            else FStar_Pprint.surround n b doc1 doc2 doc3
let soft_surround_separate_map :
  'uuuuuu838 .
    Prims.int ->
      Prims.int ->
        FStar_Pprint.document ->
          FStar_Pprint.document ->
            FStar_Pprint.document ->
              FStar_Pprint.document ->
                ('uuuuuu838 -> FStar_Pprint.document) ->
                  'uuuuuu838 Prims.list -> FStar_Pprint.document
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
                    (let uu____891 = FStar_Pprint.separate_map sep f xs in
                     FStar_Pprint.soft_surround n b opening uu____891 closing)
let soft_surround_map_or_flow :
  'uuuuuu910 .
    Prims.int ->
      Prims.int ->
        FStar_Pprint.document ->
          FStar_Pprint.document ->
            FStar_Pprint.document ->
              FStar_Pprint.document ->
                ('uuuuuu910 -> FStar_Pprint.document) ->
                  'uuuuuu910 Prims.list -> FStar_Pprint.document
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
                    (let uu____963 = separate_map_or_flow sep f xs in
                     FStar_Pprint.soft_surround n b opening uu____963 closing)
let (is_unit : FStar_Parser_AST.term -> Prims.bool) =
  fun e ->
    match e.FStar_Parser_AST.tm with
    | FStar_Parser_AST.Const (FStar_Const.Const_unit) -> true
    | uu____969 -> false
let (matches_var : FStar_Parser_AST.term -> FStar_Ident.ident -> Prims.bool)
  =
  fun t ->
    fun x ->
      match t.FStar_Parser_AST.tm with
      | FStar_Parser_AST.Var y ->
          let uu____981 = FStar_Ident.string_of_id x in
          let uu____982 = FStar_Ident.string_of_lid y in
          uu____981 = uu____982
      | uu____983 -> false
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
        | FStar_Parser_AST.Construct (lid, uu____1025::(e2, uu____1027)::[])
            -> (FStar_Ident.lid_equals lid cons_lid) && (aux e2)
        | uu____1050 -> false in
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
    | FStar_Parser_AST.Construct (uu____1068, []) -> []
    | FStar_Parser_AST.Construct
        (uu____1079,
         (e1, FStar_Parser_AST.Nothing)::(e2, FStar_Parser_AST.Nothing)::[])
        -> let uu____1100 = extract_from_list e2 in e1 :: uu____1100
    | uu____1103 ->
        let uu____1104 =
          let uu____1105 = FStar_Parser_AST.term_to_string e in
          FStar_Util.format1 "Not a list %s" uu____1105 in
        failwith uu____1104
let (is_array : FStar_Parser_AST.term -> Prims.bool) =
  fun e ->
    match e.FStar_Parser_AST.tm with
    | FStar_Parser_AST.App
        ({ FStar_Parser_AST.tm = FStar_Parser_AST.Var lid;
           FStar_Parser_AST.range = uu____1114;
           FStar_Parser_AST.level = uu____1115;_},
         l, FStar_Parser_AST.Nothing)
        ->
        (FStar_Ident.lid_equals lid FStar_Parser_Const.array_of_list_lid) &&
          (is_list l)
    | uu____1117 -> false
let rec (is_ref_set : FStar_Parser_AST.term -> Prims.bool) =
  fun e ->
    match e.FStar_Parser_AST.tm with
    | FStar_Parser_AST.Var maybe_empty_lid ->
        FStar_Ident.lid_equals maybe_empty_lid FStar_Parser_Const.set_empty
    | FStar_Parser_AST.App
        ({ FStar_Parser_AST.tm = FStar_Parser_AST.Var maybe_singleton_lid;
           FStar_Parser_AST.range = uu____1125;
           FStar_Parser_AST.level = uu____1126;_},
         {
           FStar_Parser_AST.tm = FStar_Parser_AST.App
             ({ FStar_Parser_AST.tm = FStar_Parser_AST.Var maybe_addr_of_lid;
                FStar_Parser_AST.range = uu____1128;
                FStar_Parser_AST.level = uu____1129;_},
              e1, FStar_Parser_AST.Nothing);
           FStar_Parser_AST.range = uu____1131;
           FStar_Parser_AST.level = uu____1132;_},
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
                FStar_Parser_AST.range = uu____1134;
                FStar_Parser_AST.level = uu____1135;_},
              e1, FStar_Parser_AST.Nothing);
           FStar_Parser_AST.range = uu____1137;
           FStar_Parser_AST.level = uu____1138;_},
         e2, FStar_Parser_AST.Nothing)
        ->
        ((FStar_Ident.lid_equals maybe_union_lid FStar_Parser_Const.set_union)
           && (is_ref_set e1))
          && (is_ref_set e2)
    | uu____1140 -> false
let rec (extract_from_ref_set :
  FStar_Parser_AST.term -> FStar_Parser_AST.term Prims.list) =
  fun e ->
    match e.FStar_Parser_AST.tm with
    | FStar_Parser_AST.Var uu____1150 -> []
    | FStar_Parser_AST.App
        ({ FStar_Parser_AST.tm = FStar_Parser_AST.Var uu____1151;
           FStar_Parser_AST.range = uu____1152;
           FStar_Parser_AST.level = uu____1153;_},
         {
           FStar_Parser_AST.tm = FStar_Parser_AST.App
             ({ FStar_Parser_AST.tm = FStar_Parser_AST.Var uu____1154;
                FStar_Parser_AST.range = uu____1155;
                FStar_Parser_AST.level = uu____1156;_},
              e1, FStar_Parser_AST.Nothing);
           FStar_Parser_AST.range = uu____1158;
           FStar_Parser_AST.level = uu____1159;_},
         FStar_Parser_AST.Nothing)
        -> [e1]
    | FStar_Parser_AST.App
        ({
           FStar_Parser_AST.tm = FStar_Parser_AST.App
             ({ FStar_Parser_AST.tm = FStar_Parser_AST.Var uu____1160;
                FStar_Parser_AST.range = uu____1161;
                FStar_Parser_AST.level = uu____1162;_},
              e1, FStar_Parser_AST.Nothing);
           FStar_Parser_AST.range = uu____1164;
           FStar_Parser_AST.level = uu____1165;_},
         e2, FStar_Parser_AST.Nothing)
        ->
        let uu____1167 = extract_from_ref_set e1 in
        let uu____1170 = extract_from_ref_set e2 in
        FStar_List.append uu____1167 uu____1170
    | uu____1173 ->
        let uu____1174 =
          let uu____1175 = FStar_Parser_AST.term_to_string e in
          FStar_Util.format1 "Not a ref set %s" uu____1175 in
        failwith uu____1174
let (is_general_application : FStar_Parser_AST.term -> Prims.bool) =
  fun e ->
    let uu____1183 = (is_array e) || (is_ref_set e) in
    Prims.op_Negation uu____1183
let (is_general_construction : FStar_Parser_AST.term -> Prims.bool) =
  fun e ->
    let uu____1189 = (is_list e) || (is_lex_list e) in
    Prims.op_Negation uu____1189
let (is_general_prefix_op : FStar_Ident.ident -> Prims.bool) =
  fun op ->
    let op_starting_char =
      let uu____1196 = FStar_Ident.string_of_id op in
      FStar_Util.char_at uu____1196 Prims.int_zero in
    ((op_starting_char = 33) || (op_starting_char = 63)) ||
      ((op_starting_char = 126) &&
         (let uu____1198 = FStar_Ident.string_of_id op in uu____1198 <> "~"))
let (head_and_args :
  FStar_Parser_AST.term ->
    (FStar_Parser_AST.term * (FStar_Parser_AST.term * FStar_Parser_AST.imp)
      Prims.list))
  =
  fun e ->
    let rec aux e1 acc =
      match e1.FStar_Parser_AST.tm with
      | FStar_Parser_AST.App (head, arg, imp) -> aux head ((arg, imp) :: acc)
      | uu____1264 -> (e1, acc) in
    aux e []
type associativity =
  | Left 
  | Right 
  | NonAssoc 
let (uu___is_Left : associativity -> Prims.bool) =
  fun projectee -> match projectee with | Left -> true | uu____1280 -> false
let (uu___is_Right : associativity -> Prims.bool) =
  fun projectee -> match projectee with | Right -> true | uu____1286 -> false
let (uu___is_NonAssoc : associativity -> Prims.bool) =
  fun projectee ->
    match projectee with | NonAssoc -> true | uu____1292 -> false
type token = (FStar_Char.char, Prims.string) FStar_Util.either
type associativity_level = (associativity * token Prims.list)
let (token_to_string :
  (FStar_BaseTypes.char, Prims.string) FStar_Util.either -> Prims.string) =
  fun uu___1_1311 ->
    match uu___1_1311 with
    | FStar_Util.Inl c -> Prims.op_Hat (FStar_Util.string_of_char c) ".*"
    | FStar_Util.Inr s -> s
let (matches_token :
  Prims.string ->
    (FStar_Char.char, Prims.string) FStar_Util.either -> Prims.bool)
  =
  fun s ->
    fun uu___2_1331 ->
      match uu___2_1331 with
      | FStar_Util.Inl c ->
          let uu____1337 = FStar_String.get s Prims.int_zero in
          uu____1337 = c
      | FStar_Util.Inr s' -> s = s'
let matches_level :
  'uuuuuu1345 .
    Prims.string ->
      ('uuuuuu1345 * (FStar_Char.char, Prims.string) FStar_Util.either
        Prims.list) -> Prims.bool
  =
  fun s ->
    fun uu____1365 ->
      match uu____1365 with
      | (assoc_levels, tokens) ->
          let uu____1390 = FStar_List.tryFind (matches_token s) tokens in
          uu____1390 <> FStar_Pervasives_Native.None
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
  let levels_from_associativity l uu___3_1471 =
    match uu___3_1471 with
    | Left -> (l, l, (l - Prims.int_one))
    | Right -> ((l - Prims.int_one), l, l)
    | NonAssoc -> ((l - Prims.int_one), l, (l - Prims.int_one)) in
  FStar_List.mapi
    (fun i ->
       fun uu____1501 ->
         match uu____1501 with
         | (assoc, tokens) -> ((levels_from_associativity i assoc), tokens))
    level_associativity_spec
let (assign_levels :
  associativity_level Prims.list ->
    Prims.string -> (Prims.int * Prims.int * Prims.int))
  =
  fun token_associativity_spec ->
    fun s ->
      let uu____1560 = FStar_List.tryFind (matches_level s) level_table in
      match uu____1560 with
      | FStar_Pervasives_Native.Some (assoc_levels, uu____1600) ->
          assoc_levels
      | uu____1629 -> failwith (Prims.op_Hat "Unrecognized operator " s)
let max_level :
  'uuuuuu1654 . ('uuuuuu1654 * token Prims.list) Prims.list -> Prims.int =
  fun l ->
    let find_level_and_max n level =
      let uu____1699 =
        FStar_List.tryFind
          (fun uu____1729 ->
             match uu____1729 with
             | (uu____1742, tokens) ->
                 tokens = (FStar_Pervasives_Native.snd level)) level_table in
      match uu____1699 with
      | FStar_Pervasives_Native.Some
          ((uu____1764, l1, uu____1766), uu____1767) -> max n l1
      | FStar_Pervasives_Native.None ->
          let uu____1802 =
            let uu____1803 =
              let uu____1804 =
                FStar_List.map token_to_string
                  (FStar_Pervasives_Native.snd level) in
              FStar_String.concat "," uu____1804 in
            FStar_Util.format1 "Undefined associativity level %s" uu____1803 in
          failwith uu____1802 in
    FStar_List.fold_left find_level_and_max Prims.int_zero l
let (levels : Prims.string -> (Prims.int * Prims.int * Prims.int)) =
  fun op ->
    let uu____1826 = assign_levels level_associativity_spec op in
    match uu____1826 with
    | (left, mine, right) ->
        if op = "*"
        then ((left - Prims.int_one), mine, right)
        else (left, mine, right)
let (operatorInfix0ad12 : associativity_level Prims.list) =
  [opinfix0a; opinfix0b; opinfix0c; opinfix0d; opinfix1; opinfix2]
let (is_operatorInfix0ad12 : FStar_Ident.ident -> Prims.bool) =
  fun op ->
    let uu____1856 =
      let uu____1859 =
        let uu____1864 = FStar_Ident.string_of_id op in
        FStar_All.pipe_left matches_level uu____1864 in
      FStar_List.tryFind uu____1859 operatorInfix0ad12 in
    uu____1856 <> FStar_Pervasives_Native.None
let (is_operatorInfix34 : FStar_Ident.ident -> Prims.bool) =
  let opinfix34 = [opinfix3; opinfix4] in
  fun op ->
    let uu____1918 =
      let uu____1931 =
        let uu____1946 = FStar_Ident.string_of_id op in
        FStar_All.pipe_left matches_level uu____1946 in
      FStar_List.tryFind uu____1931 opinfix34 in
    uu____1918 <> FStar_Pervasives_Native.None
let (handleable_args_length : FStar_Ident.ident -> Prims.int) =
  fun op ->
    let op_s = FStar_Ident.string_of_id op in
    let uu____1998 =
      (is_general_prefix_op op) || (FStar_List.mem op_s ["-"; "~"]) in
    if uu____1998
    then Prims.int_one
    else
      (let uu____2000 =
         ((is_operatorInfix0ad12 op) || (is_operatorInfix34 op)) ||
           (FStar_List.mem op_s
              ["<==>"; "==>"; "\\/"; "/\\"; "="; "|>"; ":="; ".()"; ".[]"]) in
       if uu____2000
       then (Prims.of_int (2))
       else
         if FStar_List.mem op_s [".()<-"; ".[]<-"]
         then (Prims.of_int (3))
         else Prims.int_zero)
let handleable_op :
  'uuuuuu2009 . FStar_Ident.ident -> 'uuuuuu2009 Prims.list -> Prims.bool =
  fun op ->
    fun args ->
      match FStar_List.length args with
      | uu____2024 when uu____2024 = Prims.int_zero -> true
      | uu____2025 when uu____2025 = Prims.int_one ->
          (is_general_prefix_op op) ||
            (let uu____2027 = FStar_Ident.string_of_id op in
             FStar_List.mem uu____2027 ["-"; "~"])
      | uu____2028 when uu____2028 = (Prims.of_int (2)) ->
          ((is_operatorInfix0ad12 op) || (is_operatorInfix34 op)) ||
            (let uu____2030 = FStar_Ident.string_of_id op in
             FStar_List.mem uu____2030
               ["<==>"; "==>"; "\\/"; "/\\"; "="; "|>"; ":="; ".()"; ".[]"])
      | uu____2031 when uu____2031 = (Prims.of_int (3)) ->
          let uu____2032 = FStar_Ident.string_of_id op in
          FStar_List.mem uu____2032 [".()<-"; ".[]<-"]
      | uu____2033 -> false
type annotation_style =
  | Binders of (Prims.int * Prims.int * Prims.bool) 
  | Arrows of (Prims.int * Prims.int) 
let (uu___is_Binders : annotation_style -> Prims.bool) =
  fun projectee ->
    match projectee with | Binders _0 -> true | uu____2066 -> false
let (__proj__Binders__item___0 :
  annotation_style -> (Prims.int * Prims.int * Prims.bool)) =
  fun projectee -> match projectee with | Binders _0 -> _0
let (uu___is_Arrows : annotation_style -> Prims.bool) =
  fun projectee ->
    match projectee with | Arrows _0 -> true | uu____2101 -> false
let (__proj__Arrows__item___0 : annotation_style -> (Prims.int * Prims.int))
  = fun projectee -> match projectee with | Arrows _0 -> _0
let (all_binders_annot : FStar_Parser_AST.term -> Prims.bool) =
  fun e ->
    let is_binder_annot b =
      match b.FStar_Parser_AST.b with
      | FStar_Parser_AST.Annotated uu____2131 -> true
      | uu____2136 -> false in
    let rec all_binders e1 l =
      match e1.FStar_Parser_AST.tm with
      | FStar_Parser_AST.Product (bs, tgt) ->
          let uu____2162 = FStar_List.for_all is_binder_annot bs in
          if uu____2162
          then all_binders tgt (l + (FStar_List.length bs))
          else (false, Prims.int_zero)
      | uu____2168 -> (true, (l + Prims.int_one)) in
    let uu____2169 = all_binders e Prims.int_zero in
    match uu____2169 with
    | (b, l) -> if b && (l > Prims.int_one) then true else false
type catf =
  FStar_Pprint.document -> FStar_Pprint.document -> FStar_Pprint.document
let (cat_with_colon :
  FStar_Pprint.document -> FStar_Pprint.document -> FStar_Pprint.document) =
  fun x ->
    fun y ->
      let uu____2193 = FStar_Pprint.op_Hat_Slash_Hat FStar_Pprint.colon y in
      FStar_Pprint.op_Hat_Hat x uu____2193
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
  'uuuuuu2259 .
    ('uuuuuu2259 -> FStar_Pprint.document) ->
      'uuuuuu2259 -> FStar_Range.range -> FStar_Pprint.document
  =
  fun printer ->
    fun tm ->
      fun tmrange ->
        let rec comments_before_pos acc print_pos lookahead_pos =
          let uu____2300 = FStar_ST.op_Bang comment_stack in
          match uu____2300 with
          | [] -> (acc, false)
          | (c, crange)::cs ->
              let comment =
                let uu____2347 = str c in
                FStar_Pprint.op_Hat_Hat uu____2347 FStar_Pprint.hardline in
              let uu____2348 = FStar_Range.range_before_pos crange print_pos in
              if uu____2348
              then
                (FStar_ST.op_Colon_Equals comment_stack cs;
                 (let uu____2372 = FStar_Pprint.op_Hat_Hat acc comment in
                  comments_before_pos uu____2372 print_pos lookahead_pos))
              else
                (let uu____2374 =
                   FStar_Range.range_before_pos crange lookahead_pos in
                 (acc, uu____2374)) in
        let uu____2375 =
          let uu____2380 =
            let uu____2381 = FStar_Range.start_of_range tmrange in
            FStar_Range.end_of_line uu____2381 in
          let uu____2382 = FStar_Range.end_of_range tmrange in
          comments_before_pos FStar_Pprint.empty uu____2380 uu____2382 in
        match uu____2375 with
        | (comments, has_lookahead) ->
            let printed_e = printer tm in
            let comments1 =
              if has_lookahead
              then
                let pos = FStar_Range.end_of_range tmrange in
                let uu____2388 = comments_before_pos comments pos pos in
                FStar_Pervasives_Native.fst uu____2388
              else comments in
            if comments1 = FStar_Pprint.empty
            then printed_e
            else
              (let uu____2395 = FStar_Pprint.op_Hat_Hat comments1 printed_e in
               FStar_Pprint.group uu____2395)
let with_comment_sep :
  'uuuuuu2406 'uuuuuu2407 .
    ('uuuuuu2406 -> 'uuuuuu2407) ->
      'uuuuuu2406 ->
        FStar_Range.range -> (FStar_Pprint.document * 'uuuuuu2407)
  =
  fun printer ->
    fun tm ->
      fun tmrange ->
        let rec comments_before_pos acc print_pos lookahead_pos =
          let uu____2452 = FStar_ST.op_Bang comment_stack in
          match uu____2452 with
          | [] -> (acc, false)
          | (c, crange)::cs ->
              let comment = str c in
              let uu____2499 = FStar_Range.range_before_pos crange print_pos in
              if uu____2499
              then
                (FStar_ST.op_Colon_Equals comment_stack cs;
                 (let uu____2523 =
                    if acc = FStar_Pprint.empty
                    then comment
                    else
                      (let uu____2525 =
                         FStar_Pprint.op_Hat_Hat FStar_Pprint.hardline
                           comment in
                       FStar_Pprint.op_Hat_Hat acc uu____2525) in
                  comments_before_pos uu____2523 print_pos lookahead_pos))
              else
                (let uu____2527 =
                   FStar_Range.range_before_pos crange lookahead_pos in
                 (acc, uu____2527)) in
        let uu____2528 =
          let uu____2533 =
            let uu____2534 = FStar_Range.start_of_range tmrange in
            FStar_Range.end_of_line uu____2534 in
          let uu____2535 = FStar_Range.end_of_range tmrange in
          comments_before_pos FStar_Pprint.empty uu____2533 uu____2535 in
        match uu____2528 with
        | (comments, has_lookahead) ->
            let printed_e = printer tm in
            let comments1 =
              if has_lookahead
              then
                let pos = FStar_Range.end_of_range tmrange in
                let uu____2545 = comments_before_pos comments pos pos in
                FStar_Pervasives_Native.fst uu____2545
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
                let uu____2586 = FStar_ST.op_Bang comment_stack in
                match uu____2586 with
                | (comment, crange)::cs when
                    FStar_Range.range_before_pos crange pos ->
                    (FStar_ST.op_Colon_Equals comment_stack cs;
                     (let lnum =
                        let uu____2644 =
                          let uu____2645 =
                            let uu____2646 =
                              FStar_Range.start_of_range crange in
                            FStar_Range.line_of_pos uu____2646 in
                          uu____2645 - lbegin in
                        max k uu____2644 in
                      let lnum1 = min (Prims.of_int (2)) lnum in
                      let doc1 =
                        let uu____2649 =
                          let uu____2650 =
                            FStar_Pprint.repeat lnum1 FStar_Pprint.hardline in
                          let uu____2651 = str comment in
                          FStar_Pprint.op_Hat_Hat uu____2650 uu____2651 in
                        FStar_Pprint.op_Hat_Hat doc uu____2649 in
                      let uu____2652 =
                        let uu____2653 = FStar_Range.end_of_range crange in
                        FStar_Range.line_of_pos uu____2653 in
                      place_comments_until_pos Prims.int_one uu____2652 pos
                        meta_decl doc1 true init))
                | uu____2654 ->
                    if doc = FStar_Pprint.empty
                    then FStar_Pprint.empty
                    else
                      (let lnum =
                         let uu____2663 = FStar_Range.line_of_pos pos in
                         uu____2663 - lbegin in
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
                       let uu____2672 =
                         FStar_Pprint.repeat lnum5 FStar_Pprint.hardline in
                       FStar_Pprint.op_Hat_Hat doc uu____2672)
let separate_map_with_comments :
  'uuuuuu2685 .
    FStar_Pprint.document ->
      FStar_Pprint.document ->
        ('uuuuuu2685 -> FStar_Pprint.document) ->
          'uuuuuu2685 Prims.list ->
            ('uuuuuu2685 -> decl_meta) -> FStar_Pprint.document
  =
  fun prefix ->
    fun sep ->
      fun f ->
        fun xs ->
          fun extract_meta ->
            let fold_fun uu____2742 x =
              match uu____2742 with
              | (last_line, doc) ->
                  let meta_decl = extract_meta x in
                  let r = meta_decl.r in
                  let doc1 =
                    let uu____2757 = FStar_Range.start_of_range r in
                    place_comments_until_pos Prims.int_one last_line
                      uu____2757 meta_decl doc false false in
                  let uu____2758 =
                    let uu____2759 = FStar_Range.end_of_range r in
                    FStar_Range.line_of_pos uu____2759 in
                  let uu____2760 =
                    let uu____2761 =
                      let uu____2762 = f x in
                      FStar_Pprint.op_Hat_Hat sep uu____2762 in
                    FStar_Pprint.op_Hat_Hat doc1 uu____2761 in
                  (uu____2758, uu____2760) in
            let uu____2763 =
              let uu____2770 = FStar_List.hd xs in
              let uu____2771 = FStar_List.tl xs in (uu____2770, uu____2771) in
            match uu____2763 with
            | (x, xs1) ->
                let init =
                  let meta_decl = extract_meta x in
                  let uu____2788 =
                    let uu____2789 = FStar_Range.end_of_range meta_decl.r in
                    FStar_Range.line_of_pos uu____2789 in
                  let uu____2790 =
                    let uu____2791 = f x in
                    FStar_Pprint.op_Hat_Hat prefix uu____2791 in
                  (uu____2788, uu____2790) in
                let uu____2792 = FStar_List.fold_left fold_fun init xs1 in
                FStar_Pervasives_Native.snd uu____2792
let separate_map_with_comments_kw :
  'uuuuuu2815 'uuuuuu2816 .
    'uuuuuu2815 ->
      'uuuuuu2815 ->
        ('uuuuuu2815 -> 'uuuuuu2816 -> FStar_Pprint.document) ->
          'uuuuuu2816 Prims.list ->
            ('uuuuuu2816 -> decl_meta) -> FStar_Pprint.document
  =
  fun prefix ->
    fun sep ->
      fun f ->
        fun xs ->
          fun extract_meta ->
            let fold_fun uu____2878 x =
              match uu____2878 with
              | (last_line, doc) ->
                  let meta_decl = extract_meta x in
                  let r = meta_decl.r in
                  let doc1 =
                    let uu____2893 = FStar_Range.start_of_range r in
                    place_comments_until_pos Prims.int_one last_line
                      uu____2893 meta_decl doc false false in
                  let uu____2894 =
                    let uu____2895 = FStar_Range.end_of_range r in
                    FStar_Range.line_of_pos uu____2895 in
                  let uu____2896 =
                    let uu____2897 = f sep x in
                    FStar_Pprint.op_Hat_Hat doc1 uu____2897 in
                  (uu____2894, uu____2896) in
            let uu____2898 =
              let uu____2905 = FStar_List.hd xs in
              let uu____2906 = FStar_List.tl xs in (uu____2905, uu____2906) in
            match uu____2898 with
            | (x, xs1) ->
                let init =
                  let meta_decl = extract_meta x in
                  let uu____2923 =
                    let uu____2924 = FStar_Range.end_of_range meta_decl.r in
                    FStar_Range.line_of_pos uu____2924 in
                  let uu____2925 = f prefix x in (uu____2923, uu____2925) in
                let uu____2926 = FStar_List.fold_left fold_fun init xs1 in
                FStar_Pervasives_Native.snd uu____2926
let rec (p_decl : FStar_Parser_AST.decl -> FStar_Pprint.document) =
  fun d ->
    let qualifiers =
      match ((d.FStar_Parser_AST.quals), (d.FStar_Parser_AST.d)) with
      | ((FStar_Parser_AST.Assumption)::[], FStar_Parser_AST.Assume
         (id, uu____3831)) ->
          let uu____3834 =
            let uu____3835 =
              let uu____3836 = FStar_Ident.string_of_id id in
              FStar_Util.char_at uu____3836 Prims.int_zero in
            FStar_All.pipe_right uu____3835 FStar_Util.is_upper in
          if uu____3834
          then
            let uu____3837 = p_qualifier FStar_Parser_AST.Assumption in
            FStar_Pprint.op_Hat_Hat uu____3837 FStar_Pprint.space
          else p_qualifiers d.FStar_Parser_AST.quals
      | uu____3839 -> p_qualifiers d.FStar_Parser_AST.quals in
    let uu____3846 = p_attributes d.FStar_Parser_AST.attrs in
    let uu____3847 =
      let uu____3848 = p_rawDecl d in
      FStar_Pprint.op_Hat_Hat qualifiers uu____3848 in
    FStar_Pprint.op_Hat_Hat uu____3846 uu____3847
and (p_attributes : FStar_Parser_AST.attributes_ -> FStar_Pprint.document) =
  fun attrs ->
    match attrs with
    | [] -> FStar_Pprint.empty
    | uu____3850 ->
        let uu____3851 =
          let uu____3852 = str "@@ " in
          let uu____3853 =
            let uu____3854 =
              let uu____3855 =
                let uu____3856 =
                  let uu____3857 = str "; " in
                  let uu____3858 =
                    FStar_List.map (p_noSeqTermAndComment false false) attrs in
                  FStar_Pprint.flow uu____3857 uu____3858 in
                FStar_Pprint.op_Hat_Hat uu____3856 FStar_Pprint.rbracket in
              FStar_Pprint.align uu____3855 in
            FStar_Pprint.op_Hat_Hat uu____3854 FStar_Pprint.hardline in
          FStar_Pprint.op_Hat_Hat uu____3852 uu____3853 in
        FStar_Pprint.op_Hat_Hat FStar_Pprint.lbracket uu____3851
and (p_justSig : FStar_Parser_AST.decl -> FStar_Pprint.document) =
  fun d ->
    match d.FStar_Parser_AST.d with
    | FStar_Parser_AST.Val (lid, t) ->
        let uu____3864 =
          let uu____3865 = str "val" in
          let uu____3866 =
            let uu____3867 =
              let uu____3868 = p_lident lid in
              let uu____3869 =
                FStar_Pprint.op_Hat_Hat FStar_Pprint.space FStar_Pprint.colon in
              FStar_Pprint.op_Hat_Hat uu____3868 uu____3869 in
            FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____3867 in
          FStar_Pprint.op_Hat_Hat uu____3865 uu____3866 in
        let uu____3870 = p_typ false false t in
        FStar_Pprint.op_Hat_Hat uu____3864 uu____3870
    | FStar_Parser_AST.TopLevelLet (uu____3871, lbs) ->
        FStar_Pprint.separate_map FStar_Pprint.hardline
          (fun lb ->
             let uu____3896 =
               let uu____3897 = str "let" in p_letlhs uu____3897 lb false in
             FStar_Pprint.group uu____3896) lbs
    | uu____3898 -> FStar_Pprint.empty
and (p_list :
  (FStar_Ident.ident -> FStar_Pprint.document) ->
    FStar_Pprint.document ->
      FStar_Ident.ident Prims.list -> FStar_Pprint.document)
  =
  fun f ->
    fun sep ->
      fun l ->
        let rec p_list' uu___4_3913 =
          match uu___4_3913 with
          | [] -> FStar_Pprint.empty
          | x::[] -> f x
          | x::xs ->
              let uu____3921 = f x in
              let uu____3922 =
                let uu____3923 = p_list' xs in
                FStar_Pprint.op_Hat_Hat sep uu____3923 in
              FStar_Pprint.op_Hat_Hat uu____3921 uu____3922 in
        let uu____3924 = str "[" in
        let uu____3925 =
          let uu____3926 = p_list' l in
          let uu____3927 = str "]" in
          FStar_Pprint.op_Hat_Hat uu____3926 uu____3927 in
        FStar_Pprint.op_Hat_Hat uu____3924 uu____3925
and (p_rawDecl : FStar_Parser_AST.decl -> FStar_Pprint.document) =
  fun d ->
    match d.FStar_Parser_AST.d with
    | FStar_Parser_AST.Open uid ->
        let uu____3930 =
          let uu____3931 = str "open" in
          let uu____3932 = p_quident uid in
          FStar_Pprint.op_Hat_Slash_Hat uu____3931 uu____3932 in
        FStar_Pprint.group uu____3930
    | FStar_Parser_AST.Include uid ->
        let uu____3934 =
          let uu____3935 = str "include" in
          let uu____3936 = p_quident uid in
          FStar_Pprint.op_Hat_Slash_Hat uu____3935 uu____3936 in
        FStar_Pprint.group uu____3934
    | FStar_Parser_AST.Friend uid ->
        let uu____3938 =
          let uu____3939 = str "friend" in
          let uu____3940 = p_quident uid in
          FStar_Pprint.op_Hat_Slash_Hat uu____3939 uu____3940 in
        FStar_Pprint.group uu____3938
    | FStar_Parser_AST.ModuleAbbrev (uid1, uid2) ->
        let uu____3943 =
          let uu____3944 = str "module" in
          let uu____3945 =
            let uu____3946 =
              let uu____3947 = p_uident uid1 in
              let uu____3948 =
                FStar_Pprint.op_Hat_Hat FStar_Pprint.space
                  FStar_Pprint.equals in
              FStar_Pprint.op_Hat_Hat uu____3947 uu____3948 in
            FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____3946 in
          FStar_Pprint.op_Hat_Hat uu____3944 uu____3945 in
        let uu____3949 = p_quident uid2 in
        op_Hat_Slash_Plus_Hat uu____3943 uu____3949
    | FStar_Parser_AST.TopLevelModule uid ->
        let uu____3951 =
          let uu____3952 = str "module" in
          let uu____3953 =
            let uu____3954 = p_quident uid in
            FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____3954 in
          FStar_Pprint.op_Hat_Hat uu____3952 uu____3953 in
        FStar_Pprint.group uu____3951
    | FStar_Parser_AST.Tycon
        (true, uu____3955, (FStar_Parser_AST.TyconAbbrev
         (uid, tpars, FStar_Pervasives_Native.None, t))::[])
        ->
        let effect_prefix_doc =
          let uu____3968 = str "effect" in
          let uu____3969 =
            let uu____3970 = p_uident uid in
            FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____3970 in
          FStar_Pprint.op_Hat_Hat uu____3968 uu____3969 in
        let uu____3971 =
          let uu____3972 = p_typars tpars in
          FStar_Pprint.surround (Prims.of_int (2)) Prims.int_one
            effect_prefix_doc uu____3972 FStar_Pprint.equals in
        let uu____3973 = p_typ false false t in
        op_Hat_Slash_Plus_Hat uu____3971 uu____3973
    | FStar_Parser_AST.Tycon (false, tc, tcdefs) ->
        let s = if tc then str "class" else str "type" in
        let uu____3982 =
          let uu____3983 = FStar_List.hd tcdefs in
          p_typeDeclWithKw s uu____3983 in
        let uu____3984 =
          let uu____3985 = FStar_List.tl tcdefs in
          FStar_All.pipe_left
            (FStar_Pprint.concat_map
               (fun x ->
                  let uu____3993 =
                    let uu____3994 = str "and" in
                    p_typeDeclWithKw uu____3994 x in
                  FStar_Pprint.op_Hat_Hat break1 uu____3993)) uu____3985 in
        FStar_Pprint.op_Hat_Hat uu____3982 uu____3984
    | FStar_Parser_AST.TopLevelLet (q, lbs) ->
        let let_doc =
          let uu____4010 = str "let" in
          let uu____4011 = p_letqualifier q in
          FStar_Pprint.op_Hat_Hat uu____4010 uu____4011 in
        let uu____4012 = str "and" in
        separate_map_with_comments_kw let_doc uu____4012 p_letbinding lbs
          (fun uu____4021 ->
             match uu____4021 with
             | (p, t) ->
                 let uu____4028 =
                   FStar_Range.union_ranges p.FStar_Parser_AST.prange
                     t.FStar_Parser_AST.range in
                 { r = uu____4028; has_qs = false; has_attrs = false })
    | FStar_Parser_AST.Val (lid, t) ->
        let uu____4031 =
          let uu____4032 = str "val" in
          let uu____4033 =
            let uu____4034 =
              let uu____4035 = p_lident lid in
              let uu____4036 = sig_as_binders_if_possible t false in
              FStar_Pprint.op_Hat_Hat uu____4035 uu____4036 in
            FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____4034 in
          FStar_Pprint.op_Hat_Hat uu____4032 uu____4033 in
        FStar_All.pipe_left FStar_Pprint.group uu____4031
    | FStar_Parser_AST.Assume (id, t) ->
        let decl_keyword =
          let uu____4040 =
            let uu____4041 =
              let uu____4042 = FStar_Ident.string_of_id id in
              FStar_Util.char_at uu____4042 Prims.int_zero in
            FStar_All.pipe_right uu____4041 FStar_Util.is_upper in
          if uu____4040
          then FStar_Pprint.empty
          else
            (let uu____4044 = str "val" in
             FStar_Pprint.op_Hat_Hat uu____4044 FStar_Pprint.space) in
        let uu____4045 =
          let uu____4046 = p_ident id in
          let uu____4047 =
            let uu____4048 =
              let uu____4049 =
                let uu____4050 = p_typ false false t in
                FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____4050 in
              FStar_Pprint.op_Hat_Hat FStar_Pprint.colon uu____4049 in
            FStar_Pprint.group uu____4048 in
          FStar_Pprint.op_Hat_Hat uu____4046 uu____4047 in
        FStar_Pprint.op_Hat_Hat decl_keyword uu____4045
    | FStar_Parser_AST.Exception (uid, t_opt) ->
        let uu____4057 = str "exception" in
        let uu____4058 =
          let uu____4059 =
            let uu____4060 = p_uident uid in
            let uu____4061 =
              FStar_Pprint.optional
                (fun t ->
                   let uu____4065 =
                     let uu____4066 = str "of" in
                     let uu____4067 = p_typ false false t in
                     op_Hat_Slash_Plus_Hat uu____4066 uu____4067 in
                   FStar_Pprint.op_Hat_Hat break1 uu____4065) t_opt in
            FStar_Pprint.op_Hat_Hat uu____4060 uu____4061 in
          FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____4059 in
        FStar_Pprint.op_Hat_Hat uu____4057 uu____4058
    | FStar_Parser_AST.NewEffect ne ->
        let uu____4069 = str "new_effect" in
        let uu____4070 =
          let uu____4071 = p_newEffect ne in
          FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____4071 in
        FStar_Pprint.op_Hat_Hat uu____4069 uu____4070
    | FStar_Parser_AST.SubEffect se ->
        let uu____4073 = str "sub_effect" in
        let uu____4074 =
          let uu____4075 = p_subEffect se in
          FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____4075 in
        FStar_Pprint.op_Hat_Hat uu____4073 uu____4074
    | FStar_Parser_AST.LayeredEffect ne ->
        let uu____4077 = str "layered_effect" in
        let uu____4078 =
          let uu____4079 = p_newEffect ne in
          FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____4079 in
        FStar_Pprint.op_Hat_Hat uu____4077 uu____4078
    | FStar_Parser_AST.Polymonadic_bind (l1, l2, l3, t) ->
        let uu____4084 = str "polymonadic_bind" in
        let uu____4085 =
          let uu____4086 =
            let uu____4087 = p_quident l1 in
            let uu____4088 =
              let uu____4089 =
                let uu____4090 =
                  let uu____4091 = p_quident l2 in
                  let uu____4092 =
                    let uu____4093 =
                      let uu____4094 = str "|>" in
                      let uu____4095 =
                        let uu____4096 = p_quident l3 in
                        let uu____4097 =
                          let uu____4098 = p_simpleTerm false false t in
                          FStar_Pprint.op_Hat_Hat FStar_Pprint.equals
                            uu____4098 in
                        FStar_Pprint.op_Hat_Hat uu____4096 uu____4097 in
                      FStar_Pprint.op_Hat_Hat uu____4094 uu____4095 in
                    FStar_Pprint.op_Hat_Hat FStar_Pprint.rparen uu____4093 in
                  FStar_Pprint.op_Hat_Hat uu____4091 uu____4092 in
                FStar_Pprint.op_Hat_Hat break1 uu____4090 in
              FStar_Pprint.op_Hat_Hat FStar_Pprint.comma uu____4089 in
            FStar_Pprint.op_Hat_Hat uu____4087 uu____4088 in
          FStar_Pprint.op_Hat_Hat FStar_Pprint.lparen uu____4086 in
        FStar_Pprint.op_Hat_Hat uu____4084 uu____4085
    | FStar_Parser_AST.Pragma p -> p_pragma p
    | FStar_Parser_AST.Tycon (true, uu____4100, uu____4101) ->
        failwith
          "Effect abbreviation is expected to be defined by an abbreviation"
    | FStar_Parser_AST.Splice (ids, t) ->
        let uu____4112 = str "%splice" in
        let uu____4113 =
          let uu____4114 =
            let uu____4115 = str ";" in p_list p_uident uu____4115 ids in
          let uu____4116 =
            let uu____4117 = p_term false false t in
            FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____4117 in
          FStar_Pprint.op_Hat_Hat uu____4114 uu____4116 in
        FStar_Pprint.op_Hat_Hat uu____4112 uu____4113
and (p_pragma : FStar_Parser_AST.pragma -> FStar_Pprint.document) =
  fun uu___5_4118 ->
    match uu___5_4118 with
    | FStar_Parser_AST.SetOptions s ->
        let uu____4120 = str "#set-options" in
        let uu____4121 =
          let uu____4122 =
            let uu____4123 = str s in FStar_Pprint.dquotes uu____4123 in
          FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____4122 in
        FStar_Pprint.op_Hat_Hat uu____4120 uu____4121
    | FStar_Parser_AST.ResetOptions s_opt ->
        let uu____4127 = str "#reset-options" in
        let uu____4128 =
          FStar_Pprint.optional
            (fun s ->
               let uu____4132 =
                 let uu____4133 = str s in FStar_Pprint.dquotes uu____4133 in
               FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____4132) s_opt in
        FStar_Pprint.op_Hat_Hat uu____4127 uu____4128
    | FStar_Parser_AST.PushOptions s_opt ->
        let uu____4137 = str "#push-options" in
        let uu____4138 =
          FStar_Pprint.optional
            (fun s ->
               let uu____4142 =
                 let uu____4143 = str s in FStar_Pprint.dquotes uu____4143 in
               FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____4142) s_opt in
        FStar_Pprint.op_Hat_Hat uu____4137 uu____4138
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
      let uu____4156 = p_typeDecl kw typedecl in
      match uu____4156 with
      | (comm, decl, body, pre) ->
          if comm = FStar_Pprint.empty
          then
            let uu____4178 = pre body in
            FStar_Pprint.op_Hat_Hat decl uu____4178
          else
            (let uu____4180 =
               let uu____4181 =
                 let uu____4182 =
                   let uu____4183 = pre body in
                   FStar_Pprint.op_Hat_Slash_Hat uu____4183 comm in
                 FStar_Pprint.op_Hat_Hat decl uu____4182 in
               let uu____4184 =
                 let uu____4185 =
                   let uu____4186 =
                     let uu____4187 =
                       let uu____4188 =
                         FStar_Pprint.op_Hat_Hat FStar_Pprint.hardline body in
                       FStar_Pprint.op_Hat_Hat comm uu____4188 in
                     FStar_Pprint.op_Hat_Hat FStar_Pprint.hardline uu____4187 in
                   FStar_Pprint.nest (Prims.of_int (2)) uu____4186 in
                 FStar_Pprint.op_Hat_Hat decl uu____4185 in
               FStar_Pprint.ifflat uu____4181 uu____4184 in
             FStar_All.pipe_left FStar_Pprint.group uu____4180)
and (p_typeDecl :
  FStar_Pprint.document ->
    FStar_Parser_AST.tycon ->
      (FStar_Pprint.document * FStar_Pprint.document * FStar_Pprint.document
        * (FStar_Pprint.document -> FStar_Pprint.document)))
  =
  fun pre ->
    fun uu___6_4190 ->
      match uu___6_4190 with
      | FStar_Parser_AST.TyconAbstract (lid, bs, typ_opt) ->
          let uu____4213 = p_typeDeclPrefix pre false lid bs typ_opt in
          (FStar_Pprint.empty, uu____4213, FStar_Pprint.empty,
            FStar_Pervasives.id)
      | FStar_Parser_AST.TyconAbbrev (lid, bs, typ_opt, t) ->
          let uu____4229 = p_typ_sep false false t in
          (match uu____4229 with
           | (comm, doc) ->
               let uu____4247 = p_typeDeclPrefix pre true lid bs typ_opt in
               (comm, uu____4247, doc, jump2))
      | FStar_Parser_AST.TyconRecord (lid, bs, typ_opt, record_field_decls)
          ->
          let p_recordField ps uu____4289 =
            match uu____4289 with
            | (lid1, t) ->
                let uu____4296 =
                  let uu____4301 =
                    FStar_Range.extend_to_end_of_line
                      t.FStar_Parser_AST.range in
                  with_comment_sep (p_recordFieldDecl ps) (lid1, t)
                    uu____4301 in
                (match uu____4296 with
                 | (comm, field) ->
                     let sep =
                       if ps then FStar_Pprint.semi else FStar_Pprint.empty in
                     inline_comment_or_above comm field sep) in
          let p_fields =
            let uu____4311 =
              separate_map_last FStar_Pprint.hardline p_recordField
                record_field_decls in
            braces_with_nesting uu____4311 in
          let uu____4316 = p_typeDeclPrefix pre true lid bs typ_opt in
          (FStar_Pprint.empty, uu____4316, p_fields,
            ((fun d -> FStar_Pprint.op_Hat_Hat FStar_Pprint.space d)))
      | FStar_Parser_AST.TyconVariant (lid, bs, typ_opt, ct_decls) ->
          let p_constructorBranchAndComments uu____4367 =
            match uu____4367 with
            | (uid, t_opt, use_of) ->
                let range =
                  let uu____4384 =
                    let uu____4385 = FStar_Ident.range_of_id uid in
                    let uu____4386 =
                      FStar_Util.map_opt t_opt
                        (fun t -> t.FStar_Parser_AST.range) in
                    FStar_Util.dflt uu____4385 uu____4386 in
                  FStar_Range.extend_to_end_of_line uu____4384 in
                let uu____4391 =
                  with_comment_sep p_constructorBranch (uid, t_opt, use_of)
                    range in
                (match uu____4391 with
                 | (comm, ctor) ->
                     inline_comment_or_above comm ctor FStar_Pprint.empty) in
          let datacon_doc =
            FStar_Pprint.separate_map FStar_Pprint.hardline
              p_constructorBranchAndComments ct_decls in
          let uu____4417 = p_typeDeclPrefix pre true lid bs typ_opt in
          (FStar_Pprint.empty, uu____4417, datacon_doc, jump2)
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
                let uu____4443 = FStar_Pprint.op_Hat_Slash_Hat kw lid_doc in
                FStar_Pprint.group uu____4443 in
              cont kw_lid in
            let typ =
              let maybe_eq =
                if eq then FStar_Pprint.equals else FStar_Pprint.empty in
              match typ_opt with
              | FStar_Pervasives_Native.None -> maybe_eq
              | FStar_Pervasives_Native.Some t ->
                  let uu____4448 =
                    let uu____4449 =
                      let uu____4450 = p_typ false false t in
                      FStar_Pprint.op_Hat_Slash_Hat uu____4450 maybe_eq in
                    FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____4449 in
                  FStar_Pprint.op_Hat_Hat FStar_Pprint.colon uu____4448 in
            if bs = []
            then with_kw (fun n -> prefix2 n typ)
            else
              (let binders = p_binders_list true bs in
               with_kw
                 (fun n ->
                    let uu____4465 =
                      let uu____4466 = FStar_Pprint.flow break1 binders in
                      prefix2 n uu____4466 in
                    prefix2 uu____4465 typ))
and (p_recordFieldDecl :
  Prims.bool ->
    (FStar_Ident.ident * FStar_Parser_AST.term) -> FStar_Pprint.document)
  =
  fun ps ->
    fun uu____4468 ->
      match uu____4468 with
      | (lid, t) ->
          let uu____4475 =
            let uu____4476 = p_lident lid in
            let uu____4477 =
              let uu____4478 = p_typ ps false t in
              FStar_Pprint.op_Hat_Hat FStar_Pprint.colon uu____4478 in
            FStar_Pprint.op_Hat_Hat uu____4476 uu____4477 in
          FStar_Pprint.group uu____4475
and (p_constructorBranch :
  (FStar_Ident.ident * FStar_Parser_AST.term FStar_Pervasives_Native.option *
    Prims.bool) -> FStar_Pprint.document)
  =
  fun uu____4479 ->
    match uu____4479 with
    | (uid, t_opt, use_of) ->
        let sep = if use_of then str "of" else FStar_Pprint.colon in
        let uid_doc =
          let uu____4498 =
            let uu____4499 =
              let uu____4500 = p_uident uid in
              FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____4500 in
            FStar_Pprint.op_Hat_Hat FStar_Pprint.bar uu____4499 in
          FStar_Pprint.group uu____4498 in
        default_or_map uid_doc
          (fun t ->
             let uu____4504 =
               let uu____4505 =
                 let uu____4506 =
                   let uu____4507 =
                     let uu____4508 = p_typ false false t in
                     FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____4508 in
                   FStar_Pprint.op_Hat_Hat sep uu____4507 in
                 FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____4506 in
               FStar_Pprint.op_Hat_Hat uid_doc uu____4505 in
             FStar_Pprint.group uu____4504) t_opt
and (p_letlhs :
  FStar_Pprint.document ->
    (FStar_Parser_AST.pattern * FStar_Parser_AST.term) ->
      Prims.bool -> FStar_Pprint.document)
  =
  fun kw ->
    fun uu____4510 ->
      fun inner_let ->
        match uu____4510 with
        | (pat, uu____4517) ->
            let uu____4518 =
              match pat.FStar_Parser_AST.pat with
              | FStar_Parser_AST.PatAscribed
                  (pat1, (t, FStar_Pervasives_Native.None)) ->
                  (pat1,
                    (FStar_Pervasives_Native.Some (t, FStar_Pprint.empty)))
              | FStar_Parser_AST.PatAscribed
                  (pat1, (t, FStar_Pervasives_Native.Some tac)) ->
                  let uu____4570 =
                    let uu____4577 =
                      let uu____4582 =
                        let uu____4583 =
                          let uu____4584 =
                            let uu____4585 = str "by" in
                            let uu____4586 =
                              let uu____4587 =
                                p_atomicTerm (maybe_unthunk tac) in
                              FStar_Pprint.op_Hat_Hat FStar_Pprint.space
                                uu____4587 in
                            FStar_Pprint.op_Hat_Hat uu____4585 uu____4586 in
                          FStar_Pprint.op_Hat_Hat FStar_Pprint.space
                            uu____4584 in
                        FStar_Pprint.group uu____4583 in
                      (t, uu____4582) in
                    FStar_Pervasives_Native.Some uu____4577 in
                  (pat1, uu____4570)
              | uu____4598 -> (pat, FStar_Pervasives_Native.None) in
            (match uu____4518 with
             | (pat1, ascr) ->
                 (match pat1.FStar_Parser_AST.pat with
                  | FStar_Parser_AST.PatApp
                      ({
                         FStar_Parser_AST.pat = FStar_Parser_AST.PatVar
                           (lid, uu____4624);
                         FStar_Parser_AST.prange = uu____4625;_},
                       pats)
                      ->
                      let ascr_doc =
                        match ascr with
                        | FStar_Pervasives_Native.Some (t, tac) ->
                            let uu____4642 =
                              sig_as_binders_if_possible t true in
                            FStar_Pprint.op_Hat_Hat uu____4642 tac
                        | FStar_Pervasives_Native.None -> FStar_Pprint.empty in
                      let uu____4647 =
                        if inner_let
                        then
                          let uu____4660 = pats_as_binders_if_possible pats in
                          match uu____4660 with
                          | (bs, style) ->
                              ((FStar_List.append bs [ascr_doc]), style)
                        else
                          (let uu____4682 = pats_as_binders_if_possible pats in
                           match uu____4682 with
                           | (bs, style) ->
                               ((FStar_List.append bs [ascr_doc]), style)) in
                      (match uu____4647 with
                       | (terms, style) ->
                           let uu____4709 =
                             let uu____4710 =
                               let uu____4711 =
                                 let uu____4712 = p_lident lid in
                                 let uu____4713 =
                                   format_sig style terms true true in
                                 FStar_Pprint.op_Hat_Hat uu____4712
                                   uu____4713 in
                               FStar_Pprint.op_Hat_Hat FStar_Pprint.space
                                 uu____4711 in
                             FStar_Pprint.op_Hat_Hat kw uu____4710 in
                           FStar_All.pipe_left FStar_Pprint.group uu____4709)
                  | uu____4714 ->
                      let ascr_doc =
                        match ascr with
                        | FStar_Pervasives_Native.Some (t, tac) ->
                            let uu____4722 =
                              let uu____4723 =
                                let uu____4724 =
                                  p_typ_top
                                    (Arrows
                                       ((Prims.of_int (2)),
                                         (Prims.of_int (2)))) false false t in
                                FStar_Pprint.op_Hat_Hat FStar_Pprint.colon
                                  uu____4724 in
                              FStar_Pprint.group uu____4723 in
                            FStar_Pprint.op_Hat_Hat uu____4722 tac
                        | FStar_Pervasives_Native.None -> FStar_Pprint.empty in
                      let uu____4729 =
                        let uu____4730 =
                          let uu____4731 =
                            let uu____4732 = p_tuplePattern pat1 in
                            FStar_Pprint.op_Hat_Slash_Hat kw uu____4732 in
                          FStar_Pprint.group uu____4731 in
                        FStar_Pprint.op_Hat_Hat uu____4730 ascr_doc in
                      FStar_Pprint.group uu____4729))
and (p_letbinding :
  FStar_Pprint.document ->
    (FStar_Parser_AST.pattern * FStar_Parser_AST.term) ->
      FStar_Pprint.document)
  =
  fun kw ->
    fun uu____4734 ->
      match uu____4734 with
      | (pat, e) ->
          let doc_pat = p_letlhs kw (pat, e) false in
          let uu____4742 = p_term_sep false false e in
          (match uu____4742 with
           | (comm, doc_expr) ->
               let doc_expr1 =
                 inline_comment_or_above comm doc_expr FStar_Pprint.empty in
               let uu____4750 =
                 let uu____4751 =
                   FStar_Pprint.op_Hat_Slash_Hat FStar_Pprint.equals
                     doc_expr1 in
                 FStar_Pprint.op_Hat_Slash_Hat doc_pat uu____4751 in
               let uu____4752 =
                 let uu____4753 =
                   let uu____4754 =
                     let uu____4755 =
                       let uu____4756 = jump2 doc_expr1 in
                       FStar_Pprint.op_Hat_Hat FStar_Pprint.equals uu____4756 in
                     FStar_Pprint.group uu____4755 in
                   FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____4754 in
                 FStar_Pprint.op_Hat_Hat doc_pat uu____4753 in
               FStar_Pprint.ifflat uu____4750 uu____4752)
and (p_newEffect : FStar_Parser_AST.effect_decl -> FStar_Pprint.document) =
  fun uu___7_4757 ->
    match uu___7_4757 with
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
        let uu____4782 = p_uident uid in
        let uu____4783 = p_binders true bs in
        let uu____4784 =
          let uu____4785 = p_simpleTerm false false t in
          prefix2 FStar_Pprint.equals uu____4785 in
        surround_maybe_empty (Prims.of_int (2)) Prims.int_one uu____4782
          uu____4783 uu____4784
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
          let uu____4795 =
            let uu____4796 =
              let uu____4797 =
                let uu____4798 = p_uident uid in
                let uu____4799 = p_binders true bs in
                let uu____4800 =
                  let uu____4801 = p_typ false false t in
                  prefix2 FStar_Pprint.colon uu____4801 in
                surround_maybe_empty (Prims.of_int (2)) Prims.int_one
                  uu____4798 uu____4799 uu____4800 in
              FStar_Pprint.group uu____4797 in
            let uu____4802 =
              let uu____4803 = str "with" in
              let uu____4804 =
                let uu____4805 =
                  let uu____4806 =
                    let uu____4807 =
                      let uu____4808 =
                        let uu____4809 =
                          FStar_Pprint.op_Hat_Hat FStar_Pprint.semi
                            FStar_Pprint.space in
                        FStar_Pprint.op_Hat_Hat FStar_Pprint.hardline
                          uu____4809 in
                      separate_map_last uu____4808 p_effectDecl eff_decls in
                    FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____4807 in
                  FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____4806 in
                FStar_Pprint.op_Hat_Hat FStar_Pprint.hardline uu____4805 in
              FStar_Pprint.op_Hat_Hat uu____4803 uu____4804 in
            FStar_Pprint.op_Hat_Slash_Hat uu____4796 uu____4802 in
          braces_with_nesting uu____4795
and (p_effectDecl :
  Prims.bool -> FStar_Parser_AST.decl -> FStar_Pprint.document) =
  fun ps ->
    fun d ->
      match d.FStar_Parser_AST.d with
      | FStar_Parser_AST.Tycon
          (false, uu____4812, (FStar_Parser_AST.TyconAbbrev
           (lid, [], FStar_Pervasives_Native.None, e))::[])
          ->
          let uu____4821 =
            let uu____4822 = p_lident lid in
            let uu____4823 =
              FStar_Pprint.op_Hat_Hat FStar_Pprint.space FStar_Pprint.equals in
            FStar_Pprint.op_Hat_Hat uu____4822 uu____4823 in
          let uu____4824 = p_simpleTerm ps false e in
          prefix2 uu____4821 uu____4824
      | uu____4825 ->
          let uu____4826 =
            let uu____4827 = FStar_Parser_AST.decl_to_string d in
            FStar_Util.format1
              "Not a declaration of an effect member... or at least I hope so : %s"
              uu____4827 in
          failwith uu____4826
and (p_subEffect : FStar_Parser_AST.lift -> FStar_Pprint.document) =
  fun lift ->
    let lift_op_doc =
      let lifts =
        match lift.FStar_Parser_AST.lift_op with
        | FStar_Parser_AST.NonReifiableLift t -> [("lift_wp", t)]
        | FStar_Parser_AST.ReifiableLift (t1, t2) ->
            [("lift_wp", t1); ("lift", t2)]
        | FStar_Parser_AST.LiftForFree t -> [("lift", t)] in
      let p_lift ps uu____4889 =
        match uu____4889 with
        | (kwd, t) ->
            let uu____4896 =
              let uu____4897 = str kwd in
              let uu____4898 =
                FStar_Pprint.op_Hat_Hat FStar_Pprint.space
                  FStar_Pprint.equals in
              FStar_Pprint.op_Hat_Hat uu____4897 uu____4898 in
            let uu____4899 = p_simpleTerm ps false t in
            prefix2 uu____4896 uu____4899 in
      separate_break_map_last FStar_Pprint.semi p_lift lifts in
    let uu____4904 =
      let uu____4905 =
        let uu____4906 = p_quident lift.FStar_Parser_AST.msource in
        let uu____4907 =
          let uu____4908 = str "~>" in
          FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____4908 in
        FStar_Pprint.op_Hat_Hat uu____4906 uu____4907 in
      let uu____4909 = p_quident lift.FStar_Parser_AST.mdest in
      prefix2 uu____4905 uu____4909 in
    let uu____4910 =
      let uu____4911 = braces_with_nesting lift_op_doc in
      FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____4911 in
    FStar_Pprint.op_Hat_Hat uu____4904 uu____4910
and (p_qualifier : FStar_Parser_AST.qualifier -> FStar_Pprint.document) =
  fun uu___8_4912 ->
    match uu___8_4912 with
    | FStar_Parser_AST.Private -> str "private"
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
        let uu____4915 = p_qualifier q in
        FStar_Pprint.op_Hat_Hat uu____4915 FStar_Pprint.hardline
    | uu____4916 ->
        let uu____4917 =
          let uu____4918 = FStar_List.map p_qualifier qs in
          FStar_Pprint.flow break1 uu____4918 in
        FStar_Pprint.op_Hat_Hat uu____4917 FStar_Pprint.hardline
and (p_letqualifier :
  FStar_Parser_AST.let_qualifier -> FStar_Pprint.document) =
  fun uu___9_4921 ->
    match uu___9_4921 with
    | FStar_Parser_AST.Rec ->
        let uu____4922 = str "rec" in
        FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____4922
    | FStar_Parser_AST.NoLetQualifier -> FStar_Pprint.empty
and (p_aqual : FStar_Parser_AST.arg_qualifier -> FStar_Pprint.document) =
  fun uu___10_4923 ->
    match uu___10_4923 with
    | FStar_Parser_AST.Implicit -> str "#"
    | FStar_Parser_AST.Equality -> str "$"
    | FStar_Parser_AST.Meta (FStar_Parser_AST.Arg_qualifier_meta_tac t) ->
        let t1 =
          match t.FStar_Parser_AST.tm with
          | FStar_Parser_AST.Abs (uu____4926, e) -> e
          | uu____4932 ->
              FStar_Parser_AST.mk_term
                (FStar_Parser_AST.App
                   (t,
                     (FStar_Parser_AST.unit_const t.FStar_Parser_AST.range),
                     FStar_Parser_AST.Nothing)) t.FStar_Parser_AST.range
                FStar_Parser_AST.Expr in
        let uu____4933 = str "#[" in
        let uu____4934 =
          let uu____4935 = p_term false false t1 in
          let uu____4936 =
            let uu____4937 = str "]" in
            FStar_Pprint.op_Hat_Hat uu____4937 break1 in
          FStar_Pprint.op_Hat_Hat uu____4935 uu____4936 in
        FStar_Pprint.op_Hat_Hat uu____4933 uu____4934
    | FStar_Parser_AST.Meta (FStar_Parser_AST.Arg_qualifier_meta_attr t) ->
        let uu____4939 = str "#[@" in
        let uu____4940 =
          let uu____4941 = p_term false false t in
          let uu____4942 =
            let uu____4943 = str "]" in
            FStar_Pprint.op_Hat_Hat uu____4943 break1 in
          FStar_Pprint.op_Hat_Hat uu____4941 uu____4942 in
        FStar_Pprint.op_Hat_Hat uu____4939 uu____4940
and (p_disjunctivePattern :
  FStar_Parser_AST.pattern -> FStar_Pprint.document) =
  fun p ->
    match p.FStar_Parser_AST.pat with
    | FStar_Parser_AST.PatOr pats ->
        let uu____4948 =
          let uu____4949 =
            let uu____4950 =
              FStar_Pprint.op_Hat_Hat FStar_Pprint.bar FStar_Pprint.space in
            FStar_Pprint.op_Hat_Hat break1 uu____4950 in
          FStar_Pprint.separate_map uu____4949 p_tuplePattern pats in
        FStar_Pprint.group uu____4948
    | uu____4951 -> p_tuplePattern p
and (p_tuplePattern : FStar_Parser_AST.pattern -> FStar_Pprint.document) =
  fun p ->
    match p.FStar_Parser_AST.pat with
    | FStar_Parser_AST.PatTuple (pats, false) ->
        let uu____4958 =
          let uu____4959 = FStar_Pprint.op_Hat_Hat FStar_Pprint.comma break1 in
          FStar_Pprint.separate_map uu____4959 p_constructorPattern pats in
        FStar_Pprint.group uu____4958
    | uu____4960 -> p_constructorPattern p
and (p_constructorPattern :
  FStar_Parser_AST.pattern -> FStar_Pprint.document) =
  fun p ->
    match p.FStar_Parser_AST.pat with
    | FStar_Parser_AST.PatApp
        ({ FStar_Parser_AST.pat = FStar_Parser_AST.PatName maybe_cons_lid;
           FStar_Parser_AST.prange = uu____4963;_},
         hd::tl::[])
        when
        FStar_Ident.lid_equals maybe_cons_lid FStar_Parser_Const.cons_lid ->
        let uu____4968 =
          FStar_Pprint.op_Hat_Hat FStar_Pprint.colon FStar_Pprint.colon in
        let uu____4969 = p_constructorPattern hd in
        let uu____4970 = p_constructorPattern tl in
        infix0 uu____4968 uu____4969 uu____4970
    | FStar_Parser_AST.PatApp
        ({ FStar_Parser_AST.pat = FStar_Parser_AST.PatName uid;
           FStar_Parser_AST.prange = uu____4972;_},
         pats)
        ->
        let uu____4978 = p_quident uid in
        let uu____4979 =
          FStar_Pprint.separate_map break1 p_atomicPattern pats in
        prefix2 uu____4978 uu____4979
    | uu____4980 -> p_atomicPattern p
and (p_atomicPattern : FStar_Parser_AST.pattern -> FStar_Pprint.document) =
  fun p ->
    match p.FStar_Parser_AST.pat with
    | FStar_Parser_AST.PatAscribed (pat, (t, FStar_Pervasives_Native.None))
        ->
        (match ((pat.FStar_Parser_AST.pat), (t.FStar_Parser_AST.tm)) with
         | (FStar_Parser_AST.PatVar (lid, aqual), FStar_Parser_AST.Refine
            ({ FStar_Parser_AST.b = FStar_Parser_AST.Annotated (lid', t1);
               FStar_Parser_AST.brange = uu____4996;
               FStar_Parser_AST.blevel = uu____4997;
               FStar_Parser_AST.aqual = uu____4998;_},
             phi)) when
             let uu____5006 = FStar_Ident.string_of_id lid in
             let uu____5007 = FStar_Ident.string_of_id lid' in
             uu____5006 = uu____5007 ->
             let uu____5008 =
               let uu____5009 = p_ident lid in
               p_refinement aqual uu____5009 t1 phi in
             soft_parens_with_nesting uu____5008
         | (FStar_Parser_AST.PatWild aqual, FStar_Parser_AST.Refine
            ({ FStar_Parser_AST.b = FStar_Parser_AST.NoName t1;
               FStar_Parser_AST.brange = uu____5012;
               FStar_Parser_AST.blevel = uu____5013;
               FStar_Parser_AST.aqual = uu____5014;_},
             phi)) ->
             let uu____5020 =
               p_refinement aqual FStar_Pprint.underscore t1 phi in
             soft_parens_with_nesting uu____5020
         | uu____5021 ->
             let uu____5026 =
               let uu____5027 = p_tuplePattern pat in
               let uu____5028 =
                 let uu____5029 = p_tmEqNoRefinement t in
                 FStar_Pprint.op_Hat_Slash_Hat FStar_Pprint.colon uu____5029 in
               FStar_Pprint.op_Hat_Hat uu____5027 uu____5028 in
             soft_parens_with_nesting uu____5026)
    | FStar_Parser_AST.PatList pats ->
        let uu____5033 =
          separate_break_map FStar_Pprint.semi p_tuplePattern pats in
        FStar_Pprint.surround (Prims.of_int (2)) Prims.int_zero
          FStar_Pprint.lbracket uu____5033 FStar_Pprint.rbracket
    | FStar_Parser_AST.PatRecord pats ->
        let p_recordFieldPat uu____5050 =
          match uu____5050 with
          | (lid, pat) ->
              let uu____5057 = p_qlident lid in
              let uu____5058 = p_tuplePattern pat in
              infix2 FStar_Pprint.equals uu____5057 uu____5058 in
        let uu____5059 =
          separate_break_map FStar_Pprint.semi p_recordFieldPat pats in
        soft_braces_with_nesting uu____5059
    | FStar_Parser_AST.PatTuple (pats, true) ->
        let uu____5069 =
          FStar_Pprint.op_Hat_Hat FStar_Pprint.lparen FStar_Pprint.bar in
        let uu____5070 =
          separate_break_map FStar_Pprint.comma p_constructorPattern pats in
        let uu____5071 =
          FStar_Pprint.op_Hat_Hat FStar_Pprint.bar FStar_Pprint.rparen in
        FStar_Pprint.surround (Prims.of_int (2)) Prims.int_one uu____5069
          uu____5070 uu____5071
    | FStar_Parser_AST.PatTvar (tv, arg_qualifier_opt) -> p_tvar tv
    | FStar_Parser_AST.PatOp op ->
        let uu____5080 =
          let uu____5081 =
            let uu____5082 =
              let uu____5083 = FStar_Ident.string_of_id op in str uu____5083 in
            let uu____5084 =
              FStar_Pprint.op_Hat_Hat FStar_Pprint.space FStar_Pprint.rparen in
            FStar_Pprint.op_Hat_Hat uu____5082 uu____5084 in
          FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____5081 in
        FStar_Pprint.op_Hat_Hat FStar_Pprint.lparen uu____5080
    | FStar_Parser_AST.PatWild aqual ->
        let uu____5088 = FStar_Pprint.optional p_aqual aqual in
        FStar_Pprint.op_Hat_Hat uu____5088 FStar_Pprint.underscore
    | FStar_Parser_AST.PatConst c -> p_constant c
    | FStar_Parser_AST.PatVar (lid, aqual) ->
        let uu____5096 = FStar_Pprint.optional p_aqual aqual in
        let uu____5097 = p_lident lid in
        FStar_Pprint.op_Hat_Hat uu____5096 uu____5097
    | FStar_Parser_AST.PatName uid -> p_quident uid
    | FStar_Parser_AST.PatOr uu____5099 -> failwith "Inner or pattern !"
    | FStar_Parser_AST.PatApp
        ({ FStar_Parser_AST.pat = FStar_Parser_AST.PatName uu____5102;
           FStar_Parser_AST.prange = uu____5103;_},
         uu____5104)
        ->
        let uu____5109 = p_tuplePattern p in
        soft_parens_with_nesting uu____5109
    | FStar_Parser_AST.PatTuple (uu____5110, false) ->
        let uu____5115 = p_tuplePattern p in
        soft_parens_with_nesting uu____5115
    | uu____5116 ->
        let uu____5117 =
          let uu____5118 = FStar_Parser_AST.pat_to_string p in
          FStar_Util.format1 "Invalid pattern %s" uu____5118 in
        failwith uu____5117
and (is_typ_tuple : FStar_Parser_AST.term -> Prims.bool) =
  fun e ->
    match e.FStar_Parser_AST.tm with
    | FStar_Parser_AST.Op (id, uu____5121) when
        let uu____5126 = FStar_Ident.string_of_id id in uu____5126 = "*" ->
        true
    | uu____5127 -> false
and (is_meta_qualifier :
  FStar_Parser_AST.arg_qualifier FStar_Pervasives_Native.option -> Prims.bool)
  =
  fun aq ->
    match aq with
    | FStar_Pervasives_Native.Some (FStar_Parser_AST.Meta uu____5131) -> true
    | uu____5132 -> false
and (p_binder :
  Prims.bool -> FStar_Parser_AST.binder -> FStar_Pprint.document) =
  fun is_atomic ->
    fun b ->
      let uu____5137 = p_binder' is_atomic b in
      match uu____5137 with
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
          let uu____5173 =
            let uu____5174 =
              FStar_Pprint.optional p_aqual b.FStar_Parser_AST.aqual in
            let uu____5175 = p_lident lid in
            FStar_Pprint.op_Hat_Hat uu____5174 uu____5175 in
          (uu____5173, FStar_Pervasives_Native.None, cat_with_colon)
      | FStar_Parser_AST.TVariable lid ->
          let uu____5181 = p_lident lid in
          (uu____5181, FStar_Pervasives_Native.None, cat_with_colon)
      | FStar_Parser_AST.Annotated (lid, t) ->
          let uu____5188 =
            match t.FStar_Parser_AST.tm with
            | FStar_Parser_AST.Refine
                ({
                   FStar_Parser_AST.b = FStar_Parser_AST.Annotated (lid', t1);
                   FStar_Parser_AST.brange = uu____5199;
                   FStar_Parser_AST.blevel = uu____5200;
                   FStar_Parser_AST.aqual = uu____5201;_},
                 phi)
                when
                let uu____5205 = FStar_Ident.string_of_id lid in
                let uu____5206 = FStar_Ident.string_of_id lid' in
                uu____5205 = uu____5206 ->
                let uu____5207 = p_lident lid in
                p_refinement' b.FStar_Parser_AST.aqual uu____5207 t1 phi
            | uu____5208 ->
                let t' =
                  let uu____5210 = is_typ_tuple t in
                  if uu____5210
                  then
                    let uu____5211 = p_tmFormula t in
                    soft_parens_with_nesting uu____5211
                  else p_tmFormula t in
                let uu____5213 =
                  let uu____5214 =
                    FStar_Pprint.optional p_aqual b.FStar_Parser_AST.aqual in
                  let uu____5215 = p_lident lid in
                  FStar_Pprint.op_Hat_Hat uu____5214 uu____5215 in
                (uu____5213, t') in
          (match uu____5188 with
           | (b', t') ->
               let catf1 =
                 let uu____5233 =
                   is_atomic || (is_meta_qualifier b.FStar_Parser_AST.aqual) in
                 if uu____5233
                 then
                   fun x ->
                     fun y ->
                       let uu____5238 =
                         let uu____5239 =
                           let uu____5240 = cat_with_colon x y in
                           FStar_Pprint.op_Hat_Hat uu____5240
                             FStar_Pprint.rparen in
                         FStar_Pprint.op_Hat_Hat FStar_Pprint.lparen
                           uu____5239 in
                       FStar_Pprint.group uu____5238
                 else
                   (fun x ->
                      fun y ->
                        let uu____5244 = cat_with_colon x y in
                        FStar_Pprint.group uu____5244) in
               (b', (FStar_Pervasives_Native.Some t'), catf1))
      | FStar_Parser_AST.TAnnotated uu____5249 ->
          failwith "Is this still used ?"
      | FStar_Parser_AST.NoName t ->
          (match t.FStar_Parser_AST.tm with
           | FStar_Parser_AST.Refine
               ({ FStar_Parser_AST.b = FStar_Parser_AST.NoName t1;
                  FStar_Parser_AST.brange = uu____5276;
                  FStar_Parser_AST.blevel = uu____5277;
                  FStar_Parser_AST.aqual = uu____5278;_},
                phi)
               ->
               let uu____5282 =
                 p_refinement' b.FStar_Parser_AST.aqual
                   FStar_Pprint.underscore t1 phi in
               (match uu____5282 with
                | (b', t') ->
                    (b', (FStar_Pervasives_Native.Some t'), cat_with_colon))
           | uu____5303 ->
               if is_atomic
               then
                 let uu____5314 = p_atomicTerm t in
                 (uu____5314, FStar_Pervasives_Native.None, cat_with_colon)
               else
                 (let uu____5320 = p_appTerm t in
                  (uu____5320, FStar_Pervasives_Native.None, cat_with_colon)))
and (p_refinement :
  FStar_Parser_AST.arg_qualifier FStar_Pervasives_Native.option ->
    FStar_Pprint.document ->
      FStar_Parser_AST.term -> FStar_Parser_AST.term -> FStar_Pprint.document)
  =
  fun aqual_opt ->
    fun binder ->
      fun t ->
        fun phi ->
          let uu____5331 = p_refinement' aqual_opt binder t phi in
          match uu____5331 with | (b, typ) -> cat_with_colon b typ
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
            | FStar_Parser_AST.Construct uu____5345 -> false
            | FStar_Parser_AST.App uu____5356 -> false
            | FStar_Parser_AST.Op uu____5363 -> false
            | uu____5370 -> true in
          let uu____5371 = p_noSeqTerm false false phi in
          match uu____5371 with
          | (comm, phi1) ->
              let phi2 =
                if comm = FStar_Pprint.empty
                then phi1
                else
                  (let uu____5384 =
                     FStar_Pprint.op_Hat_Hat FStar_Pprint.hardline phi1 in
                   FStar_Pprint.op_Hat_Hat comm uu____5384) in
              let jump_break =
                if is_t_atomic then Prims.int_zero else Prims.int_one in
              let uu____5387 =
                let uu____5388 = FStar_Pprint.optional p_aqual aqual_opt in
                FStar_Pprint.op_Hat_Hat uu____5388 binder in
              let uu____5389 =
                let uu____5390 = p_appTerm t in
                let uu____5391 =
                  let uu____5392 =
                    let uu____5393 =
                      let uu____5394 = soft_braces_with_nesting_tight phi2 in
                      let uu____5395 = soft_braces_with_nesting phi2 in
                      FStar_Pprint.ifflat uu____5394 uu____5395 in
                    FStar_Pprint.group uu____5393 in
                  FStar_Pprint.jump (Prims.of_int (2)) jump_break uu____5392 in
                FStar_Pprint.op_Hat_Hat uu____5390 uu____5391 in
              (uu____5387, uu____5389)
and (p_binders_list :
  Prims.bool ->
    FStar_Parser_AST.binder Prims.list -> FStar_Pprint.document Prims.list)
  = fun is_atomic -> fun bs -> FStar_List.map (p_binder is_atomic) bs
and (p_binders :
  Prims.bool -> FStar_Parser_AST.binder Prims.list -> FStar_Pprint.document)
  =
  fun is_atomic ->
    fun bs ->
      let uu____5406 = p_binders_list is_atomic bs in
      separate_or_flow break1 uu____5406
and (string_of_id_or_underscore : FStar_Ident.ident -> FStar_Pprint.document)
  =
  fun lid ->
    let uu____5410 =
      (let uu____5413 = FStar_Ident.string_of_id lid in
       FStar_Util.starts_with uu____5413 FStar_Ident.reserved_prefix) &&
        (let uu____5415 = FStar_Options.print_real_names () in
         Prims.op_Negation uu____5415) in
    if uu____5410
    then FStar_Pprint.underscore
    else (let uu____5417 = FStar_Ident.string_of_id lid in str uu____5417)
and (text_of_lid_or_underscore : FStar_Ident.lident -> FStar_Pprint.document)
  =
  fun lid ->
    let uu____5419 =
      (let uu____5422 =
         let uu____5423 = FStar_Ident.ident_of_lid lid in
         FStar_Ident.string_of_id uu____5423 in
       FStar_Util.starts_with uu____5422 FStar_Ident.reserved_prefix) &&
        (let uu____5425 = FStar_Options.print_real_names () in
         Prims.op_Negation uu____5425) in
    if uu____5419
    then FStar_Pprint.underscore
    else (let uu____5427 = FStar_Ident.string_of_lid lid in str uu____5427)
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
          let uu____5443 = FStar_Pprint.op_Hat_Hat doc sep in
          FStar_Pprint.group uu____5443
        else
          (let uu____5445 =
             let uu____5446 =
               let uu____5447 =
                 let uu____5448 =
                   let uu____5449 = FStar_Pprint.op_Hat_Hat break1 comm in
                   FStar_Pprint.op_Hat_Hat sep uu____5449 in
                 FStar_Pprint.op_Hat_Hat doc uu____5448 in
               FStar_Pprint.group uu____5447 in
             let uu____5450 =
               let uu____5451 =
                 let uu____5452 = FStar_Pprint.op_Hat_Hat doc sep in
                 FStar_Pprint.op_Hat_Hat FStar_Pprint.hardline uu____5452 in
               FStar_Pprint.op_Hat_Hat comm uu____5451 in
             FStar_Pprint.ifflat uu____5446 uu____5450 in
           FStar_All.pipe_left FStar_Pprint.group uu____5445)
and (p_term :
  Prims.bool -> Prims.bool -> FStar_Parser_AST.term -> FStar_Pprint.document)
  =
  fun ps ->
    fun pb ->
      fun e ->
        match e.FStar_Parser_AST.tm with
        | FStar_Parser_AST.Seq (e1, e2) ->
            let uu____5458 = p_noSeqTerm true false e1 in
            (match uu____5458 with
             | (comm, t1) ->
                 let uu____5465 =
                   inline_comment_or_above comm t1 FStar_Pprint.semi in
                 let uu____5466 =
                   let uu____5467 = p_term ps pb e2 in
                   FStar_Pprint.op_Hat_Hat FStar_Pprint.hardline uu____5467 in
                 FStar_Pprint.op_Hat_Hat uu____5465 uu____5466)
        | FStar_Parser_AST.Bind (x, e1, e2) ->
            let uu____5471 =
              let uu____5472 =
                let uu____5473 =
                  let uu____5474 = p_lident x in
                  let uu____5475 =
                    FStar_Pprint.op_Hat_Hat FStar_Pprint.space
                      FStar_Pprint.long_left_arrow in
                  FStar_Pprint.op_Hat_Hat uu____5474 uu____5475 in
                let uu____5476 =
                  let uu____5477 = p_noSeqTermAndComment true false e1 in
                  let uu____5478 =
                    FStar_Pprint.op_Hat_Hat FStar_Pprint.space
                      FStar_Pprint.semi in
                  FStar_Pprint.op_Hat_Hat uu____5477 uu____5478 in
                op_Hat_Slash_Plus_Hat uu____5473 uu____5476 in
              FStar_Pprint.group uu____5472 in
            let uu____5479 = p_term ps pb e2 in
            FStar_Pprint.op_Hat_Slash_Hat uu____5471 uu____5479
        | uu____5480 ->
            let uu____5481 = p_noSeqTermAndComment ps pb e in
            FStar_Pprint.group uu____5481
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
            let uu____5491 = p_noSeqTerm true false e1 in
            (match uu____5491 with
             | (comm, t1) ->
                 let uu____5502 =
                   let uu____5503 =
                     let uu____5504 =
                       FStar_Pprint.op_Hat_Hat t1 FStar_Pprint.semi in
                     FStar_Pprint.group uu____5504 in
                   let uu____5505 =
                     let uu____5506 = p_term ps pb e2 in
                     FStar_Pprint.op_Hat_Hat FStar_Pprint.hardline uu____5506 in
                   FStar_Pprint.op_Hat_Hat uu____5503 uu____5505 in
                 (comm, uu____5502))
        | FStar_Parser_AST.Bind (x, e1, e2) ->
            let uu____5510 =
              let uu____5511 =
                let uu____5512 =
                  let uu____5513 =
                    let uu____5514 = p_lident x in
                    let uu____5515 =
                      FStar_Pprint.op_Hat_Hat FStar_Pprint.space
                        FStar_Pprint.long_left_arrow in
                    FStar_Pprint.op_Hat_Hat uu____5514 uu____5515 in
                  let uu____5516 =
                    let uu____5517 = p_noSeqTermAndComment true false e1 in
                    let uu____5518 =
                      FStar_Pprint.op_Hat_Hat FStar_Pprint.space
                        FStar_Pprint.semi in
                    FStar_Pprint.op_Hat_Hat uu____5517 uu____5518 in
                  op_Hat_Slash_Plus_Hat uu____5513 uu____5516 in
                FStar_Pprint.group uu____5512 in
              let uu____5519 = p_term ps pb e2 in
              FStar_Pprint.op_Hat_Slash_Hat uu____5511 uu____5519 in
            (FStar_Pprint.empty, uu____5510)
        | uu____5520 -> p_noSeqTerm ps pb e
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
            let uu____5534 =
              let uu____5535 = p_tmIff e1 in
              let uu____5536 =
                let uu____5537 =
                  let uu____5538 = p_typ ps pb t in
                  FStar_Pprint.op_Hat_Slash_Hat FStar_Pprint.colon uu____5538 in
                FStar_Pprint.op_Hat_Hat FStar_Pprint.langle uu____5537 in
              FStar_Pprint.op_Hat_Slash_Hat uu____5535 uu____5536 in
            FStar_Pprint.group uu____5534
        | FStar_Parser_AST.Ascribed (e1, t, FStar_Pervasives_Native.Some tac)
            ->
            let uu____5544 =
              let uu____5545 = p_tmIff e1 in
              let uu____5546 =
                let uu____5547 =
                  let uu____5548 =
                    let uu____5549 = p_typ false false t in
                    let uu____5550 =
                      let uu____5551 = str "by" in
                      let uu____5552 = p_typ ps pb (maybe_unthunk tac) in
                      FStar_Pprint.op_Hat_Slash_Hat uu____5551 uu____5552 in
                    FStar_Pprint.op_Hat_Slash_Hat uu____5549 uu____5550 in
                  FStar_Pprint.op_Hat_Slash_Hat FStar_Pprint.colon uu____5548 in
                FStar_Pprint.op_Hat_Hat FStar_Pprint.langle uu____5547 in
              FStar_Pprint.op_Hat_Slash_Hat uu____5545 uu____5546 in
            FStar_Pprint.group uu____5544
        | FStar_Parser_AST.Op (id, e1::e2::e3::[]) when
            let uu____5559 = FStar_Ident.string_of_id id in
            uu____5559 = ".()<-" ->
            let uu____5560 =
              let uu____5561 =
                let uu____5562 =
                  let uu____5563 = p_atomicTermNotQUident e1 in
                  let uu____5564 =
                    let uu____5565 =
                      let uu____5566 =
                        let uu____5567 = p_term false false e2 in
                        soft_parens_with_nesting uu____5567 in
                      let uu____5568 =
                        FStar_Pprint.op_Hat_Hat FStar_Pprint.space
                          FStar_Pprint.larrow in
                      FStar_Pprint.op_Hat_Hat uu____5566 uu____5568 in
                    FStar_Pprint.op_Hat_Hat FStar_Pprint.dot uu____5565 in
                  FStar_Pprint.op_Hat_Hat uu____5563 uu____5564 in
                FStar_Pprint.group uu____5562 in
              let uu____5569 =
                let uu____5570 = p_noSeqTermAndComment ps pb e3 in
                jump2 uu____5570 in
              FStar_Pprint.op_Hat_Hat uu____5561 uu____5569 in
            FStar_Pprint.group uu____5560
        | FStar_Parser_AST.Op (id, e1::e2::e3::[]) when
            let uu____5577 = FStar_Ident.string_of_id id in
            uu____5577 = ".[]<-" ->
            let uu____5578 =
              let uu____5579 =
                let uu____5580 =
                  let uu____5581 = p_atomicTermNotQUident e1 in
                  let uu____5582 =
                    let uu____5583 =
                      let uu____5584 =
                        let uu____5585 = p_term false false e2 in
                        soft_brackets_with_nesting uu____5585 in
                      let uu____5586 =
                        FStar_Pprint.op_Hat_Hat FStar_Pprint.space
                          FStar_Pprint.larrow in
                      FStar_Pprint.op_Hat_Hat uu____5584 uu____5586 in
                    FStar_Pprint.op_Hat_Hat FStar_Pprint.dot uu____5583 in
                  FStar_Pprint.op_Hat_Hat uu____5581 uu____5582 in
                FStar_Pprint.group uu____5580 in
              let uu____5587 =
                let uu____5588 = p_noSeqTermAndComment ps pb e3 in
                jump2 uu____5588 in
              FStar_Pprint.op_Hat_Hat uu____5579 uu____5587 in
            FStar_Pprint.group uu____5578
        | FStar_Parser_AST.Requires (e1, wtf) ->
            let uu____5596 =
              let uu____5597 = str "requires" in
              let uu____5598 = p_typ ps pb e1 in
              FStar_Pprint.op_Hat_Slash_Hat uu____5597 uu____5598 in
            FStar_Pprint.group uu____5596
        | FStar_Parser_AST.Ensures (e1, wtf) ->
            let uu____5606 =
              let uu____5607 = str "ensures" in
              let uu____5608 = p_typ ps pb e1 in
              FStar_Pprint.op_Hat_Slash_Hat uu____5607 uu____5608 in
            FStar_Pprint.group uu____5606
        | FStar_Parser_AST.Attributes es ->
            let uu____5612 =
              let uu____5613 = str "attributes" in
              let uu____5614 =
                FStar_Pprint.separate_map break1 p_atomicTerm es in
              FStar_Pprint.op_Hat_Slash_Hat uu____5613 uu____5614 in
            FStar_Pprint.group uu____5612
        | FStar_Parser_AST.If (e1, e2, e3) ->
            if is_unit e3
            then
              let uu____5618 =
                let uu____5619 =
                  let uu____5620 = str "if" in
                  let uu____5621 = p_noSeqTermAndComment false false e1 in
                  op_Hat_Slash_Plus_Hat uu____5620 uu____5621 in
                let uu____5622 =
                  let uu____5623 = str "then" in
                  let uu____5624 = p_noSeqTermAndComment ps pb e2 in
                  op_Hat_Slash_Plus_Hat uu____5623 uu____5624 in
                FStar_Pprint.op_Hat_Slash_Hat uu____5619 uu____5622 in
              FStar_Pprint.group uu____5618
            else
              (let e2_doc =
                 match e2.FStar_Parser_AST.tm with
                 | FStar_Parser_AST.If (uu____5627, uu____5628, e31) when
                     is_unit e31 ->
                     let uu____5630 = p_noSeqTermAndComment false false e2 in
                     soft_parens_with_nesting uu____5630
                 | uu____5631 -> p_noSeqTermAndComment false false e2 in
               let uu____5632 =
                 let uu____5633 =
                   let uu____5634 = str "if" in
                   let uu____5635 = p_noSeqTermAndComment false false e1 in
                   op_Hat_Slash_Plus_Hat uu____5634 uu____5635 in
                 let uu____5636 =
                   let uu____5637 =
                     let uu____5638 = str "then" in
                     op_Hat_Slash_Plus_Hat uu____5638 e2_doc in
                   let uu____5639 =
                     let uu____5640 = str "else" in
                     let uu____5641 = p_noSeqTermAndComment ps pb e3 in
                     op_Hat_Slash_Plus_Hat uu____5640 uu____5641 in
                   FStar_Pprint.op_Hat_Slash_Hat uu____5637 uu____5639 in
                 FStar_Pprint.op_Hat_Slash_Hat uu____5633 uu____5636 in
               FStar_Pprint.group uu____5632)
        | FStar_Parser_AST.TryWith (e1, branches) ->
            let uu____5664 =
              let uu____5665 =
                let uu____5666 =
                  let uu____5667 = str "try" in
                  let uu____5668 = p_noSeqTermAndComment false false e1 in
                  prefix2 uu____5667 uu____5668 in
                let uu____5669 =
                  let uu____5670 = str "with" in
                  let uu____5671 =
                    separate_map_last FStar_Pprint.hardline p_patternBranch
                      branches in
                  FStar_Pprint.op_Hat_Slash_Hat uu____5670 uu____5671 in
                FStar_Pprint.op_Hat_Slash_Hat uu____5666 uu____5669 in
              FStar_Pprint.group uu____5665 in
            let uu____5680 = paren_if (ps || pb) in uu____5680 uu____5664
        | FStar_Parser_AST.Match (e1, branches) ->
            let uu____5707 =
              let uu____5708 =
                let uu____5709 =
                  let uu____5710 = str "match" in
                  let uu____5711 = p_noSeqTermAndComment false false e1 in
                  let uu____5712 = str "with" in
                  FStar_Pprint.surround (Prims.of_int (2)) Prims.int_one
                    uu____5710 uu____5711 uu____5712 in
                let uu____5713 =
                  separate_map_last FStar_Pprint.hardline p_patternBranch
                    branches in
                FStar_Pprint.op_Hat_Slash_Hat uu____5709 uu____5713 in
              FStar_Pprint.group uu____5708 in
            let uu____5722 = paren_if (ps || pb) in uu____5722 uu____5707
        | FStar_Parser_AST.LetOpen (uid, e1) ->
            let uu____5729 =
              let uu____5730 =
                let uu____5731 =
                  let uu____5732 = str "let open" in
                  let uu____5733 = p_quident uid in
                  let uu____5734 = str "in" in
                  FStar_Pprint.surround (Prims.of_int (2)) Prims.int_one
                    uu____5732 uu____5733 uu____5734 in
                let uu____5735 = p_term false pb e1 in
                FStar_Pprint.op_Hat_Slash_Hat uu____5731 uu____5735 in
              FStar_Pprint.group uu____5730 in
            let uu____5736 = paren_if ps in uu____5736 uu____5729
        | FStar_Parser_AST.Let (q, lbs, e1) ->
            let p_lb q1 uu____5800 is_last =
              match uu____5800 with
              | (a, (pat, e2)) ->
                  let attrs = p_attrs_opt a in
                  let doc_let_or_and =
                    match q1 with
                    | FStar_Pervasives_Native.Some (FStar_Parser_AST.Rec) ->
                        let uu____5833 =
                          let uu____5834 = str "let" in
                          let uu____5835 = str "rec" in
                          FStar_Pprint.op_Hat_Slash_Hat uu____5834 uu____5835 in
                        FStar_Pprint.group uu____5833
                    | FStar_Pervasives_Native.Some
                        (FStar_Parser_AST.NoLetQualifier) -> str "let"
                    | uu____5836 -> str "and" in
                  let doc_pat = p_letlhs doc_let_or_and (pat, e2) true in
                  let uu____5840 = p_term_sep false false e2 in
                  (match uu____5840 with
                   | (comm, doc_expr) ->
                       let doc_expr1 =
                         inline_comment_or_above comm doc_expr
                           FStar_Pprint.empty in
                       let uu____5848 =
                         if is_last
                         then
                           let uu____5849 =
                             FStar_Pprint.flow break1
                               [doc_pat; FStar_Pprint.equals] in
                           let uu____5850 = str "in" in
                           FStar_Pprint.surround (Prims.of_int (2))
                             Prims.int_one uu____5849 doc_expr1 uu____5850
                         else
                           (let uu____5852 =
                              FStar_Pprint.flow break1
                                [doc_pat; FStar_Pprint.equals; doc_expr1] in
                            FStar_Pprint.hang (Prims.of_int (2)) uu____5852) in
                       FStar_Pprint.op_Hat_Hat attrs uu____5848) in
            let l = FStar_List.length lbs in
            let lbs_docs =
              FStar_List.mapi
                (fun i ->
                   fun lb ->
                     if i = Prims.int_zero
                     then
                       let uu____5898 =
                         p_lb (FStar_Pervasives_Native.Some q) lb
                           (i = (l - Prims.int_one)) in
                       FStar_Pprint.group uu____5898
                     else
                       (let uu____5900 =
                          p_lb FStar_Pervasives_Native.None lb
                            (i = (l - Prims.int_one)) in
                        FStar_Pprint.group uu____5900)) lbs in
            let lbs_doc =
              let uu____5902 = FStar_Pprint.separate break1 lbs_docs in
              FStar_Pprint.group uu____5902 in
            let uu____5903 =
              let uu____5904 =
                let uu____5905 =
                  let uu____5906 = p_term false pb e1 in
                  FStar_Pprint.op_Hat_Hat FStar_Pprint.hardline uu____5906 in
                FStar_Pprint.op_Hat_Hat lbs_doc uu____5905 in
              FStar_Pprint.group uu____5904 in
            let uu____5907 = paren_if ps in uu____5907 uu____5903
        | FStar_Parser_AST.Abs
            ({ FStar_Parser_AST.pat = FStar_Parser_AST.PatVar (x, typ_opt);
               FStar_Parser_AST.prange = uu____5914;_}::[],
             {
               FStar_Parser_AST.tm = FStar_Parser_AST.Match
                 (maybe_x, branches);
               FStar_Parser_AST.range = uu____5917;
               FStar_Parser_AST.level = uu____5918;_})
            when matches_var maybe_x x ->
            let uu____5945 =
              let uu____5946 =
                let uu____5947 = str "function" in
                let uu____5948 =
                  separate_map_last FStar_Pprint.hardline p_patternBranch
                    branches in
                FStar_Pprint.op_Hat_Slash_Hat uu____5947 uu____5948 in
              FStar_Pprint.group uu____5946 in
            let uu____5957 = paren_if (ps || pb) in uu____5957 uu____5945
        | FStar_Parser_AST.Quote (e1, FStar_Parser_AST.Dynamic) ->
            let uu____5963 =
              let uu____5964 = str "quote" in
              let uu____5965 = p_noSeqTermAndComment ps pb e1 in
              FStar_Pprint.op_Hat_Slash_Hat uu____5964 uu____5965 in
            FStar_Pprint.group uu____5963
        | FStar_Parser_AST.Quote (e1, FStar_Parser_AST.Static) ->
            let uu____5967 =
              let uu____5968 = str "`" in
              let uu____5969 = p_noSeqTermAndComment ps pb e1 in
              FStar_Pprint.op_Hat_Hat uu____5968 uu____5969 in
            FStar_Pprint.group uu____5967
        | FStar_Parser_AST.VQuote e1 ->
            let uu____5971 =
              let uu____5972 = str "`%" in
              let uu____5973 = p_noSeqTermAndComment ps pb e1 in
              FStar_Pprint.op_Hat_Hat uu____5972 uu____5973 in
            FStar_Pprint.group uu____5971
        | FStar_Parser_AST.Antiquote
            {
              FStar_Parser_AST.tm = FStar_Parser_AST.Quote
                (e1, FStar_Parser_AST.Dynamic);
              FStar_Parser_AST.range = uu____5975;
              FStar_Parser_AST.level = uu____5976;_}
            ->
            let uu____5977 =
              let uu____5978 = str "`@" in
              let uu____5979 = p_noSeqTermAndComment ps pb e1 in
              FStar_Pprint.op_Hat_Hat uu____5978 uu____5979 in
            FStar_Pprint.group uu____5977
        | FStar_Parser_AST.Antiquote e1 ->
            let uu____5981 =
              let uu____5982 = str "`#" in
              let uu____5983 = p_noSeqTermAndComment ps pb e1 in
              FStar_Pprint.op_Hat_Hat uu____5982 uu____5983 in
            FStar_Pprint.group uu____5981
        | FStar_Parser_AST.CalcProof (rel, init, steps) ->
            let head =
              let uu____5992 = str "calc" in
              let uu____5993 =
                let uu____5994 =
                  let uu____5995 = p_noSeqTermAndComment false false rel in
                  let uu____5996 =
                    FStar_Pprint.op_Hat_Hat FStar_Pprint.space
                      FStar_Pprint.lbrace in
                  FStar_Pprint.op_Hat_Hat uu____5995 uu____5996 in
                FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____5994 in
              FStar_Pprint.op_Hat_Hat uu____5992 uu____5993 in
            let bot = FStar_Pprint.rbrace in
            let uu____5998 =
              FStar_Pprint.op_Hat_Hat FStar_Pprint.hardline bot in
            let uu____5999 =
              let uu____6000 =
                let uu____6001 =
                  let uu____6002 = p_noSeqTermAndComment false false init in
                  let uu____6003 =
                    let uu____6004 = str ";" in
                    let uu____6005 =
                      let uu____6006 =
                        separate_map_last FStar_Pprint.hardline p_calcStep
                          steps in
                      FStar_Pprint.op_Hat_Hat FStar_Pprint.hardline
                        uu____6006 in
                    FStar_Pprint.op_Hat_Hat uu____6004 uu____6005 in
                  FStar_Pprint.op_Hat_Hat uu____6002 uu____6003 in
                FStar_Pprint.op_Hat_Hat FStar_Pprint.hardline uu____6001 in
              FStar_All.pipe_left (FStar_Pprint.nest (Prims.of_int (2)))
                uu____6000 in
            FStar_Pprint.enclose head uu____5998 uu____5999
        | uu____6007 -> p_typ ps pb e
and (p_calcStep :
  Prims.bool -> FStar_Parser_AST.calc_step -> FStar_Pprint.document) =
  fun uu____6008 ->
    fun uu____6009 ->
      match uu____6009 with
      | FStar_Parser_AST.CalcStep (rel, just, next) ->
          let uu____6013 =
            let uu____6014 = p_noSeqTermAndComment false false rel in
            let uu____6015 =
              let uu____6016 =
                let uu____6017 =
                  let uu____6018 =
                    let uu____6019 = p_noSeqTermAndComment false false just in
                    let uu____6020 =
                      let uu____6021 =
                        let uu____6022 =
                          let uu____6023 =
                            let uu____6024 =
                              p_noSeqTermAndComment false false next in
                            let uu____6025 = str ";" in
                            FStar_Pprint.op_Hat_Hat uu____6024 uu____6025 in
                          FStar_Pprint.op_Hat_Hat FStar_Pprint.hardline
                            uu____6023 in
                        FStar_Pprint.op_Hat_Hat FStar_Pprint.rbrace
                          uu____6022 in
                      FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____6021 in
                    FStar_Pprint.op_Hat_Hat uu____6019 uu____6020 in
                  FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____6018 in
                FStar_Pprint.op_Hat_Hat FStar_Pprint.lbrace uu____6017 in
              FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____6016 in
            FStar_Pprint.op_Hat_Hat uu____6014 uu____6015 in
          FStar_Pprint.group uu____6013
and (p_attrs_opt :
  FStar_Parser_AST.term Prims.list FStar_Pervasives_Native.option ->
    FStar_Pprint.document)
  =
  fun uu___11_6026 ->
    match uu___11_6026 with
    | FStar_Pervasives_Native.None -> FStar_Pprint.empty
    | FStar_Pervasives_Native.Some terms ->
        let uu____6038 =
          let uu____6039 = str "[@@" in
          let uu____6040 =
            let uu____6041 =
              let uu____6042 = str "; " in
              FStar_Pprint.separate_map uu____6042
                (p_noSeqTermAndComment false false) terms in
            let uu____6043 = str "]" in
            FStar_Pprint.op_Hat_Slash_Hat uu____6041 uu____6043 in
          FStar_Pprint.op_Hat_Slash_Hat uu____6039 uu____6040 in
        FStar_Pprint.group uu____6038
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
        | FStar_Parser_AST.QForall (bs, (uu____6054, trigger), e1) ->
            let binders_doc = p_binders true bs in
            let term_doc = p_noSeqTermAndComment ps pb e1 in
            (match trigger with
             | [] ->
                 let uu____6087 =
                   let uu____6088 =
                     let uu____6089 = p_quantifier e in
                     FStar_Pprint.op_Hat_Hat uu____6089 FStar_Pprint.space in
                   FStar_Pprint.soft_surround (Prims.of_int (2))
                     Prims.int_zero uu____6088 binders_doc FStar_Pprint.dot in
                 prefix2 uu____6087 term_doc
             | pats ->
                 let uu____6095 =
                   let uu____6096 =
                     let uu____6097 =
                       let uu____6098 =
                         let uu____6099 = p_quantifier e in
                         FStar_Pprint.op_Hat_Hat uu____6099
                           FStar_Pprint.space in
                       FStar_Pprint.soft_surround (Prims.of_int (2))
                         Prims.int_zero uu____6098 binders_doc
                         FStar_Pprint.dot in
                     let uu____6100 = p_trigger trigger in
                     prefix2 uu____6097 uu____6100 in
                   FStar_Pprint.group uu____6096 in
                 prefix2 uu____6095 term_doc)
        | FStar_Parser_AST.QExists (bs, (uu____6102, trigger), e1) ->
            let binders_doc = p_binders true bs in
            let term_doc = p_noSeqTermAndComment ps pb e1 in
            (match trigger with
             | [] ->
                 let uu____6135 =
                   let uu____6136 =
                     let uu____6137 = p_quantifier e in
                     FStar_Pprint.op_Hat_Hat uu____6137 FStar_Pprint.space in
                   FStar_Pprint.soft_surround (Prims.of_int (2))
                     Prims.int_zero uu____6136 binders_doc FStar_Pprint.dot in
                 prefix2 uu____6135 term_doc
             | pats ->
                 let uu____6143 =
                   let uu____6144 =
                     let uu____6145 =
                       let uu____6146 =
                         let uu____6147 = p_quantifier e in
                         FStar_Pprint.op_Hat_Hat uu____6147
                           FStar_Pprint.space in
                       FStar_Pprint.soft_surround (Prims.of_int (2))
                         Prims.int_zero uu____6146 binders_doc
                         FStar_Pprint.dot in
                     let uu____6148 = p_trigger trigger in
                     prefix2 uu____6145 uu____6148 in
                   FStar_Pprint.group uu____6144 in
                 prefix2 uu____6143 term_doc)
        | uu____6149 -> p_simpleTerm ps pb e
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
      let uu____6162 = all_binders_annot t in
      if uu____6162
      then
        let uu____6163 =
          p_typ_top (Binders ((Prims.of_int (4)), Prims.int_zero, true))
            false false t in
        FStar_Pprint.op_Hat_Hat s uu____6163
      else
        (let uu____6165 =
           let uu____6166 =
             let uu____6167 =
               p_typ_top (Arrows ((Prims.of_int (2)), (Prims.of_int (2))))
                 false false t in
             FStar_Pprint.op_Hat_Hat s uu____6167 in
           FStar_Pprint.op_Hat_Hat FStar_Pprint.colon uu____6166 in
         FStar_Pprint.group uu____6165)
and (collapse_pats :
  (FStar_Pprint.document * FStar_Pprint.document) Prims.list ->
    FStar_Pprint.document Prims.list)
  =
  fun pats ->
    let fold_fun bs x =
      let uu____6220 = x in
      match uu____6220 with
      | (b1, t1) ->
          (match bs with
           | [] -> [([b1], t1)]
           | hd::tl ->
               let uu____6285 = hd in
               (match uu____6285 with
                | (b2s, t2) ->
                    if t1 = t2
                    then ((FStar_List.append b2s [b1]), t1) :: tl
                    else ([b1], t1) :: hd :: tl)) in
    let p_collapsed_binder cb =
      let uu____6355 = cb in
      match uu____6355 with
      | (bs, typ) ->
          (match bs with
           | [] -> failwith "Impossible"
           | b::[] -> cat_with_colon b typ
           | hd::tl ->
               let uu____6373 =
                 FStar_List.fold_left
                   (fun x ->
                      fun y ->
                        let uu____6379 =
                          FStar_Pprint.op_Hat_Hat FStar_Pprint.space y in
                        FStar_Pprint.op_Hat_Hat x uu____6379) hd tl in
               cat_with_colon uu____6373 typ) in
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
                 FStar_Parser_AST.brange = uu____6458;
                 FStar_Parser_AST.blevel = uu____6459;
                 FStar_Parser_AST.aqual = uu____6460;_},
               phi)) when
               let uu____6468 = FStar_Ident.string_of_id lid in
               let uu____6469 = FStar_Ident.string_of_id lid' in
               uu____6468 = uu____6469 ->
               let uu____6470 =
                 let uu____6475 = p_ident lid in
                 p_refinement' aqual uu____6475 t1 phi in
               FStar_Pervasives_Native.Some uu____6470
           | (FStar_Parser_AST.PatVar (lid, aqual), uu____6482) ->
               let uu____6487 =
                 let uu____6492 =
                   let uu____6493 = FStar_Pprint.optional p_aqual aqual in
                   let uu____6494 = p_ident lid in
                   FStar_Pprint.op_Hat_Hat uu____6493 uu____6494 in
                 let uu____6495 = p_tmEqNoRefinement t in
                 (uu____6492, uu____6495) in
               FStar_Pervasives_Native.Some uu____6487
           | uu____6500 -> FStar_Pervasives_Native.None)
      | uu____6509 -> FStar_Pervasives_Native.None in
    let all_unbound p =
      match p.FStar_Parser_AST.pat with
      | FStar_Parser_AST.PatAscribed uu____6520 -> false
      | uu____6531 -> true in
    let uu____6532 = map_if_all all_binders pats in
    match uu____6532 with
    | FStar_Pervasives_Native.Some bs ->
        let uu____6564 = collapse_pats bs in
        (uu____6564, (Binders ((Prims.of_int (4)), Prims.int_zero, true)))
    | FStar_Pervasives_Native.None ->
        let uu____6575 = FStar_List.map p_atomicPattern pats in
        (uu____6575, (Binders ((Prims.of_int (4)), Prims.int_zero, false)))
and (p_quantifier : FStar_Parser_AST.term -> FStar_Pprint.document) =
  fun e ->
    match e.FStar_Parser_AST.tm with
    | FStar_Parser_AST.QForall uu____6581 -> str "forall"
    | FStar_Parser_AST.QExists uu____6600 -> str "exists"
    | uu____6619 ->
        failwith "Imposible : p_quantifier called on a non-quantifier term"
and (p_trigger :
  FStar_Parser_AST.term Prims.list Prims.list -> FStar_Pprint.document) =
  fun uu___12_6620 ->
    match uu___12_6620 with
    | [] -> FStar_Pprint.empty
    | pats ->
        let uu____6632 =
          let uu____6633 =
            let uu____6634 =
              let uu____6635 = str "pattern" in
              let uu____6636 =
                let uu____6637 =
                  let uu____6638 = p_disjunctivePats pats in
                  FStar_Pprint.jump (Prims.of_int (2)) Prims.int_zero
                    uu____6638 in
                FStar_Pprint.op_Hat_Hat uu____6637 FStar_Pprint.rbrace in
              FStar_Pprint.op_Hat_Slash_Hat uu____6635 uu____6636 in
            FStar_Pprint.op_Hat_Hat FStar_Pprint.colon uu____6634 in
          FStar_Pprint.op_Hat_Hat FStar_Pprint.lbrace uu____6633 in
        FStar_Pprint.group uu____6632
and (p_disjunctivePats :
  FStar_Parser_AST.term Prims.list Prims.list -> FStar_Pprint.document) =
  fun pats ->
    let uu____6644 = str "\\/" in
    FStar_Pprint.separate_map uu____6644 p_conjunctivePats pats
and (p_conjunctivePats :
  FStar_Parser_AST.term Prims.list -> FStar_Pprint.document) =
  fun pats ->
    let uu____6650 =
      let uu____6651 = FStar_Pprint.op_Hat_Hat FStar_Pprint.semi break1 in
      FStar_Pprint.separate_map uu____6651 p_appTerm pats in
    FStar_Pprint.group uu____6650
and (p_simpleTerm :
  Prims.bool -> Prims.bool -> FStar_Parser_AST.term -> FStar_Pprint.document)
  =
  fun ps ->
    fun pb ->
      fun e ->
        match e.FStar_Parser_AST.tm with
        | FStar_Parser_AST.Abs (pats, e1) ->
            let uu____6661 = p_term_sep false pb e1 in
            (match uu____6661 with
             | (comm, doc) ->
                 let prefix =
                   let uu____6669 = str "fun" in
                   let uu____6670 =
                     let uu____6671 =
                       FStar_Pprint.separate_map break1 p_atomicPattern pats in
                     FStar_Pprint.op_Hat_Slash_Hat uu____6671
                       FStar_Pprint.rarrow in
                   op_Hat_Slash_Plus_Hat uu____6669 uu____6670 in
                 let uu____6672 =
                   if comm <> FStar_Pprint.empty
                   then
                     let uu____6673 =
                       let uu____6674 =
                         let uu____6675 =
                           FStar_Pprint.op_Hat_Hat FStar_Pprint.hardline doc in
                         FStar_Pprint.op_Hat_Hat comm uu____6675 in
                       FStar_Pprint.op_Hat_Hat FStar_Pprint.hardline
                         uu____6674 in
                     FStar_Pprint.op_Hat_Hat prefix uu____6673
                   else
                     (let uu____6677 = op_Hat_Slash_Plus_Hat prefix doc in
                      FStar_Pprint.group uu____6677) in
                 let uu____6678 = paren_if ps in uu____6678 uu____6672)
        | uu____6683 -> p_tmIff e
and (p_maybeFocusArrow : Prims.bool -> FStar_Pprint.document) =
  fun b -> if b then str "~>" else FStar_Pprint.rarrow
and (p_patternBranch :
  Prims.bool ->
    (FStar_Parser_AST.pattern * FStar_Parser_AST.term
      FStar_Pervasives_Native.option * FStar_Parser_AST.term) ->
      FStar_Pprint.document)
  =
  fun pb ->
    fun uu____6687 ->
      match uu____6687 with
      | (pat, when_opt, e) ->
          let one_pattern_branch p =
            let branch =
              match when_opt with
              | FStar_Pervasives_Native.None ->
                  let uu____6710 =
                    let uu____6711 =
                      let uu____6712 =
                        let uu____6713 = p_tuplePattern p in
                        let uu____6714 =
                          FStar_Pprint.op_Hat_Hat FStar_Pprint.space
                            FStar_Pprint.rarrow in
                        FStar_Pprint.op_Hat_Hat uu____6713 uu____6714 in
                      FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____6712 in
                    FStar_Pprint.op_Hat_Hat FStar_Pprint.bar uu____6711 in
                  FStar_Pprint.group uu____6710
              | FStar_Pervasives_Native.Some f ->
                  let uu____6716 =
                    let uu____6717 =
                      let uu____6718 =
                        let uu____6719 =
                          let uu____6720 =
                            let uu____6721 = p_tuplePattern p in
                            let uu____6722 = str "when" in
                            FStar_Pprint.op_Hat_Slash_Hat uu____6721
                              uu____6722 in
                          FStar_Pprint.group uu____6720 in
                        let uu____6723 =
                          let uu____6724 =
                            let uu____6727 = p_tmFormula f in
                            [uu____6727; FStar_Pprint.rarrow] in
                          FStar_Pprint.flow break1 uu____6724 in
                        FStar_Pprint.op_Hat_Slash_Hat uu____6719 uu____6723 in
                      FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____6718 in
                    FStar_Pprint.op_Hat_Hat FStar_Pprint.bar uu____6717 in
                  FStar_Pprint.hang (Prims.of_int (2)) uu____6716 in
            let uu____6728 = p_term_sep false pb e in
            match uu____6728 with
            | (comm, doc) ->
                if pb
                then
                  (if comm = FStar_Pprint.empty
                   then
                     let uu____6735 = op_Hat_Slash_Plus_Hat branch doc in
                     FStar_Pprint.group uu____6735
                   else
                     (let uu____6737 =
                        let uu____6738 =
                          let uu____6739 =
                            let uu____6740 =
                              let uu____6741 =
                                FStar_Pprint.op_Hat_Hat break1 comm in
                              FStar_Pprint.op_Hat_Hat doc uu____6741 in
                            op_Hat_Slash_Plus_Hat branch uu____6740 in
                          FStar_Pprint.group uu____6739 in
                        let uu____6742 =
                          let uu____6743 =
                            let uu____6744 =
                              inline_comment_or_above comm doc
                                FStar_Pprint.empty in
                            jump2 uu____6744 in
                          FStar_Pprint.op_Hat_Hat branch uu____6743 in
                        FStar_Pprint.ifflat uu____6738 uu____6742 in
                      FStar_Pprint.group uu____6737))
                else
                  if comm <> FStar_Pprint.empty
                  then
                    (let uu____6746 =
                       let uu____6747 =
                         FStar_Pprint.op_Hat_Hat FStar_Pprint.hardline doc in
                       FStar_Pprint.op_Hat_Hat comm uu____6747 in
                     op_Hat_Slash_Plus_Hat branch uu____6746)
                  else op_Hat_Slash_Plus_Hat branch doc in
          (match pat.FStar_Parser_AST.pat with
           | FStar_Parser_AST.PatOr pats ->
               (match FStar_List.rev pats with
                | hd::tl ->
                    let last_pat_branch = one_pattern_branch hd in
                    let uu____6757 =
                      let uu____6758 =
                        let uu____6759 =
                          let uu____6760 =
                            let uu____6761 =
                              let uu____6762 =
                                FStar_Pprint.op_Hat_Hat FStar_Pprint.bar
                                  FStar_Pprint.space in
                              FStar_Pprint.op_Hat_Hat break1 uu____6762 in
                            FStar_Pprint.separate_map uu____6761
                              p_tuplePattern (FStar_List.rev tl) in
                          FStar_Pprint.op_Hat_Slash_Hat uu____6760
                            last_pat_branch in
                        FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____6759 in
                      FStar_Pprint.op_Hat_Hat FStar_Pprint.bar uu____6758 in
                    FStar_Pprint.group uu____6757
                | [] ->
                    failwith "Impossible: disjunctive pattern can't be empty")
           | uu____6763 -> one_pattern_branch pat)
and (p_tmIff : FStar_Parser_AST.term -> FStar_Pprint.document) =
  fun e ->
    match e.FStar_Parser_AST.tm with
    | FStar_Parser_AST.Op (id, e1::e2::[]) when
        let uu____6770 = FStar_Ident.string_of_id id in uu____6770 = "<==>"
        ->
        let uu____6771 = str "<==>" in
        let uu____6772 = p_tmImplies e1 in
        let uu____6773 = p_tmIff e2 in
        infix0 uu____6771 uu____6772 uu____6773
    | uu____6774 -> p_tmImplies e
and (p_tmImplies : FStar_Parser_AST.term -> FStar_Pprint.document) =
  fun e ->
    match e.FStar_Parser_AST.tm with
    | FStar_Parser_AST.Op (id, e1::e2::[]) when
        let uu____6781 = FStar_Ident.string_of_id id in uu____6781 = "==>" ->
        let uu____6782 = str "==>" in
        let uu____6783 =
          p_tmArrow (Arrows ((Prims.of_int (2)), (Prims.of_int (2)))) false
            p_tmFormula e1 in
        let uu____6784 = p_tmImplies e2 in
        infix0 uu____6782 uu____6783 uu____6784
    | uu____6785 ->
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
          let uu____6792 =
            FStar_List.splitAt ((FStar_List.length terms) - Prims.int_one)
              terms in
          match uu____6792 with
          | (terms', last) ->
              let uu____6811 =
                match style with
                | Arrows (n, ln) ->
                    let uu____6838 =
                      let uu____6839 =
                        FStar_Pprint.op_Hat_Hat FStar_Pprint.rarrow break1 in
                      FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____6839 in
                    let uu____6840 =
                      FStar_Pprint.op_Hat_Hat FStar_Pprint.rarrow
                        FStar_Pprint.space in
                    (n, ln, terms', uu____6838, uu____6840)
                | Binders (n, ln, parens) ->
                    let uu____6846 =
                      if parens
                      then FStar_List.map soft_parens_with_nesting terms'
                      else terms' in
                    let uu____6852 =
                      FStar_Pprint.op_Hat_Hat FStar_Pprint.colon
                        FStar_Pprint.space in
                    (n, ln, uu____6846, break1, uu____6852) in
              (match uu____6811 with
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
                    | uu____6872 when uu____6872 = Prims.int_one ->
                        FStar_List.hd terms
                    | uu____6873 ->
                        let uu____6874 =
                          let uu____6875 =
                            let uu____6876 =
                              let uu____6877 =
                                FStar_Pprint.separate sep terms'1 in
                              let uu____6878 =
                                let uu____6879 =
                                  FStar_Pprint.op_Hat_Hat last_op1 last1 in
                                FStar_Pprint.op_Hat_Hat one_line_space
                                  uu____6879 in
                              FStar_Pprint.op_Hat_Hat uu____6877 uu____6878 in
                            FStar_Pprint.op_Hat_Hat fs uu____6876 in
                          let uu____6880 =
                            let uu____6881 =
                              let uu____6882 =
                                let uu____6883 =
                                  let uu____6884 =
                                    FStar_Pprint.separate sep terms'1 in
                                  FStar_Pprint.op_Hat_Hat fs uu____6884 in
                                let uu____6885 =
                                  let uu____6886 =
                                    let uu____6887 =
                                      let uu____6888 =
                                        FStar_Pprint.op_Hat_Hat sep
                                          single_line_arg_indent in
                                      let uu____6889 =
                                        FStar_List.map
                                          (fun x ->
                                             let uu____6895 =
                                               FStar_Pprint.hang
                                                 (Prims.of_int (2)) x in
                                             FStar_Pprint.align uu____6895)
                                          terms'1 in
                                      FStar_Pprint.separate uu____6888
                                        uu____6889 in
                                    FStar_Pprint.op_Hat_Hat
                                      single_line_arg_indent uu____6887 in
                                  jump2 uu____6886 in
                                FStar_Pprint.ifflat uu____6883 uu____6885 in
                              FStar_Pprint.group uu____6882 in
                            let uu____6896 =
                              let uu____6897 =
                                let uu____6898 =
                                  FStar_Pprint.op_Hat_Hat last_op1 last1 in
                                FStar_Pprint.hang last_n uu____6898 in
                              FStar_Pprint.align uu____6897 in
                            FStar_Pprint.prefix n Prims.int_one uu____6881
                              uu____6896 in
                          FStar_Pprint.ifflat uu____6875 uu____6880 in
                        FStar_Pprint.group uu____6874))
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
            | Arrows uu____6910 -> p_tmArrow' p_Tm e
            | Binders uu____6915 -> collapse_binders p_Tm e in
          format_sig style terms false flat_space
and (p_tmArrow' :
  (FStar_Parser_AST.term -> FStar_Pprint.document) ->
    FStar_Parser_AST.term -> FStar_Pprint.document Prims.list)
  =
  fun p_Tm ->
    fun e ->
      match e.FStar_Parser_AST.tm with
      | FStar_Parser_AST.Product (bs, tgt) ->
          let uu____6934 = FStar_List.map (fun b -> p_binder false b) bs in
          let uu____6939 = p_tmArrow' p_Tm tgt in
          FStar_List.append uu____6934 uu____6939
      | uu____6942 -> let uu____6943 = p_Tm e in [uu____6943]
and (collapse_binders :
  (FStar_Parser_AST.term -> FStar_Pprint.document) ->
    FStar_Parser_AST.term -> FStar_Pprint.document Prims.list)
  =
  fun p_Tm ->
    fun e ->
      let rec accumulate_binders p_Tm1 e1 =
        match e1.FStar_Parser_AST.tm with
        | FStar_Parser_AST.Product (bs, tgt) ->
            let uu____6996 = FStar_List.map (fun b -> p_binder' false b) bs in
            let uu____7021 = accumulate_binders p_Tm1 tgt in
            FStar_List.append uu____6996 uu____7021
        | uu____7044 ->
            let uu____7045 =
              let uu____7056 = p_Tm1 e1 in
              (uu____7056, FStar_Pervasives_Native.None, cat_with_colon) in
            [uu____7045] in
      let fold_fun bs x =
        let uu____7154 = x in
        match uu____7154 with
        | (b1, t1, f1) ->
            (match bs with
             | [] -> [([b1], t1, f1)]
             | hd::tl ->
                 let uu____7286 = hd in
                 (match uu____7286 with
                  | (b2s, t2, uu____7315) ->
                      (match (t1, t2) with
                       | (FStar_Pervasives_Native.Some typ1,
                          FStar_Pervasives_Native.Some typ2) ->
                           if typ1 = typ2
                           then ((FStar_List.append b2s [b1]), t1, f1) :: tl
                           else ([b1], t1, f1) :: hd :: tl
                       | uu____7415 -> ([b1], t1, f1) :: bs))) in
      let p_collapsed_binder cb =
        let uu____7472 = cb in
        match uu____7472 with
        | (bs, t, f) ->
            (match t with
             | FStar_Pervasives_Native.None ->
                 (match bs with
                  | b::[] -> b
                  | uu____7501 -> failwith "Impossible")
             | FStar_Pervasives_Native.Some typ ->
                 (match bs with
                  | [] -> failwith "Impossible"
                  | b::[] -> f b typ
                  | hd::tl ->
                      let uu____7510 =
                        FStar_List.fold_left
                          (fun x ->
                             fun y ->
                               let uu____7516 =
                                 FStar_Pprint.op_Hat_Hat FStar_Pprint.space y in
                               FStar_Pprint.op_Hat_Hat x uu____7516) hd tl in
                      f uu____7510 typ)) in
      let binders =
        let uu____7532 = accumulate_binders p_Tm e in
        FStar_List.fold_left fold_fun [] uu____7532 in
      map_rev p_collapsed_binder binders
and (p_tmFormula : FStar_Parser_AST.term -> FStar_Pprint.document) =
  fun e ->
    let conj =
      let uu____7595 =
        let uu____7596 = str "/\\" in
        FStar_Pprint.op_Hat_Hat uu____7596 break1 in
      FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____7595 in
    let disj =
      let uu____7598 =
        let uu____7599 = str "\\/" in
        FStar_Pprint.op_Hat_Hat uu____7599 break1 in
      FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____7598 in
    let formula = p_tmDisjunction e in
    FStar_Pprint.flow_map disj
      (fun d -> FStar_Pprint.flow_map conj (fun x -> FStar_Pprint.group x) d)
      formula
and (p_tmDisjunction :
  FStar_Parser_AST.term -> FStar_Pprint.document Prims.list Prims.list) =
  fun e ->
    match e.FStar_Parser_AST.tm with
    | FStar_Parser_AST.Op (id, e1::e2::[]) when
        let uu____7623 = FStar_Ident.string_of_id id in uu____7623 = "\\/" ->
        let uu____7624 = p_tmDisjunction e1 in
        let uu____7629 = let uu____7634 = p_tmConjunction e2 in [uu____7634] in
        FStar_List.append uu____7624 uu____7629
    | uu____7643 -> let uu____7644 = p_tmConjunction e in [uu____7644]
and (p_tmConjunction :
  FStar_Parser_AST.term -> FStar_Pprint.document Prims.list) =
  fun e ->
    match e.FStar_Parser_AST.tm with
    | FStar_Parser_AST.Op (id, e1::e2::[]) when
        let uu____7659 = FStar_Ident.string_of_id id in uu____7659 = "/\\" ->
        let uu____7660 = p_tmConjunction e1 in
        let uu____7663 = let uu____7666 = p_tmTuple e2 in [uu____7666] in
        FStar_List.append uu____7660 uu____7663
    | uu____7667 -> let uu____7668 = p_tmTuple e in [uu____7668]
and (p_tmTuple : FStar_Parser_AST.term -> FStar_Pprint.document) =
  fun e -> with_comment p_tmTuple' e e.FStar_Parser_AST.range
and (p_tmTuple' : FStar_Parser_AST.term -> FStar_Pprint.document) =
  fun e ->
    match e.FStar_Parser_AST.tm with
    | FStar_Parser_AST.Construct (lid, args) when
        (is_tuple_constructor lid) && (all1_explicit args) ->
        let uu____7685 = FStar_Pprint.op_Hat_Hat FStar_Pprint.comma break1 in
        FStar_Pprint.separate_map uu____7685
          (fun uu____7693 ->
             match uu____7693 with | (e1, uu____7699) -> p_tmEq e1) args
    | uu____7700 -> p_tmEq e
and (paren_if_gt :
  Prims.int -> Prims.int -> FStar_Pprint.document -> FStar_Pprint.document) =
  fun curr ->
    fun mine ->
      fun doc ->
        if mine <= curr
        then doc
        else
          (let uu____7705 =
             let uu____7706 = FStar_Pprint.op_Hat_Hat doc FStar_Pprint.rparen in
             FStar_Pprint.op_Hat_Hat FStar_Pprint.lparen uu____7706 in
           FStar_Pprint.group uu____7705)
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
            (let uu____7724 =
               (let uu____7727 = FStar_Ident.string_of_id op in
                uu____7727 = "==>") ||
                 (let uu____7729 = FStar_Ident.string_of_id op in
                  uu____7729 = "<==>") in
             Prims.op_Negation uu____7724) &&
              (((is_operatorInfix0ad12 op) ||
                  (let uu____7731 = FStar_Ident.string_of_id op in
                   uu____7731 = "="))
                 ||
                 (let uu____7733 = FStar_Ident.string_of_id op in
                  uu____7733 = "|>"))
            ->
            let op1 = FStar_Ident.string_of_id op in
            let uu____7735 = levels op1 in
            (match uu____7735 with
             | (left, mine, right) ->
                 let uu____7745 =
                   let uu____7746 = FStar_All.pipe_left str op1 in
                   let uu____7747 = p_tmEqWith' p_X left e1 in
                   let uu____7748 = p_tmEqWith' p_X right e2 in
                   infix0 uu____7746 uu____7747 uu____7748 in
                 paren_if_gt curr mine uu____7745)
        | FStar_Parser_AST.Op (id, e1::e2::[]) when
            let uu____7754 = FStar_Ident.string_of_id id in uu____7754 = ":="
            ->
            let uu____7755 =
              let uu____7756 = p_tmEqWith p_X e1 in
              let uu____7757 =
                let uu____7758 =
                  let uu____7759 =
                    let uu____7760 = p_tmEqWith p_X e2 in
                    op_Hat_Slash_Plus_Hat FStar_Pprint.equals uu____7760 in
                  FStar_Pprint.op_Hat_Hat FStar_Pprint.colon uu____7759 in
                FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____7758 in
              FStar_Pprint.op_Hat_Hat uu____7756 uu____7757 in
            FStar_Pprint.group uu____7755
        | FStar_Parser_AST.Op (id, e1::[]) when
            let uu____7765 = FStar_Ident.string_of_id id in uu____7765 = "-"
            ->
            let uu____7766 = levels "-" in
            (match uu____7766 with
             | (left, mine, right) ->
                 let uu____7776 = p_tmEqWith' p_X mine e1 in
                 FStar_Pprint.op_Hat_Slash_Hat FStar_Pprint.minus uu____7776)
        | uu____7777 -> p_tmNoEqWith p_X e
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
              (lid, (e1, uu____7821)::(e2, uu____7823)::[]) when
              (FStar_Ident.lid_equals lid FStar_Parser_Const.cons_lid) &&
                (let uu____7843 = is_list e in Prims.op_Negation uu____7843)
              ->
              let op = "::" in
              let uu____7845 = levels op in
              (match uu____7845 with
               | (left, mine, right) ->
                   let uu____7855 =
                     let uu____7856 = str op in
                     let uu____7857 = p_tmNoEqWith' false p_X left e1 in
                     let uu____7858 = p_tmNoEqWith' false p_X right e2 in
                     infix0 uu____7856 uu____7857 uu____7858 in
                   paren_if_gt curr mine uu____7855)
          | FStar_Parser_AST.Sum (binders, res) ->
              let op = "&" in
              let uu____7874 = levels op in
              (match uu____7874 with
               | (left, mine, right) ->
                   let p_dsumfst bt =
                     match bt with
                     | FStar_Util.Inl b ->
                         let uu____7899 = p_binder false b in
                         let uu____7900 =
                           let uu____7901 =
                             let uu____7902 = str op in
                             FStar_Pprint.op_Hat_Hat uu____7902 break1 in
                           FStar_Pprint.op_Hat_Hat FStar_Pprint.space
                             uu____7901 in
                         FStar_Pprint.op_Hat_Hat uu____7899 uu____7900
                     | FStar_Util.Inr t ->
                         let uu____7904 = p_tmNoEqWith' false p_X left t in
                         let uu____7905 =
                           let uu____7906 =
                             let uu____7907 = str op in
                             FStar_Pprint.op_Hat_Hat uu____7907 break1 in
                           FStar_Pprint.op_Hat_Hat FStar_Pprint.space
                             uu____7906 in
                         FStar_Pprint.op_Hat_Hat uu____7904 uu____7905 in
                   let uu____7908 =
                     let uu____7909 =
                       FStar_Pprint.concat_map p_dsumfst binders in
                     let uu____7914 = p_tmNoEqWith' false p_X right res in
                     FStar_Pprint.op_Hat_Hat uu____7909 uu____7914 in
                   paren_if_gt curr mine uu____7908)
          | FStar_Parser_AST.Op (id, e1::e2::[]) when
              (let uu____7922 = FStar_Ident.string_of_id id in
               uu____7922 = "*") && (FStar_ST.op_Bang unfold_tuples)
              ->
              let op = "*" in
              let uu____7930 = levels op in
              (match uu____7930 with
               | (left, mine, right) ->
                   if inside_tuple
                   then
                     let uu____7940 = str op in
                     let uu____7941 = p_tmNoEqWith' true p_X left e1 in
                     let uu____7942 = p_tmNoEqWith' true p_X right e2 in
                     infix0 uu____7940 uu____7941 uu____7942
                   else
                     (let uu____7944 =
                        let uu____7945 = str op in
                        let uu____7946 = p_tmNoEqWith' true p_X left e1 in
                        let uu____7947 = p_tmNoEqWith' true p_X right e2 in
                        infix0 uu____7945 uu____7946 uu____7947 in
                      paren_if_gt curr mine uu____7944))
          | FStar_Parser_AST.Op (op, e1::e2::[]) when is_operatorInfix34 op
              ->
              let op1 = FStar_Ident.string_of_id op in
              let uu____7954 = levels op1 in
              (match uu____7954 with
               | (left, mine, right) ->
                   let uu____7964 =
                     let uu____7965 = str op1 in
                     let uu____7966 = p_tmNoEqWith' false p_X left e1 in
                     let uu____7967 = p_tmNoEqWith' false p_X right e2 in
                     infix0 uu____7965 uu____7966 uu____7967 in
                   paren_if_gt curr mine uu____7964)
          | FStar_Parser_AST.Record (with_opt, record_fields) ->
              let uu____7986 =
                let uu____7987 =
                  default_or_map FStar_Pprint.empty p_with_clause with_opt in
                let uu____7988 =
                  let uu____7989 =
                    FStar_Pprint.op_Hat_Hat FStar_Pprint.semi break1 in
                  separate_map_last uu____7989 p_simpleDef record_fields in
                FStar_Pprint.op_Hat_Hat uu____7987 uu____7988 in
              braces_with_nesting uu____7986
          | FStar_Parser_AST.Op (id, e1::[]) when
              let uu____7998 = FStar_Ident.string_of_id id in
              uu____7998 = "~" ->
              let uu____7999 =
                let uu____8000 = str "~" in
                let uu____8001 = p_atomicTerm e1 in
                FStar_Pprint.op_Hat_Hat uu____8000 uu____8001 in
              FStar_Pprint.group uu____7999
          | FStar_Parser_AST.Paren p when inside_tuple ->
              (match p.FStar_Parser_AST.tm with
               | FStar_Parser_AST.Op (id, e1::e2::[]) when
                   let uu____8008 = FStar_Ident.string_of_id id in
                   uu____8008 = "*" ->
                   let op = "*" in
                   let uu____8010 = levels op in
                   (match uu____8010 with
                    | (left, mine, right) ->
                        let uu____8020 =
                          let uu____8021 = str op in
                          let uu____8022 = p_tmNoEqWith' true p_X left e1 in
                          let uu____8023 = p_tmNoEqWith' true p_X right e2 in
                          infix0 uu____8021 uu____8022 uu____8023 in
                        paren_if_gt curr mine uu____8020)
               | uu____8024 -> p_X e)
          | uu____8025 -> p_X e
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
        let uu____8032 =
          let uu____8033 = p_lident lid in
          let uu____8034 =
            let uu____8035 = p_appTerm e1 in
            FStar_Pprint.op_Hat_Slash_Hat FStar_Pprint.colon uu____8035 in
          FStar_Pprint.op_Hat_Slash_Hat uu____8033 uu____8034 in
        FStar_Pprint.group uu____8032
    | FStar_Parser_AST.Refine (b, phi) -> p_refinedBinder b phi
    | uu____8038 -> p_appTerm e
and (p_with_clause : FStar_Parser_AST.term -> FStar_Pprint.document) =
  fun e ->
    let uu____8040 = p_appTerm e in
    let uu____8041 =
      let uu____8042 =
        let uu____8043 = str "with" in
        FStar_Pprint.op_Hat_Hat uu____8043 break1 in
      FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____8042 in
    FStar_Pprint.op_Hat_Hat uu____8040 uu____8041
and (p_refinedBinder :
  FStar_Parser_AST.binder -> FStar_Parser_AST.term -> FStar_Pprint.document)
  =
  fun b ->
    fun phi ->
      match b.FStar_Parser_AST.b with
      | FStar_Parser_AST.Annotated (lid, t) ->
          let uu____8048 = p_lident lid in
          p_refinement b.FStar_Parser_AST.aqual uu____8048 t phi
      | FStar_Parser_AST.TAnnotated uu____8049 ->
          failwith "Is this still used ?"
      | FStar_Parser_AST.Variable uu____8054 ->
          let uu____8055 =
            let uu____8056 = FStar_Parser_AST.binder_to_string b in
            FStar_Util.format1
              "Imposible : a refined binder ought to be annotated %s"
              uu____8056 in
          failwith uu____8055
      | FStar_Parser_AST.TVariable uu____8057 ->
          let uu____8058 =
            let uu____8059 = FStar_Parser_AST.binder_to_string b in
            FStar_Util.format1
              "Imposible : a refined binder ought to be annotated %s"
              uu____8059 in
          failwith uu____8058
      | FStar_Parser_AST.NoName uu____8060 ->
          let uu____8061 =
            let uu____8062 = FStar_Parser_AST.binder_to_string b in
            FStar_Util.format1
              "Imposible : a refined binder ought to be annotated %s"
              uu____8062 in
          failwith uu____8061
and (p_simpleDef :
  Prims.bool ->
    (FStar_Ident.lid * FStar_Parser_AST.term) -> FStar_Pprint.document)
  =
  fun ps ->
    fun uu____8064 ->
      match uu____8064 with
      | (lid, e) ->
          let uu____8071 =
            let uu____8072 = p_qlident lid in
            let uu____8073 =
              let uu____8074 = p_noSeqTermAndComment ps false e in
              FStar_Pprint.op_Hat_Slash_Hat FStar_Pprint.equals uu____8074 in
            FStar_Pprint.op_Hat_Slash_Hat uu____8072 uu____8073 in
          FStar_Pprint.group uu____8071
and (p_appTerm : FStar_Parser_AST.term -> FStar_Pprint.document) =
  fun e ->
    match e.FStar_Parser_AST.tm with
    | FStar_Parser_AST.App uu____8076 when is_general_application e ->
        let uu____8083 = head_and_args e in
        (match uu____8083 with
         | (head, args) ->
             (match args with
              | e1::e2::[] when
                  (FStar_Pervasives_Native.snd e1) = FStar_Parser_AST.Infix
                  ->
                  let uu____8130 = p_argTerm e1 in
                  let uu____8131 =
                    let uu____8132 =
                      let uu____8133 =
                        let uu____8134 = str "`" in
                        let uu____8135 =
                          let uu____8136 = p_indexingTerm head in
                          let uu____8137 = str "`" in
                          FStar_Pprint.op_Hat_Hat uu____8136 uu____8137 in
                        FStar_Pprint.op_Hat_Hat uu____8134 uu____8135 in
                      FStar_Pprint.group uu____8133 in
                    let uu____8138 = p_argTerm e2 in
                    FStar_Pprint.op_Hat_Slash_Hat uu____8132 uu____8138 in
                  FStar_Pprint.op_Hat_Slash_Hat uu____8130 uu____8131
              | uu____8139 ->
                  let uu____8146 =
                    let uu____8157 = FStar_ST.op_Bang should_print_fs_typ_app in
                    if uu____8157
                    then
                      let uu____8174 =
                        FStar_Util.take
                          (fun uu____8198 ->
                             match uu____8198 with
                             | (uu____8203, aq) ->
                                 aq = FStar_Parser_AST.FsTypApp) args in
                      match uu____8174 with
                      | (fs_typ_args, args1) ->
                          let uu____8241 =
                            let uu____8242 = p_indexingTerm head in
                            let uu____8243 =
                              let uu____8244 =
                                FStar_Pprint.op_Hat_Hat FStar_Pprint.comma
                                  break1 in
                              soft_surround_map_or_flow (Prims.of_int (2))
                                Prims.int_zero FStar_Pprint.empty
                                FStar_Pprint.langle uu____8244
                                FStar_Pprint.rangle p_fsTypArg fs_typ_args in
                            FStar_Pprint.op_Hat_Hat uu____8242 uu____8243 in
                          (uu____8241, args1)
                    else
                      (let uu____8256 = p_indexingTerm head in
                       (uu____8256, args)) in
                  (match uu____8146 with
                   | (head_doc, args1) ->
                       let uu____8277 =
                         let uu____8278 =
                           FStar_Pprint.op_Hat_Hat head_doc
                             FStar_Pprint.space in
                         soft_surround_map_or_flow (Prims.of_int (2))
                           Prims.int_zero head_doc uu____8278 break1
                           FStar_Pprint.empty p_argTerm args1 in
                       FStar_Pprint.group uu____8277)))
    | FStar_Parser_AST.Construct (lid, args) when
        (is_general_construction e) &&
          (let uu____8298 =
             (is_dtuple_constructor lid) && (all1_explicit args) in
           Prims.op_Negation uu____8298)
        ->
        (match args with
         | [] -> p_quident lid
         | arg::[] ->
             let uu____8316 =
               let uu____8317 = p_quident lid in
               let uu____8318 = p_argTerm arg in
               FStar_Pprint.op_Hat_Slash_Hat uu____8317 uu____8318 in
             FStar_Pprint.group uu____8316
         | hd::tl ->
             let uu____8335 =
               let uu____8336 =
                 let uu____8337 =
                   let uu____8338 = p_quident lid in
                   let uu____8339 = p_argTerm hd in
                   prefix2 uu____8338 uu____8339 in
                 FStar_Pprint.group uu____8337 in
               let uu____8340 =
                 let uu____8341 =
                   FStar_Pprint.separate_map break1 p_argTerm tl in
                 jump2 uu____8341 in
               FStar_Pprint.op_Hat_Hat uu____8336 uu____8340 in
             FStar_Pprint.group uu____8335)
    | uu____8346 -> p_indexingTerm e
and (p_argTerm :
  (FStar_Parser_AST.term * FStar_Parser_AST.imp) -> FStar_Pprint.document) =
  fun arg_imp ->
    match arg_imp with
    | (u, FStar_Parser_AST.UnivApp) -> p_universe u
    | (e, FStar_Parser_AST.FsTypApp) ->
        (FStar_Errors.log_issue e.FStar_Parser_AST.range
           (FStar_Errors.Warning_UnexpectedFsTypApp,
             "Unexpected FsTypApp, output might not be formatted correctly.");
         (let uu____8355 = p_indexingTerm e in
          FStar_Pprint.surround (Prims.of_int (2)) Prims.int_one
            FStar_Pprint.langle uu____8355 FStar_Pprint.rangle))
    | (e, FStar_Parser_AST.Hash) ->
        let uu____8357 = str "#" in
        let uu____8358 = p_indexingTerm e in
        FStar_Pprint.op_Hat_Hat uu____8357 uu____8358
    | (e, FStar_Parser_AST.HashBrace t) ->
        let uu____8361 = str "#[" in
        let uu____8362 =
          let uu____8363 = p_indexingTerm t in
          let uu____8364 =
            let uu____8365 = str "]" in
            let uu____8366 = p_indexingTerm e in
            FStar_Pprint.op_Hat_Hat uu____8365 uu____8366 in
          FStar_Pprint.op_Hat_Hat uu____8363 uu____8364 in
        FStar_Pprint.op_Hat_Hat uu____8361 uu____8362
    | (e, FStar_Parser_AST.Infix) -> p_indexingTerm e
    | (e, FStar_Parser_AST.Nothing) -> p_indexingTerm e
and (p_fsTypArg :
  (FStar_Parser_AST.term * FStar_Parser_AST.imp) -> FStar_Pprint.document) =
  fun uu____8369 ->
    match uu____8369 with | (e, uu____8375) -> p_indexingTerm e
and (p_indexingTerm_aux :
  (FStar_Parser_AST.term -> FStar_Pprint.document) ->
    FStar_Parser_AST.term -> FStar_Pprint.document)
  =
  fun exit ->
    fun e ->
      match e.FStar_Parser_AST.tm with
      | FStar_Parser_AST.Op (id, e1::e2::[]) when
          let uu____8385 = FStar_Ident.string_of_id id in uu____8385 = ".()"
          ->
          let uu____8386 =
            let uu____8387 = p_indexingTerm_aux p_atomicTermNotQUident e1 in
            let uu____8388 =
              let uu____8389 =
                let uu____8390 = p_term false false e2 in
                soft_parens_with_nesting uu____8390 in
              FStar_Pprint.op_Hat_Hat FStar_Pprint.dot uu____8389 in
            FStar_Pprint.op_Hat_Hat uu____8387 uu____8388 in
          FStar_Pprint.group uu____8386
      | FStar_Parser_AST.Op (id, e1::e2::[]) when
          let uu____8396 = FStar_Ident.string_of_id id in uu____8396 = ".[]"
          ->
          let uu____8397 =
            let uu____8398 = p_indexingTerm_aux p_atomicTermNotQUident e1 in
            let uu____8399 =
              let uu____8400 =
                let uu____8401 = p_term false false e2 in
                soft_brackets_with_nesting uu____8401 in
              FStar_Pprint.op_Hat_Hat FStar_Pprint.dot uu____8400 in
            FStar_Pprint.op_Hat_Hat uu____8398 uu____8399 in
          FStar_Pprint.group uu____8397
      | uu____8402 -> exit e
and (p_indexingTerm : FStar_Parser_AST.term -> FStar_Pprint.document) =
  fun e -> p_indexingTerm_aux p_atomicTerm e
and (p_atomicTerm : FStar_Parser_AST.term -> FStar_Pprint.document) =
  fun e ->
    match e.FStar_Parser_AST.tm with
    | FStar_Parser_AST.LetOpen (lid, e1) ->
        let uu____8407 = p_quident lid in
        let uu____8408 =
          let uu____8409 =
            let uu____8410 = p_term false false e1 in
            soft_parens_with_nesting uu____8410 in
          FStar_Pprint.op_Hat_Hat FStar_Pprint.dot uu____8409 in
        FStar_Pprint.op_Hat_Hat uu____8407 uu____8408
    | FStar_Parser_AST.Name lid -> p_quident lid
    | FStar_Parser_AST.Op (op, e1::[]) when is_general_prefix_op op ->
        let uu____8416 =
          let uu____8417 = FStar_Ident.string_of_id op in str uu____8417 in
        let uu____8418 = p_atomicTerm e1 in
        FStar_Pprint.op_Hat_Hat uu____8416 uu____8418
    | uu____8419 -> p_atomicTermNotQUident e
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
         | uu____8426 -> p_constant c)
    | FStar_Parser_AST.Name lid when
        FStar_Ident.lid_equals lid FStar_Parser_Const.true_lid -> str "True"
    | FStar_Parser_AST.Name lid when
        FStar_Ident.lid_equals lid FStar_Parser_Const.false_lid ->
        str "False"
    | FStar_Parser_AST.Op (op, e1::[]) when is_general_prefix_op op ->
        let uu____8433 =
          let uu____8434 = FStar_Ident.string_of_id op in str uu____8434 in
        let uu____8435 = p_atomicTermNotQUident e1 in
        FStar_Pprint.op_Hat_Hat uu____8433 uu____8435
    | FStar_Parser_AST.Op (op, []) ->
        let uu____8439 =
          let uu____8440 =
            let uu____8441 =
              let uu____8442 = FStar_Ident.string_of_id op in str uu____8442 in
            let uu____8443 =
              FStar_Pprint.op_Hat_Hat FStar_Pprint.space FStar_Pprint.rparen in
            FStar_Pprint.op_Hat_Hat uu____8441 uu____8443 in
          FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____8440 in
        FStar_Pprint.op_Hat_Hat FStar_Pprint.lparen uu____8439
    | FStar_Parser_AST.Construct (lid, args) when
        (is_dtuple_constructor lid) && (all1_explicit args) ->
        let uu____8458 =
          FStar_Pprint.op_Hat_Hat FStar_Pprint.lparen FStar_Pprint.bar in
        let uu____8459 =
          let uu____8460 = FStar_Pprint.op_Hat_Hat FStar_Pprint.comma break1 in
          FStar_Pprint.separate_map uu____8460
            (fun uu____8468 ->
               match uu____8468 with | (e1, uu____8474) -> p_tmEq e1) args in
        let uu____8475 =
          FStar_Pprint.op_Hat_Hat FStar_Pprint.bar FStar_Pprint.rparen in
        FStar_Pprint.surround (Prims.of_int (2)) Prims.int_one uu____8458
          uu____8459 uu____8475
    | FStar_Parser_AST.Project (e1, lid) ->
        let uu____8478 =
          let uu____8479 = p_atomicTermNotQUident e1 in
          let uu____8480 =
            let uu____8481 = p_qlident lid in
            FStar_Pprint.op_Hat_Hat FStar_Pprint.dot uu____8481 in
          FStar_Pprint.prefix (Prims.of_int (2)) Prims.int_zero uu____8479
            uu____8480 in
        FStar_Pprint.group uu____8478
    | uu____8482 -> p_projectionLHS e
and (p_projectionLHS : FStar_Parser_AST.term -> FStar_Pprint.document) =
  fun e ->
    match e.FStar_Parser_AST.tm with
    | FStar_Parser_AST.Var lid -> p_qlident lid
    | FStar_Parser_AST.Projector (constr_lid, field_lid) ->
        let uu____8487 = p_quident constr_lid in
        let uu____8488 =
          let uu____8489 =
            let uu____8490 = p_lident field_lid in
            FStar_Pprint.op_Hat_Hat FStar_Pprint.dot uu____8490 in
          FStar_Pprint.op_Hat_Hat FStar_Pprint.qmark uu____8489 in
        FStar_Pprint.op_Hat_Hat uu____8487 uu____8488
    | FStar_Parser_AST.Discrim constr_lid ->
        let uu____8492 = p_quident constr_lid in
        FStar_Pprint.op_Hat_Hat uu____8492 FStar_Pprint.qmark
    | FStar_Parser_AST.Paren e1 ->
        let uu____8494 = p_term_sep false false e1 in
        (match uu____8494 with
         | (comm, t) ->
             let doc = soft_parens_with_nesting t in
             if comm = FStar_Pprint.empty
             then doc
             else
               (let uu____8503 =
                  FStar_Pprint.op_Hat_Hat FStar_Pprint.hardline doc in
                FStar_Pprint.op_Hat_Hat comm uu____8503))
    | uu____8504 when is_array e ->
        let es = extract_from_list e in
        let uu____8508 =
          FStar_Pprint.op_Hat_Hat FStar_Pprint.lbracket FStar_Pprint.bar in
        let uu____8509 =
          let uu____8510 = FStar_Pprint.op_Hat_Hat FStar_Pprint.semi break1 in
          separate_map_or_flow_last uu____8510
            (fun ps -> p_noSeqTermAndComment ps false) es in
        let uu____8513 =
          FStar_Pprint.op_Hat_Hat FStar_Pprint.bar FStar_Pprint.rbracket in
        FStar_Pprint.surround (Prims.of_int (2)) Prims.int_zero uu____8508
          uu____8509 uu____8513
    | uu____8514 when is_list e ->
        let uu____8515 =
          let uu____8516 = FStar_Pprint.op_Hat_Hat FStar_Pprint.semi break1 in
          let uu____8517 = extract_from_list e in
          separate_map_or_flow_last uu____8516
            (fun ps -> p_noSeqTermAndComment ps false) uu____8517 in
        FStar_Pprint.surround (Prims.of_int (2)) Prims.int_zero
          FStar_Pprint.lbracket uu____8515 FStar_Pprint.rbracket
    | uu____8522 when is_lex_list e ->
        let uu____8523 =
          FStar_Pprint.op_Hat_Hat FStar_Pprint.percent FStar_Pprint.lbracket in
        let uu____8524 =
          let uu____8525 = FStar_Pprint.op_Hat_Hat FStar_Pprint.semi break1 in
          let uu____8526 = extract_from_list e in
          separate_map_or_flow_last uu____8525
            (fun ps -> p_noSeqTermAndComment ps false) uu____8526 in
        FStar_Pprint.surround (Prims.of_int (2)) Prims.int_one uu____8523
          uu____8524 FStar_Pprint.rbracket
    | uu____8531 when is_ref_set e ->
        let es = extract_from_ref_set e in
        let uu____8535 =
          FStar_Pprint.op_Hat_Hat FStar_Pprint.bang FStar_Pprint.lbrace in
        let uu____8536 =
          let uu____8537 = FStar_Pprint.op_Hat_Hat FStar_Pprint.comma break1 in
          separate_map_or_flow uu____8537 p_appTerm es in
        FStar_Pprint.surround (Prims.of_int (2)) Prims.int_zero uu____8535
          uu____8536 FStar_Pprint.rbrace
    | FStar_Parser_AST.Labeled (e1, s, b) ->
        let uu____8541 = str (Prims.op_Hat "(*" (Prims.op_Hat s "*)")) in
        let uu____8542 = p_term false false e1 in
        FStar_Pprint.op_Hat_Slash_Hat uu____8541 uu____8542
    | FStar_Parser_AST.Op (op, args) when
        let uu____8549 = handleable_op op args in
        Prims.op_Negation uu____8549 ->
        let uu____8550 =
          let uu____8551 =
            let uu____8552 = FStar_Ident.string_of_id op in
            let uu____8553 =
              let uu____8554 =
                let uu____8555 =
                  FStar_Util.string_of_int (FStar_List.length args) in
                Prims.op_Hat uu____8555
                  " arguments couldn't be handled by the pretty printer" in
              Prims.op_Hat " with " uu____8554 in
            Prims.op_Hat uu____8552 uu____8553 in
          Prims.op_Hat "Operation " uu____8551 in
        failwith uu____8550
    | FStar_Parser_AST.Uvar id ->
        failwith "Unexpected universe variable out of universe context"
    | FStar_Parser_AST.Wild ->
        let uu____8557 = p_term false false e in
        soft_parens_with_nesting uu____8557
    | FStar_Parser_AST.Const uu____8558 ->
        let uu____8559 = p_term false false e in
        soft_parens_with_nesting uu____8559
    | FStar_Parser_AST.Op uu____8560 ->
        let uu____8567 = p_term false false e in
        soft_parens_with_nesting uu____8567
    | FStar_Parser_AST.Tvar uu____8568 ->
        let uu____8569 = p_term false false e in
        soft_parens_with_nesting uu____8569
    | FStar_Parser_AST.Var uu____8570 ->
        let uu____8571 = p_term false false e in
        soft_parens_with_nesting uu____8571
    | FStar_Parser_AST.Name uu____8572 ->
        let uu____8573 = p_term false false e in
        soft_parens_with_nesting uu____8573
    | FStar_Parser_AST.Construct uu____8574 ->
        let uu____8585 = p_term false false e in
        soft_parens_with_nesting uu____8585
    | FStar_Parser_AST.Abs uu____8586 ->
        let uu____8593 = p_term false false e in
        soft_parens_with_nesting uu____8593
    | FStar_Parser_AST.App uu____8594 ->
        let uu____8601 = p_term false false e in
        soft_parens_with_nesting uu____8601
    | FStar_Parser_AST.Let uu____8602 ->
        let uu____8623 = p_term false false e in
        soft_parens_with_nesting uu____8623
    | FStar_Parser_AST.LetOpen uu____8624 ->
        let uu____8629 = p_term false false e in
        soft_parens_with_nesting uu____8629
    | FStar_Parser_AST.Seq uu____8630 ->
        let uu____8635 = p_term false false e in
        soft_parens_with_nesting uu____8635
    | FStar_Parser_AST.Bind uu____8636 ->
        let uu____8643 = p_term false false e in
        soft_parens_with_nesting uu____8643
    | FStar_Parser_AST.If uu____8644 ->
        let uu____8651 = p_term false false e in
        soft_parens_with_nesting uu____8651
    | FStar_Parser_AST.Match uu____8652 ->
        let uu____8667 = p_term false false e in
        soft_parens_with_nesting uu____8667
    | FStar_Parser_AST.TryWith uu____8668 ->
        let uu____8683 = p_term false false e in
        soft_parens_with_nesting uu____8683
    | FStar_Parser_AST.Ascribed uu____8684 ->
        let uu____8693 = p_term false false e in
        soft_parens_with_nesting uu____8693
    | FStar_Parser_AST.Record uu____8694 ->
        let uu____8707 = p_term false false e in
        soft_parens_with_nesting uu____8707
    | FStar_Parser_AST.Project uu____8708 ->
        let uu____8713 = p_term false false e in
        soft_parens_with_nesting uu____8713
    | FStar_Parser_AST.Product uu____8714 ->
        let uu____8721 = p_term false false e in
        soft_parens_with_nesting uu____8721
    | FStar_Parser_AST.Sum uu____8722 ->
        let uu____8733 = p_term false false e in
        soft_parens_with_nesting uu____8733
    | FStar_Parser_AST.QForall uu____8734 ->
        let uu____8753 = p_term false false e in
        soft_parens_with_nesting uu____8753
    | FStar_Parser_AST.QExists uu____8754 ->
        let uu____8773 = p_term false false e in
        soft_parens_with_nesting uu____8773
    | FStar_Parser_AST.Refine uu____8774 ->
        let uu____8779 = p_term false false e in
        soft_parens_with_nesting uu____8779
    | FStar_Parser_AST.NamedTyp uu____8780 ->
        let uu____8785 = p_term false false e in
        soft_parens_with_nesting uu____8785
    | FStar_Parser_AST.Requires uu____8786 ->
        let uu____8793 = p_term false false e in
        soft_parens_with_nesting uu____8793
    | FStar_Parser_AST.Ensures uu____8794 ->
        let uu____8801 = p_term false false e in
        soft_parens_with_nesting uu____8801
    | FStar_Parser_AST.Attributes uu____8802 ->
        let uu____8805 = p_term false false e in
        soft_parens_with_nesting uu____8805
    | FStar_Parser_AST.Quote uu____8806 ->
        let uu____8811 = p_term false false e in
        soft_parens_with_nesting uu____8811
    | FStar_Parser_AST.VQuote uu____8812 ->
        let uu____8813 = p_term false false e in
        soft_parens_with_nesting uu____8813
    | FStar_Parser_AST.Antiquote uu____8814 ->
        let uu____8815 = p_term false false e in
        soft_parens_with_nesting uu____8815
    | FStar_Parser_AST.CalcProof uu____8816 ->
        let uu____8825 = p_term false false e in
        soft_parens_with_nesting uu____8825
and (p_constant : FStar_Const.sconst -> FStar_Pprint.document) =
  fun uu___15_8826 ->
    match uu___15_8826 with
    | FStar_Const.Const_effect -> str "Effect"
    | FStar_Const.Const_unit -> str "()"
    | FStar_Const.Const_bool b -> FStar_Pprint.doc_of_bool b
    | FStar_Const.Const_real r -> str (Prims.op_Hat r "R")
    | FStar_Const.Const_float x -> str (FStar_Util.string_of_float x)
    | FStar_Const.Const_char x -> FStar_Pprint.doc_of_char x
    | FStar_Const.Const_string (s, uu____8832) ->
        let uu____8833 = str (FStar_String.escaped s) in
        FStar_Pprint.dquotes uu____8833
    | FStar_Const.Const_bytearray (bytes, uu____8835) ->
        let uu____8840 =
          let uu____8841 = str (FStar_Util.string_of_bytes bytes) in
          FStar_Pprint.dquotes uu____8841 in
        let uu____8842 = str "B" in
        FStar_Pprint.op_Hat_Hat uu____8840 uu____8842
    | FStar_Const.Const_int (repr, sign_width_opt) ->
        let signedness uu___13_8862 =
          match uu___13_8862 with
          | FStar_Const.Unsigned -> str "u"
          | FStar_Const.Signed -> FStar_Pprint.empty in
        let width uu___14_8868 =
          match uu___14_8868 with
          | FStar_Const.Int8 -> str "y"
          | FStar_Const.Int16 -> str "s"
          | FStar_Const.Int32 -> str "l"
          | FStar_Const.Int64 -> str "L" in
        let ending =
          default_or_map FStar_Pprint.empty
            (fun uu____8879 ->
               match uu____8879 with
               | (s, w) ->
                   let uu____8886 = signedness s in
                   let uu____8887 = width w in
                   FStar_Pprint.op_Hat_Hat uu____8886 uu____8887)
            sign_width_opt in
        let uu____8888 = str repr in
        FStar_Pprint.op_Hat_Hat uu____8888 ending
    | FStar_Const.Const_range_of -> str "range_of"
    | FStar_Const.Const_set_range_of -> str "set_range_of"
    | FStar_Const.Const_range r ->
        let uu____8890 = FStar_Range.string_of_range r in str uu____8890
    | FStar_Const.Const_reify -> str "reify"
    | FStar_Const.Const_reflect lid ->
        let uu____8892 = p_quident lid in
        let uu____8893 =
          let uu____8894 =
            let uu____8895 = str "reflect" in
            FStar_Pprint.op_Hat_Hat FStar_Pprint.dot uu____8895 in
          FStar_Pprint.op_Hat_Hat FStar_Pprint.qmark uu____8894 in
        FStar_Pprint.op_Hat_Hat uu____8892 uu____8893
and (p_universe : FStar_Parser_AST.term -> FStar_Pprint.document) =
  fun u ->
    let uu____8897 = str "u#" in
    let uu____8898 = p_atomicUniverse u in
    FStar_Pprint.op_Hat_Hat uu____8897 uu____8898
and (p_universeFrom : FStar_Parser_AST.term -> FStar_Pprint.document) =
  fun u ->
    match u.FStar_Parser_AST.tm with
    | FStar_Parser_AST.Op (id, u1::u2::[]) when
        let uu____8905 = FStar_Ident.string_of_id id in uu____8905 = "+" ->
        let uu____8906 =
          let uu____8907 = p_universeFrom u1 in
          let uu____8908 =
            let uu____8909 = p_universeFrom u2 in
            FStar_Pprint.op_Hat_Slash_Hat FStar_Pprint.plus uu____8909 in
          FStar_Pprint.op_Hat_Slash_Hat uu____8907 uu____8908 in
        FStar_Pprint.group uu____8906
    | FStar_Parser_AST.App uu____8910 ->
        let uu____8917 = head_and_args u in
        (match uu____8917 with
         | (head, args) ->
             (match head.FStar_Parser_AST.tm with
              | FStar_Parser_AST.Var maybe_max_lid when
                  FStar_Ident.lid_equals maybe_max_lid
                    FStar_Parser_Const.max_lid
                  ->
                  let uu____8943 =
                    let uu____8944 = p_qlident FStar_Parser_Const.max_lid in
                    let uu____8945 =
                      FStar_Pprint.separate_map FStar_Pprint.space
                        (fun uu____8953 ->
                           match uu____8953 with
                           | (u1, uu____8959) -> p_atomicUniverse u1) args in
                    op_Hat_Slash_Plus_Hat uu____8944 uu____8945 in
                  FStar_Pprint.group uu____8943
              | uu____8960 ->
                  let uu____8961 =
                    let uu____8962 = FStar_Parser_AST.term_to_string u in
                    FStar_Util.format1 "Invalid term in universe context %s"
                      uu____8962 in
                  failwith uu____8961))
    | uu____8963 -> p_atomicUniverse u
and (p_atomicUniverse : FStar_Parser_AST.term -> FStar_Pprint.document) =
  fun u ->
    match u.FStar_Parser_AST.tm with
    | FStar_Parser_AST.Wild -> FStar_Pprint.underscore
    | FStar_Parser_AST.Const (FStar_Const.Const_int (r, sw)) ->
        p_constant (FStar_Const.Const_int (r, sw))
    | FStar_Parser_AST.Uvar id ->
        let uu____8986 = FStar_Ident.string_of_id id in str uu____8986
    | FStar_Parser_AST.Paren u1 ->
        let uu____8988 = p_universeFrom u1 in
        soft_parens_with_nesting uu____8988
    | FStar_Parser_AST.App uu____8989 ->
        let uu____8996 = p_universeFrom u in
        soft_parens_with_nesting uu____8996
    | FStar_Parser_AST.Op (id, uu____8998::uu____8999::[]) when
        let uu____9002 = FStar_Ident.string_of_id id in uu____9002 = "+" ->
        let uu____9003 = p_universeFrom u in
        soft_parens_with_nesting uu____9003
    | uu____9004 ->
        let uu____9005 =
          let uu____9006 = FStar_Parser_AST.term_to_string u in
          FStar_Util.format1 "Invalid term in universe context %s" uu____9006 in
        failwith uu____9005
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
       | FStar_Parser_AST.Module (uu____9052, decls) ->
           let uu____9058 =
             FStar_All.pipe_right decls (FStar_List.map decl_to_document) in
           FStar_All.pipe_right uu____9058
             (FStar_Pprint.separate FStar_Pprint.hardline)
       | FStar_Parser_AST.Interface (uu____9067, decls, uu____9069) ->
           let uu____9074 =
             FStar_All.pipe_right decls (FStar_List.map decl_to_document) in
           FStar_All.pipe_right uu____9074
             (FStar_Pprint.separate FStar_Pprint.hardline) in
     FStar_ST.op_Colon_Equals should_print_fs_typ_app false; res)
let (comments_to_document :
  (Prims.string * FStar_Range.range) Prims.list -> FStar_Pprint.document) =
  fun comments ->
    FStar_Pprint.separate_map FStar_Pprint.hardline
      (fun uu____9114 ->
         match uu____9114 with | (comment, range) -> str comment) comments
let (extract_decl_range : FStar_Parser_AST.decl -> decl_meta) =
  fun d ->
    let has_qs =
      match ((d.FStar_Parser_AST.quals), (d.FStar_Parser_AST.d)) with
      | ((FStar_Parser_AST.Assumption)::[], FStar_Parser_AST.Assume
         (id, uu____9130)) -> false
      | ([], uu____9133) -> false
      | uu____9136 -> true in
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
        | FStar_Parser_AST.Module (uu____9180, decls) -> decls
        | FStar_Parser_AST.Interface (uu____9186, decls, uu____9188) -> decls in
      FStar_ST.op_Colon_Equals should_print_fs_typ_app false;
      (match decls with
       | [] -> (FStar_Pprint.empty, comments)
       | d::ds ->
           let uu____9220 =
             match ds with
             | {
                 FStar_Parser_AST.d = FStar_Parser_AST.Pragma
                   (FStar_Parser_AST.LightOff);
                 FStar_Parser_AST.drange = uu____9233;
                 FStar_Parser_AST.quals = uu____9234;
                 FStar_Parser_AST.attrs = uu____9235;_}::uu____9236 ->
                 let d0 = FStar_List.hd ds in
                 let uu____9240 =
                   let uu____9243 =
                     let uu____9246 = FStar_List.tl ds in d :: uu____9246 in
                   d0 :: uu____9243 in
                 (uu____9240, (d0.FStar_Parser_AST.drange))
             | uu____9251 -> ((d :: ds), (d.FStar_Parser_AST.drange)) in
           (match uu____9220 with
            | (decls1, first_range) ->
                (FStar_ST.op_Colon_Equals comment_stack comments;
                 (let initial_comment =
                    let uu____9292 = FStar_Range.start_of_range first_range in
                    place_comments_until_pos Prims.int_zero Prims.int_one
                      uu____9292 dummy_meta FStar_Pprint.empty false true in
                  let doc =
                    separate_map_with_comments FStar_Pprint.empty
                      FStar_Pprint.empty p_decl decls1 extract_decl_range in
                  let comments1 = FStar_ST.op_Bang comment_stack in
                  FStar_ST.op_Colon_Equals comment_stack [];
                  FStar_ST.op_Colon_Equals should_print_fs_typ_app false;
                  (let uu____9349 =
                     FStar_Pprint.op_Hat_Hat initial_comment doc in
                   (uu____9349, comments1))))))