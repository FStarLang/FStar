open Prims
let (maybe_unthunk : FStar_Parser_AST.term -> FStar_Parser_AST.term) =
  fun t ->
    match t.FStar_Parser_AST.tm with
    | FStar_Parser_AST.Abs (uu___::[], body) -> body
    | uu___ -> t
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
            let uu___ = let uu___1 = f x in uu___1 :: acc in aux xs uu___ in
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
            let uu___ = f x in
            (match uu___ with
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
      | x::xs -> let uu___ = f x in if uu___ then all f xs else false
let (all1_explicit :
  (FStar_Parser_AST.term * FStar_Parser_AST.imp) Prims.list -> Prims.bool) =
  fun args ->
    (Prims.op_Negation (FStar_List.isEmpty args)) &&
      (FStar_Util.for_all
         (fun uu___ ->
            match uu___ with
            | (uu___1, FStar_Parser_AST.Nothing) -> true
            | uu___1 -> false) args)
let (should_print_fs_typ_app : Prims.bool FStar_ST.ref) =
  FStar_Util.mk_ref false
let (unfold_tuples : Prims.bool FStar_ST.ref) = FStar_Util.mk_ref true
let with_fs_typ_app :
  'uuuuu 'uuuuu1 . Prims.bool -> ('uuuuu -> 'uuuuu1) -> 'uuuuu -> 'uuuuu1 =
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
  'uuuuu 'uuuuu1 .
    'uuuuu ->
      ('uuuuu1 -> 'uuuuu) -> 'uuuuu1 FStar_Pervasives_Native.option -> 'uuuuu
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
  'uuuuu .
    FStar_Pprint.document ->
      ('uuuuu -> FStar_Pprint.document) ->
        'uuuuu Prims.list -> FStar_Pprint.document
  =
  fun sep ->
    fun f ->
      fun l ->
        let uu___ =
          let uu___1 =
            let uu___2 = FStar_Pprint.op_Hat_Hat sep break1 in
            FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu___2 in
          FStar_Pprint.separate_map uu___1 f l in
        FStar_Pprint.group uu___
let precede_break_separate_map :
  'uuuuu .
    FStar_Pprint.document ->
      FStar_Pprint.document ->
        ('uuuuu -> FStar_Pprint.document) ->
          'uuuuu Prims.list -> FStar_Pprint.document
  =
  fun prec ->
    fun sep ->
      fun f ->
        fun l ->
          let uu___ =
            let uu___1 = FStar_Pprint.op_Hat_Hat prec FStar_Pprint.space in
            let uu___2 =
              let uu___3 = FStar_List.hd l in FStar_All.pipe_right uu___3 f in
            FStar_Pprint.precede uu___1 uu___2 in
          let uu___1 =
            let uu___2 = FStar_List.tl l in
            FStar_Pprint.concat_map
              (fun x ->
                 let uu___3 =
                   let uu___4 =
                     let uu___5 = f x in
                     FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu___5 in
                   FStar_Pprint.op_Hat_Hat sep uu___4 in
                 FStar_Pprint.op_Hat_Hat break1 uu___3) uu___2 in
          FStar_Pprint.op_Hat_Hat uu___ uu___1
let concat_break_map :
  'uuuuu .
    ('uuuuu -> FStar_Pprint.document) ->
      'uuuuu Prims.list -> FStar_Pprint.document
  =
  fun f ->
    fun l ->
      let uu___ =
        FStar_Pprint.concat_map
          (fun x -> let uu___1 = f x in FStar_Pprint.op_Hat_Hat uu___1 break1)
          l in
      FStar_Pprint.group uu___
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
    let uu___ = str "begin" in
    let uu___1 = str "end" in
    FStar_Pprint.soft_surround (Prims.of_int (2)) Prims.int_one uu___
      contents uu___1
let separate_map_last :
  'uuuuu .
    FStar_Pprint.document ->
      (Prims.bool -> 'uuuuu -> FStar_Pprint.document) ->
        'uuuuu Prims.list -> FStar_Pprint.document
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
  'uuuuu .
    FStar_Pprint.document ->
      (Prims.bool -> 'uuuuu -> FStar_Pprint.document) ->
        'uuuuu Prims.list -> FStar_Pprint.document
  =
  fun sep ->
    fun f ->
      fun l ->
        let uu___ =
          let uu___1 =
            let uu___2 = FStar_Pprint.op_Hat_Hat sep break1 in
            FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu___2 in
          separate_map_last uu___1 f l in
        FStar_Pprint.group uu___
let separate_map_or_flow :
  'uuuuu .
    FStar_Pprint.document ->
      ('uuuuu -> FStar_Pprint.document) ->
        'uuuuu Prims.list -> FStar_Pprint.document
  =
  fun sep ->
    fun f ->
      fun l ->
        if (FStar_List.length l) < (Prims.of_int (10))
        then FStar_Pprint.separate_map sep f l
        else FStar_Pprint.flow_map sep f l
let flow_map_last :
  'uuuuu .
    FStar_Pprint.document ->
      (Prims.bool -> 'uuuuu -> FStar_Pprint.document) ->
        'uuuuu Prims.list -> FStar_Pprint.document
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
  'uuuuu .
    FStar_Pprint.document ->
      (Prims.bool -> 'uuuuu -> FStar_Pprint.document) ->
        'uuuuu Prims.list -> FStar_Pprint.document
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
              let uu___ = FStar_Pprint.op_Hat_Slash_Hat doc1 doc3 in
              FStar_Pprint.group uu___
            else FStar_Pprint.surround n b doc1 doc2 doc3
let soft_surround_separate_map :
  'uuuuu .
    Prims.int ->
      Prims.int ->
        FStar_Pprint.document ->
          FStar_Pprint.document ->
            FStar_Pprint.document ->
              FStar_Pprint.document ->
                ('uuuuu -> FStar_Pprint.document) ->
                  'uuuuu Prims.list -> FStar_Pprint.document
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
                    (let uu___1 = FStar_Pprint.separate_map sep f xs in
                     FStar_Pprint.soft_surround n b opening uu___1 closing)
let soft_surround_map_or_flow :
  'uuuuu .
    Prims.int ->
      Prims.int ->
        FStar_Pprint.document ->
          FStar_Pprint.document ->
            FStar_Pprint.document ->
              FStar_Pprint.document ->
                ('uuuuu -> FStar_Pprint.document) ->
                  'uuuuu Prims.list -> FStar_Pprint.document
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
                    (let uu___1 = separate_map_or_flow sep f xs in
                     FStar_Pprint.soft_surround n b opening uu___1 closing)
let (is_unit : FStar_Parser_AST.term -> Prims.bool) =
  fun e ->
    match e.FStar_Parser_AST.tm with
    | FStar_Parser_AST.Const (FStar_Const.Const_unit) -> true
    | uu___ -> false
let (matches_var : FStar_Parser_AST.term -> FStar_Ident.ident -> Prims.bool)
  =
  fun t ->
    fun x ->
      match t.FStar_Parser_AST.tm with
      | FStar_Parser_AST.Var y ->
          let uu___ = FStar_Ident.string_of_id x in
          let uu___1 = FStar_Ident.string_of_lid y in uu___ = uu___1
      | uu___ -> false
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
        | FStar_Parser_AST.Construct (lid, uu___::(e2, uu___1)::[]) ->
            (FStar_Ident.lid_equals lid cons_lid) && (aux e2)
        | uu___ -> false in
      aux
let (is_list : FStar_Parser_AST.term -> Prims.bool) =
  is_list_structure FStar_Parser_Const.cons_lid FStar_Parser_Const.nil_lid
let rec (extract_from_list :
  FStar_Parser_AST.term -> FStar_Parser_AST.term Prims.list) =
  fun e ->
    match e.FStar_Parser_AST.tm with
    | FStar_Parser_AST.Construct (uu___, []) -> []
    | FStar_Parser_AST.Construct
        (uu___,
         (e1, FStar_Parser_AST.Nothing)::(e2, FStar_Parser_AST.Nothing)::[])
        -> let uu___1 = extract_from_list e2 in e1 :: uu___1
    | uu___ ->
        let uu___1 =
          let uu___2 = FStar_Parser_AST.term_to_string e in
          FStar_Util.format1 "Not a list %s" uu___2 in
        failwith uu___1
let (is_array : FStar_Parser_AST.term -> Prims.bool) =
  fun e ->
    match e.FStar_Parser_AST.tm with
    | FStar_Parser_AST.App
        ({ FStar_Parser_AST.tm = FStar_Parser_AST.Var lid;
           FStar_Parser_AST.range = uu___; FStar_Parser_AST.level = uu___1;_},
         l, FStar_Parser_AST.Nothing)
        ->
        (FStar_Ident.lid_equals lid FStar_Parser_Const.array_of_list_lid) &&
          (is_list l)
    | uu___ -> false
let rec (is_ref_set : FStar_Parser_AST.term -> Prims.bool) =
  fun e ->
    match e.FStar_Parser_AST.tm with
    | FStar_Parser_AST.Var maybe_empty_lid ->
        FStar_Ident.lid_equals maybe_empty_lid FStar_Parser_Const.set_empty
    | FStar_Parser_AST.App
        ({ FStar_Parser_AST.tm = FStar_Parser_AST.Var maybe_singleton_lid;
           FStar_Parser_AST.range = uu___; FStar_Parser_AST.level = uu___1;_},
         {
           FStar_Parser_AST.tm = FStar_Parser_AST.App
             ({ FStar_Parser_AST.tm = FStar_Parser_AST.Var maybe_addr_of_lid;
                FStar_Parser_AST.range = uu___2;
                FStar_Parser_AST.level = uu___3;_},
              e1, FStar_Parser_AST.Nothing);
           FStar_Parser_AST.range = uu___4;
           FStar_Parser_AST.level = uu___5;_},
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
                FStar_Parser_AST.range = uu___;
                FStar_Parser_AST.level = uu___1;_},
              e1, FStar_Parser_AST.Nothing);
           FStar_Parser_AST.range = uu___2;
           FStar_Parser_AST.level = uu___3;_},
         e2, FStar_Parser_AST.Nothing)
        ->
        ((FStar_Ident.lid_equals maybe_union_lid FStar_Parser_Const.set_union)
           && (is_ref_set e1))
          && (is_ref_set e2)
    | uu___ -> false
let rec (extract_from_ref_set :
  FStar_Parser_AST.term -> FStar_Parser_AST.term Prims.list) =
  fun e ->
    match e.FStar_Parser_AST.tm with
    | FStar_Parser_AST.Var uu___ -> []
    | FStar_Parser_AST.App
        ({ FStar_Parser_AST.tm = FStar_Parser_AST.Var uu___;
           FStar_Parser_AST.range = uu___1;
           FStar_Parser_AST.level = uu___2;_},
         {
           FStar_Parser_AST.tm = FStar_Parser_AST.App
             ({ FStar_Parser_AST.tm = FStar_Parser_AST.Var uu___3;
                FStar_Parser_AST.range = uu___4;
                FStar_Parser_AST.level = uu___5;_},
              e1, FStar_Parser_AST.Nothing);
           FStar_Parser_AST.range = uu___6;
           FStar_Parser_AST.level = uu___7;_},
         FStar_Parser_AST.Nothing)
        -> [e1]
    | FStar_Parser_AST.App
        ({
           FStar_Parser_AST.tm = FStar_Parser_AST.App
             ({ FStar_Parser_AST.tm = FStar_Parser_AST.Var uu___;
                FStar_Parser_AST.range = uu___1;
                FStar_Parser_AST.level = uu___2;_},
              e1, FStar_Parser_AST.Nothing);
           FStar_Parser_AST.range = uu___3;
           FStar_Parser_AST.level = uu___4;_},
         e2, FStar_Parser_AST.Nothing)
        ->
        let uu___5 = extract_from_ref_set e1 in
        let uu___6 = extract_from_ref_set e2 in
        FStar_List.append uu___5 uu___6
    | uu___ ->
        let uu___1 =
          let uu___2 = FStar_Parser_AST.term_to_string e in
          FStar_Util.format1 "Not a ref set %s" uu___2 in
        failwith uu___1
let (is_general_application : FStar_Parser_AST.term -> Prims.bool) =
  fun e ->
    let uu___ = (is_array e) || (is_ref_set e) in Prims.op_Negation uu___
let (is_general_construction : FStar_Parser_AST.term -> Prims.bool) =
  fun e -> let uu___ = is_list e in Prims.op_Negation uu___
let (is_general_prefix_op : FStar_Ident.ident -> Prims.bool) =
  fun op ->
    let op_starting_char =
      let uu___ = FStar_Ident.string_of_id op in
      FStar_Util.char_at uu___ Prims.int_zero in
    ((op_starting_char = 33) || (op_starting_char = 63)) ||
      ((op_starting_char = 126) &&
         (let uu___ = FStar_Ident.string_of_id op in uu___ <> "~"))
let (head_and_args :
  FStar_Parser_AST.term ->
    (FStar_Parser_AST.term * (FStar_Parser_AST.term * FStar_Parser_AST.imp)
      Prims.list))
  =
  fun e ->
    let rec aux e1 acc =
      match e1.FStar_Parser_AST.tm with
      | FStar_Parser_AST.App (head, arg, imp) -> aux head ((arg, imp) :: acc)
      | uu___ -> (e1, acc) in
    aux e []
type associativity =
  | Left 
  | Right 
  | NonAssoc 
let (uu___is_Left : associativity -> Prims.bool) =
  fun projectee -> match projectee with | Left -> true | uu___ -> false
let (uu___is_Right : associativity -> Prims.bool) =
  fun projectee -> match projectee with | Right -> true | uu___ -> false
let (uu___is_NonAssoc : associativity -> Prims.bool) =
  fun projectee -> match projectee with | NonAssoc -> true | uu___ -> false
type token = (FStar_Char.char, Prims.string) FStar_Pervasives.either
type associativity_level = (associativity * token Prims.list)
let (token_to_string :
  (FStar_BaseTypes.char, Prims.string) FStar_Pervasives.either ->
    Prims.string)
  =
  fun uu___ ->
    match uu___ with
    | FStar_Pervasives.Inl c ->
        Prims.op_Hat (FStar_Util.string_of_char c) ".*"
    | FStar_Pervasives.Inr s -> s
let (matches_token :
  Prims.string ->
    (FStar_Char.char, Prims.string) FStar_Pervasives.either -> Prims.bool)
  =
  fun s ->
    fun uu___ ->
      match uu___ with
      | FStar_Pervasives.Inl c ->
          let uu___1 = FStar_String.get s Prims.int_zero in uu___1 = c
      | FStar_Pervasives.Inr s' -> s = s'
let matches_level :
  'uuuuu .
    Prims.string ->
      ('uuuuu * (FStar_Char.char, Prims.string) FStar_Pervasives.either
        Prims.list) -> Prims.bool
  =
  fun s ->
    fun uu___ ->
      match uu___ with
      | (assoc_levels, tokens) ->
          let uu___1 = FStar_List.tryFind (matches_token s) tokens in
          uu___1 <> FStar_Pervasives_Native.None
let (opinfix4 : associativity_level) = (Right, [FStar_Pervasives.Inr "**"])
let (opinfix3 : associativity_level) =
  (Left,
    [FStar_Pervasives.Inl 42;
    FStar_Pervasives.Inl 47;
    FStar_Pervasives.Inl 37])
let (opinfix2 : associativity_level) =
  (Left, [FStar_Pervasives.Inl 43; FStar_Pervasives.Inl 45])
let (minus_lvl : associativity_level) = (Left, [FStar_Pervasives.Inr "-"])
let (opinfix1 : associativity_level) =
  (Right, [FStar_Pervasives.Inl 64; FStar_Pervasives.Inl 94])
let (pipe_right : associativity_level) = (Left, [FStar_Pervasives.Inr "|>"])
let (opinfix0d : associativity_level) = (Left, [FStar_Pervasives.Inl 36])
let (opinfix0c : associativity_level) =
  (Left,
    [FStar_Pervasives.Inl 61;
    FStar_Pervasives.Inl 60;
    FStar_Pervasives.Inl 62])
let (equal : associativity_level) = (Left, [FStar_Pervasives.Inr "="])
let (opinfix0b : associativity_level) = (Left, [FStar_Pervasives.Inl 38])
let (opinfix0a : associativity_level) = (Left, [FStar_Pervasives.Inl 124])
let (colon_equals : associativity_level) =
  (NonAssoc, [FStar_Pervasives.Inr ":="])
let (amp : associativity_level) = (Right, [FStar_Pervasives.Inr "&"])
let (colon_colon : associativity_level) =
  (Right, [FStar_Pervasives.Inr "::"])
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
  let levels_from_associativity l uu___ =
    match uu___ with
    | Left -> (l, l, (l - Prims.int_one))
    | Right -> ((l - Prims.int_one), l, l)
    | NonAssoc -> ((l - Prims.int_one), l, (l - Prims.int_one)) in
  FStar_List.mapi
    (fun i ->
       fun uu___ ->
         match uu___ with
         | (assoc, tokens) -> ((levels_from_associativity i assoc), tokens))
    level_associativity_spec
let (assign_levels :
  associativity_level Prims.list ->
    Prims.string -> (Prims.int * Prims.int * Prims.int))
  =
  fun token_associativity_spec ->
    fun s ->
      let uu___ = FStar_List.tryFind (matches_level s) level_table in
      match uu___ with
      | FStar_Pervasives_Native.Some (assoc_levels, uu___1) -> assoc_levels
      | uu___1 -> failwith (Prims.op_Hat "Unrecognized operator " s)
let max_level : 'uuuuu . ('uuuuu * token Prims.list) Prims.list -> Prims.int
  =
  fun l ->
    let find_level_and_max n level =
      let uu___ =
        FStar_List.tryFind
          (fun uu___1 ->
             match uu___1 with
             | (uu___2, tokens) ->
                 tokens = (FStar_Pervasives_Native.snd level)) level_table in
      match uu___ with
      | FStar_Pervasives_Native.Some ((uu___1, l1, uu___2), uu___3) ->
          max n l1
      | FStar_Pervasives_Native.None ->
          let uu___1 =
            let uu___2 =
              let uu___3 =
                FStar_List.map token_to_string
                  (FStar_Pervasives_Native.snd level) in
              FStar_String.concat "," uu___3 in
            FStar_Util.format1 "Undefined associativity level %s" uu___2 in
          failwith uu___1 in
    FStar_List.fold_left find_level_and_max Prims.int_zero l
let (levels : Prims.string -> (Prims.int * Prims.int * Prims.int)) =
  fun op ->
    let uu___ = assign_levels level_associativity_spec op in
    match uu___ with
    | (left, mine, right) ->
        if op = "*"
        then ((left - Prims.int_one), mine, right)
        else (left, mine, right)
let (operatorInfix0ad12 : associativity_level Prims.list) =
  [opinfix0a; opinfix0b; opinfix0c; opinfix0d; opinfix1; opinfix2]
let (is_operatorInfix0ad12 : FStar_Ident.ident -> Prims.bool) =
  fun op ->
    let uu___ =
      let uu___1 =
        let uu___2 = FStar_Ident.string_of_id op in
        FStar_All.pipe_left matches_level uu___2 in
      FStar_List.tryFind uu___1 operatorInfix0ad12 in
    uu___ <> FStar_Pervasives_Native.None
let (is_operatorInfix34 : FStar_Ident.ident -> Prims.bool) =
  let opinfix34 = [opinfix3; opinfix4] in
  fun op ->
    let uu___ =
      let uu___1 =
        let uu___2 = FStar_Ident.string_of_id op in
        FStar_All.pipe_left matches_level uu___2 in
      FStar_List.tryFind uu___1 opinfix34 in
    uu___ <> FStar_Pervasives_Native.None
let (handleable_args_length : FStar_Ident.ident -> Prims.int) =
  fun op ->
    let op_s = FStar_Ident.string_of_id op in
    let uu___ = (is_general_prefix_op op) || (FStar_List.mem op_s ["-"; "~"]) in
    if uu___
    then Prims.int_one
    else
      (let uu___2 =
         ((is_operatorInfix0ad12 op) || (is_operatorInfix34 op)) ||
           (FStar_List.mem op_s
              ["<==>"; "==>"; "\\/"; "/\\"; "="; "|>"; ":="; ".()"; ".[]"]) in
       if uu___2
       then (Prims.of_int (2))
       else
         if FStar_List.mem op_s [".()<-"; ".[]<-"]
         then (Prims.of_int (3))
         else Prims.int_zero)
let handleable_op :
  'uuuuu . FStar_Ident.ident -> 'uuuuu Prims.list -> Prims.bool =
  fun op ->
    fun args ->
      match FStar_List.length args with
      | uu___ when uu___ = Prims.int_zero -> true
      | uu___ when uu___ = Prims.int_one ->
          (is_general_prefix_op op) ||
            (let uu___1 = FStar_Ident.string_of_id op in
             FStar_List.mem uu___1 ["-"; "~"])
      | uu___ when uu___ = (Prims.of_int (2)) ->
          ((is_operatorInfix0ad12 op) || (is_operatorInfix34 op)) ||
            (let uu___1 = FStar_Ident.string_of_id op in
             FStar_List.mem uu___1
               ["<==>"; "==>"; "\\/"; "/\\"; "="; "|>"; ":="; ".()"; ".[]"])
      | uu___ when uu___ = (Prims.of_int (3)) ->
          let uu___1 = FStar_Ident.string_of_id op in
          FStar_List.mem uu___1 [".()<-"; ".[]<-"]
      | uu___ -> false
type annotation_style =
  | Binders of (Prims.int * Prims.int * Prims.bool) 
  | Arrows of (Prims.int * Prims.int) 
let (uu___is_Binders : annotation_style -> Prims.bool) =
  fun projectee -> match projectee with | Binders _0 -> true | uu___ -> false
let (__proj__Binders__item___0 :
  annotation_style -> (Prims.int * Prims.int * Prims.bool)) =
  fun projectee -> match projectee with | Binders _0 -> _0
let (uu___is_Arrows : annotation_style -> Prims.bool) =
  fun projectee -> match projectee with | Arrows _0 -> true | uu___ -> false
let (__proj__Arrows__item___0 : annotation_style -> (Prims.int * Prims.int))
  = fun projectee -> match projectee with | Arrows _0 -> _0
let (all_binders_annot : FStar_Parser_AST.term -> Prims.bool) =
  fun e ->
    let is_binder_annot b =
      match b.FStar_Parser_AST.b with
      | FStar_Parser_AST.Annotated uu___ -> true
      | uu___ -> false in
    let rec all_binders e1 l =
      match e1.FStar_Parser_AST.tm with
      | FStar_Parser_AST.Product (bs, tgt) ->
          let uu___ = FStar_List.for_all is_binder_annot bs in
          if uu___
          then all_binders tgt (l + (FStar_List.length bs))
          else (false, Prims.int_zero)
      | uu___ -> (true, (l + Prims.int_one)) in
    let uu___ = all_binders e Prims.int_zero in
    match uu___ with
    | (b, l) -> if b && (l > Prims.int_one) then true else false
type catf =
  FStar_Pprint.document -> FStar_Pprint.document -> FStar_Pprint.document
let (cat_with_colon :
  FStar_Pprint.document -> FStar_Pprint.document -> FStar_Pprint.document) =
  fun x ->
    fun y ->
      let uu___ = FStar_Pprint.op_Hat_Slash_Hat FStar_Pprint.colon y in
      FStar_Pprint.op_Hat_Hat x uu___
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
  'uuuuu .
    ('uuuuu -> FStar_Pprint.document) ->
      'uuuuu -> FStar_Range.range -> FStar_Pprint.document
  =
  fun printer ->
    fun tm ->
      fun tmrange ->
        let rec comments_before_pos acc print_pos lookahead_pos =
          let uu___ = FStar_ST.op_Bang comment_stack in
          match uu___ with
          | [] -> (acc, false)
          | (c, crange)::cs ->
              let comment =
                let uu___1 = str c in
                FStar_Pprint.op_Hat_Hat uu___1 FStar_Pprint.hardline in
              let uu___1 = FStar_Range.range_before_pos crange print_pos in
              if uu___1
              then
                (FStar_ST.op_Colon_Equals comment_stack cs;
                 (let uu___3 = FStar_Pprint.op_Hat_Hat acc comment in
                  comments_before_pos uu___3 print_pos lookahead_pos))
              else
                (let uu___3 =
                   FStar_Range.range_before_pos crange lookahead_pos in
                 (acc, uu___3)) in
        let uu___ =
          let uu___1 =
            let uu___2 = FStar_Range.start_of_range tmrange in
            FStar_Range.end_of_line uu___2 in
          let uu___2 = FStar_Range.end_of_range tmrange in
          comments_before_pos FStar_Pprint.empty uu___1 uu___2 in
        match uu___ with
        | (comments, has_lookahead) ->
            let printed_e = printer tm in
            let comments1 =
              if has_lookahead
              then
                let pos = FStar_Range.end_of_range tmrange in
                let uu___1 = comments_before_pos comments pos pos in
                FStar_Pervasives_Native.fst uu___1
              else comments in
            if comments1 = FStar_Pprint.empty
            then printed_e
            else
              (let uu___2 = FStar_Pprint.op_Hat_Hat comments1 printed_e in
               FStar_Pprint.group uu___2)
let with_comment_sep :
  'uuuuu 'uuuuu1 .
    ('uuuuu -> 'uuuuu1) ->
      'uuuuu -> FStar_Range.range -> (FStar_Pprint.document * 'uuuuu1)
  =
  fun printer ->
    fun tm ->
      fun tmrange ->
        let rec comments_before_pos acc print_pos lookahead_pos =
          let uu___ = FStar_ST.op_Bang comment_stack in
          match uu___ with
          | [] -> (acc, false)
          | (c, crange)::cs ->
              let comment = str c in
              let uu___1 = FStar_Range.range_before_pos crange print_pos in
              if uu___1
              then
                (FStar_ST.op_Colon_Equals comment_stack cs;
                 (let uu___3 =
                    if acc = FStar_Pprint.empty
                    then comment
                    else
                      (let uu___5 =
                         FStar_Pprint.op_Hat_Hat FStar_Pprint.hardline
                           comment in
                       FStar_Pprint.op_Hat_Hat acc uu___5) in
                  comments_before_pos uu___3 print_pos lookahead_pos))
              else
                (let uu___3 =
                   FStar_Range.range_before_pos crange lookahead_pos in
                 (acc, uu___3)) in
        let uu___ =
          let uu___1 =
            let uu___2 = FStar_Range.start_of_range tmrange in
            FStar_Range.end_of_line uu___2 in
          let uu___2 = FStar_Range.end_of_range tmrange in
          comments_before_pos FStar_Pprint.empty uu___1 uu___2 in
        match uu___ with
        | (comments, has_lookahead) ->
            let printed_e = printer tm in
            let comments1 =
              if has_lookahead
              then
                let pos = FStar_Range.end_of_range tmrange in
                let uu___1 = comments_before_pos comments pos pos in
                FStar_Pervasives_Native.fst uu___1
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
                let uu___ = FStar_ST.op_Bang comment_stack in
                match uu___ with
                | (comment, crange)::cs when
                    FStar_Range.range_before_pos crange pos ->
                    (FStar_ST.op_Colon_Equals comment_stack cs;
                     (let lnum =
                        let uu___2 =
                          let uu___3 =
                            let uu___4 = FStar_Range.start_of_range crange in
                            FStar_Range.line_of_pos uu___4 in
                          uu___3 - lbegin in
                        max k uu___2 in
                      let lnum1 = min (Prims.of_int (2)) lnum in
                      let doc1 =
                        let uu___2 =
                          let uu___3 =
                            FStar_Pprint.repeat lnum1 FStar_Pprint.hardline in
                          let uu___4 = str comment in
                          FStar_Pprint.op_Hat_Hat uu___3 uu___4 in
                        FStar_Pprint.op_Hat_Hat doc uu___2 in
                      let uu___2 =
                        let uu___3 = FStar_Range.end_of_range crange in
                        FStar_Range.line_of_pos uu___3 in
                      place_comments_until_pos Prims.int_one uu___2 pos
                        meta_decl doc1 true init))
                | uu___1 ->
                    if doc = FStar_Pprint.empty
                    then FStar_Pprint.empty
                    else
                      (let lnum =
                         let uu___3 = FStar_Range.line_of_pos pos in
                         uu___3 - lbegin in
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
                       let uu___3 =
                         FStar_Pprint.repeat lnum5 FStar_Pprint.hardline in
                       FStar_Pprint.op_Hat_Hat doc uu___3)
let separate_map_with_comments :
  'uuuuu .
    FStar_Pprint.document ->
      FStar_Pprint.document ->
        ('uuuuu -> FStar_Pprint.document) ->
          'uuuuu Prims.list -> ('uuuuu -> decl_meta) -> FStar_Pprint.document
  =
  fun prefix ->
    fun sep ->
      fun f ->
        fun xs ->
          fun extract_meta ->
            let fold_fun uu___ x =
              match uu___ with
              | (last_line, doc) ->
                  let meta_decl = extract_meta x in
                  let r = meta_decl.r in
                  let doc1 =
                    let uu___1 = FStar_Range.start_of_range r in
                    place_comments_until_pos Prims.int_one last_line uu___1
                      meta_decl doc false false in
                  let uu___1 =
                    let uu___2 = FStar_Range.end_of_range r in
                    FStar_Range.line_of_pos uu___2 in
                  let uu___2 =
                    let uu___3 =
                      let uu___4 = f x in FStar_Pprint.op_Hat_Hat sep uu___4 in
                    FStar_Pprint.op_Hat_Hat doc1 uu___3 in
                  (uu___1, uu___2) in
            let uu___ =
              let uu___1 = FStar_List.hd xs in
              let uu___2 = FStar_List.tl xs in (uu___1, uu___2) in
            match uu___ with
            | (x, xs1) ->
                let init =
                  let meta_decl = extract_meta x in
                  let uu___1 =
                    let uu___2 = FStar_Range.end_of_range meta_decl.r in
                    FStar_Range.line_of_pos uu___2 in
                  let uu___2 =
                    let uu___3 = f x in FStar_Pprint.op_Hat_Hat prefix uu___3 in
                  (uu___1, uu___2) in
                let uu___1 = FStar_List.fold_left fold_fun init xs1 in
                FStar_Pervasives_Native.snd uu___1
let separate_map_with_comments_kw :
  'uuuuu 'uuuuu1 .
    'uuuuu ->
      'uuuuu ->
        ('uuuuu -> 'uuuuu1 -> FStar_Pprint.document) ->
          'uuuuu1 Prims.list ->
            ('uuuuu1 -> decl_meta) -> FStar_Pprint.document
  =
  fun prefix ->
    fun sep ->
      fun f ->
        fun xs ->
          fun extract_meta ->
            let fold_fun uu___ x =
              match uu___ with
              | (last_line, doc) ->
                  let meta_decl = extract_meta x in
                  let r = meta_decl.r in
                  let doc1 =
                    let uu___1 = FStar_Range.start_of_range r in
                    place_comments_until_pos Prims.int_one last_line uu___1
                      meta_decl doc false false in
                  let uu___1 =
                    let uu___2 = FStar_Range.end_of_range r in
                    FStar_Range.line_of_pos uu___2 in
                  let uu___2 =
                    let uu___3 = f sep x in
                    FStar_Pprint.op_Hat_Hat doc1 uu___3 in
                  (uu___1, uu___2) in
            let uu___ =
              let uu___1 = FStar_List.hd xs in
              let uu___2 = FStar_List.tl xs in (uu___1, uu___2) in
            match uu___ with
            | (x, xs1) ->
                let init =
                  let meta_decl = extract_meta x in
                  let uu___1 =
                    let uu___2 = FStar_Range.end_of_range meta_decl.r in
                    FStar_Range.line_of_pos uu___2 in
                  let uu___2 = f prefix x in (uu___1, uu___2) in
                let uu___1 = FStar_List.fold_left fold_fun init xs1 in
                FStar_Pervasives_Native.snd uu___1
let rec (p_decl : FStar_Parser_AST.decl -> FStar_Pprint.document) =
  fun d ->
    let qualifiers =
      match ((d.FStar_Parser_AST.quals), (d.FStar_Parser_AST.d)) with
      | ((FStar_Parser_AST.Assumption)::[], FStar_Parser_AST.Assume
         (id, uu___)) ->
          let uu___1 =
            let uu___2 =
              let uu___3 = FStar_Ident.string_of_id id in
              FStar_Util.char_at uu___3 Prims.int_zero in
            FStar_All.pipe_right uu___2 FStar_Util.is_upper in
          if uu___1
          then
            let uu___2 = p_qualifier FStar_Parser_AST.Assumption in
            FStar_Pprint.op_Hat_Hat uu___2 FStar_Pprint.space
          else p_qualifiers d.FStar_Parser_AST.quals
      | uu___ -> p_qualifiers d.FStar_Parser_AST.quals in
    let uu___ = p_attributes d.FStar_Parser_AST.attrs in
    let uu___1 =
      let uu___2 = p_rawDecl d in FStar_Pprint.op_Hat_Hat qualifiers uu___2 in
    FStar_Pprint.op_Hat_Hat uu___ uu___1
and (p_attributes : FStar_Parser_AST.attributes_ -> FStar_Pprint.document) =
  fun attrs ->
    match attrs with
    | [] -> FStar_Pprint.empty
    | uu___ ->
        let uu___1 =
          let uu___2 = str "@@ " in
          let uu___3 =
            let uu___4 =
              let uu___5 =
                let uu___6 =
                  let uu___7 = str "; " in
                  let uu___8 =
                    FStar_List.map (p_noSeqTermAndComment false false) attrs in
                  FStar_Pprint.flow uu___7 uu___8 in
                FStar_Pprint.op_Hat_Hat uu___6 FStar_Pprint.rbracket in
              FStar_Pprint.align uu___5 in
            FStar_Pprint.op_Hat_Hat uu___4 FStar_Pprint.hardline in
          FStar_Pprint.op_Hat_Hat uu___2 uu___3 in
        FStar_Pprint.op_Hat_Hat FStar_Pprint.lbracket uu___1
and (p_justSig : FStar_Parser_AST.decl -> FStar_Pprint.document) =
  fun d ->
    match d.FStar_Parser_AST.d with
    | FStar_Parser_AST.Val (lid, t) ->
        let uu___ =
          let uu___1 = str "val" in
          let uu___2 =
            let uu___3 =
              let uu___4 = p_lident lid in
              let uu___5 =
                FStar_Pprint.op_Hat_Hat FStar_Pprint.space FStar_Pprint.colon in
              FStar_Pprint.op_Hat_Hat uu___4 uu___5 in
            FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu___3 in
          FStar_Pprint.op_Hat_Hat uu___1 uu___2 in
        let uu___1 = p_typ false false t in
        FStar_Pprint.op_Hat_Hat uu___ uu___1
    | FStar_Parser_AST.TopLevelLet (uu___, lbs) ->
        FStar_Pprint.separate_map FStar_Pprint.hardline
          (fun lb ->
             let uu___1 = let uu___2 = str "let" in p_letlhs uu___2 lb false in
             FStar_Pprint.group uu___1) lbs
    | uu___ -> FStar_Pprint.empty
and (p_list :
  (FStar_Ident.ident -> FStar_Pprint.document) ->
    FStar_Pprint.document ->
      FStar_Ident.ident Prims.list -> FStar_Pprint.document)
  =
  fun f ->
    fun sep ->
      fun l ->
        let rec p_list' uu___ =
          match uu___ with
          | [] -> FStar_Pprint.empty
          | x::[] -> f x
          | x::xs ->
              let uu___1 = f x in
              let uu___2 =
                let uu___3 = p_list' xs in FStar_Pprint.op_Hat_Hat sep uu___3 in
              FStar_Pprint.op_Hat_Hat uu___1 uu___2 in
        let uu___ = str "[" in
        let uu___1 =
          let uu___2 = p_list' l in
          let uu___3 = str "]" in FStar_Pprint.op_Hat_Hat uu___2 uu___3 in
        FStar_Pprint.op_Hat_Hat uu___ uu___1
and (p_rawDecl : FStar_Parser_AST.decl -> FStar_Pprint.document) =
  fun d ->
    match d.FStar_Parser_AST.d with
    | FStar_Parser_AST.Open uid ->
        let uu___ =
          let uu___1 = str "open" in
          let uu___2 = p_quident uid in
          FStar_Pprint.op_Hat_Slash_Hat uu___1 uu___2 in
        FStar_Pprint.group uu___
    | FStar_Parser_AST.Include uid ->
        let uu___ =
          let uu___1 = str "include" in
          let uu___2 = p_quident uid in
          FStar_Pprint.op_Hat_Slash_Hat uu___1 uu___2 in
        FStar_Pprint.group uu___
    | FStar_Parser_AST.Friend uid ->
        let uu___ =
          let uu___1 = str "friend" in
          let uu___2 = p_quident uid in
          FStar_Pprint.op_Hat_Slash_Hat uu___1 uu___2 in
        FStar_Pprint.group uu___
    | FStar_Parser_AST.ModuleAbbrev (uid1, uid2) ->
        let uu___ =
          let uu___1 = str "module" in
          let uu___2 =
            let uu___3 =
              let uu___4 = p_uident uid1 in
              let uu___5 =
                FStar_Pprint.op_Hat_Hat FStar_Pprint.space
                  FStar_Pprint.equals in
              FStar_Pprint.op_Hat_Hat uu___4 uu___5 in
            FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu___3 in
          FStar_Pprint.op_Hat_Hat uu___1 uu___2 in
        let uu___1 = p_quident uid2 in op_Hat_Slash_Plus_Hat uu___ uu___1
    | FStar_Parser_AST.TopLevelModule uid ->
        let uu___ =
          let uu___1 = str "module" in
          let uu___2 =
            let uu___3 = p_quident uid in
            FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu___3 in
          FStar_Pprint.op_Hat_Hat uu___1 uu___2 in
        FStar_Pprint.group uu___
    | FStar_Parser_AST.Tycon
        (true, uu___, (FStar_Parser_AST.TyconAbbrev
         (uid, tpars, FStar_Pervasives_Native.None, t))::[])
        ->
        let effect_prefix_doc =
          let uu___1 = str "effect" in
          let uu___2 =
            let uu___3 = p_uident uid in
            FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu___3 in
          FStar_Pprint.op_Hat_Hat uu___1 uu___2 in
        let uu___1 =
          let uu___2 = p_typars tpars in
          FStar_Pprint.surround (Prims.of_int (2)) Prims.int_one
            effect_prefix_doc uu___2 FStar_Pprint.equals in
        let uu___2 = p_typ false false t in
        op_Hat_Slash_Plus_Hat uu___1 uu___2
    | FStar_Parser_AST.Tycon (false, tc, tcdefs) ->
        let s = if tc then str "class" else str "type" in
        let uu___ =
          let uu___1 = FStar_List.hd tcdefs in p_typeDeclWithKw s uu___1 in
        let uu___1 =
          let uu___2 = FStar_List.tl tcdefs in
          FStar_All.pipe_left
            (FStar_Pprint.concat_map
               (fun x ->
                  let uu___3 =
                    let uu___4 = str "and" in p_typeDeclWithKw uu___4 x in
                  FStar_Pprint.op_Hat_Hat break1 uu___3)) uu___2 in
        FStar_Pprint.op_Hat_Hat uu___ uu___1
    | FStar_Parser_AST.TopLevelLet (q, lbs) ->
        let let_doc =
          let uu___ = str "let" in
          let uu___1 = p_letqualifier q in
          FStar_Pprint.op_Hat_Hat uu___ uu___1 in
        let uu___ = str "and" in
        separate_map_with_comments_kw let_doc uu___ p_letbinding lbs
          (fun uu___1 ->
             match uu___1 with
             | (p, t) ->
                 let uu___2 =
                   FStar_Range.union_ranges p.FStar_Parser_AST.prange
                     t.FStar_Parser_AST.range in
                 { r = uu___2; has_qs = false; has_attrs = false })
    | FStar_Parser_AST.Val (lid, t) ->
        let uu___ =
          let uu___1 = str "val" in
          let uu___2 =
            let uu___3 =
              let uu___4 = p_lident lid in
              let uu___5 = sig_as_binders_if_possible t false in
              FStar_Pprint.op_Hat_Hat uu___4 uu___5 in
            FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu___3 in
          FStar_Pprint.op_Hat_Hat uu___1 uu___2 in
        FStar_All.pipe_left FStar_Pprint.group uu___
    | FStar_Parser_AST.Assume (id, t) ->
        let decl_keyword =
          let uu___ =
            let uu___1 =
              let uu___2 = FStar_Ident.string_of_id id in
              FStar_Util.char_at uu___2 Prims.int_zero in
            FStar_All.pipe_right uu___1 FStar_Util.is_upper in
          if uu___
          then FStar_Pprint.empty
          else
            (let uu___2 = str "val" in
             FStar_Pprint.op_Hat_Hat uu___2 FStar_Pprint.space) in
        let uu___ =
          let uu___1 = p_ident id in
          let uu___2 =
            let uu___3 =
              let uu___4 =
                let uu___5 = p_typ false false t in
                FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu___5 in
              FStar_Pprint.op_Hat_Hat FStar_Pprint.colon uu___4 in
            FStar_Pprint.group uu___3 in
          FStar_Pprint.op_Hat_Hat uu___1 uu___2 in
        FStar_Pprint.op_Hat_Hat decl_keyword uu___
    | FStar_Parser_AST.Exception (uid, t_opt) ->
        let uu___ = str "exception" in
        let uu___1 =
          let uu___2 =
            let uu___3 = p_uident uid in
            let uu___4 =
              FStar_Pprint.optional
                (fun t ->
                   let uu___5 =
                     let uu___6 = str "of" in
                     let uu___7 = p_typ false false t in
                     op_Hat_Slash_Plus_Hat uu___6 uu___7 in
                   FStar_Pprint.op_Hat_Hat break1 uu___5) t_opt in
            FStar_Pprint.op_Hat_Hat uu___3 uu___4 in
          FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu___2 in
        FStar_Pprint.op_Hat_Hat uu___ uu___1
    | FStar_Parser_AST.NewEffect ne ->
        let uu___ = str "new_effect" in
        let uu___1 =
          let uu___2 = p_newEffect ne in
          FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu___2 in
        FStar_Pprint.op_Hat_Hat uu___ uu___1
    | FStar_Parser_AST.SubEffect se ->
        let uu___ = str "sub_effect" in
        let uu___1 =
          let uu___2 = p_subEffect se in
          FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu___2 in
        FStar_Pprint.op_Hat_Hat uu___ uu___1
    | FStar_Parser_AST.LayeredEffect ne ->
        let uu___ = str "layered_effect" in
        let uu___1 =
          let uu___2 = p_newEffect ne in
          FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu___2 in
        FStar_Pprint.op_Hat_Hat uu___ uu___1
    | FStar_Parser_AST.Polymonadic_bind (l1, l2, l3, t) ->
        let uu___ = str "polymonadic_bind" in
        let uu___1 =
          let uu___2 =
            let uu___3 = p_quident l1 in
            let uu___4 =
              let uu___5 =
                let uu___6 =
                  let uu___7 = p_quident l2 in
                  let uu___8 =
                    let uu___9 =
                      let uu___10 = str "|>" in
                      let uu___11 =
                        let uu___12 = p_quident l3 in
                        let uu___13 =
                          let uu___14 = p_simpleTerm false false t in
                          FStar_Pprint.op_Hat_Hat FStar_Pprint.equals uu___14 in
                        FStar_Pprint.op_Hat_Hat uu___12 uu___13 in
                      FStar_Pprint.op_Hat_Hat uu___10 uu___11 in
                    FStar_Pprint.op_Hat_Hat FStar_Pprint.rparen uu___9 in
                  FStar_Pprint.op_Hat_Hat uu___7 uu___8 in
                FStar_Pprint.op_Hat_Hat break1 uu___6 in
              FStar_Pprint.op_Hat_Hat FStar_Pprint.comma uu___5 in
            FStar_Pprint.op_Hat_Hat uu___3 uu___4 in
          FStar_Pprint.op_Hat_Hat FStar_Pprint.lparen uu___2 in
        FStar_Pprint.op_Hat_Hat uu___ uu___1
    | FStar_Parser_AST.Pragma p -> p_pragma p
    | FStar_Parser_AST.Tycon (true, uu___, uu___1) ->
        failwith
          "Effect abbreviation is expected to be defined by an abbreviation"
    | FStar_Parser_AST.Splice (ids, t) ->
        let uu___ = str "%splice" in
        let uu___1 =
          let uu___2 = let uu___3 = str ";" in p_list p_uident uu___3 ids in
          let uu___3 =
            let uu___4 = p_term false false t in
            FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu___4 in
          FStar_Pprint.op_Hat_Hat uu___2 uu___3 in
        FStar_Pprint.op_Hat_Hat uu___ uu___1
and (p_pragma : FStar_Parser_AST.pragma -> FStar_Pprint.document) =
  fun uu___ ->
    match uu___ with
    | FStar_Parser_AST.SetOptions s ->
        let uu___1 = str "#set-options" in
        let uu___2 =
          let uu___3 = let uu___4 = str s in FStar_Pprint.dquotes uu___4 in
          FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu___3 in
        FStar_Pprint.op_Hat_Hat uu___1 uu___2
    | FStar_Parser_AST.ResetOptions s_opt ->
        let uu___1 = str "#reset-options" in
        let uu___2 =
          FStar_Pprint.optional
            (fun s ->
               let uu___3 = let uu___4 = str s in FStar_Pprint.dquotes uu___4 in
               FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu___3) s_opt in
        FStar_Pprint.op_Hat_Hat uu___1 uu___2
    | FStar_Parser_AST.PushOptions s_opt ->
        let uu___1 = str "#push-options" in
        let uu___2 =
          FStar_Pprint.optional
            (fun s ->
               let uu___3 = let uu___4 = str s in FStar_Pprint.dquotes uu___4 in
               FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu___3) s_opt in
        FStar_Pprint.op_Hat_Hat uu___1 uu___2
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
      let uu___ = p_typeDecl kw typedecl in
      match uu___ with
      | (comm, decl, body, pre) ->
          if comm = FStar_Pprint.empty
          then let uu___1 = pre body in FStar_Pprint.op_Hat_Hat decl uu___1
          else
            (let uu___2 =
               let uu___3 =
                 let uu___4 =
                   let uu___5 = pre body in
                   FStar_Pprint.op_Hat_Slash_Hat uu___5 comm in
                 FStar_Pprint.op_Hat_Hat decl uu___4 in
               let uu___4 =
                 let uu___5 =
                   let uu___6 =
                     let uu___7 =
                       let uu___8 =
                         FStar_Pprint.op_Hat_Hat FStar_Pprint.hardline body in
                       FStar_Pprint.op_Hat_Hat comm uu___8 in
                     FStar_Pprint.op_Hat_Hat FStar_Pprint.hardline uu___7 in
                   FStar_Pprint.nest (Prims.of_int (2)) uu___6 in
                 FStar_Pprint.op_Hat_Hat decl uu___5 in
               FStar_Pprint.ifflat uu___3 uu___4 in
             FStar_All.pipe_left FStar_Pprint.group uu___2)
and (p_typeDecl :
  FStar_Pprint.document ->
    FStar_Parser_AST.tycon ->
      (FStar_Pprint.document * FStar_Pprint.document * FStar_Pprint.document
        * (FStar_Pprint.document -> FStar_Pprint.document)))
  =
  fun pre ->
    fun uu___ ->
      match uu___ with
      | FStar_Parser_AST.TyconAbstract (lid, bs, typ_opt) ->
          let uu___1 = p_typeDeclPrefix pre false lid bs typ_opt in
          (FStar_Pprint.empty, uu___1, FStar_Pprint.empty,
            FStar_Pervasives.id)
      | FStar_Parser_AST.TyconAbbrev (lid, bs, typ_opt, t) ->
          let uu___1 = p_typ_sep false false t in
          (match uu___1 with
           | (comm, doc) ->
               let uu___2 = p_typeDeclPrefix pre true lid bs typ_opt in
               (comm, uu___2, doc, jump2))
      | FStar_Parser_AST.TyconRecord (lid, bs, typ_opt, record_field_decls)
          ->
          let p_recordField ps uu___1 =
            match uu___1 with
            | (lid1, aq, attrs, t) ->
                let uu___2 =
                  let uu___3 =
                    FStar_Range.extend_to_end_of_line
                      t.FStar_Parser_AST.range in
                  with_comment_sep (p_recordFieldDecl ps)
                    (lid1, aq, attrs, t) uu___3 in
                (match uu___2 with
                 | (comm, field) ->
                     let sep =
                       if ps then FStar_Pprint.semi else FStar_Pprint.empty in
                     inline_comment_or_above comm field sep) in
          let p_fields =
            let uu___1 =
              separate_map_last FStar_Pprint.hardline p_recordField
                record_field_decls in
            braces_with_nesting uu___1 in
          let uu___1 = p_typeDeclPrefix pre true lid bs typ_opt in
          (FStar_Pprint.empty, uu___1, p_fields,
            ((fun d -> FStar_Pprint.op_Hat_Hat FStar_Pprint.space d)))
      | FStar_Parser_AST.TyconVariant (lid, bs, typ_opt, ct_decls) ->
          let p_constructorBranchAndComments uu___1 =
            match uu___1 with
            | (uid, t_opt, use_of) ->
                let range =
                  let uu___2 =
                    let uu___3 = FStar_Ident.range_of_id uid in
                    let uu___4 =
                      FStar_Util.map_opt t_opt
                        (fun t -> t.FStar_Parser_AST.range) in
                    FStar_Util.dflt uu___3 uu___4 in
                  FStar_Range.extend_to_end_of_line uu___2 in
                let uu___2 =
                  with_comment_sep p_constructorBranch (uid, t_opt, use_of)
                    range in
                (match uu___2 with
                 | (comm, ctor) ->
                     inline_comment_or_above comm ctor FStar_Pprint.empty) in
          let datacon_doc =
            FStar_Pprint.separate_map FStar_Pprint.hardline
              p_constructorBranchAndComments ct_decls in
          let uu___1 = p_typeDeclPrefix pre true lid bs typ_opt in
          (FStar_Pprint.empty, uu___1, datacon_doc, jump2)
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
                let uu___ = FStar_Pprint.op_Hat_Slash_Hat kw lid_doc in
                FStar_Pprint.group uu___ in
              cont kw_lid in
            let typ =
              let maybe_eq =
                if eq then FStar_Pprint.equals else FStar_Pprint.empty in
              match typ_opt with
              | FStar_Pervasives_Native.None -> maybe_eq
              | FStar_Pervasives_Native.Some t ->
                  let uu___ =
                    let uu___1 =
                      let uu___2 = p_typ false false t in
                      FStar_Pprint.op_Hat_Slash_Hat uu___2 maybe_eq in
                    FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu___1 in
                  FStar_Pprint.op_Hat_Hat FStar_Pprint.colon uu___ in
            if bs = []
            then with_kw (fun n -> prefix2 n typ)
            else
              (let binders = p_binders_list true bs in
               with_kw
                 (fun n ->
                    let uu___1 =
                      let uu___2 = FStar_Pprint.flow break1 binders in
                      prefix2 n uu___2 in
                    prefix2 uu___1 typ))
and (p_recordFieldDecl :
  Prims.bool ->
    (FStar_Ident.ident * FStar_Parser_AST.aqual *
      FStar_Parser_AST.attributes_ * FStar_Parser_AST.term) ->
      FStar_Pprint.document)
  =
  fun ps ->
    fun uu___ ->
      match uu___ with
      | (lid, aq, attrs, t) ->
          let uu___1 =
            let uu___2 = FStar_Pprint.optional p_aqual aq in
            let uu___3 =
              let uu___4 = p_attributes attrs in
              let uu___5 =
                let uu___6 = p_lident lid in
                let uu___7 =
                  let uu___8 = p_typ ps false t in
                  FStar_Pprint.op_Hat_Hat FStar_Pprint.colon uu___8 in
                FStar_Pprint.op_Hat_Hat uu___6 uu___7 in
              FStar_Pprint.op_Hat_Hat uu___4 uu___5 in
            FStar_Pprint.op_Hat_Hat uu___2 uu___3 in
          FStar_Pprint.group uu___1
and (p_constructorBranch :
  (FStar_Ident.ident * FStar_Parser_AST.term FStar_Pervasives_Native.option *
    Prims.bool) -> FStar_Pprint.document)
  =
  fun uu___ ->
    match uu___ with
    | (uid, t_opt, use_of) ->
        let sep = if use_of then str "of" else FStar_Pprint.colon in
        let uid_doc =
          let uu___1 =
            let uu___2 =
              let uu___3 = p_uident uid in
              FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu___3 in
            FStar_Pprint.op_Hat_Hat FStar_Pprint.bar uu___2 in
          FStar_Pprint.group uu___1 in
        default_or_map uid_doc
          (fun t ->
             let uu___1 =
               let uu___2 =
                 let uu___3 =
                   let uu___4 =
                     let uu___5 = p_typ false false t in
                     FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu___5 in
                   FStar_Pprint.op_Hat_Hat sep uu___4 in
                 FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu___3 in
               FStar_Pprint.op_Hat_Hat uid_doc uu___2 in
             FStar_Pprint.group uu___1) t_opt
and (p_letlhs :
  FStar_Pprint.document ->
    (FStar_Parser_AST.pattern * FStar_Parser_AST.term) ->
      Prims.bool -> FStar_Pprint.document)
  =
  fun kw ->
    fun uu___ ->
      fun inner_let ->
        match uu___ with
        | (pat, uu___1) ->
            let uu___2 =
              match pat.FStar_Parser_AST.pat with
              | FStar_Parser_AST.PatAscribed
                  (pat1, (t, FStar_Pervasives_Native.None)) ->
                  (pat1,
                    (FStar_Pervasives_Native.Some (t, FStar_Pprint.empty)))
              | FStar_Parser_AST.PatAscribed
                  (pat1, (t, FStar_Pervasives_Native.Some tac)) ->
                  let uu___3 =
                    let uu___4 =
                      let uu___5 =
                        let uu___6 =
                          let uu___7 =
                            let uu___8 = str "by" in
                            let uu___9 =
                              let uu___10 = p_atomicTerm (maybe_unthunk tac) in
                              FStar_Pprint.op_Hat_Hat FStar_Pprint.space
                                uu___10 in
                            FStar_Pprint.op_Hat_Hat uu___8 uu___9 in
                          FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu___7 in
                        FStar_Pprint.group uu___6 in
                      (t, uu___5) in
                    FStar_Pervasives_Native.Some uu___4 in
                  (pat1, uu___3)
              | uu___3 -> (pat, FStar_Pervasives_Native.None) in
            (match uu___2 with
             | (pat1, ascr) ->
                 (match pat1.FStar_Parser_AST.pat with
                  | FStar_Parser_AST.PatApp
                      ({
                         FStar_Parser_AST.pat = FStar_Parser_AST.PatVar
                           (lid, uu___3, uu___4);
                         FStar_Parser_AST.prange = uu___5;_},
                       pats)
                      ->
                      let ascr_doc =
                        match ascr with
                        | FStar_Pervasives_Native.Some (t, tac) ->
                            let uu___6 = sig_as_binders_if_possible t true in
                            FStar_Pprint.op_Hat_Hat uu___6 tac
                        | FStar_Pervasives_Native.None -> FStar_Pprint.empty in
                      let uu___6 =
                        if inner_let
                        then
                          let uu___7 = pats_as_binders_if_possible pats in
                          match uu___7 with
                          | (bs, style) ->
                              ((FStar_List.append bs [ascr_doc]), style)
                        else
                          (let uu___8 = pats_as_binders_if_possible pats in
                           match uu___8 with
                           | (bs, style) ->
                               ((FStar_List.append bs [ascr_doc]), style)) in
                      (match uu___6 with
                       | (terms, style) ->
                           let uu___7 =
                             let uu___8 =
                               let uu___9 =
                                 let uu___10 = p_lident lid in
                                 let uu___11 =
                                   format_sig style terms true true in
                                 FStar_Pprint.op_Hat_Hat uu___10 uu___11 in
                               FStar_Pprint.op_Hat_Hat FStar_Pprint.space
                                 uu___9 in
                             FStar_Pprint.op_Hat_Hat kw uu___8 in
                           FStar_All.pipe_left FStar_Pprint.group uu___7)
                  | uu___3 ->
                      let ascr_doc =
                        match ascr with
                        | FStar_Pervasives_Native.Some (t, tac) ->
                            let uu___4 =
                              let uu___5 =
                                let uu___6 =
                                  p_typ_top
                                    (Arrows
                                       ((Prims.of_int (2)),
                                         (Prims.of_int (2)))) false false t in
                                FStar_Pprint.op_Hat_Hat FStar_Pprint.colon
                                  uu___6 in
                              FStar_Pprint.group uu___5 in
                            FStar_Pprint.op_Hat_Hat uu___4 tac
                        | FStar_Pervasives_Native.None -> FStar_Pprint.empty in
                      let uu___4 =
                        let uu___5 =
                          let uu___6 =
                            let uu___7 = p_tuplePattern pat1 in
                            FStar_Pprint.op_Hat_Slash_Hat kw uu___7 in
                          FStar_Pprint.group uu___6 in
                        FStar_Pprint.op_Hat_Hat uu___5 ascr_doc in
                      FStar_Pprint.group uu___4))
and (p_letbinding :
  FStar_Pprint.document ->
    (FStar_Parser_AST.pattern * FStar_Parser_AST.term) ->
      FStar_Pprint.document)
  =
  fun kw ->
    fun uu___ ->
      match uu___ with
      | (pat, e) ->
          let doc_pat = p_letlhs kw (pat, e) false in
          let uu___1 = p_term_sep false false e in
          (match uu___1 with
           | (comm, doc_expr) ->
               let doc_expr1 =
                 inline_comment_or_above comm doc_expr FStar_Pprint.empty in
               let uu___2 =
                 let uu___3 =
                   FStar_Pprint.op_Hat_Slash_Hat FStar_Pprint.equals
                     doc_expr1 in
                 FStar_Pprint.op_Hat_Slash_Hat doc_pat uu___3 in
               let uu___3 =
                 let uu___4 =
                   let uu___5 =
                     let uu___6 =
                       let uu___7 = jump2 doc_expr1 in
                       FStar_Pprint.op_Hat_Hat FStar_Pprint.equals uu___7 in
                     FStar_Pprint.group uu___6 in
                   FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu___5 in
                 FStar_Pprint.op_Hat_Hat doc_pat uu___4 in
               FStar_Pprint.ifflat uu___2 uu___3)
and (p_term_list :
  Prims.bool ->
    Prims.bool -> FStar_Parser_AST.term Prims.list -> FStar_Pprint.document)
  =
  fun ps ->
    fun pb ->
      fun l ->
        let rec aux uu___ =
          match uu___ with
          | [] -> FStar_Pprint.empty
          | x::[] -> p_term ps pb x
          | x::xs ->
              let uu___1 = p_term ps pb x in
              let uu___2 =
                let uu___3 = str ";" in
                let uu___4 = aux xs in FStar_Pprint.op_Hat_Hat uu___3 uu___4 in
              FStar_Pprint.op_Hat_Hat uu___1 uu___2 in
        let uu___ = str "[" in
        let uu___1 =
          let uu___2 = aux l in
          let uu___3 = str "]" in FStar_Pprint.op_Hat_Hat uu___2 uu___3 in
        FStar_Pprint.op_Hat_Hat uu___ uu___1
and (p_newEffect : FStar_Parser_AST.effect_decl -> FStar_Pprint.document) =
  fun uu___ ->
    match uu___ with
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
        let uu___ = p_uident uid in
        let uu___1 = p_binders true bs in
        let uu___2 =
          let uu___3 = p_simpleTerm false false t in
          prefix2 FStar_Pprint.equals uu___3 in
        surround_maybe_empty (Prims.of_int (2)) Prims.int_one uu___ uu___1
          uu___2
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
          let uu___ =
            let uu___1 =
              let uu___2 =
                let uu___3 = p_uident uid in
                let uu___4 = p_binders true bs in
                let uu___5 =
                  let uu___6 = p_typ false false t in
                  prefix2 FStar_Pprint.colon uu___6 in
                surround_maybe_empty (Prims.of_int (2)) Prims.int_one uu___3
                  uu___4 uu___5 in
              FStar_Pprint.group uu___2 in
            let uu___2 =
              let uu___3 = str "with" in
              let uu___4 =
                let uu___5 =
                  let uu___6 =
                    let uu___7 =
                      let uu___8 =
                        let uu___9 =
                          FStar_Pprint.op_Hat_Hat FStar_Pprint.semi
                            FStar_Pprint.space in
                        FStar_Pprint.op_Hat_Hat FStar_Pprint.hardline uu___9 in
                      separate_map_last uu___8 p_effectDecl eff_decls in
                    FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu___7 in
                  FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu___6 in
                FStar_Pprint.op_Hat_Hat FStar_Pprint.hardline uu___5 in
              FStar_Pprint.op_Hat_Hat uu___3 uu___4 in
            FStar_Pprint.op_Hat_Slash_Hat uu___1 uu___2 in
          braces_with_nesting uu___
and (p_effectDecl :
  Prims.bool -> FStar_Parser_AST.decl -> FStar_Pprint.document) =
  fun ps ->
    fun d ->
      match d.FStar_Parser_AST.d with
      | FStar_Parser_AST.Tycon
          (false, uu___, (FStar_Parser_AST.TyconAbbrev
           (lid, [], FStar_Pervasives_Native.None, e))::[])
          ->
          let uu___1 =
            let uu___2 = p_lident lid in
            let uu___3 =
              FStar_Pprint.op_Hat_Hat FStar_Pprint.space FStar_Pprint.equals in
            FStar_Pprint.op_Hat_Hat uu___2 uu___3 in
          let uu___2 = p_simpleTerm ps false e in prefix2 uu___1 uu___2
      | uu___ ->
          let uu___1 =
            let uu___2 = FStar_Parser_AST.decl_to_string d in
            FStar_Util.format1
              "Not a declaration of an effect member... or at least I hope so : %s"
              uu___2 in
          failwith uu___1
and (p_subEffect : FStar_Parser_AST.lift -> FStar_Pprint.document) =
  fun lift ->
    let lift_op_doc =
      let lifts =
        match lift.FStar_Parser_AST.lift_op with
        | FStar_Parser_AST.NonReifiableLift t -> [("lift_wp", t)]
        | FStar_Parser_AST.ReifiableLift (t1, t2) ->
            [("lift_wp", t1); ("lift", t2)]
        | FStar_Parser_AST.LiftForFree t -> [("lift", t)] in
      let p_lift ps uu___ =
        match uu___ with
        | (kwd, t) ->
            let uu___1 =
              let uu___2 = str kwd in
              let uu___3 =
                FStar_Pprint.op_Hat_Hat FStar_Pprint.space
                  FStar_Pprint.equals in
              FStar_Pprint.op_Hat_Hat uu___2 uu___3 in
            let uu___2 = p_simpleTerm ps false t in prefix2 uu___1 uu___2 in
      separate_break_map_last FStar_Pprint.semi p_lift lifts in
    let uu___ =
      let uu___1 =
        let uu___2 = p_quident lift.FStar_Parser_AST.msource in
        let uu___3 =
          let uu___4 = str "~>" in
          FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu___4 in
        FStar_Pprint.op_Hat_Hat uu___2 uu___3 in
      let uu___2 = p_quident lift.FStar_Parser_AST.mdest in
      prefix2 uu___1 uu___2 in
    let uu___1 =
      let uu___2 = braces_with_nesting lift_op_doc in
      FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu___2 in
    FStar_Pprint.op_Hat_Hat uu___ uu___1
and (p_qualifier : FStar_Parser_AST.qualifier -> FStar_Pprint.document) =
  fun uu___ ->
    match uu___ with
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
        let uu___ = p_qualifier q in
        FStar_Pprint.op_Hat_Hat uu___ FStar_Pprint.hardline
    | uu___ ->
        let uu___1 =
          let uu___2 = FStar_List.map p_qualifier qs in
          FStar_Pprint.flow break1 uu___2 in
        FStar_Pprint.op_Hat_Hat uu___1 FStar_Pprint.hardline
and (p_letqualifier :
  FStar_Parser_AST.let_qualifier -> FStar_Pprint.document) =
  fun uu___ ->
    match uu___ with
    | FStar_Parser_AST.Rec ->
        let uu___1 = str "rec" in
        FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu___1
    | FStar_Parser_AST.NoLetQualifier -> FStar_Pprint.empty
and (p_aqual : FStar_Parser_AST.arg_qualifier -> FStar_Pprint.document) =
  fun uu___ ->
    match uu___ with
    | FStar_Parser_AST.Implicit -> str "#"
    | FStar_Parser_AST.Equality -> str "$"
    | FStar_Parser_AST.Meta t ->
        let t1 =
          match t.FStar_Parser_AST.tm with
          | FStar_Parser_AST.Abs (uu___1, e) -> e
          | uu___1 ->
              FStar_Parser_AST.mk_term
                (FStar_Parser_AST.App
                   (t,
                     (FStar_Parser_AST.unit_const t.FStar_Parser_AST.range),
                     FStar_Parser_AST.Nothing)) t.FStar_Parser_AST.range
                FStar_Parser_AST.Expr in
        let uu___1 = str "#[" in
        let uu___2 =
          let uu___3 = p_term false false t1 in
          let uu___4 =
            let uu___5 = str "]" in FStar_Pprint.op_Hat_Hat uu___5 break1 in
          FStar_Pprint.op_Hat_Hat uu___3 uu___4 in
        FStar_Pprint.op_Hat_Hat uu___1 uu___2
and (p_disjunctivePattern :
  FStar_Parser_AST.pattern -> FStar_Pprint.document) =
  fun p ->
    match p.FStar_Parser_AST.pat with
    | FStar_Parser_AST.PatOr pats ->
        let uu___ =
          let uu___1 =
            let uu___2 =
              FStar_Pprint.op_Hat_Hat FStar_Pprint.bar FStar_Pprint.space in
            FStar_Pprint.op_Hat_Hat break1 uu___2 in
          FStar_Pprint.separate_map uu___1 p_tuplePattern pats in
        FStar_Pprint.group uu___
    | uu___ -> p_tuplePattern p
and (p_tuplePattern : FStar_Parser_AST.pattern -> FStar_Pprint.document) =
  fun p ->
    match p.FStar_Parser_AST.pat with
    | FStar_Parser_AST.PatTuple (pats, false) ->
        let uu___ =
          let uu___1 = FStar_Pprint.op_Hat_Hat FStar_Pprint.comma break1 in
          FStar_Pprint.separate_map uu___1 p_constructorPattern pats in
        FStar_Pprint.group uu___
    | uu___ -> p_constructorPattern p
and (p_constructorPattern :
  FStar_Parser_AST.pattern -> FStar_Pprint.document) =
  fun p ->
    match p.FStar_Parser_AST.pat with
    | FStar_Parser_AST.PatApp
        ({ FStar_Parser_AST.pat = FStar_Parser_AST.PatName maybe_cons_lid;
           FStar_Parser_AST.prange = uu___;_},
         hd::tl::[])
        when
        FStar_Ident.lid_equals maybe_cons_lid FStar_Parser_Const.cons_lid ->
        let uu___1 =
          FStar_Pprint.op_Hat_Hat FStar_Pprint.colon FStar_Pprint.colon in
        let uu___2 = p_constructorPattern hd in
        let uu___3 = p_constructorPattern tl in infix0 uu___1 uu___2 uu___3
    | FStar_Parser_AST.PatApp
        ({ FStar_Parser_AST.pat = FStar_Parser_AST.PatName uid;
           FStar_Parser_AST.prange = uu___;_},
         pats)
        ->
        let uu___1 = p_quident uid in
        let uu___2 = FStar_Pprint.separate_map break1 p_atomicPattern pats in
        prefix2 uu___1 uu___2
    | uu___ -> p_atomicPattern p
and (p_atomicPattern : FStar_Parser_AST.pattern -> FStar_Pprint.document) =
  fun p ->
    match p.FStar_Parser_AST.pat with
    | FStar_Parser_AST.PatAscribed (pat, (t, FStar_Pervasives_Native.None))
        ->
        (match ((pat.FStar_Parser_AST.pat), (t.FStar_Parser_AST.tm)) with
         | (FStar_Parser_AST.PatVar (lid, aqual, attrs),
            FStar_Parser_AST.Refine
            ({ FStar_Parser_AST.b = FStar_Parser_AST.Annotated (lid', t1);
               FStar_Parser_AST.brange = uu___;
               FStar_Parser_AST.blevel = uu___1;
               FStar_Parser_AST.aqual = uu___2;
               FStar_Parser_AST.battributes = uu___3;_},
             phi)) when
             let uu___4 = FStar_Ident.string_of_id lid in
             let uu___5 = FStar_Ident.string_of_id lid' in uu___4 = uu___5 ->
             let uu___4 =
               let uu___5 = p_ident lid in
               p_refinement aqual attrs uu___5 t1 phi in
             soft_parens_with_nesting uu___4
         | (FStar_Parser_AST.PatWild (aqual, attrs), FStar_Parser_AST.Refine
            ({ FStar_Parser_AST.b = FStar_Parser_AST.NoName t1;
               FStar_Parser_AST.brange = uu___;
               FStar_Parser_AST.blevel = uu___1;
               FStar_Parser_AST.aqual = uu___2;
               FStar_Parser_AST.battributes = uu___3;_},
             phi)) ->
             let uu___4 =
               p_refinement aqual attrs FStar_Pprint.underscore t1 phi in
             soft_parens_with_nesting uu___4
         | uu___ ->
             let uu___1 =
               let uu___2 = p_tuplePattern pat in
               let uu___3 =
                 let uu___4 = p_tmEqNoRefinement t in
                 FStar_Pprint.op_Hat_Slash_Hat FStar_Pprint.colon uu___4 in
               FStar_Pprint.op_Hat_Hat uu___2 uu___3 in
             soft_parens_with_nesting uu___1)
    | FStar_Parser_AST.PatList pats ->
        let uu___ = separate_break_map FStar_Pprint.semi p_tuplePattern pats in
        FStar_Pprint.surround (Prims.of_int (2)) Prims.int_zero
          FStar_Pprint.lbracket uu___ FStar_Pprint.rbracket
    | FStar_Parser_AST.PatRecord pats ->
        let p_recordFieldPat uu___ =
          match uu___ with
          | (lid, pat) ->
              let uu___1 = p_qlident lid in
              let uu___2 = p_tuplePattern pat in
              infix2 FStar_Pprint.equals uu___1 uu___2 in
        let uu___ =
          separate_break_map FStar_Pprint.semi p_recordFieldPat pats in
        soft_braces_with_nesting uu___
    | FStar_Parser_AST.PatTuple (pats, true) ->
        let uu___ =
          FStar_Pprint.op_Hat_Hat FStar_Pprint.lparen FStar_Pprint.bar in
        let uu___1 =
          separate_break_map FStar_Pprint.comma p_constructorPattern pats in
        let uu___2 =
          FStar_Pprint.op_Hat_Hat FStar_Pprint.bar FStar_Pprint.rparen in
        FStar_Pprint.surround (Prims.of_int (2)) Prims.int_one uu___ uu___1
          uu___2
    | FStar_Parser_AST.PatTvar (tv, arg_qualifier_opt, attrs) -> p_tvar tv
    | FStar_Parser_AST.PatOp op ->
        let uu___ =
          let uu___1 =
            let uu___2 =
              let uu___3 = FStar_Ident.string_of_id op in str uu___3 in
            let uu___3 =
              FStar_Pprint.op_Hat_Hat FStar_Pprint.space FStar_Pprint.rparen in
            FStar_Pprint.op_Hat_Hat uu___2 uu___3 in
          FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu___1 in
        FStar_Pprint.op_Hat_Hat FStar_Pprint.lparen uu___
    | FStar_Parser_AST.PatWild (aqual, attrs) ->
        let uu___ = FStar_Pprint.optional p_aqual aqual in
        let uu___1 =
          let uu___2 = p_attributes attrs in
          FStar_Pprint.op_Hat_Hat uu___2 FStar_Pprint.underscore in
        FStar_Pprint.op_Hat_Hat uu___ uu___1
    | FStar_Parser_AST.PatConst c -> p_constant c
    | FStar_Parser_AST.PatVar (lid, aqual, attrs) ->
        let uu___ = FStar_Pprint.optional p_aqual aqual in
        let uu___1 =
          let uu___2 = p_attributes attrs in
          let uu___3 = p_lident lid in FStar_Pprint.op_Hat_Hat uu___2 uu___3 in
        FStar_Pprint.op_Hat_Hat uu___ uu___1
    | FStar_Parser_AST.PatName uid -> p_quident uid
    | FStar_Parser_AST.PatOr uu___ -> failwith "Inner or pattern !"
    | FStar_Parser_AST.PatApp
        ({ FStar_Parser_AST.pat = FStar_Parser_AST.PatName uu___;
           FStar_Parser_AST.prange = uu___1;_},
         uu___2)
        -> let uu___3 = p_tuplePattern p in soft_parens_with_nesting uu___3
    | FStar_Parser_AST.PatTuple (uu___, false) ->
        let uu___1 = p_tuplePattern p in soft_parens_with_nesting uu___1
    | uu___ ->
        let uu___1 =
          let uu___2 = FStar_Parser_AST.pat_to_string p in
          FStar_Util.format1 "Invalid pattern %s" uu___2 in
        failwith uu___1
and (is_typ_tuple : FStar_Parser_AST.term -> Prims.bool) =
  fun e ->
    match e.FStar_Parser_AST.tm with
    | FStar_Parser_AST.Op (id, uu___) when
        let uu___1 = FStar_Ident.string_of_id id in uu___1 = "*" -> true
    | uu___ -> false
and (is_meta_qualifier :
  FStar_Parser_AST.arg_qualifier FStar_Pervasives_Native.option -> Prims.bool)
  =
  fun aq ->
    match aq with
    | FStar_Pervasives_Native.Some (FStar_Parser_AST.Meta uu___) -> true
    | uu___ -> false
and (p_binder :
  Prims.bool -> FStar_Parser_AST.binder -> FStar_Pprint.document) =
  fun is_atomic ->
    fun b ->
      let uu___ = p_binder' is_atomic b in
      match uu___ with
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
          let uu___ =
            let uu___1 =
              FStar_Pprint.optional p_aqual b.FStar_Parser_AST.aqual in
            let uu___2 = p_lident lid in
            FStar_Pprint.op_Hat_Hat uu___1 uu___2 in
          (uu___, FStar_Pervasives_Native.None, cat_with_colon)
      | FStar_Parser_AST.TVariable lid ->
          let uu___ = p_lident lid in
          (uu___, FStar_Pervasives_Native.None, cat_with_colon)
      | FStar_Parser_AST.Annotated (lid, t) ->
          let uu___ =
            match t.FStar_Parser_AST.tm with
            | FStar_Parser_AST.Refine
                ({
                   FStar_Parser_AST.b = FStar_Parser_AST.Annotated (lid', t1);
                   FStar_Parser_AST.brange = uu___1;
                   FStar_Parser_AST.blevel = uu___2;
                   FStar_Parser_AST.aqual = uu___3;
                   FStar_Parser_AST.battributes = uu___4;_},
                 phi)
                when
                let uu___5 = FStar_Ident.string_of_id lid in
                let uu___6 = FStar_Ident.string_of_id lid' in uu___5 = uu___6
                ->
                let uu___5 = p_lident lid in
                p_refinement' b.FStar_Parser_AST.aqual
                  b.FStar_Parser_AST.battributes uu___5 t1 phi
            | uu___1 ->
                let t' =
                  let uu___2 = is_typ_tuple t in
                  if uu___2
                  then
                    let uu___3 = p_tmFormula t in
                    soft_parens_with_nesting uu___3
                  else p_tmFormula t in
                let uu___2 =
                  let uu___3 =
                    FStar_Pprint.optional p_aqual b.FStar_Parser_AST.aqual in
                  let uu___4 = p_lident lid in
                  FStar_Pprint.op_Hat_Hat uu___3 uu___4 in
                (uu___2, t') in
          (match uu___ with
           | (b', t') ->
               let catf1 =
                 let uu___1 =
                   is_atomic || (is_meta_qualifier b.FStar_Parser_AST.aqual) in
                 if uu___1
                 then
                   fun x ->
                     fun y ->
                       let uu___2 =
                         let uu___3 =
                           let uu___4 = cat_with_colon x y in
                           FStar_Pprint.op_Hat_Hat uu___4 FStar_Pprint.rparen in
                         FStar_Pprint.op_Hat_Hat FStar_Pprint.lparen uu___3 in
                       FStar_Pprint.group uu___2
                 else
                   (fun x ->
                      fun y ->
                        let uu___3 = cat_with_colon x y in
                        FStar_Pprint.group uu___3) in
               (b', (FStar_Pervasives_Native.Some t'), catf1))
      | FStar_Parser_AST.TAnnotated uu___ -> failwith "Is this still used ?"
      | FStar_Parser_AST.NoName t ->
          (match t.FStar_Parser_AST.tm with
           | FStar_Parser_AST.Refine
               ({ FStar_Parser_AST.b = FStar_Parser_AST.NoName t1;
                  FStar_Parser_AST.brange = uu___;
                  FStar_Parser_AST.blevel = uu___1;
                  FStar_Parser_AST.aqual = uu___2;
                  FStar_Parser_AST.battributes = uu___3;_},
                phi)
               ->
               let uu___4 =
                 p_refinement' b.FStar_Parser_AST.aqual
                   b.FStar_Parser_AST.battributes FStar_Pprint.underscore t1
                   phi in
               (match uu___4 with
                | (b', t') ->
                    (b', (FStar_Pervasives_Native.Some t'), cat_with_colon))
           | uu___ ->
               if is_atomic
               then
                 let uu___1 = p_atomicTerm t in
                 (uu___1, FStar_Pervasives_Native.None, cat_with_colon)
               else
                 (let uu___2 = p_appTerm t in
                  (uu___2, FStar_Pervasives_Native.None, cat_with_colon)))
and (p_refinement :
  FStar_Parser_AST.arg_qualifier FStar_Pervasives_Native.option ->
    FStar_Parser_AST.term Prims.list ->
      FStar_Pprint.document ->
        FStar_Parser_AST.term ->
          FStar_Parser_AST.term -> FStar_Pprint.document)
  =
  fun aqual_opt ->
    fun attrs ->
      fun binder ->
        fun t ->
          fun phi ->
            let uu___ = p_refinement' aqual_opt attrs binder t phi in
            match uu___ with | (b, typ) -> cat_with_colon b typ
and (p_refinement' :
  FStar_Parser_AST.arg_qualifier FStar_Pervasives_Native.option ->
    FStar_Parser_AST.term Prims.list ->
      FStar_Pprint.document ->
        FStar_Parser_AST.term ->
          FStar_Parser_AST.term ->
            (FStar_Pprint.document * FStar_Pprint.document))
  =
  fun aqual_opt ->
    fun attrs ->
      fun binder ->
        fun t ->
          fun phi ->
            let is_t_atomic =
              match t.FStar_Parser_AST.tm with
              | FStar_Parser_AST.Construct uu___ -> false
              | FStar_Parser_AST.App uu___ -> false
              | FStar_Parser_AST.Op uu___ -> false
              | uu___ -> true in
            let uu___ = p_noSeqTerm false false phi in
            match uu___ with
            | (comm, phi1) ->
                let phi2 =
                  if comm = FStar_Pprint.empty
                  then phi1
                  else
                    (let uu___2 =
                       FStar_Pprint.op_Hat_Hat FStar_Pprint.hardline phi1 in
                     FStar_Pprint.op_Hat_Hat comm uu___2) in
                let jump_break =
                  if is_t_atomic then Prims.int_zero else Prims.int_one in
                let uu___1 =
                  let uu___2 = FStar_Pprint.optional p_aqual aqual_opt in
                  let uu___3 =
                    let uu___4 = p_attributes attrs in
                    FStar_Pprint.op_Hat_Hat uu___4 binder in
                  FStar_Pprint.op_Hat_Hat uu___2 uu___3 in
                let uu___2 =
                  let uu___3 = p_appTerm t in
                  let uu___4 =
                    let uu___5 =
                      let uu___6 =
                        let uu___7 = soft_braces_with_nesting_tight phi2 in
                        let uu___8 = soft_braces_with_nesting phi2 in
                        FStar_Pprint.ifflat uu___7 uu___8 in
                      FStar_Pprint.group uu___6 in
                    FStar_Pprint.jump (Prims.of_int (2)) jump_break uu___5 in
                  FStar_Pprint.op_Hat_Hat uu___3 uu___4 in
                (uu___1, uu___2)
and (p_binders_list :
  Prims.bool ->
    FStar_Parser_AST.binder Prims.list -> FStar_Pprint.document Prims.list)
  = fun is_atomic -> fun bs -> FStar_List.map (p_binder is_atomic) bs
and (p_binders :
  Prims.bool -> FStar_Parser_AST.binder Prims.list -> FStar_Pprint.document)
  =
  fun is_atomic ->
    fun bs ->
      let uu___ = p_binders_list is_atomic bs in
      separate_or_flow break1 uu___
and (string_of_id_or_underscore : FStar_Ident.ident -> FStar_Pprint.document)
  =
  fun lid ->
    let uu___ =
      (let uu___1 = FStar_Ident.string_of_id lid in
       FStar_Util.starts_with uu___1 FStar_Ident.reserved_prefix) &&
        (let uu___1 = FStar_Options.print_real_names () in
         Prims.op_Negation uu___1) in
    if uu___
    then FStar_Pprint.underscore
    else (let uu___2 = FStar_Ident.string_of_id lid in str uu___2)
and (text_of_lid_or_underscore : FStar_Ident.lident -> FStar_Pprint.document)
  =
  fun lid ->
    let uu___ =
      (let uu___1 =
         let uu___2 = FStar_Ident.ident_of_lid lid in
         FStar_Ident.string_of_id uu___2 in
       FStar_Util.starts_with uu___1 FStar_Ident.reserved_prefix) &&
        (let uu___1 = FStar_Options.print_real_names () in
         Prims.op_Negation uu___1) in
    if uu___
    then FStar_Pprint.underscore
    else (let uu___2 = FStar_Ident.string_of_lid lid in str uu___2)
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
          let uu___ = FStar_Pprint.op_Hat_Hat doc sep in
          FStar_Pprint.group uu___
        else
          (let uu___1 =
             let uu___2 =
               let uu___3 =
                 let uu___4 =
                   let uu___5 = FStar_Pprint.op_Hat_Hat break1 comm in
                   FStar_Pprint.op_Hat_Hat sep uu___5 in
                 FStar_Pprint.op_Hat_Hat doc uu___4 in
               FStar_Pprint.group uu___3 in
             let uu___3 =
               let uu___4 =
                 let uu___5 = FStar_Pprint.op_Hat_Hat doc sep in
                 FStar_Pprint.op_Hat_Hat FStar_Pprint.hardline uu___5 in
               FStar_Pprint.op_Hat_Hat comm uu___4 in
             FStar_Pprint.ifflat uu___2 uu___3 in
           FStar_All.pipe_left FStar_Pprint.group uu___1)
and (p_term :
  Prims.bool -> Prims.bool -> FStar_Parser_AST.term -> FStar_Pprint.document)
  =
  fun ps ->
    fun pb ->
      fun e ->
        match e.FStar_Parser_AST.tm with
        | FStar_Parser_AST.Seq (e1, e2) ->
            let uu___ = p_noSeqTerm true false e1 in
            (match uu___ with
             | (comm, t1) ->
                 let uu___1 =
                   inline_comment_or_above comm t1 FStar_Pprint.semi in
                 let uu___2 =
                   let uu___3 = p_term ps pb e2 in
                   FStar_Pprint.op_Hat_Hat FStar_Pprint.hardline uu___3 in
                 FStar_Pprint.op_Hat_Hat uu___1 uu___2)
        | FStar_Parser_AST.Bind (x, e1, e2) ->
            let uu___ =
              let uu___1 =
                let uu___2 =
                  let uu___3 = p_lident x in
                  let uu___4 =
                    FStar_Pprint.op_Hat_Hat FStar_Pprint.space
                      FStar_Pprint.long_left_arrow in
                  FStar_Pprint.op_Hat_Hat uu___3 uu___4 in
                let uu___3 =
                  let uu___4 = p_noSeqTermAndComment true false e1 in
                  let uu___5 =
                    FStar_Pprint.op_Hat_Hat FStar_Pprint.space
                      FStar_Pprint.semi in
                  FStar_Pprint.op_Hat_Hat uu___4 uu___5 in
                op_Hat_Slash_Plus_Hat uu___2 uu___3 in
              FStar_Pprint.group uu___1 in
            let uu___1 = p_term ps pb e2 in
            FStar_Pprint.op_Hat_Slash_Hat uu___ uu___1
        | uu___ ->
            let uu___1 = p_noSeqTermAndComment ps pb e in
            FStar_Pprint.group uu___1
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
            let uu___ = p_noSeqTerm true false e1 in
            (match uu___ with
             | (comm, t1) ->
                 let uu___1 =
                   let uu___2 =
                     let uu___3 =
                       FStar_Pprint.op_Hat_Hat t1 FStar_Pprint.semi in
                     FStar_Pprint.group uu___3 in
                   let uu___3 =
                     let uu___4 = p_term ps pb e2 in
                     FStar_Pprint.op_Hat_Hat FStar_Pprint.hardline uu___4 in
                   FStar_Pprint.op_Hat_Hat uu___2 uu___3 in
                 (comm, uu___1))
        | FStar_Parser_AST.Bind (x, e1, e2) ->
            let uu___ =
              let uu___1 =
                let uu___2 =
                  let uu___3 =
                    let uu___4 = p_lident x in
                    let uu___5 =
                      FStar_Pprint.op_Hat_Hat FStar_Pprint.space
                        FStar_Pprint.long_left_arrow in
                    FStar_Pprint.op_Hat_Hat uu___4 uu___5 in
                  let uu___4 =
                    let uu___5 = p_noSeqTermAndComment true false e1 in
                    let uu___6 =
                      FStar_Pprint.op_Hat_Hat FStar_Pprint.space
                        FStar_Pprint.semi in
                    FStar_Pprint.op_Hat_Hat uu___5 uu___6 in
                  op_Hat_Slash_Plus_Hat uu___3 uu___4 in
                FStar_Pprint.group uu___2 in
              let uu___2 = p_term ps pb e2 in
              FStar_Pprint.op_Hat_Slash_Hat uu___1 uu___2 in
            (FStar_Pprint.empty, uu___)
        | uu___ -> p_noSeqTerm ps pb e
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
            let uu___ =
              let uu___1 = p_tmIff e1 in
              let uu___2 =
                let uu___3 =
                  let uu___4 = p_typ ps pb t in
                  FStar_Pprint.op_Hat_Slash_Hat FStar_Pprint.colon uu___4 in
                FStar_Pprint.op_Hat_Hat FStar_Pprint.langle uu___3 in
              FStar_Pprint.op_Hat_Slash_Hat uu___1 uu___2 in
            FStar_Pprint.group uu___
        | FStar_Parser_AST.Ascribed (e1, t, FStar_Pervasives_Native.Some tac)
            ->
            let uu___ =
              let uu___1 = p_tmIff e1 in
              let uu___2 =
                let uu___3 =
                  let uu___4 =
                    let uu___5 = p_typ false false t in
                    let uu___6 =
                      let uu___7 = str "by" in
                      let uu___8 = p_typ ps pb (maybe_unthunk tac) in
                      FStar_Pprint.op_Hat_Slash_Hat uu___7 uu___8 in
                    FStar_Pprint.op_Hat_Slash_Hat uu___5 uu___6 in
                  FStar_Pprint.op_Hat_Slash_Hat FStar_Pprint.colon uu___4 in
                FStar_Pprint.op_Hat_Hat FStar_Pprint.langle uu___3 in
              FStar_Pprint.op_Hat_Slash_Hat uu___1 uu___2 in
            FStar_Pprint.group uu___
        | FStar_Parser_AST.Op (id, e1::e2::e3::[]) when
            let uu___ = FStar_Ident.string_of_id id in uu___ = ".()<-" ->
            let uu___ =
              let uu___1 =
                let uu___2 =
                  let uu___3 = p_atomicTermNotQUident e1 in
                  let uu___4 =
                    let uu___5 =
                      let uu___6 =
                        let uu___7 = p_term false false e2 in
                        soft_parens_with_nesting uu___7 in
                      let uu___7 =
                        FStar_Pprint.op_Hat_Hat FStar_Pprint.space
                          FStar_Pprint.larrow in
                      FStar_Pprint.op_Hat_Hat uu___6 uu___7 in
                    FStar_Pprint.op_Hat_Hat FStar_Pprint.dot uu___5 in
                  FStar_Pprint.op_Hat_Hat uu___3 uu___4 in
                FStar_Pprint.group uu___2 in
              let uu___2 =
                let uu___3 = p_noSeqTermAndComment ps pb e3 in jump2 uu___3 in
              FStar_Pprint.op_Hat_Hat uu___1 uu___2 in
            FStar_Pprint.group uu___
        | FStar_Parser_AST.Op (id, e1::e2::e3::[]) when
            let uu___ = FStar_Ident.string_of_id id in uu___ = ".[]<-" ->
            let uu___ =
              let uu___1 =
                let uu___2 =
                  let uu___3 = p_atomicTermNotQUident e1 in
                  let uu___4 =
                    let uu___5 =
                      let uu___6 =
                        let uu___7 = p_term false false e2 in
                        soft_brackets_with_nesting uu___7 in
                      let uu___7 =
                        FStar_Pprint.op_Hat_Hat FStar_Pprint.space
                          FStar_Pprint.larrow in
                      FStar_Pprint.op_Hat_Hat uu___6 uu___7 in
                    FStar_Pprint.op_Hat_Hat FStar_Pprint.dot uu___5 in
                  FStar_Pprint.op_Hat_Hat uu___3 uu___4 in
                FStar_Pprint.group uu___2 in
              let uu___2 =
                let uu___3 = p_noSeqTermAndComment ps pb e3 in jump2 uu___3 in
              FStar_Pprint.op_Hat_Hat uu___1 uu___2 in
            FStar_Pprint.group uu___
        | FStar_Parser_AST.Requires (e1, wtf) ->
            let uu___1 =
              let uu___2 = str "requires" in
              let uu___3 = p_typ ps pb e1 in
              FStar_Pprint.op_Hat_Slash_Hat uu___2 uu___3 in
            FStar_Pprint.group uu___1
        | FStar_Parser_AST.Ensures (e1, wtf) ->
            let uu___1 =
              let uu___2 = str "ensures" in
              let uu___3 = p_typ ps pb e1 in
              FStar_Pprint.op_Hat_Slash_Hat uu___2 uu___3 in
            FStar_Pprint.group uu___1
        | FStar_Parser_AST.WFOrder (rel, e1) -> p_dec_wf ps pb rel e1
        | FStar_Parser_AST.LexList l ->
            let uu___ =
              let uu___1 = str "%" in
              let uu___2 = p_term_list ps pb l in
              FStar_Pprint.op_Hat_Hat uu___1 uu___2 in
            FStar_Pprint.group uu___
        | FStar_Parser_AST.Decreases (e1, wtf) ->
            let uu___1 =
              let uu___2 = str "decreases" in
              let uu___3 = p_typ ps pb e1 in
              FStar_Pprint.op_Hat_Slash_Hat uu___2 uu___3 in
            FStar_Pprint.group uu___1
        | FStar_Parser_AST.Attributes es ->
            let uu___ =
              let uu___1 = str "attributes" in
              let uu___2 = FStar_Pprint.separate_map break1 p_atomicTerm es in
              FStar_Pprint.op_Hat_Slash_Hat uu___1 uu___2 in
            FStar_Pprint.group uu___
        | FStar_Parser_AST.If (e1, ret_opt, e2, e3) ->
            if is_unit e3
            then
              let uu___ =
                let uu___1 =
                  let uu___2 = str "if" in
                  let uu___3 = p_noSeqTermAndComment false false e1 in
                  op_Hat_Slash_Plus_Hat uu___2 uu___3 in
                let uu___2 =
                  let uu___3 = str "then" in
                  let uu___4 = p_noSeqTermAndComment ps pb e2 in
                  op_Hat_Slash_Plus_Hat uu___3 uu___4 in
                FStar_Pprint.op_Hat_Slash_Hat uu___1 uu___2 in
              FStar_Pprint.group uu___
            else
              (let e2_doc =
                 match e2.FStar_Parser_AST.tm with
                 | FStar_Parser_AST.If (uu___1, uu___2, uu___3, e31) when
                     is_unit e31 ->
                     let uu___4 = p_noSeqTermAndComment false false e2 in
                     soft_parens_with_nesting uu___4
                 | uu___1 -> p_noSeqTermAndComment false false e2 in
               match ret_opt with
               | FStar_Pervasives_Native.None ->
                   let uu___1 =
                     let uu___2 =
                       let uu___3 = str "if" in
                       let uu___4 = p_noSeqTermAndComment false false e1 in
                       op_Hat_Slash_Plus_Hat uu___3 uu___4 in
                     let uu___3 =
                       let uu___4 =
                         let uu___5 = str "then" in
                         op_Hat_Slash_Plus_Hat uu___5 e2_doc in
                       let uu___5 =
                         let uu___6 = str "else" in
                         let uu___7 = p_noSeqTermAndComment ps pb e3 in
                         op_Hat_Slash_Plus_Hat uu___6 uu___7 in
                       FStar_Pprint.op_Hat_Slash_Hat uu___4 uu___5 in
                     FStar_Pprint.op_Hat_Slash_Hat uu___2 uu___3 in
                   FStar_Pprint.group uu___1
               | FStar_Pervasives_Native.Some ret ->
                   let uu___1 =
                     let uu___2 =
                       let uu___3 = str "if" in
                       let uu___4 = p_noSeqTermAndComment false false e1 in
                       op_Hat_Slash_Plus_Hat uu___3 uu___4 in
                     let uu___3 =
                       let uu___4 =
                         let uu___5 = str "ret" in
                         let uu___6 = p_tmIff ret in
                         op_Hat_Slash_Plus_Hat uu___5 uu___6 in
                       let uu___5 =
                         let uu___6 =
                           let uu___7 = str "then" in
                           op_Hat_Slash_Plus_Hat uu___7 e2_doc in
                         let uu___7 =
                           let uu___8 = str "else" in
                           let uu___9 = p_noSeqTermAndComment ps pb e3 in
                           op_Hat_Slash_Plus_Hat uu___8 uu___9 in
                         FStar_Pprint.op_Hat_Slash_Hat uu___6 uu___7 in
                       FStar_Pprint.op_Hat_Slash_Hat uu___4 uu___5 in
                     FStar_Pprint.op_Hat_Slash_Hat uu___2 uu___3 in
                   FStar_Pprint.group uu___1)
        | FStar_Parser_AST.TryWith (e1, branches) ->
            let uu___ =
              let uu___1 =
                let uu___2 =
                  let uu___3 = str "try" in
                  let uu___4 = p_noSeqTermAndComment false false e1 in
                  prefix2 uu___3 uu___4 in
                let uu___3 =
                  let uu___4 = str "with" in
                  let uu___5 =
                    separate_map_last FStar_Pprint.hardline p_patternBranch
                      branches in
                  FStar_Pprint.op_Hat_Slash_Hat uu___4 uu___5 in
                FStar_Pprint.op_Hat_Slash_Hat uu___2 uu___3 in
              FStar_Pprint.group uu___1 in
            let uu___1 = paren_if (ps || pb) in uu___1 uu___
        | FStar_Parser_AST.Match (e1, ret_opt, branches) ->
            let uu___ =
              let uu___1 =
                match ret_opt with
                | FStar_Pervasives_Native.None ->
                    let uu___2 =
                      let uu___3 = str "match" in
                      let uu___4 = p_noSeqTermAndComment false false e1 in
                      let uu___5 = str "with" in
                      FStar_Pprint.surround (Prims.of_int (2)) Prims.int_one
                        uu___3 uu___4 uu___5 in
                    FStar_Pprint.group uu___2
                | FStar_Pervasives_Native.Some ret ->
                    let uu___2 =
                      let uu___3 = str "match" in
                      let uu___4 =
                        let uu___5 = p_noSeqTermAndComment false false e1 in
                        let uu___6 =
                          let uu___7 = str "returns" in
                          let uu___8 = p_tmIff ret in
                          op_Hat_Slash_Plus_Hat uu___7 uu___8 in
                        op_Hat_Slash_Plus_Hat uu___5 uu___6 in
                      let uu___5 = str "with" in
                      FStar_Pprint.surround (Prims.of_int (2)) Prims.int_one
                        uu___3 uu___4 uu___5 in
                    FStar_Pprint.group uu___2 in
              let uu___2 =
                separate_map_last FStar_Pprint.hardline p_patternBranch
                  branches in
              FStar_Pprint.op_Hat_Slash_Hat uu___1 uu___2 in
            let uu___1 = paren_if (ps || pb) in uu___1 uu___
        | FStar_Parser_AST.LetOpen (uid, e1) ->
            let uu___ =
              let uu___1 =
                let uu___2 =
                  let uu___3 = str "let open" in
                  let uu___4 = p_quident uid in
                  let uu___5 = str "in" in
                  FStar_Pprint.surround (Prims.of_int (2)) Prims.int_one
                    uu___3 uu___4 uu___5 in
                let uu___3 = p_term false pb e1 in
                FStar_Pprint.op_Hat_Slash_Hat uu___2 uu___3 in
              FStar_Pprint.group uu___1 in
            let uu___1 = paren_if ps in uu___1 uu___
        | FStar_Parser_AST.LetOpenRecord (r, rty, e1) ->
            let uu___ =
              let uu___1 =
                let uu___2 =
                  let uu___3 = str "let open" in
                  let uu___4 = p_term false pb r in
                  let uu___5 = str "as" in
                  FStar_Pprint.surround (Prims.of_int (2)) Prims.int_one
                    uu___3 uu___4 uu___5 in
                let uu___3 =
                  let uu___4 = p_term false pb rty in
                  let uu___5 =
                    let uu___6 = str "in" in
                    let uu___7 = p_term false pb e1 in
                    FStar_Pprint.op_Hat_Slash_Hat uu___6 uu___7 in
                  FStar_Pprint.op_Hat_Slash_Hat uu___4 uu___5 in
                FStar_Pprint.op_Hat_Slash_Hat uu___2 uu___3 in
              FStar_Pprint.group uu___1 in
            let uu___1 = paren_if ps in uu___1 uu___
        | FStar_Parser_AST.Let (q, lbs, e1) ->
            let p_lb q1 uu___ is_last =
              match uu___ with
              | (a, (pat, e2)) ->
                  let attrs = p_attrs_opt a in
                  let doc_let_or_and =
                    match q1 with
                    | FStar_Pervasives_Native.Some (FStar_Parser_AST.Rec) ->
                        let uu___1 =
                          let uu___2 = str "let" in
                          let uu___3 = str "rec" in
                          FStar_Pprint.op_Hat_Slash_Hat uu___2 uu___3 in
                        FStar_Pprint.group uu___1
                    | FStar_Pervasives_Native.Some
                        (FStar_Parser_AST.NoLetQualifier) -> str "let"
                    | uu___1 -> str "and" in
                  let doc_pat = p_letlhs doc_let_or_and (pat, e2) true in
                  let uu___1 = p_term_sep false false e2 in
                  (match uu___1 with
                   | (comm, doc_expr) ->
                       let doc_expr1 =
                         inline_comment_or_above comm doc_expr
                           FStar_Pprint.empty in
                       let uu___2 =
                         if is_last
                         then
                           let uu___3 =
                             FStar_Pprint.flow break1
                               [doc_pat; FStar_Pprint.equals] in
                           let uu___4 = str "in" in
                           FStar_Pprint.surround (Prims.of_int (2))
                             Prims.int_one uu___3 doc_expr1 uu___4
                         else
                           (let uu___4 =
                              FStar_Pprint.flow break1
                                [doc_pat; FStar_Pprint.equals; doc_expr1] in
                            FStar_Pprint.hang (Prims.of_int (2)) uu___4) in
                       FStar_Pprint.op_Hat_Hat attrs uu___2) in
            let l = FStar_List.length lbs in
            let lbs_docs =
              FStar_List.mapi
                (fun i ->
                   fun lb ->
                     if i = Prims.int_zero
                     then
                       let uu___ =
                         p_lb (FStar_Pervasives_Native.Some q) lb
                           (i = (l - Prims.int_one)) in
                       FStar_Pprint.group uu___
                     else
                       (let uu___1 =
                          p_lb FStar_Pervasives_Native.None lb
                            (i = (l - Prims.int_one)) in
                        FStar_Pprint.group uu___1)) lbs in
            let lbs_doc =
              let uu___ = FStar_Pprint.separate break1 lbs_docs in
              FStar_Pprint.group uu___ in
            let uu___ =
              let uu___1 =
                let uu___2 =
                  let uu___3 = p_term false pb e1 in
                  FStar_Pprint.op_Hat_Hat FStar_Pprint.hardline uu___3 in
                FStar_Pprint.op_Hat_Hat lbs_doc uu___2 in
              FStar_Pprint.group uu___1 in
            let uu___1 = paren_if ps in uu___1 uu___
        | FStar_Parser_AST.Abs
            ({
               FStar_Parser_AST.pat = FStar_Parser_AST.PatVar
                 (x, typ_opt, uu___);
               FStar_Parser_AST.prange = uu___1;_}::[],
             {
               FStar_Parser_AST.tm = FStar_Parser_AST.Match
                 (maybe_x, FStar_Pervasives_Native.None, branches);
               FStar_Parser_AST.range = uu___2;
               FStar_Parser_AST.level = uu___3;_})
            when matches_var maybe_x x ->
            let uu___4 =
              let uu___5 =
                let uu___6 = str "function" in
                let uu___7 =
                  separate_map_last FStar_Pprint.hardline p_patternBranch
                    branches in
                FStar_Pprint.op_Hat_Slash_Hat uu___6 uu___7 in
              FStar_Pprint.group uu___5 in
            let uu___5 = paren_if (ps || pb) in uu___5 uu___4
        | FStar_Parser_AST.Quote (e1, FStar_Parser_AST.Dynamic) ->
            let uu___ =
              let uu___1 = str "quote" in
              let uu___2 = p_noSeqTermAndComment ps pb e1 in
              FStar_Pprint.op_Hat_Slash_Hat uu___1 uu___2 in
            FStar_Pprint.group uu___
        | FStar_Parser_AST.Quote (e1, FStar_Parser_AST.Static) ->
            let uu___ =
              let uu___1 = str "`" in
              let uu___2 = p_noSeqTermAndComment ps pb e1 in
              FStar_Pprint.op_Hat_Hat uu___1 uu___2 in
            FStar_Pprint.group uu___
        | FStar_Parser_AST.VQuote e1 ->
            let uu___ =
              let uu___1 = str "`%" in
              let uu___2 = p_noSeqTermAndComment ps pb e1 in
              FStar_Pprint.op_Hat_Hat uu___1 uu___2 in
            FStar_Pprint.group uu___
        | FStar_Parser_AST.Antiquote
            {
              FStar_Parser_AST.tm = FStar_Parser_AST.Quote
                (e1, FStar_Parser_AST.Dynamic);
              FStar_Parser_AST.range = uu___;
              FStar_Parser_AST.level = uu___1;_}
            ->
            let uu___2 =
              let uu___3 = str "`@" in
              let uu___4 = p_noSeqTermAndComment ps pb e1 in
              FStar_Pprint.op_Hat_Hat uu___3 uu___4 in
            FStar_Pprint.group uu___2
        | FStar_Parser_AST.Antiquote e1 ->
            let uu___ =
              let uu___1 = str "`#" in
              let uu___2 = p_noSeqTermAndComment ps pb e1 in
              FStar_Pprint.op_Hat_Hat uu___1 uu___2 in
            FStar_Pprint.group uu___
        | FStar_Parser_AST.CalcProof (rel, init, steps) ->
            let head =
              let uu___ = str "calc" in
              let uu___1 =
                let uu___2 =
                  let uu___3 = p_noSeqTermAndComment false false rel in
                  let uu___4 =
                    FStar_Pprint.op_Hat_Hat FStar_Pprint.space
                      FStar_Pprint.lbrace in
                  FStar_Pprint.op_Hat_Hat uu___3 uu___4 in
                FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu___2 in
              FStar_Pprint.op_Hat_Hat uu___ uu___1 in
            let bot = FStar_Pprint.rbrace in
            let uu___ = FStar_Pprint.op_Hat_Hat FStar_Pprint.hardline bot in
            let uu___1 =
              let uu___2 =
                let uu___3 =
                  let uu___4 = p_noSeqTermAndComment false false init in
                  let uu___5 =
                    let uu___6 = str ";" in
                    let uu___7 =
                      let uu___8 =
                        separate_map_last FStar_Pprint.hardline p_calcStep
                          steps in
                      FStar_Pprint.op_Hat_Hat FStar_Pprint.hardline uu___8 in
                    FStar_Pprint.op_Hat_Hat uu___6 uu___7 in
                  FStar_Pprint.op_Hat_Hat uu___4 uu___5 in
                FStar_Pprint.op_Hat_Hat FStar_Pprint.hardline uu___3 in
              FStar_All.pipe_left (FStar_Pprint.nest (Prims.of_int (2)))
                uu___2 in
            FStar_Pprint.enclose head uu___ uu___1
        | uu___ -> p_typ ps pb e
and (p_dec_wf :
  Prims.bool ->
    Prims.bool ->
      FStar_Parser_AST.term -> FStar_Parser_AST.term -> FStar_Pprint.document)
  =
  fun ps ->
    fun pb ->
      fun rel ->
        fun e ->
          let uu___ =
            let uu___1 = str "{:well-founded " in
            let uu___2 =
              let uu___3 = p_typ ps pb rel in
              let uu___4 =
                let uu___5 = p_typ ps pb e in
                let uu___6 = str " }" in
                FStar_Pprint.op_Hat_Hat uu___5 uu___6 in
              FStar_Pprint.op_Hat_Slash_Hat uu___3 uu___4 in
            FStar_Pprint.op_Hat_Hat uu___1 uu___2 in
          FStar_Pprint.group uu___
and (p_calcStep :
  Prims.bool -> FStar_Parser_AST.calc_step -> FStar_Pprint.document) =
  fun uu___ ->
    fun uu___1 ->
      match uu___1 with
      | FStar_Parser_AST.CalcStep (rel, just, next) ->
          let uu___2 =
            let uu___3 = p_noSeqTermAndComment false false rel in
            let uu___4 =
              let uu___5 =
                let uu___6 =
                  let uu___7 =
                    let uu___8 = p_noSeqTermAndComment false false just in
                    let uu___9 =
                      let uu___10 =
                        let uu___11 =
                          let uu___12 =
                            let uu___13 =
                              p_noSeqTermAndComment false false next in
                            let uu___14 = str ";" in
                            FStar_Pprint.op_Hat_Hat uu___13 uu___14 in
                          FStar_Pprint.op_Hat_Hat FStar_Pprint.hardline
                            uu___12 in
                        FStar_Pprint.op_Hat_Hat FStar_Pprint.rbrace uu___11 in
                      FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu___10 in
                    FStar_Pprint.op_Hat_Hat uu___8 uu___9 in
                  FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu___7 in
                FStar_Pprint.op_Hat_Hat FStar_Pprint.lbrace uu___6 in
              FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu___5 in
            FStar_Pprint.op_Hat_Hat uu___3 uu___4 in
          FStar_Pprint.group uu___2
and (p_attrs_opt :
  FStar_Parser_AST.term Prims.list FStar_Pervasives_Native.option ->
    FStar_Pprint.document)
  =
  fun uu___ ->
    match uu___ with
    | FStar_Pervasives_Native.None -> FStar_Pprint.empty
    | FStar_Pervasives_Native.Some terms ->
        let uu___1 =
          let uu___2 = str "[@@" in
          let uu___3 =
            let uu___4 =
              let uu___5 = str "; " in
              FStar_Pprint.separate_map uu___5
                (p_noSeqTermAndComment false false) terms in
            let uu___5 = str "]" in
            FStar_Pprint.op_Hat_Slash_Hat uu___4 uu___5 in
          FStar_Pprint.op_Hat_Slash_Hat uu___2 uu___3 in
        FStar_Pprint.group uu___1
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
        | FStar_Parser_AST.QForall (bs, (uu___, trigger), e1) ->
            let binders_doc = p_binders true bs in
            let term_doc = p_noSeqTermAndComment ps pb e1 in
            (match trigger with
             | [] ->
                 let uu___1 =
                   let uu___2 =
                     let uu___3 = p_quantifier e in
                     FStar_Pprint.op_Hat_Hat uu___3 FStar_Pprint.space in
                   FStar_Pprint.soft_surround (Prims.of_int (2))
                     Prims.int_zero uu___2 binders_doc FStar_Pprint.dot in
                 prefix2 uu___1 term_doc
             | pats ->
                 let uu___1 =
                   let uu___2 =
                     let uu___3 =
                       let uu___4 =
                         let uu___5 = p_quantifier e in
                         FStar_Pprint.op_Hat_Hat uu___5 FStar_Pprint.space in
                       FStar_Pprint.soft_surround (Prims.of_int (2))
                         Prims.int_zero uu___4 binders_doc FStar_Pprint.dot in
                     let uu___4 = p_trigger trigger in prefix2 uu___3 uu___4 in
                   FStar_Pprint.group uu___2 in
                 prefix2 uu___1 term_doc)
        | FStar_Parser_AST.QExists (bs, (uu___, trigger), e1) ->
            let binders_doc = p_binders true bs in
            let term_doc = p_noSeqTermAndComment ps pb e1 in
            (match trigger with
             | [] ->
                 let uu___1 =
                   let uu___2 =
                     let uu___3 = p_quantifier e in
                     FStar_Pprint.op_Hat_Hat uu___3 FStar_Pprint.space in
                   FStar_Pprint.soft_surround (Prims.of_int (2))
                     Prims.int_zero uu___2 binders_doc FStar_Pprint.dot in
                 prefix2 uu___1 term_doc
             | pats ->
                 let uu___1 =
                   let uu___2 =
                     let uu___3 =
                       let uu___4 =
                         let uu___5 = p_quantifier e in
                         FStar_Pprint.op_Hat_Hat uu___5 FStar_Pprint.space in
                       FStar_Pprint.soft_surround (Prims.of_int (2))
                         Prims.int_zero uu___4 binders_doc FStar_Pprint.dot in
                     let uu___4 = p_trigger trigger in prefix2 uu___3 uu___4 in
                   FStar_Pprint.group uu___2 in
                 prefix2 uu___1 term_doc)
        | uu___ -> p_simpleTerm ps pb e
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
      let uu___ = all_binders_annot t in
      if uu___
      then
        let uu___1 =
          p_typ_top (Binders ((Prims.of_int (4)), Prims.int_zero, true))
            false false t in
        FStar_Pprint.op_Hat_Hat s uu___1
      else
        (let uu___2 =
           let uu___3 =
             let uu___4 =
               p_typ_top (Arrows ((Prims.of_int (2)), (Prims.of_int (2))))
                 false false t in
             FStar_Pprint.op_Hat_Hat s uu___4 in
           FStar_Pprint.op_Hat_Hat FStar_Pprint.colon uu___3 in
         FStar_Pprint.group uu___2)
and (collapse_pats :
  (FStar_Pprint.document * FStar_Pprint.document) Prims.list ->
    FStar_Pprint.document Prims.list)
  =
  fun pats ->
    let fold_fun bs x =
      let uu___ = x in
      match uu___ with
      | (b1, t1) ->
          (match bs with
           | [] -> [([b1], t1)]
           | hd::tl ->
               let uu___1 = hd in
               (match uu___1 with
                | (b2s, t2) ->
                    if t1 = t2
                    then ((FStar_List.append b2s [b1]), t1) :: tl
                    else ([b1], t1) :: hd :: tl)) in
    let p_collapsed_binder cb =
      let uu___ = cb in
      match uu___ with
      | (bs, typ) ->
          (match bs with
           | [] -> failwith "Impossible"
           | b::[] -> cat_with_colon b typ
           | hd::tl ->
               let uu___1 =
                 FStar_List.fold_left
                   (fun x ->
                      fun y ->
                        let uu___2 =
                          FStar_Pprint.op_Hat_Hat FStar_Pprint.space y in
                        FStar_Pprint.op_Hat_Hat x uu___2) hd tl in
               cat_with_colon uu___1 typ) in
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
           | (FStar_Parser_AST.PatVar (lid, aqual, attrs),
              FStar_Parser_AST.Refine
              ({ FStar_Parser_AST.b = FStar_Parser_AST.Annotated (lid', t1);
                 FStar_Parser_AST.brange = uu___;
                 FStar_Parser_AST.blevel = uu___1;
                 FStar_Parser_AST.aqual = uu___2;
                 FStar_Parser_AST.battributes = uu___3;_},
               phi)) when
               let uu___4 = FStar_Ident.string_of_id lid in
               let uu___5 = FStar_Ident.string_of_id lid' in uu___4 = uu___5
               ->
               let uu___4 =
                 let uu___5 = p_ident lid in
                 p_refinement' aqual attrs uu___5 t1 phi in
               FStar_Pervasives_Native.Some uu___4
           | (FStar_Parser_AST.PatVar (lid, aqual, attrs), uu___) ->
               let uu___1 =
                 let uu___2 =
                   let uu___3 = FStar_Pprint.optional p_aqual aqual in
                   let uu___4 =
                     let uu___5 = p_attributes attrs in
                     let uu___6 = p_ident lid in
                     FStar_Pprint.op_Hat_Hat uu___5 uu___6 in
                   FStar_Pprint.op_Hat_Hat uu___3 uu___4 in
                 let uu___3 = p_tmEqNoRefinement t in (uu___2, uu___3) in
               FStar_Pervasives_Native.Some uu___1
           | uu___ -> FStar_Pervasives_Native.None)
      | uu___ -> FStar_Pervasives_Native.None in
    let all_unbound p =
      match p.FStar_Parser_AST.pat with
      | FStar_Parser_AST.PatAscribed uu___ -> false
      | uu___ -> true in
    let uu___ = map_if_all all_binders pats in
    match uu___ with
    | FStar_Pervasives_Native.Some bs ->
        let uu___1 = collapse_pats bs in
        (uu___1, (Binders ((Prims.of_int (4)), Prims.int_zero, true)))
    | FStar_Pervasives_Native.None ->
        let uu___1 = FStar_List.map p_atomicPattern pats in
        (uu___1, (Binders ((Prims.of_int (4)), Prims.int_zero, false)))
and (p_quantifier : FStar_Parser_AST.term -> FStar_Pprint.document) =
  fun e ->
    match e.FStar_Parser_AST.tm with
    | FStar_Parser_AST.QForall uu___ -> str "forall"
    | FStar_Parser_AST.QExists uu___ -> str "exists"
    | uu___ ->
        failwith "Imposible : p_quantifier called on a non-quantifier term"
and (p_trigger :
  FStar_Parser_AST.term Prims.list Prims.list -> FStar_Pprint.document) =
  fun uu___ ->
    match uu___ with
    | [] -> FStar_Pprint.empty
    | pats ->
        let uu___1 =
          let uu___2 =
            let uu___3 =
              let uu___4 = str "pattern" in
              let uu___5 =
                let uu___6 =
                  let uu___7 = p_disjunctivePats pats in
                  FStar_Pprint.jump (Prims.of_int (2)) Prims.int_zero uu___7 in
                FStar_Pprint.op_Hat_Hat uu___6 FStar_Pprint.rbrace in
              FStar_Pprint.op_Hat_Slash_Hat uu___4 uu___5 in
            FStar_Pprint.op_Hat_Hat FStar_Pprint.colon uu___3 in
          FStar_Pprint.op_Hat_Hat FStar_Pprint.lbrace uu___2 in
        FStar_Pprint.group uu___1
and (p_disjunctivePats :
  FStar_Parser_AST.term Prims.list Prims.list -> FStar_Pprint.document) =
  fun pats ->
    let uu___ = str "\\/" in
    FStar_Pprint.separate_map uu___ p_conjunctivePats pats
and (p_conjunctivePats :
  FStar_Parser_AST.term Prims.list -> FStar_Pprint.document) =
  fun pats ->
    let uu___ =
      let uu___1 = FStar_Pprint.op_Hat_Hat FStar_Pprint.semi break1 in
      FStar_Pprint.separate_map uu___1 p_appTerm pats in
    FStar_Pprint.group uu___
and (p_simpleTerm :
  Prims.bool -> Prims.bool -> FStar_Parser_AST.term -> FStar_Pprint.document)
  =
  fun ps ->
    fun pb ->
      fun e ->
        match e.FStar_Parser_AST.tm with
        | FStar_Parser_AST.Abs (pats, e1) ->
            let uu___ = p_term_sep false pb e1 in
            (match uu___ with
             | (comm, doc) ->
                 let prefix =
                   let uu___1 = str "fun" in
                   let uu___2 =
                     let uu___3 =
                       FStar_Pprint.separate_map break1 p_atomicPattern pats in
                     FStar_Pprint.op_Hat_Slash_Hat uu___3 FStar_Pprint.rarrow in
                   op_Hat_Slash_Plus_Hat uu___1 uu___2 in
                 let uu___1 =
                   if comm <> FStar_Pprint.empty
                   then
                     let uu___2 =
                       let uu___3 =
                         let uu___4 =
                           FStar_Pprint.op_Hat_Hat FStar_Pprint.hardline doc in
                         FStar_Pprint.op_Hat_Hat comm uu___4 in
                       FStar_Pprint.op_Hat_Hat FStar_Pprint.hardline uu___3 in
                     FStar_Pprint.op_Hat_Hat prefix uu___2
                   else
                     (let uu___3 = op_Hat_Slash_Plus_Hat prefix doc in
                      FStar_Pprint.group uu___3) in
                 let uu___2 = paren_if ps in uu___2 uu___1)
        | uu___ -> p_tmIff e
and (p_maybeFocusArrow : Prims.bool -> FStar_Pprint.document) =
  fun b -> if b then str "~>" else FStar_Pprint.rarrow
and (p_patternBranch :
  Prims.bool ->
    (FStar_Parser_AST.pattern * FStar_Parser_AST.term
      FStar_Pervasives_Native.option * FStar_Parser_AST.term) ->
      FStar_Pprint.document)
  =
  fun pb ->
    fun uu___ ->
      match uu___ with
      | (pat, when_opt, e) ->
          let one_pattern_branch p =
            let branch =
              match when_opt with
              | FStar_Pervasives_Native.None ->
                  let uu___1 =
                    let uu___2 =
                      let uu___3 =
                        let uu___4 = p_tuplePattern p in
                        let uu___5 =
                          FStar_Pprint.op_Hat_Hat FStar_Pprint.space
                            FStar_Pprint.rarrow in
                        FStar_Pprint.op_Hat_Hat uu___4 uu___5 in
                      FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu___3 in
                    FStar_Pprint.op_Hat_Hat FStar_Pprint.bar uu___2 in
                  FStar_Pprint.group uu___1
              | FStar_Pervasives_Native.Some f ->
                  let uu___1 =
                    let uu___2 =
                      let uu___3 =
                        let uu___4 =
                          let uu___5 =
                            let uu___6 = p_tuplePattern p in
                            let uu___7 = str "when" in
                            FStar_Pprint.op_Hat_Slash_Hat uu___6 uu___7 in
                          FStar_Pprint.group uu___5 in
                        let uu___5 =
                          let uu___6 =
                            let uu___7 = p_tmFormula f in
                            [uu___7; FStar_Pprint.rarrow] in
                          FStar_Pprint.flow break1 uu___6 in
                        FStar_Pprint.op_Hat_Slash_Hat uu___4 uu___5 in
                      FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu___3 in
                    FStar_Pprint.op_Hat_Hat FStar_Pprint.bar uu___2 in
                  FStar_Pprint.hang (Prims.of_int (2)) uu___1 in
            let uu___1 = p_term_sep false pb e in
            match uu___1 with
            | (comm, doc) ->
                if pb
                then
                  (if comm = FStar_Pprint.empty
                   then
                     let uu___2 = op_Hat_Slash_Plus_Hat branch doc in
                     FStar_Pprint.group uu___2
                   else
                     (let uu___3 =
                        let uu___4 =
                          let uu___5 =
                            let uu___6 =
                              let uu___7 =
                                FStar_Pprint.op_Hat_Hat break1 comm in
                              FStar_Pprint.op_Hat_Hat doc uu___7 in
                            op_Hat_Slash_Plus_Hat branch uu___6 in
                          FStar_Pprint.group uu___5 in
                        let uu___5 =
                          let uu___6 =
                            let uu___7 =
                              inline_comment_or_above comm doc
                                FStar_Pprint.empty in
                            jump2 uu___7 in
                          FStar_Pprint.op_Hat_Hat branch uu___6 in
                        FStar_Pprint.ifflat uu___4 uu___5 in
                      FStar_Pprint.group uu___3))
                else
                  if comm <> FStar_Pprint.empty
                  then
                    (let uu___3 =
                       let uu___4 =
                         FStar_Pprint.op_Hat_Hat FStar_Pprint.hardline doc in
                       FStar_Pprint.op_Hat_Hat comm uu___4 in
                     op_Hat_Slash_Plus_Hat branch uu___3)
                  else op_Hat_Slash_Plus_Hat branch doc in
          (match pat.FStar_Parser_AST.pat with
           | FStar_Parser_AST.PatOr pats ->
               (match FStar_List.rev pats with
                | hd::tl ->
                    let last_pat_branch = one_pattern_branch hd in
                    let uu___1 =
                      let uu___2 =
                        let uu___3 =
                          let uu___4 =
                            let uu___5 =
                              let uu___6 =
                                FStar_Pprint.op_Hat_Hat FStar_Pprint.bar
                                  FStar_Pprint.space in
                              FStar_Pprint.op_Hat_Hat break1 uu___6 in
                            FStar_Pprint.separate_map uu___5 p_tuplePattern
                              (FStar_List.rev tl) in
                          FStar_Pprint.op_Hat_Slash_Hat uu___4
                            last_pat_branch in
                        FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu___3 in
                      FStar_Pprint.op_Hat_Hat FStar_Pprint.bar uu___2 in
                    FStar_Pprint.group uu___1
                | [] ->
                    failwith "Impossible: disjunctive pattern can't be empty")
           | uu___1 -> one_pattern_branch pat)
and (p_tmIff : FStar_Parser_AST.term -> FStar_Pprint.document) =
  fun e ->
    match e.FStar_Parser_AST.tm with
    | FStar_Parser_AST.Op (id, e1::e2::[]) when
        let uu___ = FStar_Ident.string_of_id id in uu___ = "<==>" ->
        let uu___ = str "<==>" in
        let uu___1 = p_tmImplies e1 in
        let uu___2 = p_tmIff e2 in infix0 uu___ uu___1 uu___2
    | uu___ -> p_tmImplies e
and (p_tmImplies : FStar_Parser_AST.term -> FStar_Pprint.document) =
  fun e ->
    match e.FStar_Parser_AST.tm with
    | FStar_Parser_AST.Op (id, e1::e2::[]) when
        let uu___ = FStar_Ident.string_of_id id in uu___ = "==>" ->
        let uu___ = str "==>" in
        let uu___1 =
          p_tmArrow (Arrows ((Prims.of_int (2)), (Prims.of_int (2)))) false
            p_tmFormula e1 in
        let uu___2 = p_tmImplies e2 in infix0 uu___ uu___1 uu___2
    | uu___ ->
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
          let uu___ =
            FStar_List.splitAt ((FStar_List.length terms) - Prims.int_one)
              terms in
          match uu___ with
          | (terms', last) ->
              let uu___1 =
                match style with
                | Arrows (n, ln) ->
                    let uu___2 =
                      let uu___3 =
                        FStar_Pprint.op_Hat_Hat FStar_Pprint.rarrow break1 in
                      FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu___3 in
                    let uu___3 =
                      FStar_Pprint.op_Hat_Hat FStar_Pprint.rarrow
                        FStar_Pprint.space in
                    (n, ln, terms', uu___2, uu___3)
                | Binders (n, ln, parens) ->
                    let uu___2 =
                      if parens
                      then FStar_List.map soft_parens_with_nesting terms'
                      else terms' in
                    let uu___3 =
                      FStar_Pprint.op_Hat_Hat FStar_Pprint.colon
                        FStar_Pprint.space in
                    (n, ln, uu___2, break1, uu___3) in
              (match uu___1 with
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
                    | uu___2 when uu___2 = Prims.int_one ->
                        FStar_List.hd terms
                    | uu___2 ->
                        let uu___3 =
                          let uu___4 =
                            let uu___5 =
                              let uu___6 = FStar_Pprint.separate sep terms'1 in
                              let uu___7 =
                                let uu___8 =
                                  FStar_Pprint.op_Hat_Hat last_op1 last1 in
                                FStar_Pprint.op_Hat_Hat one_line_space uu___8 in
                              FStar_Pprint.op_Hat_Hat uu___6 uu___7 in
                            FStar_Pprint.op_Hat_Hat fs uu___5 in
                          let uu___5 =
                            let uu___6 =
                              let uu___7 =
                                let uu___8 =
                                  let uu___9 =
                                    FStar_Pprint.separate sep terms'1 in
                                  FStar_Pprint.op_Hat_Hat fs uu___9 in
                                let uu___9 =
                                  let uu___10 =
                                    let uu___11 =
                                      let uu___12 =
                                        FStar_Pprint.op_Hat_Hat sep
                                          single_line_arg_indent in
                                      let uu___13 =
                                        FStar_List.map
                                          (fun x ->
                                             let uu___14 =
                                               FStar_Pprint.hang
                                                 (Prims.of_int (2)) x in
                                             FStar_Pprint.align uu___14)
                                          terms'1 in
                                      FStar_Pprint.separate uu___12 uu___13 in
                                    FStar_Pprint.op_Hat_Hat
                                      single_line_arg_indent uu___11 in
                                  jump2 uu___10 in
                                FStar_Pprint.ifflat uu___8 uu___9 in
                              FStar_Pprint.group uu___7 in
                            let uu___7 =
                              let uu___8 =
                                let uu___9 =
                                  FStar_Pprint.op_Hat_Hat last_op1 last1 in
                                FStar_Pprint.hang last_n uu___9 in
                              FStar_Pprint.align uu___8 in
                            FStar_Pprint.prefix n Prims.int_one uu___6 uu___7 in
                          FStar_Pprint.ifflat uu___4 uu___5 in
                        FStar_Pprint.group uu___3))
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
            | Arrows uu___ -> p_tmArrow' p_Tm e
            | Binders uu___ -> collapse_binders p_Tm e in
          format_sig style terms false flat_space
and (p_tmArrow' :
  (FStar_Parser_AST.term -> FStar_Pprint.document) ->
    FStar_Parser_AST.term -> FStar_Pprint.document Prims.list)
  =
  fun p_Tm ->
    fun e ->
      match e.FStar_Parser_AST.tm with
      | FStar_Parser_AST.Product (bs, tgt) ->
          let uu___ = FStar_List.map (fun b -> p_binder false b) bs in
          let uu___1 = p_tmArrow' p_Tm tgt in FStar_List.append uu___ uu___1
      | uu___ -> let uu___1 = p_Tm e in [uu___1]
and (collapse_binders :
  (FStar_Parser_AST.term -> FStar_Pprint.document) ->
    FStar_Parser_AST.term -> FStar_Pprint.document Prims.list)
  =
  fun p_Tm ->
    fun e ->
      let rec accumulate_binders p_Tm1 e1 =
        match e1.FStar_Parser_AST.tm with
        | FStar_Parser_AST.Product (bs, tgt) ->
            let uu___ = FStar_List.map (fun b -> p_binder' false b) bs in
            let uu___1 = accumulate_binders p_Tm1 tgt in
            FStar_List.append uu___ uu___1
        | uu___ ->
            let uu___1 =
              let uu___2 = p_Tm1 e1 in
              (uu___2, FStar_Pervasives_Native.None, cat_with_colon) in
            [uu___1] in
      let fold_fun bs x =
        let uu___ = x in
        match uu___ with
        | (b1, t1, f1) ->
            (match bs with
             | [] -> [([b1], t1, f1)]
             | hd::tl ->
                 let uu___1 = hd in
                 (match uu___1 with
                  | (b2s, t2, uu___2) ->
                      (match (t1, t2) with
                       | (FStar_Pervasives_Native.Some typ1,
                          FStar_Pervasives_Native.Some typ2) ->
                           if typ1 = typ2
                           then ((FStar_List.append b2s [b1]), t1, f1) :: tl
                           else ([b1], t1, f1) :: hd :: tl
                       | uu___3 -> ([b1], t1, f1) :: bs))) in
      let p_collapsed_binder cb =
        let uu___ = cb in
        match uu___ with
        | (bs, t, f) ->
            (match t with
             | FStar_Pervasives_Native.None ->
                 (match bs with
                  | b::[] -> b
                  | uu___1 -> failwith "Impossible")
             | FStar_Pervasives_Native.Some typ ->
                 (match bs with
                  | [] -> failwith "Impossible"
                  | b::[] -> f b typ
                  | hd::tl ->
                      let uu___1 =
                        FStar_List.fold_left
                          (fun x ->
                             fun y ->
                               let uu___2 =
                                 FStar_Pprint.op_Hat_Hat FStar_Pprint.space y in
                               FStar_Pprint.op_Hat_Hat x uu___2) hd tl in
                      f uu___1 typ)) in
      let binders =
        let uu___ = accumulate_binders p_Tm e in
        FStar_List.fold_left fold_fun [] uu___ in
      map_rev p_collapsed_binder binders
and (p_tmFormula : FStar_Parser_AST.term -> FStar_Pprint.document) =
  fun e ->
    let conj =
      let uu___ =
        let uu___1 = str "/\\" in FStar_Pprint.op_Hat_Hat uu___1 break1 in
      FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu___ in
    let disj =
      let uu___ =
        let uu___1 = str "\\/" in FStar_Pprint.op_Hat_Hat uu___1 break1 in
      FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu___ in
    let formula = p_tmDisjunction e in
    FStar_Pprint.flow_map disj
      (fun d -> FStar_Pprint.flow_map conj (fun x -> FStar_Pprint.group x) d)
      formula
and (p_tmDisjunction :
  FStar_Parser_AST.term -> FStar_Pprint.document Prims.list Prims.list) =
  fun e ->
    match e.FStar_Parser_AST.tm with
    | FStar_Parser_AST.Op (id, e1::e2::[]) when
        let uu___ = FStar_Ident.string_of_id id in uu___ = "\\/" ->
        let uu___ = p_tmDisjunction e1 in
        let uu___1 = let uu___2 = p_tmConjunction e2 in [uu___2] in
        FStar_List.append uu___ uu___1
    | uu___ -> let uu___1 = p_tmConjunction e in [uu___1]
and (p_tmConjunction :
  FStar_Parser_AST.term -> FStar_Pprint.document Prims.list) =
  fun e ->
    match e.FStar_Parser_AST.tm with
    | FStar_Parser_AST.Op (id, e1::e2::[]) when
        let uu___ = FStar_Ident.string_of_id id in uu___ = "/\\" ->
        let uu___ = p_tmConjunction e1 in
        let uu___1 = let uu___2 = p_tmTuple e2 in [uu___2] in
        FStar_List.append uu___ uu___1
    | uu___ -> let uu___1 = p_tmTuple e in [uu___1]
and (p_tmTuple : FStar_Parser_AST.term -> FStar_Pprint.document) =
  fun e -> with_comment p_tmTuple' e e.FStar_Parser_AST.range
and (p_tmTuple' : FStar_Parser_AST.term -> FStar_Pprint.document) =
  fun e ->
    match e.FStar_Parser_AST.tm with
    | FStar_Parser_AST.Construct (lid, args) when
        (is_tuple_constructor lid) && (all1_explicit args) ->
        let uu___ = FStar_Pprint.op_Hat_Hat FStar_Pprint.comma break1 in
        FStar_Pprint.separate_map uu___
          (fun uu___1 -> match uu___1 with | (e1, uu___2) -> p_tmEq e1) args
    | uu___ -> p_tmEq e
and (paren_if_gt :
  Prims.int -> Prims.int -> FStar_Pprint.document -> FStar_Pprint.document) =
  fun curr ->
    fun mine ->
      fun doc ->
        if mine <= curr
        then doc
        else
          (let uu___1 =
             let uu___2 = FStar_Pprint.op_Hat_Hat doc FStar_Pprint.rparen in
             FStar_Pprint.op_Hat_Hat FStar_Pprint.lparen uu___2 in
           FStar_Pprint.group uu___1)
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
            (let uu___ =
               (let uu___1 = FStar_Ident.string_of_id op in uu___1 = "==>")
                 ||
                 (let uu___1 = FStar_Ident.string_of_id op in uu___1 = "<==>") in
             Prims.op_Negation uu___) &&
              (((is_operatorInfix0ad12 op) ||
                  (let uu___ = FStar_Ident.string_of_id op in uu___ = "="))
                 || (let uu___ = FStar_Ident.string_of_id op in uu___ = "|>"))
            ->
            let op1 = FStar_Ident.string_of_id op in
            let uu___ = levels op1 in
            (match uu___ with
             | (left, mine, right) ->
                 let uu___1 =
                   let uu___2 = FStar_All.pipe_left str op1 in
                   let uu___3 = p_tmEqWith' p_X left e1 in
                   let uu___4 = p_tmEqWith' p_X right e2 in
                   infix0 uu___2 uu___3 uu___4 in
                 paren_if_gt curr mine uu___1)
        | FStar_Parser_AST.Op (id, e1::e2::[]) when
            let uu___ = FStar_Ident.string_of_id id in uu___ = ":=" ->
            let uu___ =
              let uu___1 = p_tmEqWith p_X e1 in
              let uu___2 =
                let uu___3 =
                  let uu___4 =
                    let uu___5 = p_tmEqWith p_X e2 in
                    op_Hat_Slash_Plus_Hat FStar_Pprint.equals uu___5 in
                  FStar_Pprint.op_Hat_Hat FStar_Pprint.colon uu___4 in
                FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu___3 in
              FStar_Pprint.op_Hat_Hat uu___1 uu___2 in
            FStar_Pprint.group uu___
        | FStar_Parser_AST.Op (id, e1::[]) when
            let uu___ = FStar_Ident.string_of_id id in uu___ = "-" ->
            let uu___ = levels "-" in
            (match uu___ with
             | (left, mine, right) ->
                 let uu___1 = p_tmEqWith' p_X mine e1 in
                 FStar_Pprint.op_Hat_Slash_Hat FStar_Pprint.minus uu___1)
        | uu___ -> p_tmNoEqWith p_X e
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
          | FStar_Parser_AST.Construct (lid, (e1, uu___)::(e2, uu___1)::[])
              when
              (FStar_Ident.lid_equals lid FStar_Parser_Const.cons_lid) &&
                (let uu___2 = is_list e in Prims.op_Negation uu___2)
              ->
              let op = "::" in
              let uu___2 = levels op in
              (match uu___2 with
               | (left, mine, right) ->
                   let uu___3 =
                     let uu___4 = str op in
                     let uu___5 = p_tmNoEqWith' false p_X left e1 in
                     let uu___6 = p_tmNoEqWith' false p_X right e2 in
                     infix0 uu___4 uu___5 uu___6 in
                   paren_if_gt curr mine uu___3)
          | FStar_Parser_AST.Sum (binders, res) ->
              let op = "&" in
              let uu___ = levels op in
              (match uu___ with
               | (left, mine, right) ->
                   let p_dsumfst bt =
                     match bt with
                     | FStar_Pervasives.Inl b ->
                         let uu___1 = p_binder false b in
                         let uu___2 =
                           let uu___3 =
                             let uu___4 = str op in
                             FStar_Pprint.op_Hat_Hat uu___4 break1 in
                           FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu___3 in
                         FStar_Pprint.op_Hat_Hat uu___1 uu___2
                     | FStar_Pervasives.Inr t ->
                         let uu___1 = p_tmNoEqWith' false p_X left t in
                         let uu___2 =
                           let uu___3 =
                             let uu___4 = str op in
                             FStar_Pprint.op_Hat_Hat uu___4 break1 in
                           FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu___3 in
                         FStar_Pprint.op_Hat_Hat uu___1 uu___2 in
                   let uu___1 =
                     let uu___2 = FStar_Pprint.concat_map p_dsumfst binders in
                     let uu___3 = p_tmNoEqWith' false p_X right res in
                     FStar_Pprint.op_Hat_Hat uu___2 uu___3 in
                   paren_if_gt curr mine uu___1)
          | FStar_Parser_AST.Op (id, e1::e2::[]) when
              (let uu___ = FStar_Ident.string_of_id id in uu___ = "*") &&
                (FStar_ST.op_Bang unfold_tuples)
              ->
              let op = "*" in
              let uu___ = levels op in
              (match uu___ with
               | (left, mine, right) ->
                   if inside_tuple
                   then
                     let uu___1 = str op in
                     let uu___2 = p_tmNoEqWith' true p_X left e1 in
                     let uu___3 = p_tmNoEqWith' true p_X right e2 in
                     infix0 uu___1 uu___2 uu___3
                   else
                     (let uu___2 =
                        let uu___3 = str op in
                        let uu___4 = p_tmNoEqWith' true p_X left e1 in
                        let uu___5 = p_tmNoEqWith' true p_X right e2 in
                        infix0 uu___3 uu___4 uu___5 in
                      paren_if_gt curr mine uu___2))
          | FStar_Parser_AST.Op (op, e1::e2::[]) when is_operatorInfix34 op
              ->
              let op1 = FStar_Ident.string_of_id op in
              let uu___ = levels op1 in
              (match uu___ with
               | (left, mine, right) ->
                   let uu___1 =
                     let uu___2 = str op1 in
                     let uu___3 = p_tmNoEqWith' false p_X left e1 in
                     let uu___4 = p_tmNoEqWith' false p_X right e2 in
                     infix0 uu___2 uu___3 uu___4 in
                   paren_if_gt curr mine uu___1)
          | FStar_Parser_AST.Record (with_opt, record_fields) ->
              let uu___ =
                let uu___1 =
                  default_or_map FStar_Pprint.empty p_with_clause with_opt in
                let uu___2 =
                  let uu___3 =
                    FStar_Pprint.op_Hat_Hat FStar_Pprint.semi break1 in
                  separate_map_last uu___3 p_simpleDef record_fields in
                FStar_Pprint.op_Hat_Hat uu___1 uu___2 in
              braces_with_nesting uu___
          | FStar_Parser_AST.Op (id, e1::[]) when
              let uu___ = FStar_Ident.string_of_id id in uu___ = "~" ->
              let uu___ =
                let uu___1 = str "~" in
                let uu___2 = p_atomicTerm e1 in
                FStar_Pprint.op_Hat_Hat uu___1 uu___2 in
              FStar_Pprint.group uu___
          | FStar_Parser_AST.Paren p when inside_tuple ->
              (match p.FStar_Parser_AST.tm with
               | FStar_Parser_AST.Op (id, e1::e2::[]) when
                   let uu___ = FStar_Ident.string_of_id id in uu___ = "*" ->
                   let op = "*" in
                   let uu___ = levels op in
                   (match uu___ with
                    | (left, mine, right) ->
                        let uu___1 =
                          let uu___2 = str op in
                          let uu___3 = p_tmNoEqWith' true p_X left e1 in
                          let uu___4 = p_tmNoEqWith' true p_X right e2 in
                          infix0 uu___2 uu___3 uu___4 in
                        paren_if_gt curr mine uu___1)
               | uu___ -> p_X e)
          | uu___ -> p_X e
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
        let uu___ =
          let uu___1 = p_lident lid in
          let uu___2 =
            let uu___3 = p_appTerm e1 in
            FStar_Pprint.op_Hat_Slash_Hat FStar_Pprint.colon uu___3 in
          FStar_Pprint.op_Hat_Slash_Hat uu___1 uu___2 in
        FStar_Pprint.group uu___
    | FStar_Parser_AST.Refine (b, phi) -> p_refinedBinder b phi
    | uu___ -> p_appTerm e
and (p_with_clause : FStar_Parser_AST.term -> FStar_Pprint.document) =
  fun e ->
    let uu___ = p_appTerm e in
    let uu___1 =
      let uu___2 =
        let uu___3 = str "with" in FStar_Pprint.op_Hat_Hat uu___3 break1 in
      FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu___2 in
    FStar_Pprint.op_Hat_Hat uu___ uu___1
and (p_refinedBinder :
  FStar_Parser_AST.binder -> FStar_Parser_AST.term -> FStar_Pprint.document)
  =
  fun b ->
    fun phi ->
      match b.FStar_Parser_AST.b with
      | FStar_Parser_AST.Annotated (lid, t) ->
          let uu___ = p_lident lid in
          p_refinement b.FStar_Parser_AST.aqual
            b.FStar_Parser_AST.battributes uu___ t phi
      | FStar_Parser_AST.TAnnotated uu___ -> failwith "Is this still used ?"
      | FStar_Parser_AST.Variable uu___ ->
          let uu___1 =
            let uu___2 = FStar_Parser_AST.binder_to_string b in
            FStar_Util.format1
              "Imposible : a refined binder ought to be annotated %s" uu___2 in
          failwith uu___1
      | FStar_Parser_AST.TVariable uu___ ->
          let uu___1 =
            let uu___2 = FStar_Parser_AST.binder_to_string b in
            FStar_Util.format1
              "Imposible : a refined binder ought to be annotated %s" uu___2 in
          failwith uu___1
      | FStar_Parser_AST.NoName uu___ ->
          let uu___1 =
            let uu___2 = FStar_Parser_AST.binder_to_string b in
            FStar_Util.format1
              "Imposible : a refined binder ought to be annotated %s" uu___2 in
          failwith uu___1
and (p_simpleDef :
  Prims.bool ->
    (FStar_Ident.lid * FStar_Parser_AST.term) -> FStar_Pprint.document)
  =
  fun ps ->
    fun uu___ ->
      match uu___ with
      | (lid, e) ->
          let uu___1 =
            let uu___2 = p_qlident lid in
            let uu___3 =
              let uu___4 = p_noSeqTermAndComment ps false e in
              FStar_Pprint.op_Hat_Slash_Hat FStar_Pprint.equals uu___4 in
            FStar_Pprint.op_Hat_Slash_Hat uu___2 uu___3 in
          FStar_Pprint.group uu___1
and (p_appTerm : FStar_Parser_AST.term -> FStar_Pprint.document) =
  fun e ->
    match e.FStar_Parser_AST.tm with
    | FStar_Parser_AST.App uu___ when is_general_application e ->
        let uu___1 = head_and_args e in
        (match uu___1 with
         | (head, args) ->
             (match args with
              | e1::e2::[] when
                  (FStar_Pervasives_Native.snd e1) = FStar_Parser_AST.Infix
                  ->
                  let uu___2 = p_argTerm e1 in
                  let uu___3 =
                    let uu___4 =
                      let uu___5 =
                        let uu___6 = str "`" in
                        let uu___7 =
                          let uu___8 = p_indexingTerm head in
                          let uu___9 = str "`" in
                          FStar_Pprint.op_Hat_Hat uu___8 uu___9 in
                        FStar_Pprint.op_Hat_Hat uu___6 uu___7 in
                      FStar_Pprint.group uu___5 in
                    let uu___5 = p_argTerm e2 in
                    FStar_Pprint.op_Hat_Slash_Hat uu___4 uu___5 in
                  FStar_Pprint.op_Hat_Slash_Hat uu___2 uu___3
              | uu___2 ->
                  let uu___3 =
                    let uu___4 = FStar_ST.op_Bang should_print_fs_typ_app in
                    if uu___4
                    then
                      let uu___5 =
                        FStar_Util.take
                          (fun uu___6 ->
                             match uu___6 with
                             | (uu___7, aq) -> aq = FStar_Parser_AST.FsTypApp)
                          args in
                      match uu___5 with
                      | (fs_typ_args, args1) ->
                          let uu___6 =
                            let uu___7 = p_indexingTerm head in
                            let uu___8 =
                              let uu___9 =
                                FStar_Pprint.op_Hat_Hat FStar_Pprint.comma
                                  break1 in
                              soft_surround_map_or_flow (Prims.of_int (2))
                                Prims.int_zero FStar_Pprint.empty
                                FStar_Pprint.langle uu___9
                                FStar_Pprint.rangle p_fsTypArg fs_typ_args in
                            FStar_Pprint.op_Hat_Hat uu___7 uu___8 in
                          (uu___6, args1)
                    else (let uu___6 = p_indexingTerm head in (uu___6, args)) in
                  (match uu___3 with
                   | (head_doc, args1) ->
                       let uu___4 =
                         let uu___5 =
                           FStar_Pprint.op_Hat_Hat head_doc
                             FStar_Pprint.space in
                         soft_surround_map_or_flow (Prims.of_int (2))
                           Prims.int_zero head_doc uu___5 break1
                           FStar_Pprint.empty p_argTerm args1 in
                       FStar_Pprint.group uu___4)))
    | FStar_Parser_AST.Construct (lid, args) when
        (is_general_construction e) &&
          (let uu___ = (is_dtuple_constructor lid) && (all1_explicit args) in
           Prims.op_Negation uu___)
        ->
        (match args with
         | [] -> p_quident lid
         | arg::[] ->
             let uu___ =
               let uu___1 = p_quident lid in
               let uu___2 = p_argTerm arg in
               FStar_Pprint.op_Hat_Slash_Hat uu___1 uu___2 in
             FStar_Pprint.group uu___
         | hd::tl ->
             let uu___ =
               let uu___1 =
                 let uu___2 =
                   let uu___3 = p_quident lid in
                   let uu___4 = p_argTerm hd in prefix2 uu___3 uu___4 in
                 FStar_Pprint.group uu___2 in
               let uu___2 =
                 let uu___3 = FStar_Pprint.separate_map break1 p_argTerm tl in
                 jump2 uu___3 in
               FStar_Pprint.op_Hat_Hat uu___1 uu___2 in
             FStar_Pprint.group uu___)
    | uu___ -> p_indexingTerm e
and (p_argTerm :
  (FStar_Parser_AST.term * FStar_Parser_AST.imp) -> FStar_Pprint.document) =
  fun arg_imp ->
    match arg_imp with
    | (u, FStar_Parser_AST.UnivApp) -> p_universe u
    | (e, FStar_Parser_AST.FsTypApp) ->
        (FStar_Errors.log_issue e.FStar_Parser_AST.range
           (FStar_Errors.Warning_UnexpectedFsTypApp,
             "Unexpected FsTypApp, output might not be formatted correctly.");
         (let uu___1 = p_indexingTerm e in
          FStar_Pprint.surround (Prims.of_int (2)) Prims.int_one
            FStar_Pprint.langle uu___1 FStar_Pprint.rangle))
    | (e, FStar_Parser_AST.Hash) ->
        let uu___ = str "#" in
        let uu___1 = p_indexingTerm e in FStar_Pprint.op_Hat_Hat uu___ uu___1
    | (e, FStar_Parser_AST.HashBrace t) ->
        let uu___ = str "#[" in
        let uu___1 =
          let uu___2 = p_indexingTerm t in
          let uu___3 =
            let uu___4 = str "]" in
            let uu___5 = p_indexingTerm e in
            FStar_Pprint.op_Hat_Hat uu___4 uu___5 in
          FStar_Pprint.op_Hat_Hat uu___2 uu___3 in
        FStar_Pprint.op_Hat_Hat uu___ uu___1
    | (e, FStar_Parser_AST.Infix) -> p_indexingTerm e
    | (e, FStar_Parser_AST.Nothing) -> p_indexingTerm e
and (p_fsTypArg :
  (FStar_Parser_AST.term * FStar_Parser_AST.imp) -> FStar_Pprint.document) =
  fun uu___ -> match uu___ with | (e, uu___1) -> p_indexingTerm e
and (p_indexingTerm_aux :
  (FStar_Parser_AST.term -> FStar_Pprint.document) ->
    FStar_Parser_AST.term -> FStar_Pprint.document)
  =
  fun exit ->
    fun e ->
      match e.FStar_Parser_AST.tm with
      | FStar_Parser_AST.Op (id, e1::e2::[]) when
          let uu___ = FStar_Ident.string_of_id id in uu___ = ".()" ->
          let uu___ =
            let uu___1 = p_indexingTerm_aux p_atomicTermNotQUident e1 in
            let uu___2 =
              let uu___3 =
                let uu___4 = p_term false false e2 in
                soft_parens_with_nesting uu___4 in
              FStar_Pprint.op_Hat_Hat FStar_Pprint.dot uu___3 in
            FStar_Pprint.op_Hat_Hat uu___1 uu___2 in
          FStar_Pprint.group uu___
      | FStar_Parser_AST.Op (id, e1::e2::[]) when
          let uu___ = FStar_Ident.string_of_id id in uu___ = ".[]" ->
          let uu___ =
            let uu___1 = p_indexingTerm_aux p_atomicTermNotQUident e1 in
            let uu___2 =
              let uu___3 =
                let uu___4 = p_term false false e2 in
                soft_brackets_with_nesting uu___4 in
              FStar_Pprint.op_Hat_Hat FStar_Pprint.dot uu___3 in
            FStar_Pprint.op_Hat_Hat uu___1 uu___2 in
          FStar_Pprint.group uu___
      | uu___ -> exit e
and (p_indexingTerm : FStar_Parser_AST.term -> FStar_Pprint.document) =
  fun e -> p_indexingTerm_aux p_atomicTerm e
and (p_atomicTerm : FStar_Parser_AST.term -> FStar_Pprint.document) =
  fun e ->
    match e.FStar_Parser_AST.tm with
    | FStar_Parser_AST.LetOpen (lid, e1) ->
        let uu___ = p_quident lid in
        let uu___1 =
          let uu___2 =
            let uu___3 = p_term false false e1 in
            soft_parens_with_nesting uu___3 in
          FStar_Pprint.op_Hat_Hat FStar_Pprint.dot uu___2 in
        FStar_Pprint.op_Hat_Hat uu___ uu___1
    | FStar_Parser_AST.Name lid -> p_quident lid
    | FStar_Parser_AST.Op (op, e1::[]) when is_general_prefix_op op ->
        let uu___ = let uu___1 = FStar_Ident.string_of_id op in str uu___1 in
        let uu___1 = p_atomicTerm e1 in FStar_Pprint.op_Hat_Hat uu___ uu___1
    | uu___ -> p_atomicTermNotQUident e
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
         | uu___ -> p_constant c)
    | FStar_Parser_AST.Name lid when
        FStar_Ident.lid_equals lid FStar_Parser_Const.true_lid -> str "True"
    | FStar_Parser_AST.Name lid when
        FStar_Ident.lid_equals lid FStar_Parser_Const.false_lid ->
        str "False"
    | FStar_Parser_AST.Op (op, e1::[]) when is_general_prefix_op op ->
        let uu___ = let uu___1 = FStar_Ident.string_of_id op in str uu___1 in
        let uu___1 = p_atomicTermNotQUident e1 in
        FStar_Pprint.op_Hat_Hat uu___ uu___1
    | FStar_Parser_AST.Op (op, []) ->
        let uu___ =
          let uu___1 =
            let uu___2 =
              let uu___3 = FStar_Ident.string_of_id op in str uu___3 in
            let uu___3 =
              FStar_Pprint.op_Hat_Hat FStar_Pprint.space FStar_Pprint.rparen in
            FStar_Pprint.op_Hat_Hat uu___2 uu___3 in
          FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu___1 in
        FStar_Pprint.op_Hat_Hat FStar_Pprint.lparen uu___
    | FStar_Parser_AST.Construct (lid, args) when
        (is_dtuple_constructor lid) && (all1_explicit args) ->
        let uu___ =
          FStar_Pprint.op_Hat_Hat FStar_Pprint.lparen FStar_Pprint.bar in
        let uu___1 =
          let uu___2 = FStar_Pprint.op_Hat_Hat FStar_Pprint.comma break1 in
          FStar_Pprint.separate_map uu___2
            (fun uu___3 -> match uu___3 with | (e1, uu___4) -> p_tmEq e1)
            args in
        let uu___2 =
          FStar_Pprint.op_Hat_Hat FStar_Pprint.bar FStar_Pprint.rparen in
        FStar_Pprint.surround (Prims.of_int (2)) Prims.int_one uu___ uu___1
          uu___2
    | FStar_Parser_AST.Project (e1, lid) ->
        let uu___ =
          let uu___1 = p_atomicTermNotQUident e1 in
          let uu___2 =
            let uu___3 = p_qlident lid in
            FStar_Pprint.op_Hat_Hat FStar_Pprint.dot uu___3 in
          FStar_Pprint.prefix (Prims.of_int (2)) Prims.int_zero uu___1 uu___2 in
        FStar_Pprint.group uu___
    | uu___ -> p_projectionLHS e
and (p_projectionLHS : FStar_Parser_AST.term -> FStar_Pprint.document) =
  fun e ->
    match e.FStar_Parser_AST.tm with
    | FStar_Parser_AST.Var lid -> p_qlident lid
    | FStar_Parser_AST.Projector (constr_lid, field_lid) ->
        let uu___ = p_quident constr_lid in
        let uu___1 =
          let uu___2 =
            let uu___3 = p_lident field_lid in
            FStar_Pprint.op_Hat_Hat FStar_Pprint.dot uu___3 in
          FStar_Pprint.op_Hat_Hat FStar_Pprint.qmark uu___2 in
        FStar_Pprint.op_Hat_Hat uu___ uu___1
    | FStar_Parser_AST.Discrim constr_lid ->
        let uu___ = p_quident constr_lid in
        FStar_Pprint.op_Hat_Hat uu___ FStar_Pprint.qmark
    | FStar_Parser_AST.Paren e1 ->
        let uu___ = p_term_sep false false e1 in
        (match uu___ with
         | (comm, t) ->
             let doc = soft_parens_with_nesting t in
             if comm = FStar_Pprint.empty
             then doc
             else
               (let uu___2 =
                  FStar_Pprint.op_Hat_Hat FStar_Pprint.hardline doc in
                FStar_Pprint.op_Hat_Hat comm uu___2))
    | uu___ when is_array e ->
        let es = extract_from_list e in
        let uu___1 =
          FStar_Pprint.op_Hat_Hat FStar_Pprint.lbracket FStar_Pprint.bar in
        let uu___2 =
          let uu___3 = FStar_Pprint.op_Hat_Hat FStar_Pprint.semi break1 in
          separate_map_or_flow_last uu___3
            (fun ps -> p_noSeqTermAndComment ps false) es in
        let uu___3 =
          FStar_Pprint.op_Hat_Hat FStar_Pprint.bar FStar_Pprint.rbracket in
        FStar_Pprint.surround (Prims.of_int (2)) Prims.int_zero uu___1 uu___2
          uu___3
    | uu___ when is_list e ->
        let uu___1 =
          let uu___2 = FStar_Pprint.op_Hat_Hat FStar_Pprint.semi break1 in
          let uu___3 = extract_from_list e in
          separate_map_or_flow_last uu___2
            (fun ps -> p_noSeqTermAndComment ps false) uu___3 in
        FStar_Pprint.surround (Prims.of_int (2)) Prims.int_zero
          FStar_Pprint.lbracket uu___1 FStar_Pprint.rbracket
    | uu___ when is_ref_set e ->
        let es = extract_from_ref_set e in
        let uu___1 =
          FStar_Pprint.op_Hat_Hat FStar_Pprint.bang FStar_Pprint.lbrace in
        let uu___2 =
          let uu___3 = FStar_Pprint.op_Hat_Hat FStar_Pprint.comma break1 in
          separate_map_or_flow uu___3 p_appTerm es in
        FStar_Pprint.surround (Prims.of_int (2)) Prims.int_zero uu___1 uu___2
          FStar_Pprint.rbrace
    | FStar_Parser_AST.Labeled (e1, s, b) ->
        let uu___ = str (Prims.op_Hat "(*" (Prims.op_Hat s "*)")) in
        let uu___1 = p_term false false e1 in
        FStar_Pprint.op_Hat_Slash_Hat uu___ uu___1
    | FStar_Parser_AST.Op (op, args) when
        let uu___ = handleable_op op args in Prims.op_Negation uu___ ->
        let uu___ =
          let uu___1 =
            let uu___2 = FStar_Ident.string_of_id op in
            let uu___3 =
              let uu___4 =
                let uu___5 =
                  FStar_Util.string_of_int (FStar_List.length args) in
                Prims.op_Hat uu___5
                  " arguments couldn't be handled by the pretty printer" in
              Prims.op_Hat " with " uu___4 in
            Prims.op_Hat uu___2 uu___3 in
          Prims.op_Hat "Operation " uu___1 in
        failwith uu___
    | FStar_Parser_AST.Uvar id ->
        failwith "Unexpected universe variable out of universe context"
    | FStar_Parser_AST.Wild ->
        let uu___ = p_term false false e in soft_parens_with_nesting uu___
    | FStar_Parser_AST.Const uu___ ->
        let uu___1 = p_term false false e in soft_parens_with_nesting uu___1
    | FStar_Parser_AST.Op uu___ ->
        let uu___1 = p_term false false e in soft_parens_with_nesting uu___1
    | FStar_Parser_AST.Tvar uu___ ->
        let uu___1 = p_term false false e in soft_parens_with_nesting uu___1
    | FStar_Parser_AST.Var uu___ ->
        let uu___1 = p_term false false e in soft_parens_with_nesting uu___1
    | FStar_Parser_AST.Name uu___ ->
        let uu___1 = p_term false false e in soft_parens_with_nesting uu___1
    | FStar_Parser_AST.Construct uu___ ->
        let uu___1 = p_term false false e in soft_parens_with_nesting uu___1
    | FStar_Parser_AST.Abs uu___ ->
        let uu___1 = p_term false false e in soft_parens_with_nesting uu___1
    | FStar_Parser_AST.App uu___ ->
        let uu___1 = p_term false false e in soft_parens_with_nesting uu___1
    | FStar_Parser_AST.Let uu___ ->
        let uu___1 = p_term false false e in soft_parens_with_nesting uu___1
    | FStar_Parser_AST.LetOpen uu___ ->
        let uu___1 = p_term false false e in soft_parens_with_nesting uu___1
    | FStar_Parser_AST.LetOpenRecord uu___ ->
        let uu___1 = p_term false false e in soft_parens_with_nesting uu___1
    | FStar_Parser_AST.Seq uu___ ->
        let uu___1 = p_term false false e in soft_parens_with_nesting uu___1
    | FStar_Parser_AST.Bind uu___ ->
        let uu___1 = p_term false false e in soft_parens_with_nesting uu___1
    | FStar_Parser_AST.If uu___ ->
        let uu___1 = p_term false false e in soft_parens_with_nesting uu___1
    | FStar_Parser_AST.Match uu___ ->
        let uu___1 = p_term false false e in soft_parens_with_nesting uu___1
    | FStar_Parser_AST.TryWith uu___ ->
        let uu___1 = p_term false false e in soft_parens_with_nesting uu___1
    | FStar_Parser_AST.Ascribed uu___ ->
        let uu___1 = p_term false false e in soft_parens_with_nesting uu___1
    | FStar_Parser_AST.Record uu___ ->
        let uu___1 = p_term false false e in soft_parens_with_nesting uu___1
    | FStar_Parser_AST.Project uu___ ->
        let uu___1 = p_term false false e in soft_parens_with_nesting uu___1
    | FStar_Parser_AST.Product uu___ ->
        let uu___1 = p_term false false e in soft_parens_with_nesting uu___1
    | FStar_Parser_AST.Sum uu___ ->
        let uu___1 = p_term false false e in soft_parens_with_nesting uu___1
    | FStar_Parser_AST.QForall uu___ ->
        let uu___1 = p_term false false e in soft_parens_with_nesting uu___1
    | FStar_Parser_AST.QExists uu___ ->
        let uu___1 = p_term false false e in soft_parens_with_nesting uu___1
    | FStar_Parser_AST.Refine uu___ ->
        let uu___1 = p_term false false e in soft_parens_with_nesting uu___1
    | FStar_Parser_AST.NamedTyp uu___ ->
        let uu___1 = p_term false false e in soft_parens_with_nesting uu___1
    | FStar_Parser_AST.Requires uu___ ->
        let uu___1 = p_term false false e in soft_parens_with_nesting uu___1
    | FStar_Parser_AST.Ensures uu___ ->
        let uu___1 = p_term false false e in soft_parens_with_nesting uu___1
    | FStar_Parser_AST.Decreases uu___ ->
        let uu___1 = p_term false false e in soft_parens_with_nesting uu___1
    | FStar_Parser_AST.Attributes uu___ ->
        let uu___1 = p_term false false e in soft_parens_with_nesting uu___1
    | FStar_Parser_AST.Quote uu___ ->
        let uu___1 = p_term false false e in soft_parens_with_nesting uu___1
    | FStar_Parser_AST.VQuote uu___ ->
        let uu___1 = p_term false false e in soft_parens_with_nesting uu___1
    | FStar_Parser_AST.Antiquote uu___ ->
        let uu___1 = p_term false false e in soft_parens_with_nesting uu___1
    | FStar_Parser_AST.CalcProof uu___ ->
        let uu___1 = p_term false false e in soft_parens_with_nesting uu___1
    | FStar_Parser_AST.LexList l ->
        let uu___ =
          let uu___1 = str "%" in
          let uu___2 = p_term_list false false l in
          FStar_Pprint.op_Hat_Hat uu___1 uu___2 in
        FStar_Pprint.group uu___
    | FStar_Parser_AST.WFOrder (rel, e1) -> p_dec_wf false false rel e1
and (p_constant : FStar_Const.sconst -> FStar_Pprint.document) =
  fun uu___ ->
    match uu___ with
    | FStar_Const.Const_effect -> str "Effect"
    | FStar_Const.Const_unit -> str "()"
    | FStar_Const.Const_bool b -> FStar_Pprint.doc_of_bool b
    | FStar_Const.Const_real r -> str (Prims.op_Hat r "R")
    | FStar_Const.Const_float x -> str (FStar_Util.string_of_float x)
    | FStar_Const.Const_char x -> FStar_Pprint.doc_of_char x
    | FStar_Const.Const_string (s, uu___1) ->
        let uu___2 = str (FStar_String.escaped s) in
        FStar_Pprint.dquotes uu___2
    | FStar_Const.Const_bytearray (bytes, uu___1) ->
        let uu___2 =
          let uu___3 = str (FStar_Util.string_of_bytes bytes) in
          FStar_Pprint.dquotes uu___3 in
        let uu___3 = str "B" in FStar_Pprint.op_Hat_Hat uu___2 uu___3
    | FStar_Const.Const_int (repr, sign_width_opt) ->
        let signedness uu___1 =
          match uu___1 with
          | FStar_Const.Unsigned -> str "u"
          | FStar_Const.Signed -> FStar_Pprint.empty in
        let width uu___1 =
          match uu___1 with
          | FStar_Const.Int8 -> str "y"
          | FStar_Const.Int16 -> str "s"
          | FStar_Const.Int32 -> str "l"
          | FStar_Const.Int64 -> str "L" in
        let ending =
          default_or_map FStar_Pprint.empty
            (fun uu___1 ->
               match uu___1 with
               | (s, w) ->
                   let uu___2 = signedness s in
                   let uu___3 = width w in
                   FStar_Pprint.op_Hat_Hat uu___2 uu___3) sign_width_opt in
        let uu___1 = str repr in FStar_Pprint.op_Hat_Hat uu___1 ending
    | FStar_Const.Const_range_of -> str "range_of"
    | FStar_Const.Const_set_range_of -> str "set_range_of"
    | FStar_Const.Const_range r ->
        let uu___1 = FStar_Range.string_of_range r in str uu___1
    | FStar_Const.Const_reify -> str "reify"
    | FStar_Const.Const_reflect lid ->
        let uu___1 = p_quident lid in
        let uu___2 =
          let uu___3 =
            let uu___4 = str "reflect" in
            FStar_Pprint.op_Hat_Hat FStar_Pprint.dot uu___4 in
          FStar_Pprint.op_Hat_Hat FStar_Pprint.qmark uu___3 in
        FStar_Pprint.op_Hat_Hat uu___1 uu___2
and (p_universe : FStar_Parser_AST.term -> FStar_Pprint.document) =
  fun u ->
    let uu___ = str "u#" in
    let uu___1 = p_atomicUniverse u in FStar_Pprint.op_Hat_Hat uu___ uu___1
and (p_universeFrom : FStar_Parser_AST.term -> FStar_Pprint.document) =
  fun u ->
    match u.FStar_Parser_AST.tm with
    | FStar_Parser_AST.Op (id, u1::u2::[]) when
        let uu___ = FStar_Ident.string_of_id id in uu___ = "+" ->
        let uu___ =
          let uu___1 = p_universeFrom u1 in
          let uu___2 =
            let uu___3 = p_universeFrom u2 in
            FStar_Pprint.op_Hat_Slash_Hat FStar_Pprint.plus uu___3 in
          FStar_Pprint.op_Hat_Slash_Hat uu___1 uu___2 in
        FStar_Pprint.group uu___
    | FStar_Parser_AST.App uu___ ->
        let uu___1 = head_and_args u in
        (match uu___1 with
         | (head, args) ->
             (match head.FStar_Parser_AST.tm with
              | FStar_Parser_AST.Var maybe_max_lid when
                  FStar_Ident.lid_equals maybe_max_lid
                    FStar_Parser_Const.max_lid
                  ->
                  let uu___2 =
                    let uu___3 = p_qlident FStar_Parser_Const.max_lid in
                    let uu___4 =
                      FStar_Pprint.separate_map FStar_Pprint.space
                        (fun uu___5 ->
                           match uu___5 with
                           | (u1, uu___6) -> p_atomicUniverse u1) args in
                    op_Hat_Slash_Plus_Hat uu___3 uu___4 in
                  FStar_Pprint.group uu___2
              | uu___2 ->
                  let uu___3 =
                    let uu___4 = FStar_Parser_AST.term_to_string u in
                    FStar_Util.format1 "Invalid term in universe context %s"
                      uu___4 in
                  failwith uu___3))
    | uu___ -> p_atomicUniverse u
and (p_atomicUniverse : FStar_Parser_AST.term -> FStar_Pprint.document) =
  fun u ->
    match u.FStar_Parser_AST.tm with
    | FStar_Parser_AST.Wild -> FStar_Pprint.underscore
    | FStar_Parser_AST.Const (FStar_Const.Const_int (r, sw)) ->
        p_constant (FStar_Const.Const_int (r, sw))
    | FStar_Parser_AST.Uvar id ->
        let uu___ = FStar_Ident.string_of_id id in str uu___
    | FStar_Parser_AST.Paren u1 ->
        let uu___ = p_universeFrom u1 in soft_parens_with_nesting uu___
    | FStar_Parser_AST.App uu___ ->
        let uu___1 = p_universeFrom u in soft_parens_with_nesting uu___1
    | FStar_Parser_AST.Op (id, uu___::uu___1::[]) when
        let uu___2 = FStar_Ident.string_of_id id in uu___2 = "+" ->
        let uu___2 = p_universeFrom u in soft_parens_with_nesting uu___2
    | uu___ ->
        let uu___1 =
          let uu___2 = FStar_Parser_AST.term_to_string u in
          FStar_Util.format1 "Invalid term in universe context %s" uu___2 in
        failwith uu___1
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
       | FStar_Parser_AST.Module (uu___1, decls) ->
           let uu___2 =
             FStar_All.pipe_right decls (FStar_List.map decl_to_document) in
           FStar_All.pipe_right uu___2
             (FStar_Pprint.separate FStar_Pprint.hardline)
       | FStar_Parser_AST.Interface (uu___1, decls, uu___2) ->
           let uu___3 =
             FStar_All.pipe_right decls (FStar_List.map decl_to_document) in
           FStar_All.pipe_right uu___3
             (FStar_Pprint.separate FStar_Pprint.hardline) in
     FStar_ST.op_Colon_Equals should_print_fs_typ_app false; res)
let (comments_to_document :
  (Prims.string * FStar_Range.range) Prims.list -> FStar_Pprint.document) =
  fun comments ->
    FStar_Pprint.separate_map FStar_Pprint.hardline
      (fun uu___ -> match uu___ with | (comment, range) -> str comment)
      comments
let (extract_decl_range : FStar_Parser_AST.decl -> decl_meta) =
  fun d ->
    let has_qs =
      match ((d.FStar_Parser_AST.quals), (d.FStar_Parser_AST.d)) with
      | ((FStar_Parser_AST.Assumption)::[], FStar_Parser_AST.Assume
         (id, uu___)) -> false
      | ([], uu___) -> false
      | uu___ -> true in
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
        | FStar_Parser_AST.Module (uu___, decls1) -> decls1
        | FStar_Parser_AST.Interface (uu___, decls1, uu___1) -> decls1 in
      FStar_ST.op_Colon_Equals should_print_fs_typ_app false;
      (match decls with
       | [] -> (FStar_Pprint.empty, comments)
       | d::ds ->
           let uu___1 =
             match ds with
             | {
                 FStar_Parser_AST.d = FStar_Parser_AST.Pragma
                   (FStar_Parser_AST.LightOff);
                 FStar_Parser_AST.drange = uu___2;
                 FStar_Parser_AST.quals = uu___3;
                 FStar_Parser_AST.attrs = uu___4;_}::uu___5 ->
                 let d0 = FStar_List.hd ds in
                 let uu___6 =
                   let uu___7 = let uu___8 = FStar_List.tl ds in d :: uu___8 in
                   d0 :: uu___7 in
                 (uu___6, (d0.FStar_Parser_AST.drange))
             | uu___2 -> ((d :: ds), (d.FStar_Parser_AST.drange)) in
           (match uu___1 with
            | (decls1, first_range) ->
                (FStar_ST.op_Colon_Equals comment_stack comments;
                 (let initial_comment =
                    let uu___3 = FStar_Range.start_of_range first_range in
                    place_comments_until_pos Prims.int_zero Prims.int_one
                      uu___3 dummy_meta FStar_Pprint.empty false true in
                  let doc =
                    separate_map_with_comments FStar_Pprint.empty
                      FStar_Pprint.empty p_decl decls1 extract_decl_range in
                  let comments1 = FStar_ST.op_Bang comment_stack in
                  FStar_ST.op_Colon_Equals comment_stack [];
                  FStar_ST.op_Colon_Equals should_print_fs_typ_app false;
                  (let uu___5 = FStar_Pprint.op_Hat_Hat initial_comment doc in
                   (uu___5, comments1))))))