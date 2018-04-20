open Prims
let (should_print_fs_typ_app : Prims.bool FStar_ST.ref) =
  FStar_Util.mk_ref false
let with_fs_typ_app :
  'Auu____43 'Auu____44 .
    Prims.bool -> ('Auu____43 -> 'Auu____44) -> 'Auu____43 -> 'Auu____44
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
  'Auu____149 'Auu____150 .
    'Auu____149 ->
      ('Auu____150 -> 'Auu____149) ->
        'Auu____150 FStar_Pervasives_Native.option -> 'Auu____149
  =
  fun n1 ->
    fun f ->
      fun x ->
        match x with
        | FStar_Pervasives_Native.None -> n1
        | FStar_Pervasives_Native.Some x' -> f x'
let (prefix2 :
  FStar_Pprint.document -> FStar_Pprint.document -> FStar_Pprint.document) =
  fun prefix_ ->
    fun body ->
      FStar_Pprint.prefix (Prims.parse_int "2") (Prims.parse_int "1") prefix_
        body
let (op_Hat_Slash_Plus_Hat :
  FStar_Pprint.document -> FStar_Pprint.document -> FStar_Pprint.document) =
  fun prefix_ -> fun body -> prefix2 prefix_ body
let (jump2 : FStar_Pprint.document -> FStar_Pprint.document) =
  fun body ->
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
  'Auu____204 .
    FStar_Pprint.document ->
      ('Auu____204 -> FStar_Pprint.document) ->
        'Auu____204 Prims.list -> FStar_Pprint.document
  =
  fun sep ->
    fun f ->
      fun l ->
        let uu____226 =
          let uu____227 =
            let uu____228 = FStar_Pprint.op_Hat_Hat sep break1 in
            FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____228 in
          FStar_Pprint.separate_map uu____227 f l in
        FStar_Pprint.group uu____226
let precede_break_separate_map :
  'Auu____234 .
    FStar_Pprint.document ->
      FStar_Pprint.document ->
        ('Auu____234 -> FStar_Pprint.document) ->
          'Auu____234 Prims.list -> FStar_Pprint.document
  =
  fun prec ->
    fun sep ->
      fun f ->
        fun l ->
          let uu____260 =
            let uu____261 = FStar_Pprint.op_Hat_Hat prec FStar_Pprint.space in
            let uu____262 =
              let uu____263 = FStar_List.hd l in
              FStar_All.pipe_right uu____263 f in
            FStar_Pprint.precede uu____261 uu____262 in
          let uu____264 =
            let uu____265 = FStar_List.tl l in
            FStar_Pprint.concat_map
              (fun x ->
                 let uu____271 =
                   let uu____272 =
                     let uu____273 = f x in
                     FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____273 in
                   FStar_Pprint.op_Hat_Hat sep uu____272 in
                 FStar_Pprint.op_Hat_Hat break1 uu____271) uu____265 in
          FStar_Pprint.op_Hat_Hat uu____260 uu____264
let concat_break_map :
  'Auu____277 .
    ('Auu____277 -> FStar_Pprint.document) ->
      'Auu____277 Prims.list -> FStar_Pprint.document
  =
  fun f ->
    fun l ->
      let uu____295 =
        FStar_Pprint.concat_map
          (fun x ->
             let uu____299 = f x in FStar_Pprint.op_Hat_Hat uu____299 break1)
          l in
      FStar_Pprint.group uu____295
let (parens_with_nesting : FStar_Pprint.document -> FStar_Pprint.document) =
  fun contents ->
    FStar_Pprint.surround (Prims.parse_int "2") (Prims.parse_int "0")
      FStar_Pprint.lparen contents FStar_Pprint.rparen
let (soft_parens_with_nesting :
  FStar_Pprint.document -> FStar_Pprint.document) =
  fun contents ->
    FStar_Pprint.soft_surround (Prims.parse_int "2") (Prims.parse_int "0")
      FStar_Pprint.lparen contents FStar_Pprint.rparen
let (braces_with_nesting : FStar_Pprint.document -> FStar_Pprint.document) =
  fun contents ->
    FStar_Pprint.surround (Prims.parse_int "2") (Prims.parse_int "1")
      FStar_Pprint.lbrace contents FStar_Pprint.rbrace
let (soft_braces_with_nesting :
  FStar_Pprint.document -> FStar_Pprint.document) =
  fun contents ->
    FStar_Pprint.soft_surround (Prims.parse_int "2") (Prims.parse_int "1")
      FStar_Pprint.lbrace contents FStar_Pprint.rbrace
let (brackets_with_nesting : FStar_Pprint.document -> FStar_Pprint.document)
  =
  fun contents ->
    FStar_Pprint.surround (Prims.parse_int "2") (Prims.parse_int "1")
      FStar_Pprint.lbracket contents FStar_Pprint.rbracket
let (soft_brackets_with_nesting :
  FStar_Pprint.document -> FStar_Pprint.document) =
  fun contents ->
    FStar_Pprint.soft_surround (Prims.parse_int "2") (Prims.parse_int "1")
      FStar_Pprint.lbracket contents FStar_Pprint.rbracket
let (soft_begin_end_with_nesting :
  FStar_Pprint.document -> FStar_Pprint.document) =
  fun contents ->
    let uu____321 = str "begin" in
    let uu____322 = str "end" in
    FStar_Pprint.soft_surround (Prims.parse_int "2") (Prims.parse_int "1")
      uu____321 contents uu____322
let separate_map_last :
  'Auu____327 .
    FStar_Pprint.document ->
      (Prims.bool -> 'Auu____327 -> FStar_Pprint.document) ->
        'Auu____327 Prims.list -> FStar_Pprint.document
  =
  fun sep ->
    fun f ->
      fun es ->
        let l = FStar_List.length es in
        let es1 =
          FStar_List.mapi
            (fun i -> fun e -> f (i <> (l - (Prims.parse_int "1"))) e) es in
        FStar_Pprint.separate sep es1
let separate_break_map_last :
  'Auu____372 .
    FStar_Pprint.document ->
      (Prims.bool -> 'Auu____372 -> FStar_Pprint.document) ->
        'Auu____372 Prims.list -> FStar_Pprint.document
  =
  fun sep ->
    fun f ->
      fun l ->
        let uu____399 =
          let uu____400 =
            let uu____401 = FStar_Pprint.op_Hat_Hat sep break1 in
            FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____401 in
          separate_map_last uu____400 f l in
        FStar_Pprint.group uu____399
let separate_map_or_flow :
  'Auu____406 .
    FStar_Pprint.document ->
      ('Auu____406 -> FStar_Pprint.document) ->
        'Auu____406 Prims.list -> FStar_Pprint.document
  =
  fun sep ->
    fun f ->
      fun l ->
        if (FStar_List.length l) < (Prims.parse_int "10")
        then FStar_Pprint.separate_map sep f l
        else FStar_Pprint.flow_map sep f l
let flow_map_last :
  'Auu____433 .
    FStar_Pprint.document ->
      (Prims.bool -> 'Auu____433 -> FStar_Pprint.document) ->
        'Auu____433 Prims.list -> FStar_Pprint.document
  =
  fun sep ->
    fun f ->
      fun es ->
        let l = FStar_List.length es in
        let es1 =
          FStar_List.mapi
            (fun i -> fun e -> f (i <> (l - (Prims.parse_int "1"))) e) es in
        FStar_Pprint.flow sep es1
let separate_map_or_flow_last :
  'Auu____478 .
    FStar_Pprint.document ->
      (Prims.bool -> 'Auu____478 -> FStar_Pprint.document) ->
        'Auu____478 Prims.list -> FStar_Pprint.document
  =
  fun sep ->
    fun f ->
      fun l ->
        if (FStar_List.length l) < (Prims.parse_int "10")
        then separate_map_last sep f l
        else flow_map_last sep f l
let soft_surround_separate_map :
  'Auu____515 .
    Prims.int ->
      Prims.int ->
        FStar_Pprint.document ->
          FStar_Pprint.document ->
            FStar_Pprint.document ->
              FStar_Pprint.document ->
                ('Auu____515 -> FStar_Pprint.document) ->
                  'Auu____515 Prims.list -> FStar_Pprint.document
  =
  fun n1 ->
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
                    (let uu____560 = FStar_Pprint.separate_map sep f xs in
                     FStar_Pprint.soft_surround n1 b opening uu____560
                       closing)
let soft_surround_map_or_flow :
  'Auu____570 .
    Prims.int ->
      Prims.int ->
        FStar_Pprint.document ->
          FStar_Pprint.document ->
            FStar_Pprint.document ->
              FStar_Pprint.document ->
                ('Auu____570 -> FStar_Pprint.document) ->
                  'Auu____570 Prims.list -> FStar_Pprint.document
  =
  fun n1 ->
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
                    (let uu____615 = separate_map_or_flow sep f xs in
                     FStar_Pprint.soft_surround n1 b opening uu____615
                       closing)
let (doc_of_fsdoc :
  (Prims.string,
    (Prims.string, Prims.string) FStar_Pervasives_Native.tuple2 Prims.list)
    FStar_Pervasives_Native.tuple2 -> FStar_Pprint.document)
  =
  fun uu____628 ->
    match uu____628 with
    | (comment, keywords) ->
        let uu____653 =
          let uu____654 =
            let uu____657 = str comment in
            let uu____658 =
              let uu____661 =
                let uu____664 =
                  FStar_Pprint.separate_map FStar_Pprint.comma
                    (fun uu____673 ->
                       match uu____673 with
                       | (k, v1) ->
                           let uu____680 =
                             let uu____683 = str k in
                             let uu____684 =
                               let uu____687 =
                                 let uu____690 = str v1 in [uu____690] in
                               FStar_Pprint.rarrow :: uu____687 in
                             uu____683 :: uu____684 in
                           FStar_Pprint.concat uu____680) keywords in
                [uu____664] in
              FStar_Pprint.space :: uu____661 in
            uu____657 :: uu____658 in
          FStar_Pprint.concat uu____654 in
        FStar_Pprint.group uu____653
let (is_unit : FStar_Parser_AST.term -> Prims.bool) =
  fun e ->
    match e.FStar_Parser_AST.tm with
    | FStar_Parser_AST.Const (FStar_Const.Const_unit) -> true
    | uu____694 -> false
let (matches_var : FStar_Parser_AST.term -> FStar_Ident.ident -> Prims.bool)
  =
  fun t ->
    fun x ->
      match t.FStar_Parser_AST.tm with
      | FStar_Parser_AST.Var y ->
          x.FStar_Ident.idText = (FStar_Ident.text_of_lid y)
      | uu____702 -> false
let (is_tuple_constructor : FStar_Ident.lident -> Prims.bool) =
  FStar_Parser_Const.is_tuple_data_lid'
let (is_dtuple_constructor : FStar_Ident.lident -> Prims.bool) =
  FStar_Parser_Const.is_dtuple_data_lid'
let (is_list_structure :
  FStar_Ident.lident ->
    FStar_Ident.lident -> FStar_Parser_AST.term -> Prims.bool)
  =
  fun cons_lid1 ->
    fun nil_lid1 ->
      let rec aux e =
        match e.FStar_Parser_AST.tm with
        | FStar_Parser_AST.Construct (lid, []) ->
            FStar_Ident.lid_equals lid nil_lid1
        | FStar_Parser_AST.Construct (lid, uu____731::(e2, uu____733)::[]) ->
            (FStar_Ident.lid_equals lid cons_lid1) && (aux e2)
        | uu____756 -> false in
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
    | FStar_Parser_AST.Construct (uu____768, []) -> []
    | FStar_Parser_AST.Construct
        (uu____779,
         (e1, FStar_Parser_AST.Nothing)::(e2, FStar_Parser_AST.Nothing)::[])
        -> let uu____800 = extract_from_list e2 in e1 :: uu____800
    | uu____803 ->
        let uu____804 =
          let uu____805 = FStar_Parser_AST.term_to_string e in
          FStar_Util.format1 "Not a list %s" uu____805 in
        failwith uu____804
let (is_array : FStar_Parser_AST.term -> Prims.bool) =
  fun e ->
    match e.FStar_Parser_AST.tm with
    | FStar_Parser_AST.App
        ({ FStar_Parser_AST.tm = FStar_Parser_AST.Var lid;
           FStar_Parser_AST.range = uu____812;
           FStar_Parser_AST.level = uu____813;_},
         l, FStar_Parser_AST.Nothing)
        ->
        (FStar_Ident.lid_equals lid FStar_Parser_Const.array_mk_array_lid) &&
          (is_list l)
    | uu____815 -> false
let rec (is_ref_set : FStar_Parser_AST.term -> Prims.bool) =
  fun e ->
    match e.FStar_Parser_AST.tm with
    | FStar_Parser_AST.Var maybe_empty_lid ->
        FStar_Ident.lid_equals maybe_empty_lid FStar_Parser_Const.set_empty
    | FStar_Parser_AST.App
        ({ FStar_Parser_AST.tm = FStar_Parser_AST.Var maybe_singleton_lid;
           FStar_Parser_AST.range = uu____821;
           FStar_Parser_AST.level = uu____822;_},
         {
           FStar_Parser_AST.tm = FStar_Parser_AST.App
             ({ FStar_Parser_AST.tm = FStar_Parser_AST.Var maybe_addr_of_lid;
                FStar_Parser_AST.range = uu____824;
                FStar_Parser_AST.level = uu____825;_},
              e1, FStar_Parser_AST.Nothing);
           FStar_Parser_AST.range = uu____827;
           FStar_Parser_AST.level = uu____828;_},
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
                FStar_Parser_AST.range = uu____830;
                FStar_Parser_AST.level = uu____831;_},
              e1, FStar_Parser_AST.Nothing);
           FStar_Parser_AST.range = uu____833;
           FStar_Parser_AST.level = uu____834;_},
         e2, FStar_Parser_AST.Nothing)
        ->
        ((FStar_Ident.lid_equals maybe_union_lid FStar_Parser_Const.set_union)
           && (is_ref_set e1))
          && (is_ref_set e2)
    | uu____836 -> false
let rec (extract_from_ref_set :
  FStar_Parser_AST.term -> FStar_Parser_AST.term Prims.list) =
  fun e ->
    match e.FStar_Parser_AST.tm with
    | FStar_Parser_AST.Var uu____844 -> []
    | FStar_Parser_AST.App
        ({ FStar_Parser_AST.tm = FStar_Parser_AST.Var uu____845;
           FStar_Parser_AST.range = uu____846;
           FStar_Parser_AST.level = uu____847;_},
         {
           FStar_Parser_AST.tm = FStar_Parser_AST.App
             ({ FStar_Parser_AST.tm = FStar_Parser_AST.Var uu____848;
                FStar_Parser_AST.range = uu____849;
                FStar_Parser_AST.level = uu____850;_},
              e1, FStar_Parser_AST.Nothing);
           FStar_Parser_AST.range = uu____852;
           FStar_Parser_AST.level = uu____853;_},
         FStar_Parser_AST.Nothing)
        -> [e1]
    | FStar_Parser_AST.App
        ({
           FStar_Parser_AST.tm = FStar_Parser_AST.App
             ({ FStar_Parser_AST.tm = FStar_Parser_AST.Var uu____854;
                FStar_Parser_AST.range = uu____855;
                FStar_Parser_AST.level = uu____856;_},
              e1, FStar_Parser_AST.Nothing);
           FStar_Parser_AST.range = uu____858;
           FStar_Parser_AST.level = uu____859;_},
         e2, FStar_Parser_AST.Nothing)
        ->
        let uu____861 = extract_from_ref_set e1 in
        let uu____864 = extract_from_ref_set e2 in
        FStar_List.append uu____861 uu____864
    | uu____867 ->
        let uu____868 =
          let uu____869 = FStar_Parser_AST.term_to_string e in
          FStar_Util.format1 "Not a ref set %s" uu____869 in
        failwith uu____868
let (is_general_application : FStar_Parser_AST.term -> Prims.bool) =
  fun e ->
    let uu____875 = (is_array e) || (is_ref_set e) in
    Prims.op_Negation uu____875
let (is_general_construction : FStar_Parser_AST.term -> Prims.bool) =
  fun e ->
    let uu____879 = (is_list e) || (is_lex_list e) in
    Prims.op_Negation uu____879
let (is_general_prefix_op : FStar_Ident.ident -> Prims.bool) =
  fun op ->
    let op_starting_char =
      FStar_Util.char_at (FStar_Ident.text_of_id op) (Prims.parse_int "0") in
    ((op_starting_char = 33) || (op_starting_char = 63)) ||
      ((op_starting_char = 126) && ((FStar_Ident.text_of_id op) <> "~"))
let (head_and_args :
  FStar_Parser_AST.term ->
    (FStar_Parser_AST.term,
      (FStar_Parser_AST.term, FStar_Parser_AST.imp)
        FStar_Pervasives_Native.tuple2 Prims.list)
      FStar_Pervasives_Native.tuple2)
  =
  fun e ->
    let rec aux e1 acc =
      match e1.FStar_Parser_AST.tm with
      | FStar_Parser_AST.App (head1, arg, imp) ->
          aux head1 ((arg, imp) :: acc)
      | uu____946 -> (e1, acc) in
    aux e []
type associativity =
  | Left 
  | Right 
  | NonAssoc [@@deriving show]
let (uu___is_Left : associativity -> Prims.bool) =
  fun projectee -> match projectee with | Left -> true | uu____960 -> false
let (uu___is_Right : associativity -> Prims.bool) =
  fun projectee -> match projectee with | Right -> true | uu____964 -> false
let (uu___is_NonAssoc : associativity -> Prims.bool) =
  fun projectee ->
    match projectee with | NonAssoc -> true | uu____968 -> false
type token = (FStar_Char.char, Prims.string) FStar_Util.either[@@deriving
                                                                show]
type associativity_level =
  (associativity, token Prims.list) FStar_Pervasives_Native.tuple2[@@deriving
                                                                    show]
let (token_to_string :
  (FStar_BaseTypes.char, Prims.string) FStar_Util.either -> Prims.string) =
  fun uu___54_986 ->
    match uu___54_986 with
    | FStar_Util.Inl c -> Prims.strcat (FStar_Util.string_of_char c) ".*"
    | FStar_Util.Inr s -> s
let (matches_token :
  Prims.string ->
    (FStar_Char.char, Prims.string) FStar_Util.either -> Prims.bool)
  =
  fun s ->
    fun uu___55_1003 ->
      match uu___55_1003 with
      | FStar_Util.Inl c ->
          let uu____1012 = FStar_String.get s (Prims.parse_int "0") in
          uu____1012 = c
      | FStar_Util.Inr s' -> s = s'
let matches_level :
  'Auu____1020 .
    Prims.string ->
      ('Auu____1020,
        (FStar_Char.char, Prims.string) FStar_Util.either Prims.list)
        FStar_Pervasives_Native.tuple2 -> Prims.bool
  =
  fun s ->
    fun uu____1039 ->
      match uu____1039 with
      | (assoc_levels, tokens) ->
          let uu____1067 = FStar_List.tryFind (matches_token s) tokens in
          uu____1067 <> FStar_Pervasives_Native.None
let opinfix4 :
  'Auu____1093 .
    Prims.unit ->
      (associativity,
        ('Auu____1093, Prims.string) FStar_Util.either Prims.list)
        FStar_Pervasives_Native.tuple2
  = fun uu____1104 -> (Right, [FStar_Util.Inr "**"])
let opinfix3 :
  'Auu____1120 .
    Prims.unit ->
      (associativity,
        (FStar_Char.char, 'Auu____1120) FStar_Util.either Prims.list)
        FStar_Pervasives_Native.tuple2
  =
  fun uu____1132 ->
    (Left, [FStar_Util.Inl 42; FStar_Util.Inl 47; FStar_Util.Inl 37])
let opinfix2 :
  'Auu____1167 .
    Prims.unit ->
      (associativity,
        (FStar_Char.char, 'Auu____1167) FStar_Util.either Prims.list)
        FStar_Pervasives_Native.tuple2
  = fun uu____1179 -> (Left, [FStar_Util.Inl 43; FStar_Util.Inl 45])
let minus_lvl :
  'Auu____1207 .
    Prims.unit ->
      (associativity,
        ('Auu____1207, Prims.string) FStar_Util.either Prims.list)
        FStar_Pervasives_Native.tuple2
  = fun uu____1218 -> (Left, [FStar_Util.Inr "-"])
let opinfix1 :
  'Auu____1234 .
    Prims.unit ->
      (associativity,
        (FStar_Char.char, 'Auu____1234) FStar_Util.either Prims.list)
        FStar_Pervasives_Native.tuple2
  = fun uu____1246 -> (Right, [FStar_Util.Inl 64; FStar_Util.Inl 94])
let pipe_right :
  'Auu____1274 .
    Prims.unit ->
      (associativity,
        ('Auu____1274, Prims.string) FStar_Util.either Prims.list)
        FStar_Pervasives_Native.tuple2
  = fun uu____1285 -> (Left, [FStar_Util.Inr "|>"])
let opinfix0d :
  'Auu____1301 .
    Prims.unit ->
      (associativity,
        (FStar_Char.char, 'Auu____1301) FStar_Util.either Prims.list)
        FStar_Pervasives_Native.tuple2
  = fun uu____1313 -> (Left, [FStar_Util.Inl 36])
let opinfix0c :
  'Auu____1334 .
    Prims.unit ->
      (associativity,
        (FStar_Char.char, 'Auu____1334) FStar_Util.either Prims.list)
        FStar_Pervasives_Native.tuple2
  =
  fun uu____1346 ->
    (Left, [FStar_Util.Inl 61; FStar_Util.Inl 60; FStar_Util.Inl 62])
let equal :
  'Auu____1381 .
    Prims.unit ->
      (associativity,
        ('Auu____1381, Prims.string) FStar_Util.either Prims.list)
        FStar_Pervasives_Native.tuple2
  = fun uu____1392 -> (Left, [FStar_Util.Inr "="])
let opinfix0b :
  'Auu____1408 .
    Prims.unit ->
      (associativity,
        (FStar_Char.char, 'Auu____1408) FStar_Util.either Prims.list)
        FStar_Pervasives_Native.tuple2
  = fun uu____1420 -> (Left, [FStar_Util.Inl 38])
let opinfix0a :
  'Auu____1441 .
    Prims.unit ->
      (associativity,
        (FStar_Char.char, 'Auu____1441) FStar_Util.either Prims.list)
        FStar_Pervasives_Native.tuple2
  = fun uu____1453 -> (Left, [FStar_Util.Inl 124])
let colon_equals :
  'Auu____1474 .
    Prims.unit ->
      (associativity,
        ('Auu____1474, Prims.string) FStar_Util.either Prims.list)
        FStar_Pervasives_Native.tuple2
  = fun uu____1485 -> (NonAssoc, [FStar_Util.Inr ":="])
let amp :
  'Auu____1501 .
    Prims.unit ->
      (associativity,
        ('Auu____1501, Prims.string) FStar_Util.either Prims.list)
        FStar_Pervasives_Native.tuple2
  = fun uu____1512 -> (Right, [FStar_Util.Inr "&"])
let colon_colon :
  'Auu____1528 .
    Prims.unit ->
      (associativity,
        ('Auu____1528, Prims.string) FStar_Util.either Prims.list)
        FStar_Pervasives_Native.tuple2
  = fun uu____1539 -> (Right, [FStar_Util.Inr "::"])
let (level_associativity_spec :
  (associativity,
    (FStar_Char.char, Prims.string) FStar_Util.either Prims.list)
    FStar_Pervasives_Native.tuple2 Prims.list)
  =
  [opinfix4 ();
  opinfix3 ();
  opinfix2 ();
  opinfix1 ();
  pipe_right ();
  opinfix0d ();
  opinfix0c ();
  opinfix0b ();
  opinfix0a ();
  colon_equals ();
  amp ();
  colon_colon ()]
let (level_table :
  ((Prims.int, Prims.int, Prims.int) FStar_Pervasives_Native.tuple3,
    (FStar_Char.char, Prims.string) FStar_Util.either Prims.list)
    FStar_Pervasives_Native.tuple2 Prims.list)
  =
  let levels_from_associativity l uu___56_1746 =
    match uu___56_1746 with
    | Left -> (l, l, (l - (Prims.parse_int "1")))
    | Right -> ((l - (Prims.parse_int "1")), l, l)
    | NonAssoc ->
        ((l - (Prims.parse_int "1")), l, (l - (Prims.parse_int "1"))) in
  FStar_List.mapi
    (fun i ->
       fun uu____1786 ->
         match uu____1786 with
         | (assoc1, tokens) -> ((levels_from_associativity i assoc1), tokens))
    level_associativity_spec
let (assign_levels :
  associativity_level Prims.list ->
    Prims.string ->
      (Prims.int, Prims.int, Prims.int) FStar_Pervasives_Native.tuple3)
  =
  fun token_associativity_spec ->
    fun s ->
      let uu____1866 = FStar_List.tryFind (matches_level s) level_table in
      match uu____1866 with
      | FStar_Pervasives_Native.Some (assoc_levels, uu____1916) ->
          assoc_levels
      | uu____1960 -> failwith (Prims.strcat "Unrecognized operator " s)
let (max : Prims.int -> Prims.int -> Prims.int) =
  fun k1 -> fun k2 -> if k1 > k2 then k1 else k2
let max_level :
  'Auu____1995 .
    ('Auu____1995,
      (FStar_Char.char, Prims.string) FStar_Util.either Prims.list)
      FStar_Pervasives_Native.tuple2 Prims.list -> Prims.int
  =
  fun l ->
    let find_level_and_max n1 level =
      let uu____2055 =
        FStar_List.tryFind
          (fun uu____2095 ->
             match uu____2095 with
             | (uu____2113, tokens) ->
                 tokens = (FStar_Pervasives_Native.snd level)) level_table in
      match uu____2055 with
      | FStar_Pervasives_Native.Some
          ((uu____2155, l1, uu____2157), uu____2158) -> max n1 l1
      | FStar_Pervasives_Native.None ->
          let uu____2213 =
            let uu____2214 =
              let uu____2215 =
                FStar_List.map token_to_string
                  (FStar_Pervasives_Native.snd level) in
              FStar_String.concat "," uu____2215 in
            FStar_Util.format1 "Undefined associativity level %s" uu____2214 in
          failwith uu____2213 in
    FStar_List.fold_left find_level_and_max (Prims.parse_int "0") l
let (levels :
  Prims.string ->
    (Prims.int, Prims.int, Prims.int) FStar_Pervasives_Native.tuple3)
  =
  fun op ->
    let uu____2249 = assign_levels level_associativity_spec op in
    match uu____2249 with
    | (left1, mine, right1) ->
        if op = "*"
        then ((left1 - (Prims.parse_int "1")), mine, right1)
        else (left1, mine, right1)
let operatorInfix0ad12 :
  'Auu____2273 .
    Prims.unit ->
      (associativity,
        (FStar_Char.char, 'Auu____2273) FStar_Util.either Prims.list)
        FStar_Pervasives_Native.tuple2 Prims.list
  =
  fun uu____2287 ->
    [opinfix0a ();
    opinfix0b ();
    opinfix0c ();
    opinfix0d ();
    opinfix1 ();
    opinfix2 ()]
let (is_operatorInfix0ad12 : FStar_Ident.ident -> Prims.bool) =
  fun op ->
    let uu____2368 =
      let uu____2382 =
        FStar_All.pipe_left matches_level (FStar_Ident.text_of_id op) in
      FStar_List.tryFind uu____2382 (operatorInfix0ad12 ()) in
    uu____2368 <> FStar_Pervasives_Native.None
let (is_operatorInfix34 : FStar_Ident.ident -> Prims.bool) =
  let opinfix34 = [opinfix3 (); opinfix4 ()] in
  fun op ->
    let uu____2495 =
      let uu____2509 =
        FStar_All.pipe_left matches_level (FStar_Ident.text_of_id op) in
      FStar_List.tryFind uu____2509 opinfix34 in
    uu____2495 <> FStar_Pervasives_Native.None
let (handleable_args_length : FStar_Ident.ident -> Prims.int) =
  fun op ->
    let op_s = FStar_Ident.text_of_id op in
    let uu____2575 =
      (is_general_prefix_op op) || (FStar_List.mem op_s ["-"; "~"]) in
    if uu____2575
    then (Prims.parse_int "1")
    else
      (let uu____2577 =
         ((is_operatorInfix0ad12 op) || (is_operatorInfix34 op)) ||
           (FStar_List.mem op_s
              ["<==>"; "==>"; "\\/"; "/\\"; "="; "|>"; ":="; ".()"; ".[]"]) in
       if uu____2577
       then (Prims.parse_int "2")
       else
         if FStar_List.mem op_s [".()<-"; ".[]<-"]
         then (Prims.parse_int "3")
         else (Prims.parse_int "0"))
let handleable_op :
  'Auu____2583 . FStar_Ident.ident -> 'Auu____2583 Prims.list -> Prims.bool =
  fun op ->
    fun args ->
      match FStar_List.length args with
      | _0_27 when _0_27 = (Prims.parse_int "0") -> true
      | _0_28 when _0_28 = (Prims.parse_int "1") ->
          (is_general_prefix_op op) ||
            (FStar_List.mem (FStar_Ident.text_of_id op) ["-"; "~"])
      | _0_29 when _0_29 = (Prims.parse_int "2") ->
          ((is_operatorInfix0ad12 op) || (is_operatorInfix34 op)) ||
            (FStar_List.mem (FStar_Ident.text_of_id op)
               ["<==>"; "==>"; "\\/"; "/\\"; "="; "|>"; ":="; ".()"; ".[]"])
      | _0_30 when _0_30 = (Prims.parse_int "3") ->
          FStar_List.mem (FStar_Ident.text_of_id op) [".()<-"; ".[]<-"]
      | uu____2596 -> false
let (comment_stack :
  (Prims.string, FStar_Range.range) FStar_Pervasives_Native.tuple2 Prims.list
    FStar_ST.ref)
  = FStar_Util.mk_ref []
let with_comment :
  'Auu____2654 .
    ('Auu____2654 -> FStar_Pprint.document) ->
      'Auu____2654 -> FStar_Range.range -> FStar_Pprint.document
  =
  fun printer ->
    fun tm ->
      fun tmrange ->
        let rec comments_before_pos acc print_pos lookahead_pos =
          let uu____2686 = FStar_ST.op_Bang comment_stack in
          match uu____2686 with
          | [] -> (acc, false)
          | (comment, crange)::cs ->
              let uu____2751 = FStar_Range.range_before_pos crange print_pos in
              if uu____2751
              then
                (FStar_ST.op_Colon_Equals comment_stack cs;
                 (let uu____2794 =
                    let uu____2795 =
                      let uu____2796 = str comment in
                      FStar_Pprint.op_Hat_Hat uu____2796
                        FStar_Pprint.hardline in
                    FStar_Pprint.op_Hat_Hat acc uu____2795 in
                  comments_before_pos uu____2794 print_pos lookahead_pos))
              else
                (let uu____2798 =
                   FStar_Range.range_before_pos crange lookahead_pos in
                 (acc, uu____2798)) in
        let uu____2799 =
          let uu____2804 =
            let uu____2805 = FStar_Range.start_of_range tmrange in
            FStar_Range.end_of_line uu____2805 in
          let uu____2806 = FStar_Range.end_of_range tmrange in
          comments_before_pos FStar_Pprint.empty uu____2804 uu____2806 in
        match uu____2799 with
        | (comments, has_lookahead) ->
            let printed_e = printer tm in
            let comments1 =
              if has_lookahead
              then
                let pos = FStar_Range.end_of_range tmrange in
                let uu____2812 = comments_before_pos comments pos pos in
                FStar_Pervasives_Native.fst uu____2812
              else comments in
            let uu____2818 = FStar_Pprint.op_Hat_Hat comments1 printed_e in
            FStar_Pprint.group uu____2818
let rec (place_comments_until_pos :
  Prims.int ->
    Prims.int ->
      FStar_Range.pos -> FStar_Pprint.document -> FStar_Pprint.document)
  =
  fun k ->
    fun lbegin ->
      fun pos_end ->
        fun doc1 ->
          let uu____2831 = FStar_ST.op_Bang comment_stack in
          match uu____2831 with
          | (comment, crange)::cs when
              FStar_Range.range_before_pos crange pos_end ->
              (FStar_ST.op_Colon_Equals comment_stack cs;
               (let lnum =
                  let uu____2927 =
                    let uu____2928 =
                      let uu____2929 = FStar_Range.start_of_range crange in
                      FStar_Range.line_of_pos uu____2929 in
                    uu____2928 - lbegin in
                  max k uu____2927 in
                let doc2 =
                  let uu____2931 =
                    let uu____2932 =
                      FStar_Pprint.repeat lnum FStar_Pprint.hardline in
                    let uu____2933 = str comment in
                    FStar_Pprint.op_Hat_Hat uu____2932 uu____2933 in
                  FStar_Pprint.op_Hat_Hat doc1 uu____2931 in
                let uu____2934 =
                  let uu____2935 = FStar_Range.end_of_range crange in
                  FStar_Range.line_of_pos uu____2935 in
                place_comments_until_pos (Prims.parse_int "1") uu____2934
                  pos_end doc2))
          | uu____2936 ->
              let lnum =
                let uu____2944 =
                  let uu____2945 = FStar_Range.line_of_pos pos_end in
                  uu____2945 - lbegin in
                max (Prims.parse_int "1") uu____2944 in
              let uu____2946 = FStar_Pprint.repeat lnum FStar_Pprint.hardline in
              FStar_Pprint.op_Hat_Hat doc1 uu____2946
let separate_map_with_comments :
  'Auu____2953 .
    FStar_Pprint.document ->
      FStar_Pprint.document ->
        ('Auu____2953 -> FStar_Pprint.document) ->
          'Auu____2953 Prims.list ->
            ('Auu____2953 -> FStar_Range.range) -> FStar_Pprint.document
  =
  fun prefix1 ->
    fun sep ->
      fun f ->
        fun xs ->
          fun extract_range ->
            let fold_fun uu____3001 x =
              match uu____3001 with
              | (last_line, doc1) ->
                  let r = extract_range x in
                  let doc2 =
                    let uu____3015 = FStar_Range.start_of_range r in
                    place_comments_until_pos (Prims.parse_int "1") last_line
                      uu____3015 doc1 in
                  let uu____3016 =
                    let uu____3017 = FStar_Range.end_of_range r in
                    FStar_Range.line_of_pos uu____3017 in
                  let uu____3018 =
                    let uu____3019 =
                      let uu____3020 = f x in
                      FStar_Pprint.op_Hat_Hat sep uu____3020 in
                    FStar_Pprint.op_Hat_Hat doc2 uu____3019 in
                  (uu____3016, uu____3018) in
            let uu____3021 =
              let uu____3028 = FStar_List.hd xs in
              let uu____3029 = FStar_List.tl xs in (uu____3028, uu____3029) in
            match uu____3021 with
            | (x, xs1) ->
                let init1 =
                  let uu____3045 =
                    let uu____3046 =
                      let uu____3047 = extract_range x in
                      FStar_Range.end_of_range uu____3047 in
                    FStar_Range.line_of_pos uu____3046 in
                  let uu____3048 =
                    let uu____3049 = f x in
                    FStar_Pprint.op_Hat_Hat prefix1 uu____3049 in
                  (uu____3045, uu____3048) in
                let uu____3050 = FStar_List.fold_left fold_fun init1 xs1 in
                FStar_Pervasives_Native.snd uu____3050
let rec (p_decl : FStar_Parser_AST.decl -> FStar_Pprint.document) =
  fun d ->
    let uu____3415 =
      let uu____3416 = FStar_Pprint.optional p_fsdoc d.FStar_Parser_AST.doc in
      let uu____3417 =
        let uu____3418 = p_attributes d.FStar_Parser_AST.attrs in
        let uu____3419 =
          let uu____3420 = p_qualifiers d.FStar_Parser_AST.quals in
          let uu____3421 =
            let uu____3422 = p_rawDecl d in
            FStar_Pprint.op_Hat_Hat
              (if d.FStar_Parser_AST.quals = []
               then FStar_Pprint.empty
               else break1) uu____3422 in
          FStar_Pprint.op_Hat_Hat uu____3420 uu____3421 in
        FStar_Pprint.op_Hat_Hat uu____3418 uu____3419 in
      FStar_Pprint.op_Hat_Hat uu____3416 uu____3417 in
    FStar_Pprint.group uu____3415
and (p_attributes : FStar_Parser_AST.attributes_ -> FStar_Pprint.document) =
  fun attrs ->
    let uu____3425 =
      let uu____3426 = str "@" in
      FStar_Pprint.op_Hat_Hat FStar_Pprint.lbracket uu____3426 in
    let uu____3427 =
      FStar_Pprint.op_Hat_Hat FStar_Pprint.rbracket FStar_Pprint.hardline in
    soft_surround_map_or_flow (Prims.parse_int "0") (Prims.parse_int "2")
      FStar_Pprint.empty uu____3425 FStar_Pprint.space uu____3427
      p_atomicTerm attrs
and (p_fsdoc : FStar_Parser_AST.fsdoc -> FStar_Pprint.document) =
  fun uu____3428 ->
    match uu____3428 with
    | (doc1, kwd_args) ->
        let kwd_args_doc =
          match kwd_args with
          | [] -> FStar_Pprint.empty
          | kwd_args1 ->
              let process_kwd_arg uu____3462 =
                match uu____3462 with
                | (kwd, arg) ->
                    let uu____3469 = str "@" in
                    let uu____3470 =
                      let uu____3471 = str kwd in
                      let uu____3472 =
                        let uu____3473 = str arg in
                        FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____3473 in
                      FStar_Pprint.op_Hat_Hat uu____3471 uu____3472 in
                    FStar_Pprint.op_Hat_Hat uu____3469 uu____3470 in
              let uu____3474 =
                let uu____3475 =
                  FStar_Pprint.separate_map FStar_Pprint.hardline
                    process_kwd_arg kwd_args1 in
                FStar_Pprint.op_Hat_Hat uu____3475 FStar_Pprint.hardline in
              FStar_Pprint.op_Hat_Hat FStar_Pprint.hardline uu____3474 in
        let uu____3480 =
          let uu____3481 =
            let uu____3482 =
              let uu____3483 =
                let uu____3484 = str doc1 in
                let uu____3485 =
                  let uu____3486 =
                    let uu____3487 =
                      FStar_Pprint.op_Hat_Hat FStar_Pprint.rparen
                        FStar_Pprint.hardline in
                    FStar_Pprint.op_Hat_Hat FStar_Pprint.star uu____3487 in
                  FStar_Pprint.op_Hat_Hat kwd_args_doc uu____3486 in
                FStar_Pprint.op_Hat_Hat uu____3484 uu____3485 in
              FStar_Pprint.op_Hat_Hat FStar_Pprint.star uu____3483 in
            FStar_Pprint.op_Hat_Hat FStar_Pprint.star uu____3482 in
          FStar_Pprint.op_Hat_Hat FStar_Pprint.lparen uu____3481 in
        FStar_Pprint.op_Hat_Hat FStar_Pprint.hardline uu____3480
and (p_justSig : FStar_Parser_AST.decl -> FStar_Pprint.document) =
  fun d ->
    match d.FStar_Parser_AST.d with
    | FStar_Parser_AST.Val (lid, t) ->
        let uu____3491 =
          let uu____3492 = str "val" in
          let uu____3493 =
            let uu____3494 =
              let uu____3495 = p_lident lid in
              let uu____3496 =
                FStar_Pprint.op_Hat_Hat FStar_Pprint.space FStar_Pprint.colon in
              FStar_Pprint.op_Hat_Hat uu____3495 uu____3496 in
            FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____3494 in
          FStar_Pprint.op_Hat_Hat uu____3492 uu____3493 in
        let uu____3497 = p_typ false false t in
        op_Hat_Slash_Plus_Hat uu____3491 uu____3497
    | FStar_Parser_AST.TopLevelLet (uu____3498, lbs) ->
        FStar_Pprint.separate_map FStar_Pprint.hardline
          (fun lb ->
             let uu____3523 =
               let uu____3524 = str "let" in
               let uu____3525 = p_letlhs lb in
               FStar_Pprint.op_Hat_Slash_Hat uu____3524 uu____3525 in
             FStar_Pprint.group uu____3523) lbs
    | uu____3526 -> FStar_Pprint.empty
and (p_rawDecl : FStar_Parser_AST.decl -> FStar_Pprint.document) =
  fun d ->
    match d.FStar_Parser_AST.d with
    | FStar_Parser_AST.Open uid ->
        let uu____3529 =
          let uu____3530 = str "open" in
          let uu____3531 = p_quident uid in
          FStar_Pprint.op_Hat_Slash_Hat uu____3530 uu____3531 in
        FStar_Pprint.group uu____3529
    | FStar_Parser_AST.Include uid ->
        let uu____3533 =
          let uu____3534 = str "include" in
          let uu____3535 = p_quident uid in
          FStar_Pprint.op_Hat_Slash_Hat uu____3534 uu____3535 in
        FStar_Pprint.group uu____3533
    | FStar_Parser_AST.ModuleAbbrev (uid1, uid2) ->
        let uu____3538 =
          let uu____3539 = str "module" in
          let uu____3540 =
            let uu____3541 =
              let uu____3542 = p_uident uid1 in
              let uu____3543 =
                FStar_Pprint.op_Hat_Hat FStar_Pprint.space
                  FStar_Pprint.equals in
              FStar_Pprint.op_Hat_Hat uu____3542 uu____3543 in
            FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____3541 in
          FStar_Pprint.op_Hat_Hat uu____3539 uu____3540 in
        let uu____3544 = p_quident uid2 in
        op_Hat_Slash_Plus_Hat uu____3538 uu____3544
    | FStar_Parser_AST.TopLevelModule uid ->
        let uu____3546 =
          let uu____3547 = str "module" in
          let uu____3548 =
            let uu____3549 = p_quident uid in
            FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____3549 in
          FStar_Pprint.op_Hat_Hat uu____3547 uu____3548 in
        FStar_Pprint.group uu____3546
    | FStar_Parser_AST.Tycon
        (true,
         (FStar_Parser_AST.TyconAbbrev
          (uid, tpars, FStar_Pervasives_Native.None, t),
          FStar_Pervasives_Native.None)::[])
        ->
        let effect_prefix_doc =
          let uu____3582 = str "effect" in
          let uu____3583 =
            let uu____3584 = p_uident uid in
            FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____3584 in
          FStar_Pprint.op_Hat_Hat uu____3582 uu____3583 in
        let uu____3585 =
          let uu____3586 = p_typars tpars in
          FStar_Pprint.surround (Prims.parse_int "2") (Prims.parse_int "1")
            effect_prefix_doc uu____3586 FStar_Pprint.equals in
        let uu____3587 = p_typ false false t in
        op_Hat_Slash_Plus_Hat uu____3585 uu____3587
    | FStar_Parser_AST.Tycon (false, tcdefs) ->
        let uu____3605 = str "type" in
        let uu____3606 = str "and" in
        precede_break_separate_map uu____3605 uu____3606 p_fsdocTypeDeclPairs
          tcdefs
    | FStar_Parser_AST.TopLevelLet (q, lbs) ->
        let let_doc =
          let uu____3628 = str "let" in
          let uu____3629 =
            let uu____3630 = p_letqualifier q in
            FStar_Pprint.op_Hat_Hat uu____3630 FStar_Pprint.space in
          FStar_Pprint.op_Hat_Hat uu____3628 uu____3629 in
        let uu____3631 =
          let uu____3632 = str "and" in
          FStar_Pprint.op_Hat_Hat uu____3632 FStar_Pprint.space in
        separate_map_with_comments let_doc uu____3631 p_letbinding lbs
          (fun uu____3640 ->
             match uu____3640 with
             | (p, t) ->
                 FStar_Range.union_ranges p.FStar_Parser_AST.prange
                   t.FStar_Parser_AST.range)
    | FStar_Parser_AST.Val (lid, t) ->
        let uu____3649 =
          let uu____3650 = str "val" in
          let uu____3651 =
            let uu____3652 =
              let uu____3653 = p_lident lid in
              let uu____3654 =
                FStar_Pprint.op_Hat_Hat FStar_Pprint.space FStar_Pprint.colon in
              FStar_Pprint.op_Hat_Hat uu____3653 uu____3654 in
            FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____3652 in
          FStar_Pprint.op_Hat_Hat uu____3650 uu____3651 in
        let uu____3655 = p_typ false false t in
        op_Hat_Slash_Plus_Hat uu____3649 uu____3655
    | FStar_Parser_AST.Assume (id1, t) ->
        let decl_keyword =
          let uu____3659 =
            let uu____3660 =
              FStar_Util.char_at id1.FStar_Ident.idText (Prims.parse_int "0") in
            FStar_All.pipe_right uu____3660 FStar_Util.is_upper in
          if uu____3659
          then FStar_Pprint.empty
          else
            (let uu____3662 = str "val" in
             FStar_Pprint.op_Hat_Hat uu____3662 FStar_Pprint.space) in
        let uu____3663 =
          let uu____3664 =
            let uu____3665 = p_ident id1 in
            let uu____3666 =
              FStar_Pprint.op_Hat_Hat FStar_Pprint.space FStar_Pprint.colon in
            FStar_Pprint.op_Hat_Hat uu____3665 uu____3666 in
          FStar_Pprint.op_Hat_Hat decl_keyword uu____3664 in
        let uu____3667 = p_typ false false t in
        op_Hat_Slash_Plus_Hat uu____3663 uu____3667
    | FStar_Parser_AST.Exception (uid, t_opt) ->
        let uu____3674 = str "exception" in
        let uu____3675 =
          let uu____3676 =
            let uu____3677 = p_uident uid in
            let uu____3678 =
              FStar_Pprint.optional
                (fun t ->
                   let uu____3682 =
                     let uu____3683 = str "of" in
                     let uu____3684 = p_typ false false t in
                     op_Hat_Slash_Plus_Hat uu____3683 uu____3684 in
                   FStar_Pprint.op_Hat_Hat break1 uu____3682) t_opt in
            FStar_Pprint.op_Hat_Hat uu____3677 uu____3678 in
          FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____3676 in
        FStar_Pprint.op_Hat_Hat uu____3674 uu____3675
    | FStar_Parser_AST.NewEffect ne ->
        let uu____3686 = str "new_effect" in
        let uu____3687 =
          let uu____3688 = p_newEffect ne in
          FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____3688 in
        FStar_Pprint.op_Hat_Hat uu____3686 uu____3687
    | FStar_Parser_AST.SubEffect se ->
        let uu____3690 = str "sub_effect" in
        let uu____3691 =
          let uu____3692 = p_subEffect se in
          FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____3692 in
        FStar_Pprint.op_Hat_Hat uu____3690 uu____3691
    | FStar_Parser_AST.Pragma p -> p_pragma p
    | FStar_Parser_AST.Fsdoc doc1 ->
        let uu____3695 = p_fsdoc doc1 in
        FStar_Pprint.op_Hat_Hat uu____3695 FStar_Pprint.hardline
    | FStar_Parser_AST.Main uu____3696 ->
        failwith "*Main declaration* : Is that really still in use ??"
    | FStar_Parser_AST.Tycon (true, uu____3697) ->
        failwith
          "Effect abbreviation is expected to be defined by an abbreviation"
    | FStar_Parser_AST.Splice t ->
        let uu____3715 = str "%splice" in
        let uu____3716 =
          let uu____3717 = p_term false false t in
          FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____3717 in
        FStar_Pprint.op_Hat_Hat uu____3715 uu____3716
and (p_pragma : FStar_Parser_AST.pragma -> FStar_Pprint.document) =
  fun uu___57_3718 ->
    match uu___57_3718 with
    | FStar_Parser_AST.SetOptions s ->
        let uu____3720 = str "#set-options" in
        let uu____3721 =
          let uu____3722 =
            let uu____3723 = str s in FStar_Pprint.dquotes uu____3723 in
          FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____3722 in
        FStar_Pprint.op_Hat_Hat uu____3720 uu____3721
    | FStar_Parser_AST.ResetOptions s_opt ->
        let uu____3727 = str "#reset-options" in
        let uu____3728 =
          FStar_Pprint.optional
            (fun s ->
               let uu____3732 =
                 let uu____3733 = str s in FStar_Pprint.dquotes uu____3733 in
               FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____3732) s_opt in
        FStar_Pprint.op_Hat_Hat uu____3727 uu____3728
    | FStar_Parser_AST.LightOff ->
        (FStar_ST.op_Colon_Equals should_print_fs_typ_app true;
         str "#light \"off\"")
and (p_typars : FStar_Parser_AST.binder Prims.list -> FStar_Pprint.document)
  = fun bs -> p_binders true bs
and (p_fsdocTypeDeclPairs :
  (FStar_Parser_AST.tycon,
    FStar_Parser_AST.fsdoc FStar_Pervasives_Native.option)
    FStar_Pervasives_Native.tuple2 -> FStar_Pprint.document)
  =
  fun uu____3763 ->
    match uu____3763 with
    | (typedecl, fsdoc_opt) ->
        let uu____3776 = FStar_Pprint.optional p_fsdoc fsdoc_opt in
        let uu____3777 = p_typeDecl typedecl in
        FStar_Pprint.op_Hat_Hat uu____3776 uu____3777
and (p_typeDecl : FStar_Parser_AST.tycon -> FStar_Pprint.document) =
  fun uu___58_3778 ->
    match uu___58_3778 with
    | FStar_Parser_AST.TyconAbstract (lid, bs, typ_opt) ->
        let empty' uu____3793 = FStar_Pprint.empty in
        p_typeDeclPrefix lid bs typ_opt empty'
    | FStar_Parser_AST.TyconAbbrev (lid, bs, typ_opt, t) ->
        let f uu____3809 =
          let uu____3810 = p_typ false false t in
          prefix2 FStar_Pprint.equals uu____3810 in
        p_typeDeclPrefix lid bs typ_opt f
    | FStar_Parser_AST.TyconRecord (lid, bs, typ_opt, record_field_decls) ->
        let p_recordFieldAndComments ps uu____3857 =
          match uu____3857 with
          | (lid1, t, doc_opt) ->
              let uu____3873 =
                FStar_Range.extend_to_end_of_line t.FStar_Parser_AST.range in
              with_comment (p_recordFieldDecl ps) (lid1, t, doc_opt)
                uu____3873 in
        let p_fields uu____3887 =
          let uu____3888 =
            let uu____3889 =
              let uu____3890 =
                let uu____3891 =
                  FStar_Pprint.op_Hat_Hat FStar_Pprint.semi break1 in
                separate_map_last uu____3891 p_recordFieldAndComments
                  record_field_decls in
              braces_with_nesting uu____3890 in
            FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____3889 in
          FStar_Pprint.op_Hat_Hat FStar_Pprint.equals uu____3888 in
        p_typeDeclPrefix lid bs typ_opt p_fields
    | FStar_Parser_AST.TyconVariant (lid, bs, typ_opt, ct_decls) ->
        let p_constructorBranchAndComments uu____3955 =
          match uu____3955 with
          | (uid, t_opt, doc_opt, use_of) ->
              let range =
                let uu____3981 =
                  let uu____3982 =
                    FStar_Util.map_opt t_opt
                      (fun t -> t.FStar_Parser_AST.range) in
                  FStar_Util.dflt uid.FStar_Ident.idRange uu____3982 in
                FStar_Range.extend_to_end_of_line uu____3981 in
              let p_constructorBranch decl =
                let uu____4015 =
                  let uu____4016 =
                    let uu____4017 = p_constructorDecl decl in
                    FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____4017 in
                  FStar_Pprint.op_Hat_Hat FStar_Pprint.bar uu____4016 in
                FStar_Pprint.group uu____4015 in
              with_comment p_constructorBranch (uid, t_opt, doc_opt, use_of)
                range in
        let datacon_doc uu____4037 =
          let uu____4038 =
            FStar_Pprint.separate_map break1 p_constructorBranchAndComments
              ct_decls in
          FStar_Pprint.group uu____4038 in
        p_typeDeclPrefix lid bs typ_opt
          (fun uu____4053 ->
             let uu____4054 = datacon_doc () in
             prefix2 FStar_Pprint.equals uu____4054)
and (p_typeDeclPrefix :
  FStar_Ident.ident ->
    FStar_Parser_AST.binder Prims.list ->
      FStar_Parser_AST.knd FStar_Pervasives_Native.option ->
        (Prims.unit -> FStar_Pprint.document) -> FStar_Pprint.document)
  =
  fun lid ->
    fun bs ->
      fun typ_opt ->
        fun cont ->
          if (bs = []) && (typ_opt = FStar_Pervasives_Native.None)
          then
            let uu____4069 = p_ident lid in
            let uu____4070 =
              let uu____4071 = cont () in
              FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____4071 in
            FStar_Pprint.op_Hat_Hat uu____4069 uu____4070
          else
            (let binders_doc =
               let uu____4074 = p_typars bs in
               let uu____4075 =
                 FStar_Pprint.optional
                   (fun t ->
                      let uu____4079 =
                        let uu____4080 =
                          let uu____4081 = p_typ false false t in
                          FStar_Pprint.op_Hat_Hat FStar_Pprint.space
                            uu____4081 in
                        FStar_Pprint.op_Hat_Hat FStar_Pprint.colon uu____4080 in
                      FStar_Pprint.op_Hat_Hat break1 uu____4079) typ_opt in
               FStar_Pprint.op_Hat_Hat uu____4074 uu____4075 in
             let uu____4082 = p_ident lid in
             let uu____4083 = cont () in
             FStar_Pprint.surround (Prims.parse_int "2")
               (Prims.parse_int "1") uu____4082 binders_doc uu____4083)
and (p_recordFieldDecl :
  Prims.bool ->
    (FStar_Ident.ident, FStar_Parser_AST.term,
      FStar_Parser_AST.fsdoc FStar_Pervasives_Native.option)
      FStar_Pervasives_Native.tuple3 -> FStar_Pprint.document)
  =
  fun ps ->
    fun uu____4085 ->
      match uu____4085 with
      | (lid, t, doc_opt) ->
          let uu____4101 =
            let uu____4102 = FStar_Pprint.optional p_fsdoc doc_opt in
            let uu____4103 =
              let uu____4104 = p_lident lid in
              let uu____4105 =
                let uu____4106 = p_typ ps false t in
                FStar_Pprint.op_Hat_Hat FStar_Pprint.colon uu____4106 in
              FStar_Pprint.op_Hat_Hat uu____4104 uu____4105 in
            FStar_Pprint.op_Hat_Hat uu____4102 uu____4103 in
          FStar_Pprint.group uu____4101
and (p_constructorDecl :
  (FStar_Ident.ident, FStar_Parser_AST.term FStar_Pervasives_Native.option,
    FStar_Parser_AST.fsdoc FStar_Pervasives_Native.option, Prims.bool)
    FStar_Pervasives_Native.tuple4 -> FStar_Pprint.document)
  =
  fun uu____4107 ->
    match uu____4107 with
    | (uid, t_opt, doc_opt, use_of) ->
        let sep = if use_of then str "of" else FStar_Pprint.colon in
        let uid_doc = p_uident uid in
        let uu____4135 = FStar_Pprint.optional p_fsdoc doc_opt in
        let uu____4136 =
          let uu____4137 = FStar_Pprint.break_ (Prims.parse_int "0") in
          let uu____4138 =
            default_or_map uid_doc
              (fun t ->
                 let uu____4143 =
                   let uu____4144 =
                     FStar_Pprint.op_Hat_Hat FStar_Pprint.space sep in
                   FStar_Pprint.op_Hat_Hat uid_doc uu____4144 in
                 let uu____4145 = p_typ false false t in
                 op_Hat_Slash_Plus_Hat uu____4143 uu____4145) t_opt in
          FStar_Pprint.op_Hat_Hat uu____4137 uu____4138 in
        FStar_Pprint.op_Hat_Hat uu____4135 uu____4136
and (p_letlhs :
  (FStar_Parser_AST.pattern, FStar_Parser_AST.term)
    FStar_Pervasives_Native.tuple2 -> FStar_Pprint.document)
  =
  fun uu____4146 ->
    match uu____4146 with
    | (pat, uu____4152) ->
        let uu____4153 =
          match pat.FStar_Parser_AST.pat with
          | FStar_Parser_AST.PatAscribed
              (pat1, (t, FStar_Pervasives_Native.None)) ->
              let uu____4172 =
                let uu____4173 =
                  let uu____4174 =
                    let uu____4175 =
                      let uu____4176 = p_tmArrow p_tmNoEq t in
                      FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____4176 in
                    FStar_Pprint.op_Hat_Hat FStar_Pprint.colon uu____4175 in
                  FStar_Pprint.group uu____4174 in
                FStar_Pprint.op_Hat_Hat break1 uu____4173 in
              (pat1, uu____4172)
          | FStar_Parser_AST.PatAscribed
              (pat1, (t, FStar_Pervasives_Native.Some tac)) ->
              let uu____4188 =
                let uu____4189 =
                  let uu____4190 =
                    let uu____4191 =
                      let uu____4192 =
                        let uu____4193 = p_tmArrow p_tmNoEq t in
                        FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____4193 in
                      FStar_Pprint.op_Hat_Hat FStar_Pprint.colon uu____4192 in
                    FStar_Pprint.group uu____4191 in
                  let uu____4194 =
                    let uu____4195 =
                      let uu____4196 = str "by" in
                      let uu____4197 =
                        let uu____4198 = p_atomicTerm tac in
                        FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____4198 in
                      FStar_Pprint.op_Hat_Hat uu____4196 uu____4197 in
                    FStar_Pprint.group uu____4195 in
                  FStar_Pprint.op_Hat_Hat uu____4190 uu____4194 in
                FStar_Pprint.op_Hat_Hat break1 uu____4189 in
              (pat1, uu____4188)
          | uu____4199 -> (pat, FStar_Pprint.empty) in
        (match uu____4153 with
         | (pat1, ascr_doc) ->
             (match pat1.FStar_Parser_AST.pat with
              | FStar_Parser_AST.PatApp
                  ({
                     FStar_Parser_AST.pat = FStar_Parser_AST.PatVar
                       (x, uu____4203);
                     FStar_Parser_AST.prange = uu____4204;_},
                   pats)
                  ->
                  let uu____4214 =
                    let uu____4215 = p_lident x in
                    let uu____4216 =
                      let uu____4217 =
                        separate_map_or_flow break1 p_atomicPattern pats in
                      FStar_Pprint.op_Hat_Hat uu____4217 ascr_doc in
                    FStar_Pprint.op_Hat_Slash_Hat uu____4215 uu____4216 in
                  FStar_Pprint.group uu____4214
              | uu____4218 ->
                  let uu____4219 =
                    let uu____4220 = p_tuplePattern pat1 in
                    FStar_Pprint.op_Hat_Hat uu____4220 ascr_doc in
                  FStar_Pprint.group uu____4219))
and (p_letbinding :
  (FStar_Parser_AST.pattern, FStar_Parser_AST.term)
    FStar_Pervasives_Native.tuple2 -> FStar_Pprint.document)
  =
  fun uu____4221 ->
    match uu____4221 with
    | (pat, e) ->
        let pat_doc = p_letlhs (pat, e) in
        let uu____4229 =
          let uu____4230 =
            FStar_Pprint.op_Hat_Slash_Hat pat_doc FStar_Pprint.equals in
          FStar_Pprint.group uu____4230 in
        let uu____4231 = p_term false false e in
        prefix2 uu____4229 uu____4231
and (p_newEffect : FStar_Parser_AST.effect_decl -> FStar_Pprint.document) =
  fun uu___59_4232 ->
    match uu___59_4232 with
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
        let uu____4257 = p_uident uid in
        let uu____4258 = p_binders true bs in
        let uu____4259 =
          let uu____4260 = p_simpleTerm false false t in
          prefix2 FStar_Pprint.equals uu____4260 in
        FStar_Pprint.surround (Prims.parse_int "2") (Prims.parse_int "1")
          uu____4257 uu____4258 uu____4259
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
          let uu____4269 =
            let uu____4270 =
              let uu____4271 =
                let uu____4272 = p_uident uid in
                let uu____4273 = p_binders true bs in
                let uu____4274 =
                  let uu____4275 = p_typ false false t in
                  prefix2 FStar_Pprint.colon uu____4275 in
                FStar_Pprint.surround (Prims.parse_int "2")
                  (Prims.parse_int "1") uu____4272 uu____4273 uu____4274 in
              FStar_Pprint.group uu____4271 in
            let uu____4276 =
              let uu____4277 = str "with" in
              let uu____4278 =
                separate_break_map_last FStar_Pprint.semi p_effectDecl
                  eff_decls in
              prefix2 uu____4277 uu____4278 in
            FStar_Pprint.op_Hat_Slash_Hat uu____4270 uu____4276 in
          braces_with_nesting uu____4269
and (p_effectDecl :
  Prims.bool -> FStar_Parser_AST.decl -> FStar_Pprint.document) =
  fun ps ->
    fun d ->
      match d.FStar_Parser_AST.d with
      | FStar_Parser_AST.Tycon
          (false,
           (FStar_Parser_AST.TyconAbbrev
            (lid, [], FStar_Pervasives_Native.None, e),
            FStar_Pervasives_Native.None)::[])
          ->
          let uu____4309 =
            let uu____4310 = p_lident lid in
            let uu____4311 =
              FStar_Pprint.op_Hat_Hat FStar_Pprint.space FStar_Pprint.equals in
            FStar_Pprint.op_Hat_Hat uu____4310 uu____4311 in
          let uu____4312 = p_simpleTerm ps false e in
          prefix2 uu____4309 uu____4312
      | uu____4313 ->
          let uu____4314 =
            let uu____4315 = FStar_Parser_AST.decl_to_string d in
            FStar_Util.format1
              "Not a declaration of an effect member... or at least I hope so : %s"
              uu____4315 in
          failwith uu____4314
and (p_subEffect : FStar_Parser_AST.lift -> FStar_Pprint.document) =
  fun lift ->
    let lift_op_doc =
      let lifts =
        match lift.FStar_Parser_AST.lift_op with
        | FStar_Parser_AST.NonReifiableLift t -> [("lift_wp", t)]
        | FStar_Parser_AST.ReifiableLift (t1, t2) ->
            [("lift_wp", t1); ("lift", t2)]
        | FStar_Parser_AST.LiftForFree t -> [("lift", t)] in
      let p_lift ps uu____4373 =
        match uu____4373 with
        | (kwd, t) ->
            let uu____4380 =
              let uu____4381 = str kwd in
              let uu____4382 =
                FStar_Pprint.op_Hat_Hat FStar_Pprint.space
                  FStar_Pprint.equals in
              FStar_Pprint.op_Hat_Hat uu____4381 uu____4382 in
            let uu____4383 = p_simpleTerm ps false t in
            prefix2 uu____4380 uu____4383 in
      separate_break_map_last FStar_Pprint.semi p_lift lifts in
    let uu____4388 =
      let uu____4389 =
        let uu____4390 = p_quident lift.FStar_Parser_AST.msource in
        let uu____4391 =
          let uu____4392 = str "~>" in
          FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____4392 in
        FStar_Pprint.op_Hat_Hat uu____4390 uu____4391 in
      let uu____4393 = p_quident lift.FStar_Parser_AST.mdest in
      prefix2 uu____4389 uu____4393 in
    let uu____4394 =
      let uu____4395 = braces_with_nesting lift_op_doc in
      FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____4395 in
    FStar_Pprint.op_Hat_Hat uu____4388 uu____4394
and (p_qualifier : FStar_Parser_AST.qualifier -> FStar_Pprint.document) =
  fun uu___60_4396 ->
    match uu___60_4396 with
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
    let uu____4398 = FStar_Pprint.separate_map break1 p_qualifier qs in
    FStar_Pprint.group uu____4398
and (p_letqualifier :
  FStar_Parser_AST.let_qualifier -> FStar_Pprint.document) =
  fun uu___61_4399 ->
    match uu___61_4399 with
    | FStar_Parser_AST.Rec ->
        let uu____4400 = str "rec" in
        FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____4400
    | FStar_Parser_AST.Mutable ->
        let uu____4401 = str "mutable" in
        FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____4401
    | FStar_Parser_AST.NoLetQualifier -> FStar_Pprint.empty
and (p_aqual : FStar_Parser_AST.arg_qualifier -> FStar_Pprint.document) =
  fun uu___62_4402 ->
    match uu___62_4402 with
    | FStar_Parser_AST.Implicit -> str "#"
    | FStar_Parser_AST.Equality -> str "$"
and (p_disjunctivePattern :
  FStar_Parser_AST.pattern -> FStar_Pprint.document) =
  fun p ->
    match p.FStar_Parser_AST.pat with
    | FStar_Parser_AST.PatOr pats ->
        let uu____4407 =
          let uu____4408 =
            let uu____4409 =
              FStar_Pprint.op_Hat_Hat FStar_Pprint.bar FStar_Pprint.space in
            FStar_Pprint.op_Hat_Hat break1 uu____4409 in
          FStar_Pprint.separate_map uu____4408 p_tuplePattern pats in
        FStar_Pprint.group uu____4407
    | uu____4410 -> p_tuplePattern p
and (p_tuplePattern : FStar_Parser_AST.pattern -> FStar_Pprint.document) =
  fun p ->
    match p.FStar_Parser_AST.pat with
    | FStar_Parser_AST.PatTuple (pats, false) ->
        let uu____4417 =
          let uu____4418 = FStar_Pprint.op_Hat_Hat FStar_Pprint.comma break1 in
          FStar_Pprint.separate_map uu____4418 p_constructorPattern pats in
        FStar_Pprint.group uu____4417
    | uu____4419 -> p_constructorPattern p
and (p_constructorPattern :
  FStar_Parser_AST.pattern -> FStar_Pprint.document) =
  fun p ->
    match p.FStar_Parser_AST.pat with
    | FStar_Parser_AST.PatApp
        ({ FStar_Parser_AST.pat = FStar_Parser_AST.PatName maybe_cons_lid;
           FStar_Parser_AST.prange = uu____4422;_},
         hd1::tl1::[])
        when
        FStar_Ident.lid_equals maybe_cons_lid FStar_Parser_Const.cons_lid ->
        let uu____4427 =
          FStar_Pprint.op_Hat_Hat FStar_Pprint.colon FStar_Pprint.colon in
        let uu____4428 = p_constructorPattern hd1 in
        let uu____4429 = p_constructorPattern tl1 in
        infix0 uu____4427 uu____4428 uu____4429
    | FStar_Parser_AST.PatApp
        ({ FStar_Parser_AST.pat = FStar_Parser_AST.PatName uid;
           FStar_Parser_AST.prange = uu____4431;_},
         pats)
        ->
        let uu____4437 = p_quident uid in
        let uu____4438 =
          FStar_Pprint.separate_map break1 p_atomicPattern pats in
        prefix2 uu____4437 uu____4438
    | uu____4439 -> p_atomicPattern p
and (p_atomicPattern : FStar_Parser_AST.pattern -> FStar_Pprint.document) =
  fun p ->
    match p.FStar_Parser_AST.pat with
    | FStar_Parser_AST.PatAscribed (pat, (t, FStar_Pervasives_Native.None))
        ->
        (match ((pat.FStar_Parser_AST.pat), (t.FStar_Parser_AST.tm)) with
         | (FStar_Parser_AST.PatVar (lid, aqual), FStar_Parser_AST.Refine
            ({ FStar_Parser_AST.b = FStar_Parser_AST.Annotated (lid', t1);
               FStar_Parser_AST.brange = uu____4455;
               FStar_Parser_AST.blevel = uu____4456;
               FStar_Parser_AST.aqual = uu____4457;_},
             phi)) when lid.FStar_Ident.idText = lid'.FStar_Ident.idText ->
             let uu____4463 =
               let uu____4464 = p_ident lid in
               p_refinement aqual uu____4464 t1 phi in
             soft_parens_with_nesting uu____4463
         | (FStar_Parser_AST.PatWild, FStar_Parser_AST.Refine
            ({ FStar_Parser_AST.b = FStar_Parser_AST.NoName t1;
               FStar_Parser_AST.brange = uu____4466;
               FStar_Parser_AST.blevel = uu____4467;
               FStar_Parser_AST.aqual = uu____4468;_},
             phi)) ->
             let uu____4470 =
               p_refinement FStar_Pervasives_Native.None
                 FStar_Pprint.underscore t1 phi in
             soft_parens_with_nesting uu____4470
         | uu____4471 ->
             let uu____4476 =
               let uu____4477 = p_tuplePattern pat in
               let uu____4478 =
                 let uu____4479 = FStar_Pprint.break_ (Prims.parse_int "0") in
                 let uu____4480 =
                   let uu____4481 = p_tmEqNoRefinement t in
                   FStar_Pprint.op_Hat_Hat FStar_Pprint.colon uu____4481 in
                 FStar_Pprint.op_Hat_Hat uu____4479 uu____4480 in
               FStar_Pprint.op_Hat_Hat uu____4477 uu____4478 in
             soft_parens_with_nesting uu____4476)
    | FStar_Parser_AST.PatList pats ->
        let uu____4485 =
          separate_break_map FStar_Pprint.semi p_tuplePattern pats in
        FStar_Pprint.surround (Prims.parse_int "2") (Prims.parse_int "0")
          FStar_Pprint.lbracket uu____4485 FStar_Pprint.rbracket
    | FStar_Parser_AST.PatRecord pats ->
        let p_recordFieldPat uu____4500 =
          match uu____4500 with
          | (lid, pat) ->
              let uu____4507 = p_qlident lid in
              let uu____4508 = p_tuplePattern pat in
              infix2 FStar_Pprint.equals uu____4507 uu____4508 in
        let uu____4509 =
          separate_break_map FStar_Pprint.semi p_recordFieldPat pats in
        soft_braces_with_nesting uu____4509
    | FStar_Parser_AST.PatTuple (pats, true) ->
        let uu____4519 =
          FStar_Pprint.op_Hat_Hat FStar_Pprint.lparen FStar_Pprint.bar in
        let uu____4520 =
          separate_break_map FStar_Pprint.comma p_constructorPattern pats in
        let uu____4521 =
          FStar_Pprint.op_Hat_Hat FStar_Pprint.bar FStar_Pprint.rparen in
        FStar_Pprint.surround (Prims.parse_int "2") (Prims.parse_int "1")
          uu____4519 uu____4520 uu____4521
    | FStar_Parser_AST.PatTvar (tv, arg_qualifier_opt) -> p_tvar tv
    | FStar_Parser_AST.PatOp op ->
        let uu____4538 =
          let uu____4539 =
            let uu____4540 = str (FStar_Ident.text_of_id op) in
            let uu____4541 =
              FStar_Pprint.op_Hat_Hat FStar_Pprint.space FStar_Pprint.rparen in
            FStar_Pprint.op_Hat_Hat uu____4540 uu____4541 in
          FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____4539 in
        FStar_Pprint.op_Hat_Hat FStar_Pprint.lparen uu____4538
    | FStar_Parser_AST.PatWild -> FStar_Pprint.underscore
    | FStar_Parser_AST.PatConst c -> p_constant c
    | FStar_Parser_AST.PatVar (lid, aqual) ->
        let uu____4549 = FStar_Pprint.optional p_aqual aqual in
        let uu____4550 = p_lident lid in
        FStar_Pprint.op_Hat_Hat uu____4549 uu____4550
    | FStar_Parser_AST.PatName uid -> p_quident uid
    | FStar_Parser_AST.PatOr uu____4552 -> failwith "Inner or pattern !"
    | FStar_Parser_AST.PatApp
        ({ FStar_Parser_AST.pat = FStar_Parser_AST.PatName uu____4555;
           FStar_Parser_AST.prange = uu____4556;_},
         uu____4557)
        ->
        let uu____4562 = p_tuplePattern p in
        soft_parens_with_nesting uu____4562
    | FStar_Parser_AST.PatTuple (uu____4563, false) ->
        let uu____4568 = p_tuplePattern p in
        soft_parens_with_nesting uu____4568
    | uu____4569 ->
        let uu____4570 =
          let uu____4571 = FStar_Parser_AST.pat_to_string p in
          FStar_Util.format1 "Invalid pattern %s" uu____4571 in
        failwith uu____4570
and (p_binder :
  Prims.bool -> FStar_Parser_AST.binder -> FStar_Pprint.document) =
  fun is_atomic ->
    fun b ->
      match b.FStar_Parser_AST.b with
      | FStar_Parser_AST.Variable lid ->
          let uu____4575 =
            FStar_Pprint.optional p_aqual b.FStar_Parser_AST.aqual in
          let uu____4576 = p_lident lid in
          FStar_Pprint.op_Hat_Hat uu____4575 uu____4576
      | FStar_Parser_AST.TVariable lid -> p_lident lid
      | FStar_Parser_AST.Annotated (lid, t) ->
          let doc1 =
            match t.FStar_Parser_AST.tm with
            | FStar_Parser_AST.Refine
                ({
                   FStar_Parser_AST.b = FStar_Parser_AST.Annotated (lid', t1);
                   FStar_Parser_AST.brange = uu____4583;
                   FStar_Parser_AST.blevel = uu____4584;
                   FStar_Parser_AST.aqual = uu____4585;_},
                 phi)
                when lid.FStar_Ident.idText = lid'.FStar_Ident.idText ->
                let uu____4587 = p_ident lid in
                p_refinement b.FStar_Parser_AST.aqual uu____4587 t1 phi
            | uu____4588 ->
                let uu____4589 =
                  FStar_Pprint.optional p_aqual b.FStar_Parser_AST.aqual in
                let uu____4590 =
                  let uu____4591 = p_lident lid in
                  let uu____4592 =
                    let uu____4593 =
                      let uu____4594 =
                        FStar_Pprint.break_ (Prims.parse_int "0") in
                      let uu____4595 = p_tmFormula t in
                      FStar_Pprint.op_Hat_Hat uu____4594 uu____4595 in
                    FStar_Pprint.op_Hat_Hat FStar_Pprint.colon uu____4593 in
                  FStar_Pprint.op_Hat_Hat uu____4591 uu____4592 in
                FStar_Pprint.op_Hat_Hat uu____4589 uu____4590 in
          if is_atomic
          then
            let uu____4596 =
              let uu____4597 =
                FStar_Pprint.op_Hat_Hat doc1 FStar_Pprint.rparen in
              FStar_Pprint.op_Hat_Hat FStar_Pprint.lparen uu____4597 in
            FStar_Pprint.group uu____4596
          else FStar_Pprint.group doc1
      | FStar_Parser_AST.TAnnotated uu____4599 ->
          failwith "Is this still used ?"
      | FStar_Parser_AST.NoName t ->
          (match t.FStar_Parser_AST.tm with
           | FStar_Parser_AST.Refine
               ({ FStar_Parser_AST.b = FStar_Parser_AST.NoName t1;
                  FStar_Parser_AST.brange = uu____4606;
                  FStar_Parser_AST.blevel = uu____4607;
                  FStar_Parser_AST.aqual = uu____4608;_},
                phi)
               ->
               if is_atomic
               then
                 let uu____4610 =
                   let uu____4611 =
                     let uu____4612 =
                       p_refinement b.FStar_Parser_AST.aqual
                         FStar_Pprint.underscore t1 phi in
                     FStar_Pprint.op_Hat_Hat uu____4612 FStar_Pprint.rparen in
                   FStar_Pprint.op_Hat_Hat FStar_Pprint.lparen uu____4611 in
                 FStar_Pprint.group uu____4610
               else
                 (let uu____4614 =
                    p_refinement b.FStar_Parser_AST.aqual
                      FStar_Pprint.underscore t1 phi in
                  FStar_Pprint.group uu____4614)
           | uu____4615 -> if is_atomic then p_atomicTerm t else p_appTerm t)
and (p_refinement :
  FStar_Parser_AST.arg_qualifier FStar_Pervasives_Native.option ->
    FStar_Pprint.document ->
      FStar_Parser_AST.term -> FStar_Parser_AST.term -> FStar_Pprint.document)
  =
  fun aqual_opt ->
    fun binder ->
      fun t ->
        fun phi ->
          let uu____4623 = FStar_Pprint.optional p_aqual aqual_opt in
          let uu____4624 =
            let uu____4625 =
              let uu____4626 =
                let uu____4627 = p_appTerm t in
                let uu____4628 =
                  let uu____4629 = p_noSeqTerm false false phi in
                  soft_braces_with_nesting uu____4629 in
                FStar_Pprint.op_Hat_Hat uu____4627 uu____4628 in
              FStar_Pprint.op_Hat_Hat FStar_Pprint.colon uu____4626 in
            FStar_Pprint.op_Hat_Hat binder uu____4625 in
          FStar_Pprint.op_Hat_Hat uu____4623 uu____4624
and (p_binders :
  Prims.bool -> FStar_Parser_AST.binder Prims.list -> FStar_Pprint.document)
  =
  fun is_atomic ->
    fun bs -> separate_map_or_flow break1 (p_binder is_atomic) bs
and (p_qlident : FStar_Ident.lid -> FStar_Pprint.document) =
  fun lid -> str (FStar_Ident.text_of_lid lid)
and (p_quident : FStar_Ident.lid -> FStar_Pprint.document) =
  fun lid -> str (FStar_Ident.text_of_lid lid)
and (p_ident : FStar_Ident.ident -> FStar_Pprint.document) =
  fun lid -> str (FStar_Ident.text_of_id lid)
and (p_lident : FStar_Ident.ident -> FStar_Pprint.document) =
  fun lid -> str (FStar_Ident.text_of_id lid)
and (p_uident : FStar_Ident.ident -> FStar_Pprint.document) =
  fun lid -> str (FStar_Ident.text_of_id lid)
and (p_tvar : FStar_Ident.ident -> FStar_Pprint.document) =
  fun lid -> str (FStar_Ident.text_of_id lid)
and (p_lidentOrUnderscore : FStar_Ident.ident -> FStar_Pprint.document) =
  fun id1 ->
    if
      FStar_Util.starts_with FStar_Ident.reserved_prefix
        id1.FStar_Ident.idText
    then FStar_Pprint.underscore
    else p_lident id1
and (paren_if : Prims.bool -> FStar_Pprint.document -> FStar_Pprint.document)
  = fun b -> if b then soft_parens_with_nesting else (fun x -> x)
and (p_term :
  Prims.bool -> Prims.bool -> FStar_Parser_AST.term -> FStar_Pprint.document)
  =
  fun ps ->
    fun pb ->
      fun e ->
        match e.FStar_Parser_AST.tm with
        | FStar_Parser_AST.Seq (e1, e2) ->
            let uu____4652 =
              let uu____4653 =
                let uu____4654 = p_noSeqTerm true false e1 in
                FStar_Pprint.op_Hat_Hat uu____4654 FStar_Pprint.semi in
              FStar_Pprint.group uu____4653 in
            let uu____4655 = p_term ps pb e2 in
            FStar_Pprint.op_Hat_Slash_Hat uu____4652 uu____4655
        | FStar_Parser_AST.Bind (x, e1, e2) ->
            let uu____4659 =
              let uu____4660 =
                let uu____4661 =
                  let uu____4662 = p_lident x in
                  let uu____4663 =
                    FStar_Pprint.op_Hat_Hat FStar_Pprint.space
                      FStar_Pprint.long_left_arrow in
                  FStar_Pprint.op_Hat_Hat uu____4662 uu____4663 in
                let uu____4664 =
                  let uu____4665 = p_noSeqTerm true false e1 in
                  let uu____4666 =
                    FStar_Pprint.op_Hat_Hat FStar_Pprint.space
                      FStar_Pprint.semi in
                  FStar_Pprint.op_Hat_Hat uu____4665 uu____4666 in
                op_Hat_Slash_Plus_Hat uu____4661 uu____4664 in
              FStar_Pprint.group uu____4660 in
            let uu____4667 = p_term ps pb e2 in
            FStar_Pprint.op_Hat_Slash_Hat uu____4659 uu____4667
        | uu____4668 ->
            let uu____4669 = p_noSeqTerm ps pb e in
            FStar_Pprint.group uu____4669
and (p_noSeqTerm :
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
            let uu____4680 =
              let uu____4681 = p_tmIff e1 in
              let uu____4682 =
                let uu____4683 =
                  let uu____4684 = p_typ ps pb t in
                  FStar_Pprint.op_Hat_Slash_Hat FStar_Pprint.colon uu____4684 in
                FStar_Pprint.op_Hat_Hat FStar_Pprint.langle uu____4683 in
              FStar_Pprint.op_Hat_Slash_Hat uu____4681 uu____4682 in
            FStar_Pprint.group uu____4680
        | FStar_Parser_AST.Ascribed (e1, t, FStar_Pervasives_Native.Some tac)
            ->
            let uu____4690 =
              let uu____4691 = p_tmIff e1 in
              let uu____4692 =
                let uu____4693 =
                  let uu____4694 =
                    let uu____4695 = p_typ false false t in
                    let uu____4696 =
                      let uu____4697 = str "by" in
                      let uu____4698 = p_typ ps pb tac in
                      FStar_Pprint.op_Hat_Slash_Hat uu____4697 uu____4698 in
                    FStar_Pprint.op_Hat_Slash_Hat uu____4695 uu____4696 in
                  FStar_Pprint.op_Hat_Slash_Hat FStar_Pprint.colon uu____4694 in
                FStar_Pprint.op_Hat_Hat FStar_Pprint.langle uu____4693 in
              FStar_Pprint.op_Hat_Slash_Hat uu____4691 uu____4692 in
            FStar_Pprint.group uu____4690
        | FStar_Parser_AST.Op
            ({ FStar_Ident.idText = ".()<-";
               FStar_Ident.idRange = uu____4699;_},
             e1::e2::e3::[])
            ->
            let uu____4705 =
              let uu____4706 =
                let uu____4707 =
                  let uu____4708 = p_atomicTermNotQUident e1 in
                  let uu____4709 =
                    let uu____4710 =
                      let uu____4711 =
                        let uu____4712 = p_term false false e2 in
                        soft_parens_with_nesting uu____4712 in
                      let uu____4713 =
                        FStar_Pprint.op_Hat_Hat FStar_Pprint.space
                          FStar_Pprint.larrow in
                      FStar_Pprint.op_Hat_Hat uu____4711 uu____4713 in
                    FStar_Pprint.op_Hat_Hat FStar_Pprint.dot uu____4710 in
                  FStar_Pprint.op_Hat_Hat uu____4708 uu____4709 in
                FStar_Pprint.group uu____4707 in
              let uu____4714 =
                let uu____4715 = p_noSeqTerm ps pb e3 in jump2 uu____4715 in
              FStar_Pprint.op_Hat_Hat uu____4706 uu____4714 in
            FStar_Pprint.group uu____4705
        | FStar_Parser_AST.Op
            ({ FStar_Ident.idText = ".[]<-";
               FStar_Ident.idRange = uu____4716;_},
             e1::e2::e3::[])
            ->
            let uu____4722 =
              let uu____4723 =
                let uu____4724 =
                  let uu____4725 = p_atomicTermNotQUident e1 in
                  let uu____4726 =
                    let uu____4727 =
                      let uu____4728 =
                        let uu____4729 = p_term false false e2 in
                        soft_brackets_with_nesting uu____4729 in
                      let uu____4730 =
                        FStar_Pprint.op_Hat_Hat FStar_Pprint.space
                          FStar_Pprint.larrow in
                      FStar_Pprint.op_Hat_Hat uu____4728 uu____4730 in
                    FStar_Pprint.op_Hat_Hat FStar_Pprint.dot uu____4727 in
                  FStar_Pprint.op_Hat_Hat uu____4725 uu____4726 in
                FStar_Pprint.group uu____4724 in
              let uu____4731 =
                let uu____4732 = p_noSeqTerm ps pb e3 in jump2 uu____4732 in
              FStar_Pprint.op_Hat_Hat uu____4723 uu____4731 in
            FStar_Pprint.group uu____4722
        | FStar_Parser_AST.Requires (e1, wtf) ->
            let uu____4748 =
              let uu____4749 = str "requires" in
              let uu____4750 = p_typ ps pb e1 in
              FStar_Pprint.op_Hat_Slash_Hat uu____4749 uu____4750 in
            FStar_Pprint.group uu____4748
        | FStar_Parser_AST.Ensures (e1, wtf) ->
            let uu____4766 =
              let uu____4767 = str "ensures" in
              let uu____4768 = p_typ ps pb e1 in
              FStar_Pprint.op_Hat_Slash_Hat uu____4767 uu____4768 in
            FStar_Pprint.group uu____4766
        | FStar_Parser_AST.Attributes es ->
            let uu____4772 =
              let uu____4773 = str "attributes" in
              let uu____4774 =
                FStar_Pprint.separate_map break1 p_atomicTerm es in
              FStar_Pprint.op_Hat_Slash_Hat uu____4773 uu____4774 in
            FStar_Pprint.group uu____4772
        | FStar_Parser_AST.If (e1, e2, e3) ->
            if is_unit e3
            then
              let uu____4778 =
                let uu____4779 =
                  let uu____4780 = str "if" in
                  let uu____4781 = p_noSeqTerm false false e1 in
                  op_Hat_Slash_Plus_Hat uu____4780 uu____4781 in
                let uu____4782 =
                  let uu____4783 = str "then" in
                  let uu____4784 = p_noSeqTerm ps pb e2 in
                  op_Hat_Slash_Plus_Hat uu____4783 uu____4784 in
                FStar_Pprint.op_Hat_Slash_Hat uu____4779 uu____4782 in
              FStar_Pprint.group uu____4778
            else
              (let e2_doc =
                 match e2.FStar_Parser_AST.tm with
                 | FStar_Parser_AST.If (uu____4787, uu____4788, e31) when
                     is_unit e31 ->
                     let uu____4790 = p_noSeqTerm false false e2 in
                     soft_parens_with_nesting uu____4790
                 | uu____4791 -> p_noSeqTerm false false e2 in
               let uu____4792 =
                 let uu____4793 =
                   let uu____4794 = str "if" in
                   let uu____4795 = p_noSeqTerm false false e1 in
                   op_Hat_Slash_Plus_Hat uu____4794 uu____4795 in
                 let uu____4796 =
                   let uu____4797 =
                     let uu____4798 = str "then" in
                     op_Hat_Slash_Plus_Hat uu____4798 e2_doc in
                   let uu____4799 =
                     let uu____4800 = str "else" in
                     let uu____4801 = p_noSeqTerm ps pb e3 in
                     op_Hat_Slash_Plus_Hat uu____4800 uu____4801 in
                   FStar_Pprint.op_Hat_Slash_Hat uu____4797 uu____4799 in
                 FStar_Pprint.op_Hat_Slash_Hat uu____4793 uu____4796 in
               FStar_Pprint.group uu____4792)
        | FStar_Parser_AST.TryWith (e1, branches) ->
            let uu____4824 =
              let uu____4825 =
                let uu____4826 =
                  let uu____4827 = str "try" in
                  let uu____4828 = p_noSeqTerm false false e1 in
                  prefix2 uu____4827 uu____4828 in
                let uu____4829 =
                  let uu____4830 = str "with" in
                  let uu____4831 =
                    separate_map_last FStar_Pprint.hardline p_patternBranch
                      branches in
                  FStar_Pprint.op_Hat_Slash_Hat uu____4830 uu____4831 in
                FStar_Pprint.op_Hat_Slash_Hat uu____4826 uu____4829 in
              FStar_Pprint.group uu____4825 in
            let uu____4840 = paren_if (ps || pb) in uu____4840 uu____4824
        | FStar_Parser_AST.Match (e1, branches) ->
            let uu____4865 =
              let uu____4866 =
                let uu____4867 =
                  let uu____4868 = str "match" in
                  let uu____4869 = p_noSeqTerm false false e1 in
                  let uu____4870 = str "with" in
                  FStar_Pprint.surround (Prims.parse_int "2")
                    (Prims.parse_int "1") uu____4868 uu____4869 uu____4870 in
                let uu____4871 =
                  separate_map_last FStar_Pprint.hardline p_patternBranch
                    branches in
                FStar_Pprint.op_Hat_Slash_Hat uu____4867 uu____4871 in
              FStar_Pprint.group uu____4866 in
            let uu____4880 = paren_if (ps || pb) in uu____4880 uu____4865
        | FStar_Parser_AST.LetOpen (uid, e1) ->
            let uu____4885 =
              let uu____4886 =
                let uu____4887 =
                  let uu____4888 = str "let open" in
                  let uu____4889 = p_quident uid in
                  let uu____4890 = str "in" in
                  FStar_Pprint.surround (Prims.parse_int "2")
                    (Prims.parse_int "1") uu____4888 uu____4889 uu____4890 in
                let uu____4891 = p_term false pb e1 in
                FStar_Pprint.op_Hat_Slash_Hat uu____4887 uu____4891 in
              FStar_Pprint.group uu____4886 in
            let uu____4892 = paren_if ps in uu____4892 uu____4885
        | FStar_Parser_AST.Let (q, lbs, e1) ->
            let p_lb q1 uu____4948 is_last =
              match uu____4948 with
              | (a, (pat, e2)) ->
                  let attrs = p_attrs_opt a in
                  let doc_let_or_and =
                    match q1 with
                    | FStar_Pervasives_Native.Some (FStar_Parser_AST.Rec) ->
                        let uu____4981 =
                          let uu____4982 = str "let" in
                          let uu____4983 = str "rec" in
                          FStar_Pprint.op_Hat_Slash_Hat uu____4982 uu____4983 in
                        FStar_Pprint.group uu____4981
                    | FStar_Pervasives_Native.Some
                        (FStar_Parser_AST.NoLetQualifier) -> str "let"
                    | uu____4984 -> str "and" in
                  let doc_pat = p_letlhs (pat, e2) in
                  let doc_expr = p_term false false e2 in
                  let uu____4989 =
                    if is_last
                    then
                      let uu____4990 =
                        let uu____4991 =
                          FStar_Pprint.surround (Prims.parse_int "2")
                            (Prims.parse_int "1") doc_let_or_and doc_pat
                            FStar_Pprint.equals in
                        let uu____4992 = str "in" in
                        FStar_Pprint.surround (Prims.parse_int "2")
                          (Prims.parse_int "1") uu____4991 doc_expr
                          uu____4992 in
                      FStar_Pprint.group uu____4990
                    else
                      (let uu____4994 =
                         let uu____4995 =
                           FStar_Pprint.surround (Prims.parse_int "2")
                             (Prims.parse_int "1") doc_let_or_and doc_pat
                             FStar_Pprint.equals in
                         FStar_Pprint.prefix (Prims.parse_int "2")
                           (Prims.parse_int "1") uu____4995 doc_expr in
                       FStar_Pprint.group uu____4994) in
                  FStar_Pprint.op_Hat_Hat attrs uu____4989 in
            let l = FStar_List.length lbs in
            let lbs_docs =
              FStar_List.mapi
                (fun i ->
                   fun lb ->
                     if i = (Prims.parse_int "0")
                     then
                       let uu____5041 =
                         p_lb (FStar_Pervasives_Native.Some q) lb
                           (i = (l - (Prims.parse_int "1"))) in
                       FStar_Pprint.group uu____5041
                     else
                       (let uu____5049 =
                          p_lb FStar_Pervasives_Native.None lb
                            (i = (l - (Prims.parse_int "1"))) in
                        FStar_Pprint.group uu____5049)) lbs in
            let lbs_doc =
              let uu____5057 = FStar_Pprint.separate break1 lbs_docs in
              FStar_Pprint.group uu____5057 in
            let uu____5058 =
              let uu____5059 =
                let uu____5060 =
                  let uu____5061 = p_term false pb e1 in
                  FStar_Pprint.op_Hat_Hat FStar_Pprint.hardline uu____5061 in
                FStar_Pprint.op_Hat_Hat lbs_doc uu____5060 in
              FStar_Pprint.group uu____5059 in
            let uu____5062 = paren_if ps in uu____5062 uu____5058
        | FStar_Parser_AST.Abs
            ({ FStar_Parser_AST.pat = FStar_Parser_AST.PatVar (x, typ_opt);
               FStar_Parser_AST.prange = uu____5067;_}::[],
             {
               FStar_Parser_AST.tm = FStar_Parser_AST.Match
                 (maybe_x, branches);
               FStar_Parser_AST.range = uu____5070;
               FStar_Parser_AST.level = uu____5071;_})
            when matches_var maybe_x x ->
            let uu____5098 =
              let uu____5099 =
                let uu____5100 = str "function" in
                let uu____5101 =
                  separate_map_last FStar_Pprint.hardline p_patternBranch
                    branches in
                FStar_Pprint.op_Hat_Slash_Hat uu____5100 uu____5101 in
              FStar_Pprint.group uu____5099 in
            let uu____5110 = paren_if (ps || pb) in uu____5110 uu____5098
        | FStar_Parser_AST.Quote (e1, FStar_Parser_AST.Dynamic) ->
            let uu____5114 =
              let uu____5115 = str "quote" in
              let uu____5116 = p_noSeqTerm ps pb e1 in
              FStar_Pprint.op_Hat_Slash_Hat uu____5115 uu____5116 in
            FStar_Pprint.group uu____5114
        | FStar_Parser_AST.Quote (e1, FStar_Parser_AST.Static) ->
            let uu____5118 =
              let uu____5119 = str "`" in
              let uu____5120 = p_noSeqTerm ps pb e1 in
              FStar_Pprint.op_Hat_Hat uu____5119 uu____5120 in
            FStar_Pprint.group uu____5118
        | FStar_Parser_AST.VQuote e1 ->
            let uu____5122 =
              let uu____5123 = str "%`" in
              let uu____5124 = p_noSeqTerm ps pb e1 in
              FStar_Pprint.op_Hat_Hat uu____5123 uu____5124 in
            FStar_Pprint.group uu____5122
        | FStar_Parser_AST.Antiquote (false, e1) ->
            let uu____5126 =
              let uu____5127 = str "`#" in
              let uu____5128 = p_noSeqTerm ps pb e1 in
              FStar_Pprint.op_Hat_Hat uu____5127 uu____5128 in
            FStar_Pprint.group uu____5126
        | FStar_Parser_AST.Antiquote (true, e1) ->
            let uu____5130 =
              let uu____5131 = str "`@" in
              let uu____5132 = p_noSeqTerm ps pb e1 in
              FStar_Pprint.op_Hat_Hat uu____5131 uu____5132 in
            FStar_Pprint.group uu____5130
        | uu____5133 -> p_typ ps pb e
and (p_attrs_opt :
  FStar_Parser_AST.term Prims.list FStar_Pervasives_Native.option ->
    FStar_Pprint.document)
  =
  fun uu___63_5134 ->
    match uu___63_5134 with
    | FStar_Pervasives_Native.None -> FStar_Pprint.empty
    | FStar_Pervasives_Native.Some terms ->
        let uu____5146 =
          let uu____5147 =
            let uu____5148 = str "[@" in
            let uu____5149 =
              let uu____5150 =
                FStar_Pprint.separate_map break1 p_atomicTerm terms in
              let uu____5151 = str "]" in
              FStar_Pprint.op_Hat_Slash_Hat uu____5150 uu____5151 in
            FStar_Pprint.op_Hat_Slash_Hat uu____5148 uu____5149 in
          FStar_Pprint.group uu____5147 in
        FStar_Pprint.op_Hat_Hat uu____5146 break1
and (p_typ :
  Prims.bool -> Prims.bool -> FStar_Parser_AST.term -> FStar_Pprint.document)
  =
  fun ps ->
    fun pb -> fun e -> with_comment (p_typ' ps pb) e e.FStar_Parser_AST.range
and (p_typ' :
  Prims.bool -> Prims.bool -> FStar_Parser_AST.term -> FStar_Pprint.document)
  =
  fun ps ->
    fun pb ->
      fun e ->
        match e.FStar_Parser_AST.tm with
        | FStar_Parser_AST.QForall (bs, trigger, e1) ->
            let uu____5173 =
              let uu____5174 =
                let uu____5175 = p_quantifier e in
                FStar_Pprint.op_Hat_Hat uu____5175 FStar_Pprint.space in
              let uu____5176 = p_binders true bs in
              FStar_Pprint.soft_surround (Prims.parse_int "2")
                (Prims.parse_int "0") uu____5174 uu____5176 FStar_Pprint.dot in
            let uu____5177 =
              let uu____5178 = p_trigger trigger in
              let uu____5179 = p_noSeqTerm ps pb e1 in
              FStar_Pprint.op_Hat_Hat uu____5178 uu____5179 in
            prefix2 uu____5173 uu____5177
        | FStar_Parser_AST.QExists (bs, trigger, e1) ->
            let uu____5195 =
              let uu____5196 =
                let uu____5197 = p_quantifier e in
                FStar_Pprint.op_Hat_Hat uu____5197 FStar_Pprint.space in
              let uu____5198 = p_binders true bs in
              FStar_Pprint.soft_surround (Prims.parse_int "2")
                (Prims.parse_int "0") uu____5196 uu____5198 FStar_Pprint.dot in
            let uu____5199 =
              let uu____5200 = p_trigger trigger in
              let uu____5201 = p_noSeqTerm ps pb e1 in
              FStar_Pprint.op_Hat_Hat uu____5200 uu____5201 in
            prefix2 uu____5195 uu____5199
        | uu____5202 -> p_simpleTerm ps pb e
and (p_quantifier : FStar_Parser_AST.term -> FStar_Pprint.document) =
  fun e ->
    match e.FStar_Parser_AST.tm with
    | FStar_Parser_AST.QForall uu____5204 -> str "forall"
    | FStar_Parser_AST.QExists uu____5217 -> str "exists"
    | uu____5230 ->
        failwith "Imposible : p_quantifier called on a non-quantifier term"
and (p_trigger :
  FStar_Parser_AST.term Prims.list Prims.list -> FStar_Pprint.document) =
  fun uu___64_5231 ->
    match uu___64_5231 with
    | [] -> FStar_Pprint.empty
    | pats ->
        let uu____5243 =
          let uu____5244 =
            let uu____5245 = str "pattern" in
            let uu____5246 =
              let uu____5247 =
                let uu____5248 = p_disjunctivePats pats in jump2 uu____5248 in
              let uu____5249 =
                FStar_Pprint.op_Hat_Hat FStar_Pprint.rbrace break1 in
              FStar_Pprint.op_Hat_Slash_Hat uu____5247 uu____5249 in
            FStar_Pprint.op_Hat_Slash_Hat uu____5245 uu____5246 in
          FStar_Pprint.op_Hat_Hat FStar_Pprint.colon uu____5244 in
        FStar_Pprint.op_Hat_Hat FStar_Pprint.lbrace uu____5243
and (p_disjunctivePats :
  FStar_Parser_AST.term Prims.list Prims.list -> FStar_Pprint.document) =
  fun pats ->
    let uu____5255 = str "\\/" in
    FStar_Pprint.separate_map uu____5255 p_conjunctivePats pats
and (p_conjunctivePats :
  FStar_Parser_AST.term Prims.list -> FStar_Pprint.document) =
  fun pats ->
    let uu____5261 =
      FStar_Pprint.separate_map FStar_Pprint.semi p_appTerm pats in
    FStar_Pprint.group uu____5261
and (p_simpleTerm :
  Prims.bool -> Prims.bool -> FStar_Parser_AST.term -> FStar_Pprint.document)
  =
  fun ps ->
    fun pb ->
      fun e ->
        match e.FStar_Parser_AST.tm with
        | FStar_Parser_AST.Abs (pats, e1) ->
            let uu____5271 =
              let uu____5272 =
                let uu____5273 = str "fun" in
                let uu____5274 =
                  let uu____5275 =
                    FStar_Pprint.separate_map break1 p_atomicPattern pats in
                  FStar_Pprint.op_Hat_Slash_Hat uu____5275
                    FStar_Pprint.rarrow in
                op_Hat_Slash_Plus_Hat uu____5273 uu____5274 in
              let uu____5276 = p_term false pb e1 in
              op_Hat_Slash_Plus_Hat uu____5272 uu____5276 in
            let uu____5277 = paren_if ps in uu____5277 uu____5271
        | uu____5280 -> p_tmIff e
and (p_maybeFocusArrow : Prims.bool -> FStar_Pprint.document) =
  fun b -> if b then str "~>" else FStar_Pprint.rarrow
and (p_patternBranch :
  Prims.bool ->
    (FStar_Parser_AST.pattern,
      FStar_Parser_AST.term FStar_Pervasives_Native.option,
      FStar_Parser_AST.term) FStar_Pervasives_Native.tuple3 ->
      FStar_Pprint.document)
  =
  fun pb ->
    fun uu____5284 ->
      match uu____5284 with
      | (pat, when_opt, e) ->
          let uu____5300 =
            let uu____5301 =
              let uu____5302 =
                let uu____5303 =
                  let uu____5304 =
                    let uu____5305 = p_disjunctivePattern pat in
                    let uu____5306 =
                      let uu____5307 = p_maybeWhen when_opt in
                      FStar_Pprint.op_Hat_Hat uu____5307 FStar_Pprint.rarrow in
                    op_Hat_Slash_Plus_Hat uu____5305 uu____5306 in
                  FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____5304 in
                FStar_Pprint.op_Hat_Hat FStar_Pprint.bar uu____5303 in
              FStar_Pprint.group uu____5302 in
            let uu____5308 = p_term false pb e in
            op_Hat_Slash_Plus_Hat uu____5301 uu____5308 in
          FStar_Pprint.group uu____5300
and (p_maybeWhen :
  FStar_Parser_AST.term FStar_Pervasives_Native.option ->
    FStar_Pprint.document)
  =
  fun uu___65_5309 ->
    match uu___65_5309 with
    | FStar_Pervasives_Native.None -> FStar_Pprint.empty
    | FStar_Pervasives_Native.Some e ->
        let uu____5313 = str "when" in
        let uu____5314 =
          let uu____5315 = p_tmFormula e in
          FStar_Pprint.op_Hat_Hat uu____5315 FStar_Pprint.space in
        op_Hat_Slash_Plus_Hat uu____5313 uu____5314
and (p_tmIff : FStar_Parser_AST.term -> FStar_Pprint.document) =
  fun e ->
    match e.FStar_Parser_AST.tm with
    | FStar_Parser_AST.Op
        ({ FStar_Ident.idText = "<==>"; FStar_Ident.idRange = uu____5317;_},
         e1::e2::[])
        ->
        let uu____5322 = str "<==>" in
        let uu____5323 = p_tmImplies e1 in
        let uu____5324 = p_tmIff e2 in
        infix0 uu____5322 uu____5323 uu____5324
    | uu____5325 -> p_tmImplies e
and (p_tmImplies : FStar_Parser_AST.term -> FStar_Pprint.document) =
  fun e ->
    match e.FStar_Parser_AST.tm with
    | FStar_Parser_AST.Op
        ({ FStar_Ident.idText = "==>"; FStar_Ident.idRange = uu____5327;_},
         e1::e2::[])
        ->
        let uu____5332 = str "==>" in
        let uu____5333 = p_tmArrow p_tmFormula e1 in
        let uu____5334 = p_tmImplies e2 in
        infix0 uu____5332 uu____5333 uu____5334
    | uu____5335 -> p_tmArrow p_tmFormula e
and (p_tmArrow :
  (FStar_Parser_AST.term -> FStar_Pprint.document) ->
    FStar_Parser_AST.term -> FStar_Pprint.document)
  =
  fun p_Tm ->
    fun e ->
      match e.FStar_Parser_AST.tm with
      | FStar_Parser_AST.Product (bs, tgt) ->
          let uu____5346 =
            let uu____5347 =
              separate_map_or_flow FStar_Pprint.empty
                (fun b ->
                   let uu____5352 = p_binder false b in
                   let uu____5353 =
                     let uu____5354 =
                       FStar_Pprint.op_Hat_Hat FStar_Pprint.rarrow break1 in
                     FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____5354 in
                   FStar_Pprint.op_Hat_Hat uu____5352 uu____5353) bs in
            let uu____5355 = p_tmArrow p_Tm tgt in
            FStar_Pprint.op_Hat_Hat uu____5347 uu____5355 in
          FStar_Pprint.group uu____5346
      | uu____5356 -> p_Tm e
and (p_tmFormula : FStar_Parser_AST.term -> FStar_Pprint.document) =
  fun e ->
    match e.FStar_Parser_AST.tm with
    | FStar_Parser_AST.Op
        ({ FStar_Ident.idText = "\\/"; FStar_Ident.idRange = uu____5358;_},
         e1::e2::[])
        ->
        let uu____5363 = str "\\/" in
        let uu____5364 = p_tmFormula e1 in
        let uu____5365 = p_tmConjunction e2 in
        infix0 uu____5363 uu____5364 uu____5365
    | uu____5366 -> p_tmConjunction e
and (p_tmConjunction : FStar_Parser_AST.term -> FStar_Pprint.document) =
  fun e ->
    match e.FStar_Parser_AST.tm with
    | FStar_Parser_AST.Op
        ({ FStar_Ident.idText = "/\\"; FStar_Ident.idRange = uu____5368;_},
         e1::e2::[])
        ->
        let uu____5373 = str "/\\" in
        let uu____5374 = p_tmConjunction e1 in
        let uu____5375 = p_tmTuple e2 in
        infix0 uu____5373 uu____5374 uu____5375
    | uu____5376 -> p_tmTuple e
and (p_tmTuple : FStar_Parser_AST.term -> FStar_Pprint.document) =
  fun e -> with_comment p_tmTuple' e e.FStar_Parser_AST.range
and (p_tmTuple' : FStar_Parser_AST.term -> FStar_Pprint.document) =
  fun e ->
    match e.FStar_Parser_AST.tm with
    | FStar_Parser_AST.Construct (lid, args) when is_tuple_constructor lid ->
        let uu____5393 = FStar_Pprint.op_Hat_Hat FStar_Pprint.comma break1 in
        FStar_Pprint.separate_map uu____5393
          (fun uu____5401 ->
             match uu____5401 with | (e1, uu____5407) -> p_tmEq e1) args
    | uu____5408 -> p_tmEq e
and (paren_if_gt :
  Prims.int -> Prims.int -> FStar_Pprint.document -> FStar_Pprint.document) =
  fun curr ->
    fun mine ->
      fun doc1 ->
        if mine <= curr
        then doc1
        else
          (let uu____5413 =
             let uu____5414 =
               FStar_Pprint.op_Hat_Hat doc1 FStar_Pprint.rparen in
             FStar_Pprint.op_Hat_Hat FStar_Pprint.lparen uu____5414 in
           FStar_Pprint.group uu____5413)
and (p_tmEqWith :
  (FStar_Parser_AST.term -> FStar_Pprint.document) ->
    FStar_Parser_AST.term -> FStar_Pprint.document)
  =
  fun p_X ->
    fun e ->
      let n1 =
        max_level
          (FStar_List.append [colon_equals (); pipe_right ()]
             (operatorInfix0ad12 ())) in
      p_tmEqWith' p_X n1 e
and (p_tmEqWith' :
  (FStar_Parser_AST.term -> FStar_Pprint.document) ->
    Prims.int -> FStar_Parser_AST.term -> FStar_Pprint.document)
  =
  fun p_X ->
    fun curr ->
      fun e ->
        match e.FStar_Parser_AST.tm with
        | FStar_Parser_AST.Op (op, e1::e2::[]) when
            ((is_operatorInfix0ad12 op) ||
               ((FStar_Ident.text_of_id op) = "="))
              || ((FStar_Ident.text_of_id op) = "|>")
            ->
            let op1 = FStar_Ident.text_of_id op in
            let uu____5477 = levels op1 in
            (match uu____5477 with
             | (left1, mine, right1) ->
                 let uu____5487 =
                   let uu____5488 = FStar_All.pipe_left str op1 in
                   let uu____5489 = p_tmEqWith' p_X left1 e1 in
                   let uu____5490 = p_tmEqWith' p_X right1 e2 in
                   infix0 uu____5488 uu____5489 uu____5490 in
                 paren_if_gt curr mine uu____5487)
        | FStar_Parser_AST.Op
            ({ FStar_Ident.idText = ":="; FStar_Ident.idRange = uu____5491;_},
             e1::e2::[])
            ->
            let uu____5496 =
              let uu____5497 = p_tmEqWith p_X e1 in
              let uu____5498 =
                let uu____5499 =
                  let uu____5500 =
                    let uu____5501 = p_tmEqWith p_X e2 in
                    op_Hat_Slash_Plus_Hat FStar_Pprint.equals uu____5501 in
                  FStar_Pprint.op_Hat_Hat FStar_Pprint.colon uu____5500 in
                FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____5499 in
              FStar_Pprint.op_Hat_Hat uu____5497 uu____5498 in
            FStar_Pprint.group uu____5496
        | FStar_Parser_AST.Op
            ({ FStar_Ident.idText = "-"; FStar_Ident.idRange = uu____5502;_},
             e1::[])
            ->
            let uu____5506 = levels "-" in
            (match uu____5506 with
             | (left1, mine, right1) ->
                 let uu____5516 = p_tmEqWith' p_X mine e1 in
                 FStar_Pprint.op_Hat_Slash_Hat FStar_Pprint.minus uu____5516)
        | uu____5517 -> p_tmNoEqWith p_X e
and (p_tmNoEqWith :
  (FStar_Parser_AST.term -> FStar_Pprint.document) ->
    FStar_Parser_AST.term -> FStar_Pprint.document)
  =
  fun p_X ->
    fun e ->
      let n1 = max_level [colon_colon (); amp (); opinfix3 (); opinfix4 ()] in
      p_tmNoEqWith' p_X n1 e
and (p_tmNoEqWith' :
  (FStar_Parser_AST.term -> FStar_Pprint.document) ->
    Prims.int -> FStar_Parser_AST.term -> FStar_Pprint.document)
  =
  fun p_X ->
    fun curr ->
      fun e ->
        match e.FStar_Parser_AST.tm with
        | FStar_Parser_AST.Construct
            (lid, (e1, uu____5588)::(e2, uu____5590)::[]) when
            (FStar_Ident.lid_equals lid FStar_Parser_Const.cons_lid) &&
              (let uu____5610 = is_list e in Prims.op_Negation uu____5610)
            ->
            let op = "::" in
            let uu____5612 = levels op in
            (match uu____5612 with
             | (left1, mine, right1) ->
                 let uu____5622 =
                   let uu____5623 = str op in
                   let uu____5624 = p_tmNoEqWith' p_X left1 e1 in
                   let uu____5625 = p_tmNoEqWith' p_X right1 e2 in
                   infix0 uu____5623 uu____5624 uu____5625 in
                 paren_if_gt curr mine uu____5622)
        | FStar_Parser_AST.Sum (binders, res) ->
            let op = "&" in
            let uu____5633 = levels op in
            (match uu____5633 with
             | (left1, mine, right1) ->
                 let p_dsumfst b =
                   let uu____5647 = p_binder false b in
                   let uu____5648 =
                     let uu____5649 =
                       let uu____5650 = str op in
                       FStar_Pprint.op_Hat_Hat uu____5650 break1 in
                     FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____5649 in
                   FStar_Pprint.op_Hat_Hat uu____5647 uu____5648 in
                 let uu____5651 =
                   let uu____5652 = FStar_Pprint.concat_map p_dsumfst binders in
                   let uu____5653 = p_tmNoEqWith' p_X right1 res in
                   FStar_Pprint.op_Hat_Hat uu____5652 uu____5653 in
                 paren_if_gt curr mine uu____5651)
        | FStar_Parser_AST.Op (op, e1::e2::[]) when is_operatorInfix34 op ->
            let op1 = FStar_Ident.text_of_id op in
            let uu____5660 = levels op1 in
            (match uu____5660 with
             | (left1, mine, right1) ->
                 let uu____5670 =
                   let uu____5671 = str op1 in
                   let uu____5672 = p_tmNoEqWith' p_X left1 e1 in
                   let uu____5673 = p_tmNoEqWith' p_X right1 e2 in
                   infix0 uu____5671 uu____5672 uu____5673 in
                 paren_if_gt curr mine uu____5670)
        | FStar_Parser_AST.Record (with_opt, record_fields) ->
            let uu____5692 =
              let uu____5693 =
                default_or_map FStar_Pprint.empty p_with_clause with_opt in
              let uu____5694 =
                let uu____5695 =
                  FStar_Pprint.op_Hat_Hat FStar_Pprint.semi break1 in
                separate_map_last uu____5695 p_simpleDef record_fields in
              FStar_Pprint.op_Hat_Hat uu____5693 uu____5694 in
            braces_with_nesting uu____5692
        | FStar_Parser_AST.Op
            ({ FStar_Ident.idText = "~"; FStar_Ident.idRange = uu____5700;_},
             e1::[])
            ->
            let uu____5704 =
              let uu____5705 = str "~" in
              let uu____5706 = p_atomicTerm e1 in
              FStar_Pprint.op_Hat_Hat uu____5705 uu____5706 in
            FStar_Pprint.group uu____5704
        | uu____5707 -> p_X e
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
        let uu____5714 =
          let uu____5715 = p_lidentOrUnderscore lid in
          let uu____5716 =
            let uu____5717 = p_appTerm e1 in
            FStar_Pprint.op_Hat_Slash_Hat FStar_Pprint.colon uu____5717 in
          FStar_Pprint.op_Hat_Slash_Hat uu____5715 uu____5716 in
        FStar_Pprint.group uu____5714
    | FStar_Parser_AST.Refine (b, phi) -> p_refinedBinder b phi
    | uu____5720 -> p_appTerm e
and (p_with_clause : FStar_Parser_AST.term -> FStar_Pprint.document) =
  fun e ->
    let uu____5722 = p_appTerm e in
    let uu____5723 =
      let uu____5724 =
        let uu____5725 = str "with" in
        FStar_Pprint.op_Hat_Hat uu____5725 break1 in
      FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____5724 in
    FStar_Pprint.op_Hat_Hat uu____5722 uu____5723
and (p_refinedBinder :
  FStar_Parser_AST.binder -> FStar_Parser_AST.term -> FStar_Pprint.document)
  =
  fun b ->
    fun phi ->
      match b.FStar_Parser_AST.b with
      | FStar_Parser_AST.Annotated (lid, t) ->
          let uu____5730 =
            let uu____5731 = p_lident lid in
            p_refinement b.FStar_Parser_AST.aqual uu____5731 t phi in
          soft_parens_with_nesting uu____5730
      | FStar_Parser_AST.TAnnotated uu____5732 ->
          failwith "Is this still used ?"
      | FStar_Parser_AST.Variable uu____5737 ->
          let uu____5738 =
            let uu____5739 = FStar_Parser_AST.binder_to_string b in
            FStar_Util.format1
              "Imposible : a refined binder ought to be annotated %s"
              uu____5739 in
          failwith uu____5738
      | FStar_Parser_AST.TVariable uu____5740 ->
          let uu____5741 =
            let uu____5742 = FStar_Parser_AST.binder_to_string b in
            FStar_Util.format1
              "Imposible : a refined binder ought to be annotated %s"
              uu____5742 in
          failwith uu____5741
      | FStar_Parser_AST.NoName uu____5743 ->
          let uu____5744 =
            let uu____5745 = FStar_Parser_AST.binder_to_string b in
            FStar_Util.format1
              "Imposible : a refined binder ought to be annotated %s"
              uu____5745 in
          failwith uu____5744
and (p_simpleDef :
  Prims.bool ->
    (FStar_Ident.lid, FStar_Parser_AST.term) FStar_Pervasives_Native.tuple2
      -> FStar_Pprint.document)
  =
  fun ps ->
    fun uu____5747 ->
      match uu____5747 with
      | (lid, e) ->
          let uu____5754 =
            let uu____5755 = p_qlident lid in
            let uu____5756 =
              let uu____5757 = p_noSeqTerm ps false e in
              FStar_Pprint.op_Hat_Slash_Hat FStar_Pprint.equals uu____5757 in
            FStar_Pprint.op_Hat_Slash_Hat uu____5755 uu____5756 in
          FStar_Pprint.group uu____5754
and (p_appTerm : FStar_Parser_AST.term -> FStar_Pprint.document) =
  fun e ->
    match e.FStar_Parser_AST.tm with
    | FStar_Parser_AST.App uu____5759 when is_general_application e ->
        let uu____5766 = head_and_args e in
        (match uu____5766 with
         | (head1, args) ->
             let uu____5791 =
               let uu____5802 = FStar_ST.op_Bang should_print_fs_typ_app in
               if uu____5802
               then
                 let uu____5838 =
                   FStar_Util.take
                     (fun uu____5862 ->
                        match uu____5862 with
                        | (uu____5867, aq) -> aq = FStar_Parser_AST.FsTypApp)
                     args in
                 match uu____5838 with
                 | (fs_typ_args, args1) ->
                     let uu____5905 =
                       let uu____5906 = p_indexingTerm head1 in
                       let uu____5907 =
                         let uu____5908 =
                           FStar_Pprint.op_Hat_Hat FStar_Pprint.comma break1 in
                         soft_surround_map_or_flow (Prims.parse_int "2")
                           (Prims.parse_int "0") FStar_Pprint.empty
                           FStar_Pprint.langle uu____5908 FStar_Pprint.rangle
                           p_fsTypArg fs_typ_args in
                       FStar_Pprint.op_Hat_Hat uu____5906 uu____5907 in
                     (uu____5905, args1)
               else
                 (let uu____5920 = p_indexingTerm head1 in (uu____5920, args)) in
             (match uu____5791 with
              | (head_doc, args1) ->
                  let uu____5941 =
                    let uu____5942 =
                      FStar_Pprint.op_Hat_Hat head_doc FStar_Pprint.space in
                    soft_surround_map_or_flow (Prims.parse_int "2")
                      (Prims.parse_int "0") head_doc uu____5942 break1
                      FStar_Pprint.empty p_argTerm args1 in
                  FStar_Pprint.group uu____5941))
    | FStar_Parser_AST.Construct (lid, args) when
        (is_general_construction e) &&
          (let uu____5962 = is_dtuple_constructor lid in
           Prims.op_Negation uu____5962)
        ->
        (match args with
         | [] -> p_quident lid
         | arg::[] ->
             let uu____5980 =
               let uu____5981 = p_quident lid in
               let uu____5982 = p_argTerm arg in
               FStar_Pprint.op_Hat_Slash_Hat uu____5981 uu____5982 in
             FStar_Pprint.group uu____5980
         | hd1::tl1 ->
             let uu____5999 =
               let uu____6000 =
                 let uu____6001 =
                   let uu____6002 = p_quident lid in
                   let uu____6003 = p_argTerm hd1 in
                   prefix2 uu____6002 uu____6003 in
                 FStar_Pprint.group uu____6001 in
               let uu____6004 =
                 let uu____6005 =
                   FStar_Pprint.separate_map break1 p_argTerm tl1 in
                 jump2 uu____6005 in
               FStar_Pprint.op_Hat_Hat uu____6000 uu____6004 in
             FStar_Pprint.group uu____5999)
    | uu____6010 -> p_indexingTerm e
and (p_argTerm :
  (FStar_Parser_AST.term, FStar_Parser_AST.imp)
    FStar_Pervasives_Native.tuple2 -> FStar_Pprint.document)
  =
  fun arg_imp ->
    match arg_imp with
    | (u, FStar_Parser_AST.UnivApp) -> p_universe u
    | (e, FStar_Parser_AST.FsTypApp) ->
        (FStar_Errors.log_issue e.FStar_Parser_AST.range
           (FStar_Errors.Warning_UnexpectedFsTypApp,
             "Unexpected FsTypApp, output might not be formatted correctly.");
         (let uu____6019 = p_indexingTerm e in
          FStar_Pprint.surround (Prims.parse_int "2") (Prims.parse_int "1")
            FStar_Pprint.langle uu____6019 FStar_Pprint.rangle))
    | (e, FStar_Parser_AST.Hash) ->
        let uu____6021 = str "#" in
        let uu____6022 = p_indexingTerm e in
        FStar_Pprint.op_Hat_Hat uu____6021 uu____6022
    | (e, FStar_Parser_AST.Nothing) -> p_indexingTerm e
and (p_fsTypArg :
  (FStar_Parser_AST.term, FStar_Parser_AST.imp)
    FStar_Pervasives_Native.tuple2 -> FStar_Pprint.document)
  =
  fun uu____6024 ->
    match uu____6024 with | (e, uu____6030) -> p_indexingTerm e
and (p_indexingTerm_aux :
  (FStar_Parser_AST.term -> FStar_Pprint.document) ->
    FStar_Parser_AST.term -> FStar_Pprint.document)
  =
  fun exit1 ->
    fun e ->
      match e.FStar_Parser_AST.tm with
      | FStar_Parser_AST.Op
          ({ FStar_Ident.idText = ".()"; FStar_Ident.idRange = uu____6035;_},
           e1::e2::[])
          ->
          let uu____6040 =
            let uu____6041 = p_indexingTerm_aux p_atomicTermNotQUident e1 in
            let uu____6042 =
              let uu____6043 =
                let uu____6044 = p_term false false e2 in
                soft_parens_with_nesting uu____6044 in
              FStar_Pprint.op_Hat_Hat FStar_Pprint.dot uu____6043 in
            FStar_Pprint.op_Hat_Hat uu____6041 uu____6042 in
          FStar_Pprint.group uu____6040
      | FStar_Parser_AST.Op
          ({ FStar_Ident.idText = ".[]"; FStar_Ident.idRange = uu____6045;_},
           e1::e2::[])
          ->
          let uu____6050 =
            let uu____6051 = p_indexingTerm_aux p_atomicTermNotQUident e1 in
            let uu____6052 =
              let uu____6053 =
                let uu____6054 = p_term false false e2 in
                soft_brackets_with_nesting uu____6054 in
              FStar_Pprint.op_Hat_Hat FStar_Pprint.dot uu____6053 in
            FStar_Pprint.op_Hat_Hat uu____6051 uu____6052 in
          FStar_Pprint.group uu____6050
      | uu____6055 -> exit1 e
and (p_indexingTerm : FStar_Parser_AST.term -> FStar_Pprint.document) =
  fun e -> p_indexingTerm_aux p_atomicTerm e
and (p_atomicTerm : FStar_Parser_AST.term -> FStar_Pprint.document) =
  fun e ->
    match e.FStar_Parser_AST.tm with
    | FStar_Parser_AST.LetOpen (lid, e1) ->
        let uu____6060 = p_quident lid in
        let uu____6061 =
          let uu____6062 =
            let uu____6063 = p_term false false e1 in
            soft_parens_with_nesting uu____6063 in
          FStar_Pprint.op_Hat_Hat FStar_Pprint.dot uu____6062 in
        FStar_Pprint.op_Hat_Hat uu____6060 uu____6061
    | FStar_Parser_AST.Name lid -> p_quident lid
    | FStar_Parser_AST.Op (op, e1::[]) when is_general_prefix_op op ->
        let uu____6069 = str (FStar_Ident.text_of_id op) in
        let uu____6070 = p_atomicTerm e1 in
        FStar_Pprint.op_Hat_Hat uu____6069 uu____6070
    | uu____6071 -> p_atomicTermNotQUident e
and (p_atomicTermNotQUident : FStar_Parser_AST.term -> FStar_Pprint.document)
  =
  fun e ->
    match e.FStar_Parser_AST.tm with
    | FStar_Parser_AST.Wild -> FStar_Pprint.underscore
    | FStar_Parser_AST.Var lid when
        FStar_Ident.lid_equals lid FStar_Parser_Const.assert_lid ->
        str "assert"
    | FStar_Parser_AST.Tvar tv -> p_tvar tv
    | FStar_Parser_AST.Const c ->
        (match c with
         | FStar_Const.Const_char x when x = 10 -> str "0x0Az"
         | uu____6078 -> p_constant c)
    | FStar_Parser_AST.Name lid when
        FStar_Ident.lid_equals lid FStar_Parser_Const.true_lid -> str "True"
    | FStar_Parser_AST.Name lid when
        FStar_Ident.lid_equals lid FStar_Parser_Const.false_lid ->
        str "False"
    | FStar_Parser_AST.Op (op, e1::[]) when is_general_prefix_op op ->
        let uu____6085 = str (FStar_Ident.text_of_id op) in
        let uu____6086 = p_atomicTermNotQUident e1 in
        FStar_Pprint.op_Hat_Hat uu____6085 uu____6086
    | FStar_Parser_AST.Op (op, []) ->
        let uu____6090 =
          let uu____6091 =
            let uu____6092 = str (FStar_Ident.text_of_id op) in
            let uu____6093 =
              FStar_Pprint.op_Hat_Hat FStar_Pprint.space FStar_Pprint.rparen in
            FStar_Pprint.op_Hat_Hat uu____6092 uu____6093 in
          FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____6091 in
        FStar_Pprint.op_Hat_Hat FStar_Pprint.lparen uu____6090
    | FStar_Parser_AST.Construct (lid, args) when is_dtuple_constructor lid
        ->
        let uu____6108 =
          FStar_Pprint.op_Hat_Hat FStar_Pprint.lparen FStar_Pprint.bar in
        let uu____6109 =
          let uu____6110 = FStar_Pprint.op_Hat_Hat FStar_Pprint.comma break1 in
          let uu____6111 = FStar_List.map FStar_Pervasives_Native.fst args in
          FStar_Pprint.separate_map uu____6110 p_tmEq uu____6111 in
        let uu____6118 =
          FStar_Pprint.op_Hat_Hat FStar_Pprint.bar FStar_Pprint.rparen in
        FStar_Pprint.surround (Prims.parse_int "2") (Prims.parse_int "1")
          uu____6108 uu____6109 uu____6118
    | FStar_Parser_AST.Project (e1, lid) ->
        let uu____6121 =
          let uu____6122 = p_atomicTermNotQUident e1 in
          let uu____6123 =
            let uu____6124 = p_qlident lid in
            FStar_Pprint.op_Hat_Hat FStar_Pprint.dot uu____6124 in
          FStar_Pprint.prefix (Prims.parse_int "2") (Prims.parse_int "0")
            uu____6122 uu____6123 in
        FStar_Pprint.group uu____6121
    | uu____6125 -> p_projectionLHS e
and (p_projectionLHS : FStar_Parser_AST.term -> FStar_Pprint.document) =
  fun e ->
    match e.FStar_Parser_AST.tm with
    | FStar_Parser_AST.Var lid -> p_qlident lid
    | FStar_Parser_AST.Projector (constr_lid, field_lid) ->
        let uu____6130 = p_quident constr_lid in
        let uu____6131 =
          let uu____6132 =
            let uu____6133 = p_lident field_lid in
            FStar_Pprint.op_Hat_Hat FStar_Pprint.dot uu____6133 in
          FStar_Pprint.op_Hat_Hat FStar_Pprint.qmark uu____6132 in
        FStar_Pprint.op_Hat_Hat uu____6130 uu____6131
    | FStar_Parser_AST.Discrim constr_lid ->
        let uu____6135 = p_quident constr_lid in
        FStar_Pprint.op_Hat_Hat uu____6135 FStar_Pprint.qmark
    | FStar_Parser_AST.Paren e1 ->
        let uu____6137 = p_term false false e1 in
        soft_parens_with_nesting uu____6137
    | uu____6138 when is_array e ->
        let es = extract_from_list e in
        let uu____6142 =
          FStar_Pprint.op_Hat_Hat FStar_Pprint.lbracket FStar_Pprint.bar in
        let uu____6143 =
          let uu____6144 = FStar_Pprint.op_Hat_Hat FStar_Pprint.semi break1 in
          separate_map_or_flow_last uu____6144
            (fun ps -> p_noSeqTerm ps false) es in
        let uu____6147 =
          FStar_Pprint.op_Hat_Hat FStar_Pprint.bar FStar_Pprint.rbracket in
        FStar_Pprint.surround (Prims.parse_int "2") (Prims.parse_int "0")
          uu____6142 uu____6143 uu____6147
    | uu____6148 when is_list e ->
        let uu____6149 =
          let uu____6150 = FStar_Pprint.op_Hat_Hat FStar_Pprint.semi break1 in
          let uu____6151 = extract_from_list e in
          separate_map_or_flow_last uu____6150
            (fun ps -> p_noSeqTerm ps false) uu____6151 in
        FStar_Pprint.surround (Prims.parse_int "2") (Prims.parse_int "0")
          FStar_Pprint.lbracket uu____6149 FStar_Pprint.rbracket
    | uu____6156 when is_lex_list e ->
        let uu____6157 =
          FStar_Pprint.op_Hat_Hat FStar_Pprint.percent FStar_Pprint.lbracket in
        let uu____6158 =
          let uu____6159 = FStar_Pprint.op_Hat_Hat FStar_Pprint.semi break1 in
          let uu____6160 = extract_from_list e in
          separate_map_or_flow_last uu____6159
            (fun ps -> p_noSeqTerm ps false) uu____6160 in
        FStar_Pprint.surround (Prims.parse_int "2") (Prims.parse_int "1")
          uu____6157 uu____6158 FStar_Pprint.rbracket
    | uu____6165 when is_ref_set e ->
        let es = extract_from_ref_set e in
        let uu____6169 =
          FStar_Pprint.op_Hat_Hat FStar_Pprint.bang FStar_Pprint.lbrace in
        let uu____6170 =
          let uu____6171 = FStar_Pprint.op_Hat_Hat FStar_Pprint.comma break1 in
          separate_map_or_flow uu____6171 p_appTerm es in
        FStar_Pprint.surround (Prims.parse_int "2") (Prims.parse_int "0")
          uu____6169 uu____6170 FStar_Pprint.rbrace
    | FStar_Parser_AST.Labeled (e1, s, b) ->
        let uu____6175 = str (Prims.strcat "(*" (Prims.strcat s "*)")) in
        let uu____6176 = p_term false false e1 in
        FStar_Pprint.op_Hat_Slash_Hat uu____6175 uu____6176
    | FStar_Parser_AST.Op (op, args) when
        let uu____6183 = handleable_op op args in
        Prims.op_Negation uu____6183 ->
        let uu____6184 =
          let uu____6185 =
            let uu____6186 =
              let uu____6187 =
                let uu____6188 =
                  FStar_Util.string_of_int (FStar_List.length args) in
                Prims.strcat uu____6188
                  " arguments couldn't be handled by the pretty printer" in
              Prims.strcat " with " uu____6187 in
            Prims.strcat (FStar_Ident.text_of_id op) uu____6186 in
          Prims.strcat "Operation " uu____6185 in
        failwith uu____6184
    | FStar_Parser_AST.Uvar uu____6189 ->
        failwith "Unexpected universe variable out of universe context"
    | FStar_Parser_AST.Wild ->
        let uu____6190 = p_term false false e in
        soft_parens_with_nesting uu____6190
    | FStar_Parser_AST.Const uu____6191 ->
        let uu____6192 = p_term false false e in
        soft_parens_with_nesting uu____6192
    | FStar_Parser_AST.Op uu____6193 ->
        let uu____6200 = p_term false false e in
        soft_parens_with_nesting uu____6200
    | FStar_Parser_AST.Tvar uu____6201 ->
        let uu____6202 = p_term false false e in
        soft_parens_with_nesting uu____6202
    | FStar_Parser_AST.Var uu____6203 ->
        let uu____6204 = p_term false false e in
        soft_parens_with_nesting uu____6204
    | FStar_Parser_AST.Name uu____6205 ->
        let uu____6206 = p_term false false e in
        soft_parens_with_nesting uu____6206
    | FStar_Parser_AST.Construct uu____6207 ->
        let uu____6218 = p_term false false e in
        soft_parens_with_nesting uu____6218
    | FStar_Parser_AST.Abs uu____6219 ->
        let uu____6226 = p_term false false e in
        soft_parens_with_nesting uu____6226
    | FStar_Parser_AST.App uu____6227 ->
        let uu____6234 = p_term false false e in
        soft_parens_with_nesting uu____6234
    | FStar_Parser_AST.Let uu____6235 ->
        let uu____6256 = p_term false false e in
        soft_parens_with_nesting uu____6256
    | FStar_Parser_AST.LetOpen uu____6257 ->
        let uu____6262 = p_term false false e in
        soft_parens_with_nesting uu____6262
    | FStar_Parser_AST.Seq uu____6263 ->
        let uu____6268 = p_term false false e in
        soft_parens_with_nesting uu____6268
    | FStar_Parser_AST.Bind uu____6269 ->
        let uu____6276 = p_term false false e in
        soft_parens_with_nesting uu____6276
    | FStar_Parser_AST.If uu____6277 ->
        let uu____6284 = p_term false false e in
        soft_parens_with_nesting uu____6284
    | FStar_Parser_AST.Match uu____6285 ->
        let uu____6300 = p_term false false e in
        soft_parens_with_nesting uu____6300
    | FStar_Parser_AST.TryWith uu____6301 ->
        let uu____6316 = p_term false false e in
        soft_parens_with_nesting uu____6316
    | FStar_Parser_AST.Ascribed uu____6317 ->
        let uu____6326 = p_term false false e in
        soft_parens_with_nesting uu____6326
    | FStar_Parser_AST.Record uu____6327 ->
        let uu____6340 = p_term false false e in
        soft_parens_with_nesting uu____6340
    | FStar_Parser_AST.Project uu____6341 ->
        let uu____6346 = p_term false false e in
        soft_parens_with_nesting uu____6346
    | FStar_Parser_AST.Product uu____6347 ->
        let uu____6354 = p_term false false e in
        soft_parens_with_nesting uu____6354
    | FStar_Parser_AST.Sum uu____6355 ->
        let uu____6362 = p_term false false e in
        soft_parens_with_nesting uu____6362
    | FStar_Parser_AST.QForall uu____6363 ->
        let uu____6376 = p_term false false e in
        soft_parens_with_nesting uu____6376
    | FStar_Parser_AST.QExists uu____6377 ->
        let uu____6390 = p_term false false e in
        soft_parens_with_nesting uu____6390
    | FStar_Parser_AST.Refine uu____6391 ->
        let uu____6396 = p_term false false e in
        soft_parens_with_nesting uu____6396
    | FStar_Parser_AST.NamedTyp uu____6397 ->
        let uu____6402 = p_term false false e in
        soft_parens_with_nesting uu____6402
    | FStar_Parser_AST.Requires uu____6403 ->
        let uu____6410 = p_term false false e in
        soft_parens_with_nesting uu____6410
    | FStar_Parser_AST.Ensures uu____6411 ->
        let uu____6418 = p_term false false e in
        soft_parens_with_nesting uu____6418
    | FStar_Parser_AST.Attributes uu____6419 ->
        let uu____6422 = p_term false false e in
        soft_parens_with_nesting uu____6422
    | FStar_Parser_AST.Quote uu____6423 ->
        let uu____6428 = p_term false false e in
        soft_parens_with_nesting uu____6428
    | FStar_Parser_AST.VQuote uu____6429 ->
        let uu____6430 = p_term false false e in
        soft_parens_with_nesting uu____6430
    | FStar_Parser_AST.Antiquote uu____6431 ->
        let uu____6436 = p_term false false e in
        soft_parens_with_nesting uu____6436
and (p_constant : FStar_Const.sconst -> FStar_Pprint.document) =
  fun uu___68_6437 ->
    match uu___68_6437 with
    | FStar_Const.Const_effect -> str "Effect"
    | FStar_Const.Const_unit -> str "()"
    | FStar_Const.Const_bool b -> FStar_Pprint.doc_of_bool b
    | FStar_Const.Const_float x -> str (FStar_Util.string_of_float x)
    | FStar_Const.Const_char x ->
        let uu____6441 = FStar_Pprint.doc_of_char x in
        FStar_Pprint.squotes uu____6441
    | FStar_Const.Const_string (s, uu____6443) ->
        let uu____6444 = str s in FStar_Pprint.dquotes uu____6444
    | FStar_Const.Const_bytearray (bytes, uu____6446) ->
        let uu____6451 =
          let uu____6452 = str (FStar_Util.string_of_bytes bytes) in
          FStar_Pprint.dquotes uu____6452 in
        let uu____6453 = str "B" in
        FStar_Pprint.op_Hat_Hat uu____6451 uu____6453
    | FStar_Const.Const_int (repr, sign_width_opt) ->
        let signedness uu___66_6471 =
          match uu___66_6471 with
          | FStar_Const.Unsigned -> str "u"
          | FStar_Const.Signed -> FStar_Pprint.empty in
        let width uu___67_6475 =
          match uu___67_6475 with
          | FStar_Const.Int8 -> str "y"
          | FStar_Const.Int16 -> str "s"
          | FStar_Const.Int32 -> str "l"
          | FStar_Const.Int64 -> str "L" in
        let ending =
          default_or_map FStar_Pprint.empty
            (fun uu____6486 ->
               match uu____6486 with
               | (s, w) ->
                   let uu____6493 = signedness s in
                   let uu____6494 = width w in
                   FStar_Pprint.op_Hat_Hat uu____6493 uu____6494)
            sign_width_opt in
        let uu____6495 = str repr in
        FStar_Pprint.op_Hat_Hat uu____6495 ending
    | FStar_Const.Const_range_of -> str "range_of"
    | FStar_Const.Const_set_range_of -> str "set_range_of"
    | FStar_Const.Const_range r ->
        let uu____6497 = FStar_Range.string_of_range r in str uu____6497
    | FStar_Const.Const_reify -> str "reify"
    | FStar_Const.Const_reflect lid ->
        let uu____6499 = p_quident lid in
        let uu____6500 =
          let uu____6501 =
            let uu____6502 = str "reflect" in
            FStar_Pprint.op_Hat_Hat FStar_Pprint.dot uu____6502 in
          FStar_Pprint.op_Hat_Hat FStar_Pprint.qmark uu____6501 in
        FStar_Pprint.op_Hat_Hat uu____6499 uu____6500
and (p_universe : FStar_Parser_AST.term -> FStar_Pprint.document) =
  fun u ->
    let uu____6504 = str "u#" in
    let uu____6505 = p_atomicUniverse u in
    FStar_Pprint.op_Hat_Hat uu____6504 uu____6505
and (p_universeFrom : FStar_Parser_AST.term -> FStar_Pprint.document) =
  fun u ->
    match u.FStar_Parser_AST.tm with
    | FStar_Parser_AST.Op
        ({ FStar_Ident.idText = "+"; FStar_Ident.idRange = uu____6507;_},
         u1::u2::[])
        ->
        let uu____6512 =
          let uu____6513 = p_universeFrom u1 in
          let uu____6514 =
            let uu____6515 = p_universeFrom u2 in
            FStar_Pprint.op_Hat_Slash_Hat FStar_Pprint.plus uu____6515 in
          FStar_Pprint.op_Hat_Slash_Hat uu____6513 uu____6514 in
        FStar_Pprint.group uu____6512
    | FStar_Parser_AST.App uu____6516 ->
        let uu____6523 = head_and_args u in
        (match uu____6523 with
         | (head1, args) ->
             (match head1.FStar_Parser_AST.tm with
              | FStar_Parser_AST.Var maybe_max_lid when
                  FStar_Ident.lid_equals maybe_max_lid
                    FStar_Parser_Const.max_lid
                  ->
                  let uu____6549 =
                    let uu____6550 = p_qlident FStar_Parser_Const.max_lid in
                    let uu____6551 =
                      FStar_Pprint.separate_map FStar_Pprint.space
                        (fun uu____6559 ->
                           match uu____6559 with
                           | (u1, uu____6565) -> p_atomicUniverse u1) args in
                    op_Hat_Slash_Plus_Hat uu____6550 uu____6551 in
                  FStar_Pprint.group uu____6549
              | uu____6566 ->
                  let uu____6567 =
                    let uu____6568 = FStar_Parser_AST.term_to_string u in
                    FStar_Util.format1 "Invalid term in universe context %s"
                      uu____6568 in
                  failwith uu____6567))
    | uu____6569 -> p_atomicUniverse u
and (p_atomicUniverse : FStar_Parser_AST.term -> FStar_Pprint.document) =
  fun u ->
    match u.FStar_Parser_AST.tm with
    | FStar_Parser_AST.Wild -> FStar_Pprint.underscore
    | FStar_Parser_AST.Const (FStar_Const.Const_int (r, sw)) ->
        p_constant (FStar_Const.Const_int (r, sw))
    | FStar_Parser_AST.Uvar id1 -> str (FStar_Ident.text_of_id id1)
    | FStar_Parser_AST.Paren u1 ->
        let uu____6593 = p_universeFrom u1 in
        soft_parens_with_nesting uu____6593
    | FStar_Parser_AST.Op
        ({ FStar_Ident.idText = "+"; FStar_Ident.idRange = uu____6594;_},
         uu____6595::uu____6596::[])
        ->
        let uu____6599 = p_universeFrom u in
        soft_parens_with_nesting uu____6599
    | FStar_Parser_AST.App uu____6600 ->
        let uu____6607 = p_universeFrom u in
        soft_parens_with_nesting uu____6607
    | uu____6608 ->
        let uu____6609 =
          let uu____6610 = FStar_Parser_AST.term_to_string u in
          FStar_Util.format1 "Invalid term in universe context %s" uu____6610 in
        failwith uu____6609
let (term_to_document : FStar_Parser_AST.term -> FStar_Pprint.document) =
  fun e -> p_term false false e
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
       | FStar_Parser_AST.Module (uu____6656, decls) ->
           let uu____6662 =
             FStar_All.pipe_right decls (FStar_List.map decl_to_document) in
           FStar_All.pipe_right uu____6662
             (FStar_Pprint.separate FStar_Pprint.hardline)
       | FStar_Parser_AST.Interface (uu____6671, decls, uu____6673) ->
           let uu____6678 =
             FStar_All.pipe_right decls (FStar_List.map decl_to_document) in
           FStar_All.pipe_right uu____6678
             (FStar_Pprint.separate FStar_Pprint.hardline) in
     FStar_ST.op_Colon_Equals should_print_fs_typ_app false; res)
let (comments_to_document :
  (Prims.string, FStar_Range.range) FStar_Pervasives_Native.tuple2 Prims.list
    -> FStar_Pprint.document)
  =
  fun comments ->
    FStar_Pprint.separate_map FStar_Pprint.hardline
      (fun uu____6735 ->
         match uu____6735 with | (comment, range) -> str comment) comments
let (modul_with_comments_to_document :
  FStar_Parser_AST.modul ->
    (Prims.string, FStar_Range.range) FStar_Pervasives_Native.tuple2
      Prims.list ->
      (FStar_Pprint.document,
        (Prims.string, FStar_Range.range) FStar_Pervasives_Native.tuple2
          Prims.list)
        FStar_Pervasives_Native.tuple2)
  =
  fun m ->
    fun comments ->
      let decls =
        match m with
        | FStar_Parser_AST.Module (uu____6775, decls) -> decls
        | FStar_Parser_AST.Interface (uu____6781, decls, uu____6783) -> decls in
      FStar_ST.op_Colon_Equals should_print_fs_typ_app false;
      (match decls with
       | [] -> (FStar_Pprint.empty, comments)
       | d::ds ->
           let uu____6834 =
             match ds with
             | {
                 FStar_Parser_AST.d = FStar_Parser_AST.Pragma
                   (FStar_Parser_AST.LightOff);
                 FStar_Parser_AST.drange = uu____6847;
                 FStar_Parser_AST.doc = uu____6848;
                 FStar_Parser_AST.quals = uu____6849;
                 FStar_Parser_AST.attrs = uu____6850;_}::uu____6851 ->
                 let d0 = FStar_List.hd ds in
                 let uu____6857 =
                   let uu____6860 =
                     let uu____6863 = FStar_List.tl ds in d :: uu____6863 in
                   d0 :: uu____6860 in
                 (uu____6857, (d0.FStar_Parser_AST.drange))
             | uu____6868 -> ((d :: ds), (d.FStar_Parser_AST.drange)) in
           (match uu____6834 with
            | (decls1, first_range) ->
                let extract_decl_range d1 = d1.FStar_Parser_AST.drange in
                (FStar_ST.op_Colon_Equals comment_stack comments;
                 (let initial_comment =
                    let uu____6932 = FStar_Range.start_of_range first_range in
                    place_comments_until_pos (Prims.parse_int "0")
                      (Prims.parse_int "1") uu____6932 FStar_Pprint.empty in
                  let doc1 =
                    separate_map_with_comments FStar_Pprint.empty
                      FStar_Pprint.empty decl_to_document decls1
                      extract_decl_range in
                  let comments1 = FStar_ST.op_Bang comment_stack in
                  FStar_ST.op_Colon_Equals comment_stack [];
                  FStar_ST.op_Colon_Equals should_print_fs_typ_app false;
                  (let uu____7046 =
                     FStar_Pprint.op_Hat_Hat initial_comment doc1 in
                   (uu____7046, comments1))))))