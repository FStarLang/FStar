open Prims
let should_print_fs_typ_app: Prims.bool FStar_ST.ref =
  FStar_Util.mk_ref false
let with_fs_typ_app b printer t =
  let b0 = FStar_ST.read should_print_fs_typ_app in
  FStar_ST.write should_print_fs_typ_app b;
  (let res = printer t in FStar_ST.write should_print_fs_typ_app b0; res)
let should_unparen: Prims.bool FStar_ST.ref = FStar_Util.mk_ref true
let rec unparen: FStar_Parser_AST.term -> FStar_Parser_AST.term =
  fun t  ->
    let uu____44 =
      let uu____45 = FStar_ST.read should_unparen in
      Prims.op_Negation uu____45 in
    if uu____44
    then t
    else
      (match t.FStar_Parser_AST.tm with
       | FStar_Parser_AST.Paren t1 -> unparen t1
       | uu____50 -> t)
let str: Prims.string -> FStar_Pprint.document =
  fun s  -> FStar_Pprint.doc_of_string s
let default_or_map n1 f x = match x with | None  -> n1 | Some x' -> f x'
let prefix2:
  FStar_Pprint.document -> FStar_Pprint.document -> FStar_Pprint.document =
  fun prefix_  ->
    fun body  ->
      FStar_Pprint.prefix (Prims.parse_int "2") (Prims.parse_int "1") prefix_
        body
let op_Hat_Slash_Plus_Hat:
  FStar_Pprint.document -> FStar_Pprint.document -> FStar_Pprint.document =
  fun prefix_  -> fun body  -> prefix2 prefix_ body
let jump2: FStar_Pprint.document -> FStar_Pprint.document =
  fun body  ->
    FStar_Pprint.jump (Prims.parse_int "2") (Prims.parse_int "1") body
let infix2:
  FStar_Pprint.document ->
    FStar_Pprint.document -> FStar_Pprint.document -> FStar_Pprint.document
  = FStar_Pprint.infix (Prims.parse_int "2") (Prims.parse_int "1")
let infix0:
  FStar_Pprint.document ->
    FStar_Pprint.document -> FStar_Pprint.document -> FStar_Pprint.document
  = FStar_Pprint.infix (Prims.parse_int "0") (Prims.parse_int "1")
let break1: FStar_Pprint.document = FStar_Pprint.break_ (Prims.parse_int "1")
let separate_break_map sep f l =
  let uu____132 =
    let uu____133 =
      let uu____134 = FStar_Pprint.op_Hat_Hat sep break1 in
      FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____134 in
    FStar_Pprint.separate_map uu____133 f l in
  FStar_Pprint.group uu____132
let precede_break_separate_map prec sep f l =
  let uu____164 =
    let uu____165 = FStar_Pprint.op_Hat_Hat prec FStar_Pprint.space in
    let uu____166 =
      let uu____167 = FStar_List.hd l in FStar_All.pipe_right uu____167 f in
    FStar_Pprint.precede uu____165 uu____166 in
  let uu____168 =
    let uu____169 = FStar_List.tl l in
    FStar_Pprint.concat_map
      (fun x  ->
         let uu____172 =
           let uu____173 =
             let uu____174 = f x in
             FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____174 in
           FStar_Pprint.op_Hat_Hat sep uu____173 in
         FStar_Pprint.op_Hat_Hat break1 uu____172) uu____169 in
  FStar_Pprint.op_Hat_Hat uu____164 uu____168
let concat_break_map f l =
  let uu____194 =
    FStar_Pprint.concat_map
      (fun x  ->
         let uu____196 = f x in FStar_Pprint.op_Hat_Hat uu____196 break1) l in
  FStar_Pprint.group uu____194
let parens_with_nesting: FStar_Pprint.document -> FStar_Pprint.document =
  fun contents  ->
    FStar_Pprint.surround (Prims.parse_int "2") (Prims.parse_int "0")
      FStar_Pprint.lparen contents FStar_Pprint.rparen
let soft_parens_with_nesting: FStar_Pprint.document -> FStar_Pprint.document
  =
  fun contents  ->
    FStar_Pprint.soft_surround (Prims.parse_int "2") (Prims.parse_int "0")
      FStar_Pprint.lparen contents FStar_Pprint.rparen
let braces_with_nesting: FStar_Pprint.document -> FStar_Pprint.document =
  fun contents  ->
    FStar_Pprint.surround (Prims.parse_int "2") (Prims.parse_int "1")
      FStar_Pprint.lbrace contents FStar_Pprint.rbrace
let soft_braces_with_nesting: FStar_Pprint.document -> FStar_Pprint.document
  =
  fun contents  ->
    FStar_Pprint.soft_surround (Prims.parse_int "2") (Prims.parse_int "1")
      FStar_Pprint.lbrace contents FStar_Pprint.rbrace
let brackets_with_nesting: FStar_Pprint.document -> FStar_Pprint.document =
  fun contents  ->
    FStar_Pprint.surround (Prims.parse_int "2") (Prims.parse_int "1")
      FStar_Pprint.lbracket contents FStar_Pprint.rbracket
let soft_brackets_with_nesting:
  FStar_Pprint.document -> FStar_Pprint.document =
  fun contents  ->
    FStar_Pprint.soft_surround (Prims.parse_int "2") (Prims.parse_int "1")
      FStar_Pprint.lbracket contents FStar_Pprint.rbracket
let soft_begin_end_with_nesting:
  FStar_Pprint.document -> FStar_Pprint.document =
  fun contents  ->
    let uu____218 = str "begin" in
    let uu____219 = str "end" in
    FStar_Pprint.soft_surround (Prims.parse_int "2") (Prims.parse_int "1")
      uu____218 contents uu____219
let separate_map_or_flow sep f l =
  if (FStar_List.length l) < (Prims.parse_int "10")
  then FStar_Pprint.separate_map sep f l
  else FStar_Pprint.flow_map sep f l
let soft_surround_separate_map n1 b void_ opening sep closing f xs =
  if xs = []
  then void_
  else
    (let uu____299 = FStar_Pprint.separate_map sep f xs in
     FStar_Pprint.soft_surround n1 b opening uu____299 closing)
let doc_of_fsdoc:
  (Prims.string* (Prims.string* Prims.string) Prims.list) ->
    FStar_Pprint.document
  =
  fun uu____307  ->
    match uu____307 with
    | (comment,keywords1) ->
        let uu____321 =
          let uu____322 =
            let uu____324 = str comment in
            let uu____325 =
              let uu____327 =
                let uu____329 =
                  FStar_Pprint.separate_map FStar_Pprint.comma
                    (fun uu____332  ->
                       match uu____332 with
                       | (k,v1) ->
                           let uu____337 =
                             let uu____339 = str k in
                             let uu____340 =
                               let uu____342 =
                                 let uu____344 = str v1 in [uu____344] in
                               FStar_Pprint.rarrow :: uu____342 in
                             uu____339 :: uu____340 in
                           FStar_Pprint.concat uu____337) keywords1 in
                [uu____329] in
              FStar_Pprint.space :: uu____327 in
            uu____324 :: uu____325 in
          FStar_Pprint.concat uu____322 in
        FStar_Pprint.group uu____321
let is_unit: FStar_Parser_AST.term -> Prims.bool =
  fun e  ->
    let uu____348 =
      let uu____349 = unparen e in uu____349.FStar_Parser_AST.tm in
    match uu____348 with
    | FStar_Parser_AST.Const (FStar_Const.Const_unit ) -> true
    | uu____350 -> false
let matches_var: FStar_Parser_AST.term -> FStar_Ident.ident -> Prims.bool =
  fun t  ->
    fun x  ->
      let uu____357 =
        let uu____358 = unparen t in uu____358.FStar_Parser_AST.tm in
      match uu____357 with
      | FStar_Parser_AST.Var y ->
          x.FStar_Ident.idText = (FStar_Ident.text_of_lid y)
      | uu____360 -> false
let is_tuple_constructor: FStar_Ident.lident -> Prims.bool =
  FStar_Syntax_Util.is_tuple_data_lid'
let is_dtuple_constructor: FStar_Ident.lident -> Prims.bool =
  FStar_Syntax_Util.is_dtuple_data_lid'
let is_list_structure:
  FStar_Ident.lident ->
    FStar_Ident.lident -> FStar_Parser_AST.term -> Prims.bool
  =
  fun cons_lid1  ->
    fun nil_lid1  ->
      let rec aux e =
        let uu____377 =
          let uu____378 = unparen e in uu____378.FStar_Parser_AST.tm in
        match uu____377 with
        | FStar_Parser_AST.Construct (lid,[]) ->
            FStar_Ident.lid_equals lid nil_lid1
        | FStar_Parser_AST.Construct (lid,uu____386::(e2,uu____388)::[]) ->
            (FStar_Ident.lid_equals lid cons_lid1) && (aux e2)
        | uu____400 -> false in
      aux
let is_list: FStar_Parser_AST.term -> Prims.bool =
  is_list_structure FStar_Syntax_Const.cons_lid FStar_Syntax_Const.nil_lid
let is_lex_list: FStar_Parser_AST.term -> Prims.bool =
  is_list_structure FStar_Syntax_Const.lexcons_lid
    FStar_Syntax_Const.lextop_lid
let rec extract_from_list:
  FStar_Parser_AST.term -> FStar_Parser_AST.term Prims.list =
  fun e  ->
    let uu____409 =
      let uu____410 = unparen e in uu____410.FStar_Parser_AST.tm in
    match uu____409 with
    | FStar_Parser_AST.Construct (uu____412,[]) -> []
    | FStar_Parser_AST.Construct
        (uu____418,(e1,FStar_Parser_AST.Nothing )::(e2,FStar_Parser_AST.Nothing
                                                    )::[])
        -> let uu____430 = extract_from_list e2 in e1 :: uu____430
    | uu____432 ->
        let uu____433 =
          let uu____434 = FStar_Parser_AST.term_to_string e in
          FStar_Util.format1 "Not a list %s" uu____434 in
        failwith uu____433
let is_array: FStar_Parser_AST.term -> Prims.bool =
  fun e  ->
    let uu____439 =
      let uu____440 = unparen e in uu____440.FStar_Parser_AST.tm in
    match uu____439 with
    | FStar_Parser_AST.App
        ({ FStar_Parser_AST.tm = FStar_Parser_AST.Var lid;
           FStar_Parser_AST.range = uu____442;
           FStar_Parser_AST.level = uu____443;_},l,FStar_Parser_AST.Nothing
         )
        ->
        (FStar_Ident.lid_equals lid FStar_Syntax_Const.array_mk_array_lid) &&
          (is_list l)
    | uu____445 -> false
let rec is_ref_set: FStar_Parser_AST.term -> Prims.bool =
  fun e  ->
    let uu____449 =
      let uu____450 = unparen e in uu____450.FStar_Parser_AST.tm in
    match uu____449 with
    | FStar_Parser_AST.Var maybe_empty_lid ->
        FStar_Ident.lid_equals maybe_empty_lid FStar_Syntax_Const.tset_empty
    | FStar_Parser_AST.App
        ({ FStar_Parser_AST.tm = FStar_Parser_AST.Var maybe_singleton_lid;
           FStar_Parser_AST.range = uu____453;
           FStar_Parser_AST.level = uu____454;_},{
                                                   FStar_Parser_AST.tm =
                                                     FStar_Parser_AST.App
                                                     ({
                                                        FStar_Parser_AST.tm =
                                                          FStar_Parser_AST.Var
                                                          maybe_ref_lid;
                                                        FStar_Parser_AST.range
                                                          = uu____456;
                                                        FStar_Parser_AST.level
                                                          = uu____457;_},e1,FStar_Parser_AST.Nothing
                                                      );
                                                   FStar_Parser_AST.range =
                                                     uu____459;
                                                   FStar_Parser_AST.level =
                                                     uu____460;_},FStar_Parser_AST.Nothing
         )
        ->
        (FStar_Ident.lid_equals maybe_singleton_lid
           FStar_Syntax_Const.tset_singleton)
          &&
          (FStar_Ident.lid_equals maybe_ref_lid FStar_Syntax_Const.heap_ref)
    | FStar_Parser_AST.App
        ({
           FStar_Parser_AST.tm = FStar_Parser_AST.App
             ({ FStar_Parser_AST.tm = FStar_Parser_AST.Var maybe_union_lid;
                FStar_Parser_AST.range = uu____462;
                FStar_Parser_AST.level = uu____463;_},e1,FStar_Parser_AST.Nothing
              );
           FStar_Parser_AST.range = uu____465;
           FStar_Parser_AST.level = uu____466;_},e2,FStar_Parser_AST.Nothing
         )
        ->
        ((FStar_Ident.lid_equals maybe_union_lid
            FStar_Syntax_Const.tset_union)
           && (is_ref_set e1))
          && (is_ref_set e2)
    | uu____468 -> false
let rec extract_from_ref_set:
  FStar_Parser_AST.term -> FStar_Parser_AST.term Prims.list =
  fun e  ->
    let uu____473 =
      let uu____474 = unparen e in uu____474.FStar_Parser_AST.tm in
    match uu____473 with
    | FStar_Parser_AST.Var uu____476 -> []
    | FStar_Parser_AST.App
        ({ FStar_Parser_AST.tm = FStar_Parser_AST.Var uu____477;
           FStar_Parser_AST.range = uu____478;
           FStar_Parser_AST.level = uu____479;_},{
                                                   FStar_Parser_AST.tm =
                                                     FStar_Parser_AST.App
                                                     ({
                                                        FStar_Parser_AST.tm =
                                                          FStar_Parser_AST.Var
                                                          uu____480;
                                                        FStar_Parser_AST.range
                                                          = uu____481;
                                                        FStar_Parser_AST.level
                                                          = uu____482;_},e1,FStar_Parser_AST.Nothing
                                                      );
                                                   FStar_Parser_AST.range =
                                                     uu____484;
                                                   FStar_Parser_AST.level =
                                                     uu____485;_},FStar_Parser_AST.Nothing
         )
        -> [e1]
    | FStar_Parser_AST.App
        ({
           FStar_Parser_AST.tm = FStar_Parser_AST.App
             ({ FStar_Parser_AST.tm = FStar_Parser_AST.Var uu____486;
                FStar_Parser_AST.range = uu____487;
                FStar_Parser_AST.level = uu____488;_},e1,FStar_Parser_AST.Nothing
              );
           FStar_Parser_AST.range = uu____490;
           FStar_Parser_AST.level = uu____491;_},e2,FStar_Parser_AST.Nothing
         )
        ->
        let uu____493 = extract_from_ref_set e1 in
        let uu____495 = extract_from_ref_set e2 in
        FStar_List.append uu____493 uu____495
    | uu____497 ->
        let uu____498 =
          let uu____499 = FStar_Parser_AST.term_to_string e in
          FStar_Util.format1 "Not a ref set %s" uu____499 in
        failwith uu____498
let is_general_application: FStar_Parser_AST.term -> Prims.bool =
  fun e  ->
    let uu____504 = (is_array e) || (is_ref_set e) in
    Prims.op_Negation uu____504
let is_general_construction: FStar_Parser_AST.term -> Prims.bool =
  fun e  ->
    let uu____508 = (is_list e) || (is_lex_list e) in
    Prims.op_Negation uu____508
let is_general_prefix_op: FStar_Ident.ident -> Prims.bool =
  fun op  ->
    let op_starting_char =
      FStar_Util.char_at (FStar_Ident.text_of_id op) (Prims.parse_int "0") in
    ((op_starting_char = '!') || (op_starting_char = '?')) ||
      ((op_starting_char = '~') && ((FStar_Ident.text_of_id op) <> "~"))
let head_and_args:
  FStar_Parser_AST.term ->
    (FStar_Parser_AST.term* (FStar_Parser_AST.term* FStar_Parser_AST.imp)
      Prims.list)
  =
  fun e  ->
    let rec aux e1 acc =
      let uu____539 =
        let uu____540 = unparen e1 in uu____540.FStar_Parser_AST.tm in
      match uu____539 with
      | FStar_Parser_AST.App (head1,arg,imp) -> aux head1 ((arg, imp) :: acc)
      | uu____551 -> (e1, acc) in
    aux e []
type associativity =
  | Left
  | Right
  | NonAssoc
let uu___is_Left: associativity -> Prims.bool =
  fun projectee  -> match projectee with | Left  -> true | uu____560 -> false
let uu___is_Right: associativity -> Prims.bool =
  fun projectee  ->
    match projectee with | Right  -> true | uu____564 -> false
let uu___is_NonAssoc: associativity -> Prims.bool =
  fun projectee  ->
    match projectee with | NonAssoc  -> true | uu____568 -> false
type token = (FStar_Char.char,Prims.string) FStar_Util.either
type associativity_level = (associativity* token Prims.list)
let token_to_string:
  (FStar_BaseTypes.char,Prims.string) FStar_Util.either -> Prims.string =
  fun uu___124_578  ->
    match uu___124_578 with
    | FStar_Util.Inl c -> Prims.strcat (FStar_Util.string_of_char c) ".*"
    | FStar_Util.Inr s -> s
let matches_token:
  Prims.string ->
    (FStar_Char.char,Prims.string) FStar_Util.either -> Prims.bool
  =
  fun s  ->
    fun uu___125_590  ->
      match uu___125_590 with
      | FStar_Util.Inl c ->
          let uu____594 = FStar_String.get s (Prims.parse_int "0") in
          uu____594 = c
      | FStar_Util.Inr s' -> s = s'
let matches_level s uu____612 =
  match uu____612 with
  | (assoc_levels,tokens) ->
      let uu____626 = FStar_List.tryFind (matches_token s) tokens in
      uu____626 <> None
let opinfix4 uu____644 = (Right, [FStar_Util.Inr "**"])
let opinfix3 uu____659 =
  (Left, [FStar_Util.Inl '*'; FStar_Util.Inl '/'; FStar_Util.Inl '%'])
let opinfix2 uu____678 = (Left, [FStar_Util.Inl '+'; FStar_Util.Inl '-'])
let minus_lvl uu____695 = (Left, [FStar_Util.Inr "-"])
let opinfix1 uu____710 = (Right, [FStar_Util.Inl '@'; FStar_Util.Inl '^'])
let pipe_right uu____727 = (Left, [FStar_Util.Inr "|>"])
let opinfix0d uu____742 = (Left, [FStar_Util.Inl '$'])
let opinfix0c uu____757 =
  (Left, [FStar_Util.Inl '='; FStar_Util.Inl '<'; FStar_Util.Inl '>'])
let equal uu____776 = (Left, [FStar_Util.Inr "="])
let opinfix0b uu____791 = (Left, [FStar_Util.Inl '&'])
let opinfix0a uu____806 = (Left, [FStar_Util.Inl '|'])
let colon_equals uu____821 = (NonAssoc, [FStar_Util.Inr ":="])
let amp uu____836 = (Right, [FStar_Util.Inr "&"])
let colon_colon uu____851 = (Right, [FStar_Util.Inr "::"])
let level_associativity_spec:
  (associativity* (FStar_Char.char,Prims.string) FStar_Util.either
    Prims.list) Prims.list
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
let level_table:
  ((Prims.int* Prims.int* Prims.int)* (FStar_Char.char,Prims.string)
    FStar_Util.either Prims.list) Prims.list
  =
  let levels_from_associativity l uu___126_948 =
    match uu___126_948 with
    | Left  -> (l, l, (l - (Prims.parse_int "1")))
    | Right  -> ((l - (Prims.parse_int "1")), l, l)
    | NonAssoc  -> (l, l, l) in
  FStar_List.mapi
    (fun i  ->
       fun uu____966  ->
         match uu____966 with
         | (assoc1,tokens) -> ((levels_from_associativity i assoc1), tokens))
    level_associativity_spec
let assign_levels:
  associativity_level Prims.list ->
    Prims.string -> (Prims.int* Prims.int* Prims.int)
  =
  fun token_associativity_spec  ->
    fun s  ->
      let uu____1008 = FStar_List.tryFind (matches_level s) level_table in
      match uu____1008 with
      | Some (assoc_levels,uu____1033) -> assoc_levels
      | uu____1054 -> failwith (Prims.strcat "Unrecognized operator " s)
let max: Prims.int -> Prims.int -> Prims.int =
  fun k1  -> fun k2  -> if k1 > k2 then k1 else k2
let max_level l =
  let find_level_and_max n1 level =
    let uu____1110 =
      FStar_List.tryFind
        (fun uu____1128  ->
           match uu____1128 with
           | (uu____1137,tokens) -> tokens = (Prims.snd level)) level_table in
    match uu____1110 with
    | Some ((uu____1157,l1,uu____1159),uu____1160) -> max n1 l1
    | None  ->
        let uu____1186 =
          let uu____1187 =
            let uu____1188 = FStar_List.map token_to_string (Prims.snd level) in
            FStar_String.concat "," uu____1188 in
          FStar_Util.format1 "Undefined associativity level %s" uu____1187 in
        failwith uu____1186 in
  FStar_List.fold_left find_level_and_max (Prims.parse_int "0") l
let levels: Prims.string -> (Prims.int* Prims.int* Prims.int) =
  assign_levels level_associativity_spec
let operatorInfix0ad12 uu____1213 =
  [opinfix0a ();
  opinfix0b ();
  opinfix0c ();
  opinfix0d ();
  opinfix1 ();
  opinfix2 ()]
let is_operatorInfix0ad12: FStar_Ident.ident -> Prims.bool =
  fun op  ->
    let uu____1252 =
      let uu____1259 =
        FStar_All.pipe_left matches_level (FStar_Ident.text_of_id op) in
      FStar_List.tryFind uu____1259 (operatorInfix0ad12 ()) in
    uu____1252 <> None
let is_operatorInfix34: FStar_Ident.ident -> Prims.bool =
  let opinfix34 = [opinfix3 (); opinfix4 ()] in
  fun op  ->
    let uu____1315 =
      let uu____1322 =
        FStar_All.pipe_left matches_level (FStar_Ident.text_of_id op) in
      FStar_List.tryFind uu____1322 opinfix34 in
    uu____1315 <> None
let handleable_op op args =
  match FStar_List.length args with
  | _0_28 when _0_28 = (Prims.parse_int "0") -> true
  | _0_29 when _0_29 = (Prims.parse_int "1") ->
      (is_general_prefix_op op) ||
        (FStar_List.mem (FStar_Ident.text_of_id op) ["-"; "~"])
  | _0_30 when _0_30 = (Prims.parse_int "2") ->
      ((is_operatorInfix0ad12 op) || (is_operatorInfix34 op)) ||
        (FStar_List.mem (FStar_Ident.text_of_id op)
           ["<==>"; "==>"; "\\/"; "/\\"; "="; "|>"; ":="; ".()"; ".[]"])
  | _0_31 when _0_31 = (Prims.parse_int "3") ->
      FStar_List.mem (FStar_Ident.text_of_id op) [".()<-"; ".[]<-"]
  | uu____1368 -> false
let comment_stack: (Prims.string* FStar_Range.range) Prims.list FStar_ST.ref
  = FStar_Util.mk_ref []
let with_comment printer tm tmrange =
  let rec comments_before_pos acc print_pos lookahead_pos =
    let uu____1414 = FStar_ST.read comment_stack in
    match uu____1414 with
    | [] -> (acc, false)
    | (comment,crange)::cs ->
        let uu____1435 = FStar_Range.range_before_pos crange print_pos in
        if uu____1435
        then
          (FStar_ST.write comment_stack cs;
           (let uu____1444 =
              let uu____1445 =
                let uu____1446 = str comment in
                FStar_Pprint.op_Hat_Hat uu____1446 FStar_Pprint.hardline in
              FStar_Pprint.op_Hat_Hat acc uu____1445 in
            comments_before_pos uu____1444 print_pos lookahead_pos))
        else
          (let uu____1448 = FStar_Range.range_before_pos crange lookahead_pos in
           (acc, uu____1448)) in
  let uu____1449 =
    let uu____1452 =
      let uu____1453 = FStar_Range.start_of_range tmrange in
      FStar_Range.end_of_line uu____1453 in
    let uu____1454 = FStar_Range.end_of_range tmrange in
    comments_before_pos FStar_Pprint.empty uu____1452 uu____1454 in
  match uu____1449 with
  | (comments,has_lookahead) ->
      let printed_e = printer tm in
      let comments1 =
        if has_lookahead
        then
          let pos = FStar_Range.end_of_range tmrange in
          let uu____1460 = comments_before_pos comments pos pos in
          Prims.fst uu____1460
        else comments in
      let uu____1464 = FStar_Pprint.op_Hat_Hat comments1 printed_e in
      FStar_Pprint.group uu____1464
let rec place_comments_until_pos:
  Prims.int ->
    Prims.int ->
      FStar_Range.pos -> FStar_Pprint.document -> FStar_Pprint.document
  =
  fun k  ->
    fun lbegin  ->
      fun pos_end  ->
        fun doc1  ->
          let uu____1477 = FStar_ST.read comment_stack in
          match uu____1477 with
          | (comment,crange)::cs when
              FStar_Range.range_before_pos crange pos_end ->
              (FStar_ST.write comment_stack cs;
               (let lnum =
                  let uu____1501 =
                    let uu____1502 =
                      let uu____1503 = FStar_Range.start_of_range crange in
                      FStar_Range.line_of_pos uu____1503 in
                    uu____1502 - lbegin in
                  max k uu____1501 in
                let doc2 =
                  let uu____1505 =
                    let uu____1506 =
                      FStar_Pprint.repeat lnum FStar_Pprint.hardline in
                    let uu____1507 = str comment in
                    FStar_Pprint.op_Hat_Hat uu____1506 uu____1507 in
                  FStar_Pprint.op_Hat_Hat doc1 uu____1505 in
                let uu____1508 =
                  let uu____1509 = FStar_Range.end_of_range crange in
                  FStar_Range.line_of_pos uu____1509 in
                place_comments_until_pos (Prims.parse_int "1") uu____1508
                  pos_end doc2))
          | uu____1510 ->
              let lnum =
                let uu____1515 =
                  let uu____1516 = FStar_Range.line_of_pos pos_end in
                  uu____1516 - lbegin in
                max (Prims.parse_int "1") uu____1515 in
              let uu____1517 = FStar_Pprint.repeat lnum FStar_Pprint.hardline in
              FStar_Pprint.op_Hat_Hat doc1 uu____1517
let separate_map_with_comments prefix1 sep f xs extract_range =
  let fold_fun uu____1566 x =
    match uu____1566 with
    | (last_line,doc1) ->
        let r = extract_range x in
        let doc2 =
          let uu____1576 = FStar_Range.start_of_range r in
          place_comments_until_pos (Prims.parse_int "1") last_line uu____1576
            doc1 in
        let uu____1577 =
          let uu____1578 = FStar_Range.end_of_range r in
          FStar_Range.line_of_pos uu____1578 in
        let uu____1579 =
          let uu____1580 =
            let uu____1581 = f x in FStar_Pprint.op_Hat_Hat sep uu____1581 in
          FStar_Pprint.op_Hat_Hat doc2 uu____1580 in
        (uu____1577, uu____1579) in
  let uu____1582 =
    let uu____1586 = FStar_List.hd xs in
    let uu____1587 = FStar_List.tl xs in (uu____1586, uu____1587) in
  match uu____1582 with
  | (x,xs1) ->
      let init1 =
        let uu____1597 =
          let uu____1598 =
            let uu____1599 = extract_range x in
            FStar_Range.end_of_range uu____1599 in
          FStar_Range.line_of_pos uu____1598 in
        let uu____1600 =
          let uu____1601 = f x in FStar_Pprint.op_Hat_Hat prefix1 uu____1601 in
        (uu____1597, uu____1600) in
      let uu____1602 = FStar_List.fold_left fold_fun init1 xs1 in
      Prims.snd uu____1602
let rec p_decl: FStar_Parser_AST.decl -> FStar_Pprint.document =
  fun d  ->
    let uu____1848 =
      let uu____1849 = FStar_Pprint.optional p_fsdoc d.FStar_Parser_AST.doc in
      let uu____1850 =
        let uu____1851 = p_attributes d.FStar_Parser_AST.attrs in
        let uu____1852 =
          let uu____1853 = p_qualifiers d.FStar_Parser_AST.quals in
          let uu____1854 =
            let uu____1855 = p_rawDecl d in
            FStar_Pprint.op_Hat_Hat
              (if d.FStar_Parser_AST.quals = []
               then FStar_Pprint.empty
               else break1) uu____1855 in
          FStar_Pprint.op_Hat_Hat uu____1853 uu____1854 in
        FStar_Pprint.op_Hat_Hat uu____1851 uu____1852 in
      FStar_Pprint.op_Hat_Hat uu____1849 uu____1850 in
    FStar_Pprint.group uu____1848
and p_attributes: FStar_Parser_AST.attributes_ -> FStar_Pprint.document =
  fun attrs  ->
    let uu____1858 =
      let uu____1859 = str "@" in
      FStar_Pprint.op_Hat_Hat FStar_Pprint.lbracket uu____1859 in
    let uu____1860 =
      FStar_Pprint.op_Hat_Hat FStar_Pprint.rbracket FStar_Pprint.hardline in
    soft_surround_separate_map (Prims.parse_int "0") (Prims.parse_int "2")
      FStar_Pprint.empty uu____1858 FStar_Pprint.space uu____1860
      p_atomicTerm attrs
and p_fsdoc: FStar_Parser_AST.fsdoc -> FStar_Pprint.document =
  fun uu____1861  ->
    match uu____1861 with
    | (doc1,kwd_args) ->
        let kwd_args_doc =
          match kwd_args with
          | [] -> FStar_Pprint.empty
          | kwd_args1 ->
              let process_kwd_arg uu____1882 =
                match uu____1882 with
                | (kwd1,arg) ->
                    let uu____1887 = str "@" in
                    let uu____1888 =
                      let uu____1889 = str kwd1 in
                      let uu____1890 =
                        let uu____1891 = str arg in
                        FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____1891 in
                      FStar_Pprint.op_Hat_Hat uu____1889 uu____1890 in
                    FStar_Pprint.op_Hat_Hat uu____1887 uu____1888 in
              let uu____1892 =
                let uu____1893 =
                  FStar_Pprint.separate_map FStar_Pprint.hardline
                    process_kwd_arg kwd_args1 in
                FStar_Pprint.op_Hat_Hat uu____1893 FStar_Pprint.hardline in
              FStar_Pprint.op_Hat_Hat FStar_Pprint.hardline uu____1892 in
        let uu____1896 =
          let uu____1897 =
            let uu____1898 =
              let uu____1899 =
                let uu____1900 = str doc1 in
                let uu____1901 =
                  let uu____1902 =
                    let uu____1903 =
                      FStar_Pprint.op_Hat_Hat FStar_Pprint.rparen
                        FStar_Pprint.hardline in
                    FStar_Pprint.op_Hat_Hat FStar_Pprint.star uu____1903 in
                  FStar_Pprint.op_Hat_Hat kwd_args_doc uu____1902 in
                FStar_Pprint.op_Hat_Hat uu____1900 uu____1901 in
              FStar_Pprint.op_Hat_Hat FStar_Pprint.star uu____1899 in
            FStar_Pprint.op_Hat_Hat FStar_Pprint.star uu____1898 in
          FStar_Pprint.op_Hat_Hat FStar_Pprint.lparen uu____1897 in
        FStar_Pprint.op_Hat_Hat FStar_Pprint.hardline uu____1896
and p_rawDecl: FStar_Parser_AST.decl -> FStar_Pprint.document =
  fun d  ->
    match d.FStar_Parser_AST.d with
    | FStar_Parser_AST.Open uid ->
        let uu____1906 =
          let uu____1907 = str "open" in
          let uu____1908 = p_quident uid in
          FStar_Pprint.op_Hat_Slash_Hat uu____1907 uu____1908 in
        FStar_Pprint.group uu____1906
    | FStar_Parser_AST.Include uid ->
        let uu____1910 =
          let uu____1911 = str "include" in
          let uu____1912 = p_quident uid in
          FStar_Pprint.op_Hat_Slash_Hat uu____1911 uu____1912 in
        FStar_Pprint.group uu____1910
    | FStar_Parser_AST.ModuleAbbrev (uid1,uid2) ->
        let uu____1915 =
          let uu____1916 = str "module" in
          let uu____1917 =
            let uu____1918 =
              let uu____1919 = p_uident uid1 in
              let uu____1920 =
                FStar_Pprint.op_Hat_Hat FStar_Pprint.space
                  FStar_Pprint.equals in
              FStar_Pprint.op_Hat_Hat uu____1919 uu____1920 in
            FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____1918 in
          FStar_Pprint.op_Hat_Hat uu____1916 uu____1917 in
        let uu____1921 = p_quident uid2 in
        op_Hat_Slash_Plus_Hat uu____1915 uu____1921
    | FStar_Parser_AST.TopLevelModule uid ->
        let uu____1923 =
          let uu____1924 = str "module" in
          let uu____1925 =
            let uu____1926 = p_quident uid in
            FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____1926 in
          FStar_Pprint.op_Hat_Hat uu____1924 uu____1925 in
        FStar_Pprint.group uu____1923
    | FStar_Parser_AST.Tycon
        (true ,(FStar_Parser_AST.TyconAbbrev (uid,tpars,None ,t),None )::[])
        ->
        let effect_prefix_doc =
          let uu____1945 = str "effect" in
          let uu____1946 =
            let uu____1947 = p_uident uid in
            FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____1947 in
          FStar_Pprint.op_Hat_Hat uu____1945 uu____1946 in
        let uu____1948 =
          let uu____1949 = p_typars tpars in
          FStar_Pprint.surround (Prims.parse_int "2") (Prims.parse_int "1")
            effect_prefix_doc uu____1949 FStar_Pprint.equals in
        let uu____1950 = p_typ t in
        op_Hat_Slash_Plus_Hat uu____1948 uu____1950
    | FStar_Parser_AST.Tycon (false ,tcdefs) ->
        let uu____1960 = str "type" in
        let uu____1961 = str "and" in
        precede_break_separate_map uu____1960 uu____1961 p_fsdocTypeDeclPairs
          tcdefs
    | FStar_Parser_AST.TopLevelLet (q,lbs) ->
        let let_doc =
          let uu____1974 = str "let" in
          let uu____1975 =
            let uu____1976 = p_letqualifier q in
            FStar_Pprint.op_Hat_Hat uu____1976 FStar_Pprint.space in
          FStar_Pprint.op_Hat_Hat uu____1974 uu____1975 in
        let uu____1977 =
          let uu____1978 = str "and" in
          FStar_Pprint.op_Hat_Hat uu____1978 FStar_Pprint.space in
        separate_map_with_comments let_doc uu____1977 p_letbinding lbs
          (fun uu____1981  ->
             match uu____1981 with
             | (p,t) ->
                 FStar_Range.union_ranges p.FStar_Parser_AST.prange
                   t.FStar_Parser_AST.range)
    | FStar_Parser_AST.Val (lid,t) ->
        let uu____1988 =
          let uu____1989 = str "val" in
          let uu____1990 =
            let uu____1991 =
              let uu____1992 = p_lident lid in
              let uu____1993 =
                FStar_Pprint.op_Hat_Hat FStar_Pprint.space FStar_Pprint.colon in
              FStar_Pprint.op_Hat_Hat uu____1992 uu____1993 in
            FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____1991 in
          FStar_Pprint.op_Hat_Hat uu____1989 uu____1990 in
        let uu____1994 = p_typ t in
        op_Hat_Slash_Plus_Hat uu____1988 uu____1994
    | FStar_Parser_AST.Assume (id,t) ->
        let decl_keyword =
          let uu____1998 =
            let uu____1999 =
              FStar_Util.char_at id.FStar_Ident.idText (Prims.parse_int "0") in
            FStar_All.pipe_right uu____1999 FStar_Util.is_upper in
          if uu____1998
          then FStar_Pprint.empty
          else
            (let uu____2001 = str "val" in
             FStar_Pprint.op_Hat_Hat uu____2001 FStar_Pprint.space) in
        let uu____2002 =
          let uu____2003 =
            let uu____2004 = p_ident id in
            let uu____2005 =
              FStar_Pprint.op_Hat_Hat FStar_Pprint.space FStar_Pprint.colon in
            FStar_Pprint.op_Hat_Hat uu____2004 uu____2005 in
          FStar_Pprint.op_Hat_Hat decl_keyword uu____2003 in
        let uu____2006 = p_typ t in
        op_Hat_Slash_Plus_Hat uu____2002 uu____2006
    | FStar_Parser_AST.Exception (uid,t_opt) ->
        let uu____2011 = str "exception" in
        let uu____2012 =
          let uu____2013 =
            let uu____2014 = p_uident uid in
            let uu____2015 =
              FStar_Pprint.optional
                (fun t  ->
                   let uu____2017 = str "of" in
                   let uu____2018 = p_typ t in
                   op_Hat_Slash_Plus_Hat uu____2017 uu____2018) t_opt in
            FStar_Pprint.op_Hat_Hat uu____2014 uu____2015 in
          FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____2013 in
        FStar_Pprint.op_Hat_Hat uu____2011 uu____2012
    | FStar_Parser_AST.NewEffect ne ->
        let uu____2020 = str "new_effect" in
        let uu____2021 =
          let uu____2022 = p_newEffect ne in
          FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____2022 in
        FStar_Pprint.op_Hat_Hat uu____2020 uu____2021
    | FStar_Parser_AST.SubEffect se ->
        let uu____2024 = str "sub_effect" in
        let uu____2025 =
          let uu____2026 = p_subEffect se in
          FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____2026 in
        FStar_Pprint.op_Hat_Hat uu____2024 uu____2025
    | FStar_Parser_AST.Pragma p -> p_pragma p
    | FStar_Parser_AST.Fsdoc doc1 ->
        let uu____2029 = p_fsdoc doc1 in
        FStar_Pprint.op_Hat_Hat uu____2029 FStar_Pprint.hardline
    | FStar_Parser_AST.Main uu____2030 ->
        failwith "*Main declaration* : Is that really still in use ??"
    | FStar_Parser_AST.Tycon (true ,uu____2031) ->
        failwith
          "Effect abbreviation is expected to be defined by an abbreviation"
and p_pragma: FStar_Parser_AST.pragma -> FStar_Pprint.document =
  fun uu___127_2040  ->
    match uu___127_2040 with
    | FStar_Parser_AST.SetOptions s ->
        let uu____2042 = str "#set-options" in
        let uu____2043 =
          let uu____2044 =
            let uu____2045 = str s in FStar_Pprint.dquotes uu____2045 in
          FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____2044 in
        FStar_Pprint.op_Hat_Hat uu____2042 uu____2043
    | FStar_Parser_AST.ResetOptions s_opt ->
        let uu____2048 = str "#reset-options" in
        let uu____2049 =
          FStar_Pprint.optional
            (fun s  ->
               let uu____2051 =
                 let uu____2052 = str s in FStar_Pprint.dquotes uu____2052 in
               FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____2051) s_opt in
        FStar_Pprint.op_Hat_Hat uu____2048 uu____2049
    | FStar_Parser_AST.LightOff  ->
        (FStar_ST.write should_print_fs_typ_app true; str "#light \"off\"")
and p_typars: FStar_Parser_AST.binder Prims.list -> FStar_Pprint.document =
  fun bs  -> p_binders true bs
and p_fsdocTypeDeclPairs:
  (FStar_Parser_AST.tycon* FStar_Parser_AST.fsdoc Prims.option) ->
    FStar_Pprint.document
  =
  fun uu____2058  ->
    match uu____2058 with
    | (typedecl,fsdoc_opt) ->
        let uu____2066 = FStar_Pprint.optional p_fsdoc fsdoc_opt in
        let uu____2067 = p_typeDecl typedecl in
        FStar_Pprint.op_Hat_Hat uu____2066 uu____2067
and p_typeDecl: FStar_Parser_AST.tycon -> FStar_Pprint.document =
  fun uu___128_2068  ->
    match uu___128_2068 with
    | FStar_Parser_AST.TyconAbstract (lid,bs,typ_opt) ->
        let empty' uu____2079 = FStar_Pprint.empty in
        p_typeDeclPrefix lid bs typ_opt empty'
    | FStar_Parser_AST.TyconAbbrev (lid,bs,typ_opt,t) ->
        let f uu____2091 =
          let uu____2092 = p_typ t in prefix2 FStar_Pprint.equals uu____2092 in
        p_typeDeclPrefix lid bs typ_opt f
    | FStar_Parser_AST.TyconRecord (lid,bs,typ_opt,record_field_decls) ->
        let p_recordFieldAndComments uu____2118 =
          match uu____2118 with
          | (lid1,t,doc_opt) ->
              let uu____2128 =
                FStar_Range.extend_to_end_of_line t.FStar_Parser_AST.range in
              with_comment p_recordFieldDecl (lid1, t, doc_opt) uu____2128 in
        let p_fields uu____2137 =
          let uu____2138 =
            let uu____2139 =
              let uu____2140 =
                let uu____2141 =
                  FStar_Pprint.op_Hat_Hat FStar_Pprint.semi break1 in
                FStar_Pprint.separate_map uu____2141 p_recordFieldAndComments
                  record_field_decls in
              braces_with_nesting uu____2140 in
            FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____2139 in
          FStar_Pprint.op_Hat_Hat FStar_Pprint.equals uu____2138 in
        p_typeDeclPrefix lid bs typ_opt p_fields
    | FStar_Parser_AST.TyconVariant (lid,bs,typ_opt,ct_decls) ->
        let p_constructorBranchAndComments uu____2177 =
          match uu____2177 with
          | (uid,t_opt,doc_opt,use_of) ->
              let range =
                let uu____2193 =
                  let uu____2194 =
                    FStar_Util.map_opt t_opt
                      (fun t  -> t.FStar_Parser_AST.range) in
                  FStar_Util.dflt uid.FStar_Ident.idRange uu____2194 in
                FStar_Range.extend_to_end_of_line uu____2193 in
              let p_constructorBranch decl =
                let uu____2213 =
                  let uu____2214 =
                    let uu____2215 = p_constructorDecl decl in
                    FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____2215 in
                  FStar_Pprint.op_Hat_Hat FStar_Pprint.bar uu____2214 in
                FStar_Pprint.group uu____2213 in
              with_comment p_constructorBranch (uid, t_opt, doc_opt, use_of)
                range in
        let datacon_doc uu____2227 =
          let uu____2228 =
            FStar_Pprint.separate_map break1 p_constructorBranchAndComments
              ct_decls in
          FStar_Pprint.group uu____2228 in
        p_typeDeclPrefix lid bs typ_opt
          (fun uu____2235  ->
             let uu____2236 = datacon_doc () in
             prefix2 FStar_Pprint.equals uu____2236)
and p_typeDeclPrefix:
  FStar_Ident.ident ->
    FStar_Parser_AST.binder Prims.list ->
      FStar_Parser_AST.knd Prims.option ->
        (Prims.unit -> FStar_Pprint.document) -> FStar_Pprint.document
  =
  fun lid  ->
    fun bs  ->
      fun typ_opt  ->
        fun cont  ->
          if (bs = []) && (typ_opt = None)
          then
            let uu____2247 = p_ident lid in
            let uu____2248 =
              let uu____2249 = cont () in
              FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____2249 in
            FStar_Pprint.op_Hat_Hat uu____2247 uu____2248
          else
            (let binders_doc =
               let uu____2252 = p_typars bs in
               let uu____2253 =
                 FStar_Pprint.optional
                   (fun t  ->
                      let uu____2255 =
                        let uu____2256 =
                          let uu____2257 = p_typ t in
                          FStar_Pprint.op_Hat_Hat FStar_Pprint.space
                            uu____2257 in
                        FStar_Pprint.op_Hat_Hat FStar_Pprint.colon uu____2256 in
                      FStar_Pprint.op_Hat_Hat break1 uu____2255) typ_opt in
               FStar_Pprint.op_Hat_Hat uu____2252 uu____2253 in
             let uu____2258 = p_ident lid in
             let uu____2259 = cont () in
             FStar_Pprint.surround (Prims.parse_int "2")
               (Prims.parse_int "1") uu____2258 binders_doc uu____2259)
and p_recordFieldDecl:
  (FStar_Ident.ident* FStar_Parser_AST.term* FStar_Parser_AST.fsdoc
    Prims.option) -> FStar_Pprint.document
  =
  fun uu____2260  ->
    match uu____2260 with
    | (lid,t,doc_opt) ->
        let uu____2270 =
          let uu____2271 = FStar_Pprint.optional p_fsdoc doc_opt in
          let uu____2272 =
            let uu____2273 = p_lident lid in
            let uu____2274 =
              let uu____2275 = p_typ t in
              FStar_Pprint.op_Hat_Hat FStar_Pprint.colon uu____2275 in
            FStar_Pprint.op_Hat_Hat uu____2273 uu____2274 in
          FStar_Pprint.op_Hat_Hat uu____2271 uu____2272 in
        FStar_Pprint.group uu____2270
and p_constructorDecl:
  (FStar_Ident.ident* FStar_Parser_AST.term Prims.option*
    FStar_Parser_AST.fsdoc Prims.option* Prims.bool) -> FStar_Pprint.document
  =
  fun uu____2276  ->
    match uu____2276 with
    | (uid,t_opt,doc_opt,use_of) ->
        let sep = if use_of then str "of" else FStar_Pprint.colon in
        let uid_doc = p_uident uid in
        let uu____2294 = FStar_Pprint.optional p_fsdoc doc_opt in
        let uu____2295 =
          let uu____2296 = FStar_Pprint.break_ (Prims.parse_int "0") in
          let uu____2297 =
            default_or_map uid_doc
              (fun t  ->
                 let uu____2299 =
                   let uu____2300 =
                     FStar_Pprint.op_Hat_Hat FStar_Pprint.space sep in
                   FStar_Pprint.op_Hat_Hat uid_doc uu____2300 in
                 let uu____2301 = p_typ t in
                 op_Hat_Slash_Plus_Hat uu____2299 uu____2301) t_opt in
          FStar_Pprint.op_Hat_Hat uu____2296 uu____2297 in
        FStar_Pprint.op_Hat_Hat uu____2294 uu____2295
and p_letbinding:
  (FStar_Parser_AST.pattern* FStar_Parser_AST.term) -> FStar_Pprint.document
  =
  fun uu____2302  ->
    match uu____2302 with
    | (pat,e) ->
        let pat_doc =
          let uu____2308 =
            match pat.FStar_Parser_AST.pat with
            | FStar_Parser_AST.PatAscribed (pat1,t) ->
                let uu____2315 =
                  let uu____2316 =
                    let uu____2317 =
                      let uu____2318 =
                        let uu____2319 = p_tmArrow p_tmNoEq t in
                        FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____2319 in
                      FStar_Pprint.op_Hat_Hat FStar_Pprint.colon uu____2318 in
                    FStar_Pprint.group uu____2317 in
                  FStar_Pprint.op_Hat_Hat break1 uu____2316 in
                (pat1, uu____2315)
            | uu____2320 -> (pat, FStar_Pprint.empty) in
          match uu____2308 with
          | (pat1,ascr_doc) ->
              (match pat1.FStar_Parser_AST.pat with
               | FStar_Parser_AST.PatApp
                   ({
                      FStar_Parser_AST.pat = FStar_Parser_AST.PatVar
                        (x,uu____2324);
                      FStar_Parser_AST.prange = uu____2325;_},pats)
                   ->
                   let uu____2331 = p_lident x in
                   let uu____2332 =
                     let uu____2333 =
                       FStar_Pprint.separate_map break1 p_atomicPattern pats in
                     FStar_Pprint.op_Hat_Hat uu____2333 ascr_doc in
                   FStar_Pprint.surround (Prims.parse_int "2")
                     (Prims.parse_int "1") uu____2331 uu____2332
                     FStar_Pprint.equals
               | uu____2334 ->
                   let uu____2335 =
                     let uu____2336 = p_tuplePattern pat1 in
                     let uu____2337 =
                       FStar_Pprint.op_Hat_Slash_Hat ascr_doc
                         FStar_Pprint.equals in
                     FStar_Pprint.op_Hat_Hat uu____2336 uu____2337 in
                   FStar_Pprint.group uu____2335) in
        let uu____2338 = p_term e in prefix2 pat_doc uu____2338
and p_newEffect: FStar_Parser_AST.effect_decl -> FStar_Pprint.document =
  fun uu___129_2339  ->
    match uu___129_2339 with
    | FStar_Parser_AST.RedefineEffect (lid,bs,t) ->
        p_effectRedefinition lid bs t
    | FStar_Parser_AST.DefineEffect (lid,bs,t,eff_decls) ->
        p_effectDefinition lid bs t eff_decls
and p_effectRedefinition:
  FStar_Ident.ident ->
    FStar_Parser_AST.binder Prims.list ->
      FStar_Parser_AST.term -> FStar_Pprint.document
  =
  fun uid  ->
    fun bs  ->
      fun t  ->
        let uu____2357 = p_uident uid in
        let uu____2358 = p_binders true bs in
        let uu____2359 =
          let uu____2360 = p_simpleTerm t in
          prefix2 FStar_Pprint.equals uu____2360 in
        FStar_Pprint.surround (Prims.parse_int "2") (Prims.parse_int "1")
          uu____2357 uu____2358 uu____2359
and p_effectDefinition:
  FStar_Ident.ident ->
    FStar_Parser_AST.binder Prims.list ->
      FStar_Parser_AST.term ->
        FStar_Parser_AST.decl Prims.list -> FStar_Pprint.document
  =
  fun uid  ->
    fun bs  ->
      fun t  ->
        fun eff_decls  ->
          let uu____2367 =
            let uu____2368 =
              let uu____2369 =
                let uu____2370 = p_uident uid in
                let uu____2371 = p_binders true bs in
                let uu____2372 =
                  let uu____2373 = p_typ t in
                  prefix2 FStar_Pprint.colon uu____2373 in
                FStar_Pprint.surround (Prims.parse_int "2")
                  (Prims.parse_int "1") uu____2370 uu____2371 uu____2372 in
              FStar_Pprint.group uu____2369 in
            let uu____2374 =
              let uu____2375 = str "with" in
              let uu____2376 =
                separate_break_map FStar_Pprint.semi p_effectDecl eff_decls in
              prefix2 uu____2375 uu____2376 in
            FStar_Pprint.op_Hat_Slash_Hat uu____2368 uu____2374 in
          braces_with_nesting uu____2367
and p_effectDecl: FStar_Parser_AST.decl -> FStar_Pprint.document =
  fun d  ->
    match d.FStar_Parser_AST.d with
    | FStar_Parser_AST.Tycon
        (false ,(FStar_Parser_AST.TyconAbbrev (lid,[],None ,e),None )::[]) ->
        let uu____2393 =
          let uu____2394 = p_lident lid in
          let uu____2395 =
            FStar_Pprint.op_Hat_Hat FStar_Pprint.space FStar_Pprint.equals in
          FStar_Pprint.op_Hat_Hat uu____2394 uu____2395 in
        let uu____2396 = p_simpleTerm e in prefix2 uu____2393 uu____2396
    | uu____2397 ->
        let uu____2398 =
          let uu____2399 = FStar_Parser_AST.decl_to_string d in
          FStar_Util.format1
            "Not a declaration of an effect member... or at least I hope so : %s"
            uu____2399 in
        failwith uu____2398
and p_subEffect: FStar_Parser_AST.lift -> FStar_Pprint.document =
  fun lift  ->
    let lift_op_doc =
      let lifts =
        match lift.FStar_Parser_AST.lift_op with
        | FStar_Parser_AST.NonReifiableLift t -> [("lift_wp", t)]
        | FStar_Parser_AST.ReifiableLift (t1,t2) ->
            [("lif_wp", t1); ("lift", t2)]
        | FStar_Parser_AST.LiftForFree t -> [("lift", t)] in
      let p_lift uu____2432 =
        match uu____2432 with
        | (kwd1,t) ->
            let uu____2437 =
              let uu____2438 = str kwd1 in
              let uu____2439 =
                FStar_Pprint.op_Hat_Hat FStar_Pprint.space
                  FStar_Pprint.equals in
              FStar_Pprint.op_Hat_Hat uu____2438 uu____2439 in
            let uu____2440 = p_simpleTerm t in prefix2 uu____2437 uu____2440 in
      separate_break_map FStar_Pprint.semi p_lift lifts in
    let uu____2443 =
      let uu____2444 =
        let uu____2445 = p_quident lift.FStar_Parser_AST.msource in
        let uu____2446 =
          let uu____2447 = str "~>" in
          FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____2447 in
        FStar_Pprint.op_Hat_Hat uu____2445 uu____2446 in
      let uu____2448 = p_quident lift.FStar_Parser_AST.mdest in
      prefix2 uu____2444 uu____2448 in
    let uu____2449 =
      let uu____2450 = braces_with_nesting lift_op_doc in
      FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____2450 in
    FStar_Pprint.op_Hat_Hat uu____2443 uu____2449
and p_qualifier: FStar_Parser_AST.qualifier -> FStar_Pprint.document =
  fun uu___130_2451  ->
    match uu___130_2451 with
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
and p_qualifiers: FStar_Parser_AST.qualifiers -> FStar_Pprint.document =
  fun qs  ->
    let uu____2453 = FStar_Pprint.separate_map break1 p_qualifier qs in
    FStar_Pprint.group uu____2453
and p_letqualifier: FStar_Parser_AST.let_qualifier -> FStar_Pprint.document =
  fun uu___131_2454  ->
    match uu___131_2454 with
    | FStar_Parser_AST.Rec  ->
        let uu____2455 = str "rec" in
        FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____2455
    | FStar_Parser_AST.Mutable  ->
        let uu____2456 = str "mutable" in
        FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____2456
    | FStar_Parser_AST.NoLetQualifier  -> FStar_Pprint.empty
and p_aqual: FStar_Parser_AST.arg_qualifier -> FStar_Pprint.document =
  fun uu___132_2457  ->
    match uu___132_2457 with
    | FStar_Parser_AST.Implicit  -> str "#"
    | FStar_Parser_AST.Equality  -> str "$"
and p_disjunctivePattern: FStar_Parser_AST.pattern -> FStar_Pprint.document =
  fun p  ->
    match p.FStar_Parser_AST.pat with
    | FStar_Parser_AST.PatOr pats ->
        let uu____2461 =
          let uu____2462 =
            let uu____2463 =
              FStar_Pprint.op_Hat_Hat FStar_Pprint.bar FStar_Pprint.space in
            FStar_Pprint.op_Hat_Hat break1 uu____2463 in
          FStar_Pprint.separate_map uu____2462 p_tuplePattern pats in
        FStar_Pprint.group uu____2461
    | uu____2464 -> p_tuplePattern p
and p_tuplePattern: FStar_Parser_AST.pattern -> FStar_Pprint.document =
  fun p  ->
    match p.FStar_Parser_AST.pat with
    | FStar_Parser_AST.PatTuple (pats,false ) ->
        let uu____2469 =
          let uu____2470 = FStar_Pprint.op_Hat_Hat FStar_Pprint.comma break1 in
          FStar_Pprint.separate_map uu____2470 p_constructorPattern pats in
        FStar_Pprint.group uu____2469
    | uu____2471 -> p_constructorPattern p
and p_constructorPattern: FStar_Parser_AST.pattern -> FStar_Pprint.document =
  fun p  ->
    match p.FStar_Parser_AST.pat with
    | FStar_Parser_AST.PatApp
        ({ FStar_Parser_AST.pat = FStar_Parser_AST.PatName maybe_cons_lid;
           FStar_Parser_AST.prange = uu____2474;_},hd1::tl1::[])
        when
        FStar_Ident.lid_equals maybe_cons_lid FStar_Syntax_Const.cons_lid ->
        let uu____2478 =
          FStar_Pprint.op_Hat_Hat FStar_Pprint.colon FStar_Pprint.colon in
        let uu____2479 = p_constructorPattern hd1 in
        let uu____2480 = p_constructorPattern tl1 in
        infix0 uu____2478 uu____2479 uu____2480
    | FStar_Parser_AST.PatApp
        ({ FStar_Parser_AST.pat = FStar_Parser_AST.PatName uid;
           FStar_Parser_AST.prange = uu____2482;_},pats)
        ->
        let uu____2486 = p_quident uid in
        let uu____2487 =
          FStar_Pprint.separate_map break1 p_atomicPattern pats in
        prefix2 uu____2486 uu____2487
    | uu____2488 -> p_atomicPattern p
and p_atomicPattern: FStar_Parser_AST.pattern -> FStar_Pprint.document =
  fun p  ->
    match p.FStar_Parser_AST.pat with
    | FStar_Parser_AST.PatAscribed (pat,t) ->
        let uu____2492 =
          let uu____2495 =
            let uu____2496 = unparen t in uu____2496.FStar_Parser_AST.tm in
          ((pat.FStar_Parser_AST.pat), uu____2495) in
        (match uu____2492 with
         | (FStar_Parser_AST.PatVar (lid,aqual),FStar_Parser_AST.Refine
            ({ FStar_Parser_AST.b = FStar_Parser_AST.Annotated (lid',t1);
               FStar_Parser_AST.brange = uu____2501;
               FStar_Parser_AST.blevel = uu____2502;
               FStar_Parser_AST.aqual = uu____2503;_},phi))
             when lid.FStar_Ident.idText = lid'.FStar_Ident.idText ->
             let uu____2507 =
               let uu____2508 = p_ident lid in
               p_refinement aqual uu____2508 t1 phi in
             soft_parens_with_nesting uu____2507
         | (FStar_Parser_AST.PatWild ,FStar_Parser_AST.Refine
            ({ FStar_Parser_AST.b = FStar_Parser_AST.NoName t1;
               FStar_Parser_AST.brange = uu____2510;
               FStar_Parser_AST.blevel = uu____2511;
               FStar_Parser_AST.aqual = uu____2512;_},phi))
             ->
             let uu____2514 =
               p_refinement None FStar_Pprint.underscore t1 phi in
             soft_parens_with_nesting uu____2514
         | uu____2515 ->
             let uu____2518 =
               let uu____2519 = p_tuplePattern pat in
               let uu____2520 =
                 let uu____2521 = FStar_Pprint.break_ (Prims.parse_int "0") in
                 let uu____2522 =
                   let uu____2523 = p_typ t in
                   FStar_Pprint.op_Hat_Hat FStar_Pprint.colon uu____2523 in
                 FStar_Pprint.op_Hat_Hat uu____2521 uu____2522 in
               FStar_Pprint.op_Hat_Hat uu____2519 uu____2520 in
             soft_parens_with_nesting uu____2518)
    | FStar_Parser_AST.PatList pats ->
        let uu____2526 =
          separate_break_map FStar_Pprint.semi p_tuplePattern pats in
        FStar_Pprint.surround (Prims.parse_int "2") (Prims.parse_int "0")
          FStar_Pprint.lbracket uu____2526 FStar_Pprint.rbracket
    | FStar_Parser_AST.PatRecord pats ->
        let p_recordFieldPat uu____2536 =
          match uu____2536 with
          | (lid,pat) ->
              let uu____2541 = p_qlident lid in
              let uu____2542 = p_tuplePattern pat in
              infix2 FStar_Pprint.equals uu____2541 uu____2542 in
        let uu____2543 =
          separate_break_map FStar_Pprint.semi p_recordFieldPat pats in
        soft_braces_with_nesting uu____2543
    | FStar_Parser_AST.PatTuple (pats,true ) ->
        let uu____2549 =
          FStar_Pprint.op_Hat_Hat FStar_Pprint.lparen FStar_Pprint.bar in
        let uu____2550 =
          separate_break_map FStar_Pprint.comma p_constructorPattern pats in
        let uu____2551 =
          FStar_Pprint.op_Hat_Hat FStar_Pprint.bar FStar_Pprint.rparen in
        FStar_Pprint.surround (Prims.parse_int "2") (Prims.parse_int "1")
          uu____2549 uu____2550 uu____2551
    | FStar_Parser_AST.PatTvar (tv,arg_qualifier_opt) -> p_tvar tv
    | FStar_Parser_AST.PatOp op ->
        let uu____2558 =
          let uu____2559 =
            let uu____2560 = str (FStar_Ident.text_of_id op) in
            let uu____2561 =
              FStar_Pprint.op_Hat_Hat FStar_Pprint.space FStar_Pprint.rparen in
            FStar_Pprint.op_Hat_Hat uu____2560 uu____2561 in
          FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____2559 in
        FStar_Pprint.op_Hat_Hat FStar_Pprint.lparen uu____2558
    | FStar_Parser_AST.PatWild  -> FStar_Pprint.underscore
    | FStar_Parser_AST.PatConst c -> p_constant c
    | FStar_Parser_AST.PatVar (lid,aqual) ->
        let uu____2567 = FStar_Pprint.optional p_aqual aqual in
        let uu____2568 = p_lident lid in
        FStar_Pprint.op_Hat_Hat uu____2567 uu____2568
    | FStar_Parser_AST.PatName uid -> p_quident uid
    | FStar_Parser_AST.PatOr uu____2570 -> failwith "Inner or pattern !"
    | FStar_Parser_AST.PatApp
      ({ FStar_Parser_AST.pat = FStar_Parser_AST.PatName _;
         FStar_Parser_AST.prange = _;_},_)|FStar_Parser_AST.PatTuple
      (_,false ) ->
        let uu____2578 = p_tuplePattern p in
        soft_parens_with_nesting uu____2578
    | uu____2579 ->
        let uu____2580 =
          let uu____2581 = FStar_Parser_AST.pat_to_string p in
          FStar_Util.format1 "Invalid pattern %s" uu____2581 in
        failwith uu____2580
and p_binder: Prims.bool -> FStar_Parser_AST.binder -> FStar_Pprint.document
  =
  fun is_atomic  ->
    fun b  ->
      match b.FStar_Parser_AST.b with
      | FStar_Parser_AST.Variable lid ->
          let uu____2585 =
            FStar_Pprint.optional p_aqual b.FStar_Parser_AST.aqual in
          let uu____2586 = p_lident lid in
          FStar_Pprint.op_Hat_Hat uu____2585 uu____2586
      | FStar_Parser_AST.TVariable lid -> p_lident lid
      | FStar_Parser_AST.Annotated (lid,t) ->
          let doc1 =
            let uu____2591 =
              let uu____2592 = unparen t in uu____2592.FStar_Parser_AST.tm in
            match uu____2591 with
            | FStar_Parser_AST.Refine
                ({ FStar_Parser_AST.b = FStar_Parser_AST.Annotated (lid',t1);
                   FStar_Parser_AST.brange = uu____2595;
                   FStar_Parser_AST.blevel = uu____2596;
                   FStar_Parser_AST.aqual = uu____2597;_},phi)
                when lid.FStar_Ident.idText = lid'.FStar_Ident.idText ->
                let uu____2599 = p_ident lid in
                p_refinement b.FStar_Parser_AST.aqual uu____2599 t1 phi
            | uu____2600 ->
                let uu____2601 =
                  FStar_Pprint.optional p_aqual b.FStar_Parser_AST.aqual in
                let uu____2602 =
                  let uu____2603 = p_lident lid in
                  let uu____2604 =
                    let uu____2605 =
                      let uu____2606 =
                        FStar_Pprint.break_ (Prims.parse_int "0") in
                      let uu____2607 = p_tmFormula t in
                      FStar_Pprint.op_Hat_Hat uu____2606 uu____2607 in
                    FStar_Pprint.op_Hat_Hat FStar_Pprint.colon uu____2605 in
                  FStar_Pprint.op_Hat_Hat uu____2603 uu____2604 in
                FStar_Pprint.op_Hat_Hat uu____2601 uu____2602 in
          if is_atomic
          then
            let uu____2608 =
              let uu____2609 =
                FStar_Pprint.op_Hat_Hat doc1 FStar_Pprint.rparen in
              FStar_Pprint.op_Hat_Hat FStar_Pprint.lparen uu____2609 in
            FStar_Pprint.group uu____2608
          else FStar_Pprint.group doc1
      | FStar_Parser_AST.TAnnotated uu____2611 ->
          failwith "Is this still used ?"
      | FStar_Parser_AST.NoName t ->
          let uu____2615 =
            let uu____2616 = unparen t in uu____2616.FStar_Parser_AST.tm in
          (match uu____2615 with
           | FStar_Parser_AST.Refine
               ({ FStar_Parser_AST.b = FStar_Parser_AST.NoName t1;
                  FStar_Parser_AST.brange = uu____2618;
                  FStar_Parser_AST.blevel = uu____2619;
                  FStar_Parser_AST.aqual = uu____2620;_},phi)
               ->
               if is_atomic
               then
                 let uu____2622 =
                   let uu____2623 =
                     let uu____2624 =
                       p_refinement b.FStar_Parser_AST.aqual
                         FStar_Pprint.underscore t1 phi in
                     FStar_Pprint.op_Hat_Hat uu____2624 FStar_Pprint.rparen in
                   FStar_Pprint.op_Hat_Hat FStar_Pprint.lparen uu____2623 in
                 FStar_Pprint.group uu____2622
               else
                 (let uu____2626 =
                    p_refinement b.FStar_Parser_AST.aqual
                      FStar_Pprint.underscore t1 phi in
                  FStar_Pprint.group uu____2626)
           | uu____2627 -> if is_atomic then p_atomicTerm t else p_appTerm t)
and p_refinement:
  FStar_Parser_AST.arg_qualifier Prims.option ->
    FStar_Pprint.document ->
      FStar_Parser_AST.term -> FStar_Parser_AST.term -> FStar_Pprint.document
  =
  fun aqual_opt  ->
    fun binder  ->
      fun t  ->
        fun phi  ->
          let uu____2634 = FStar_Pprint.optional p_aqual aqual_opt in
          let uu____2635 =
            let uu____2636 =
              let uu____2637 =
                let uu____2638 = p_appTerm t in
                let uu____2639 =
                  let uu____2640 = p_noSeqTerm phi in
                  soft_braces_with_nesting uu____2640 in
                FStar_Pprint.op_Hat_Hat uu____2638 uu____2639 in
              FStar_Pprint.op_Hat_Hat FStar_Pprint.colon uu____2637 in
            FStar_Pprint.op_Hat_Hat binder uu____2636 in
          FStar_Pprint.op_Hat_Hat uu____2634 uu____2635
and p_binders:
  Prims.bool -> FStar_Parser_AST.binder Prims.list -> FStar_Pprint.document =
  fun is_atomic  ->
    fun bs  -> FStar_Pprint.separate_map break1 (p_binder is_atomic) bs
and p_qlident: FStar_Ident.lid -> FStar_Pprint.document =
  fun lid  -> str (FStar_Ident.text_of_lid lid)
and p_quident: FStar_Ident.lid -> FStar_Pprint.document =
  fun lid  -> str (FStar_Ident.text_of_lid lid)
and p_ident: FStar_Ident.ident -> FStar_Pprint.document =
  fun lid  -> str (FStar_Ident.text_of_id lid)
and p_lident: FStar_Ident.ident -> FStar_Pprint.document =
  fun lid  -> str (FStar_Ident.text_of_id lid)
and p_uident: FStar_Ident.ident -> FStar_Pprint.document =
  fun lid  -> str (FStar_Ident.text_of_id lid)
and p_tvar: FStar_Ident.ident -> FStar_Pprint.document =
  fun lid  -> str (FStar_Ident.text_of_id lid)
and p_lidentOrUnderscore: FStar_Ident.ident -> FStar_Pprint.document =
  fun id  ->
    if
      FStar_Util.starts_with FStar_Ident.reserved_prefix
        id.FStar_Ident.idText
    then FStar_Pprint.underscore
    else p_lident id
and p_term: FStar_Parser_AST.term -> FStar_Pprint.document =
  fun e  ->
    let uu____2653 =
      let uu____2654 = unparen e in uu____2654.FStar_Parser_AST.tm in
    match uu____2653 with
    | FStar_Parser_AST.Seq (e1,e2) ->
        let uu____2657 =
          let uu____2658 =
            let uu____2659 = p_noSeqTerm e1 in
            FStar_Pprint.op_Hat_Hat uu____2659 FStar_Pprint.semi in
          FStar_Pprint.group uu____2658 in
        let uu____2660 = p_term e2 in
        FStar_Pprint.op_Hat_Slash_Hat uu____2657 uu____2660
    | FStar_Parser_AST.Bind (x,e1,e2) ->
        let uu____2664 =
          let uu____2665 =
            let uu____2666 = p_lident x in
            let uu____2667 =
              let uu____2668 =
                let uu____2669 = p_noSeqTerm e1 in
                FStar_Pprint.op_Hat_Hat uu____2669 FStar_Pprint.semi in
              FStar_Pprint.op_Hat_Hat FStar_Pprint.long_left_arrow uu____2668 in
            FStar_Pprint.op_Hat_Hat uu____2666 uu____2667 in
          FStar_Pprint.group uu____2665 in
        let uu____2670 = p_term e2 in
        FStar_Pprint.op_Hat_Slash_Hat uu____2664 uu____2670
    | uu____2671 ->
        let uu____2672 = p_noSeqTerm e in FStar_Pprint.group uu____2672
and p_noSeqTerm: FStar_Parser_AST.term -> FStar_Pprint.document =
  fun e  -> with_comment p_noSeqTerm' e e.FStar_Parser_AST.range
and p_noSeqTerm': FStar_Parser_AST.term -> FStar_Pprint.document =
  fun e  ->
    let uu____2675 =
      let uu____2676 = unparen e in uu____2676.FStar_Parser_AST.tm in
    match uu____2675 with
    | FStar_Parser_AST.Ascribed (e1,t,None ) ->
        let uu____2680 =
          let uu____2681 = p_tmIff e1 in
          let uu____2682 =
            let uu____2683 =
              let uu____2684 = p_typ t in
              FStar_Pprint.op_Hat_Slash_Hat FStar_Pprint.colon uu____2684 in
            FStar_Pprint.op_Hat_Hat FStar_Pprint.langle uu____2683 in
          FStar_Pprint.op_Hat_Slash_Hat uu____2681 uu____2682 in
        FStar_Pprint.group uu____2680
    | FStar_Parser_AST.Ascribed (e1,t,Some tac) ->
        let uu____2689 =
          let uu____2690 = p_tmIff e1 in
          let uu____2691 =
            let uu____2692 =
              let uu____2693 =
                let uu____2694 = p_typ t in
                let uu____2695 =
                  let uu____2696 = str "by" in
                  let uu____2697 = p_typ tac in
                  FStar_Pprint.op_Hat_Slash_Hat uu____2696 uu____2697 in
                FStar_Pprint.op_Hat_Slash_Hat uu____2694 uu____2695 in
              FStar_Pprint.op_Hat_Slash_Hat FStar_Pprint.colon uu____2693 in
            FStar_Pprint.op_Hat_Hat FStar_Pprint.langle uu____2692 in
          FStar_Pprint.op_Hat_Slash_Hat uu____2690 uu____2691 in
        FStar_Pprint.group uu____2689
    | FStar_Parser_AST.Op
        ({ FStar_Ident.idText = ".()<-"; FStar_Ident.idRange = uu____2698;_},e1::e2::e3::[])
        ->
        let uu____2703 =
          let uu____2704 =
            let uu____2705 =
              let uu____2706 = p_atomicTermNotQUident e1 in
              let uu____2707 =
                let uu____2708 =
                  let uu____2709 =
                    let uu____2710 = p_term e2 in
                    soft_parens_with_nesting uu____2710 in
                  let uu____2711 =
                    FStar_Pprint.op_Hat_Hat FStar_Pprint.space
                      FStar_Pprint.larrow in
                  FStar_Pprint.op_Hat_Hat uu____2709 uu____2711 in
                FStar_Pprint.op_Hat_Hat FStar_Pprint.dot uu____2708 in
              FStar_Pprint.op_Hat_Hat uu____2706 uu____2707 in
            FStar_Pprint.group uu____2705 in
          let uu____2712 =
            let uu____2713 = p_noSeqTerm e3 in jump2 uu____2713 in
          FStar_Pprint.op_Hat_Hat uu____2704 uu____2712 in
        FStar_Pprint.group uu____2703
    | FStar_Parser_AST.Op
        ({ FStar_Ident.idText = ".[]<-"; FStar_Ident.idRange = uu____2714;_},e1::e2::e3::[])
        ->
        let uu____2719 =
          let uu____2720 =
            let uu____2721 =
              let uu____2722 = p_atomicTermNotQUident e1 in
              let uu____2723 =
                let uu____2724 =
                  let uu____2725 =
                    let uu____2726 = p_term e2 in
                    soft_brackets_with_nesting uu____2726 in
                  let uu____2727 =
                    FStar_Pprint.op_Hat_Hat FStar_Pprint.space
                      FStar_Pprint.larrow in
                  FStar_Pprint.op_Hat_Hat uu____2725 uu____2727 in
                FStar_Pprint.op_Hat_Hat FStar_Pprint.dot uu____2724 in
              FStar_Pprint.op_Hat_Hat uu____2722 uu____2723 in
            FStar_Pprint.group uu____2721 in
          let uu____2728 =
            let uu____2729 = p_noSeqTerm e3 in jump2 uu____2729 in
          FStar_Pprint.op_Hat_Hat uu____2720 uu____2728 in
        FStar_Pprint.group uu____2719
    | FStar_Parser_AST.Requires (e1,wtf) ->
        let uu____2735 =
          let uu____2736 = str "requires" in
          let uu____2737 = p_typ e1 in
          FStar_Pprint.op_Hat_Slash_Hat uu____2736 uu____2737 in
        FStar_Pprint.group uu____2735
    | FStar_Parser_AST.Ensures (e1,wtf) ->
        let uu____2743 =
          let uu____2744 = str "ensures" in
          let uu____2745 = p_typ e1 in
          FStar_Pprint.op_Hat_Slash_Hat uu____2744 uu____2745 in
        FStar_Pprint.group uu____2743
    | FStar_Parser_AST.Attributes es ->
        let uu____2748 =
          let uu____2749 = str "attributes" in
          let uu____2750 = FStar_Pprint.separate_map break1 p_atomicTerm es in
          FStar_Pprint.op_Hat_Slash_Hat uu____2749 uu____2750 in
        FStar_Pprint.group uu____2748
    | FStar_Parser_AST.If (e1,e2,e3) ->
        let uu____2754 = is_unit e3 in
        if uu____2754
        then
          let uu____2755 =
            let uu____2756 =
              let uu____2757 = str "if" in
              let uu____2758 = p_noSeqTerm e1 in
              op_Hat_Slash_Plus_Hat uu____2757 uu____2758 in
            let uu____2759 =
              let uu____2760 = str "then" in
              let uu____2761 = p_noSeqTerm e2 in
              op_Hat_Slash_Plus_Hat uu____2760 uu____2761 in
            FStar_Pprint.op_Hat_Slash_Hat uu____2756 uu____2759 in
          FStar_Pprint.group uu____2755
        else
          (let e2_doc =
             let uu____2764 =
               let uu____2765 = unparen e2 in uu____2765.FStar_Parser_AST.tm in
             match uu____2764 with
             | FStar_Parser_AST.If (uu____2766,uu____2767,e31) when
                 is_unit e31 ->
                 let uu____2769 = p_noSeqTerm e2 in
                 soft_parens_with_nesting uu____2769
             | uu____2770 -> p_noSeqTerm e2 in
           let uu____2771 =
             let uu____2772 =
               let uu____2773 = str "if" in
               let uu____2774 = p_noSeqTerm e1 in
               op_Hat_Slash_Plus_Hat uu____2773 uu____2774 in
             let uu____2775 =
               let uu____2776 =
                 let uu____2777 = str "then" in
                 op_Hat_Slash_Plus_Hat uu____2777 e2_doc in
               let uu____2778 =
                 let uu____2779 = str "else" in
                 let uu____2780 = p_noSeqTerm e3 in
                 op_Hat_Slash_Plus_Hat uu____2779 uu____2780 in
               FStar_Pprint.op_Hat_Slash_Hat uu____2776 uu____2778 in
             FStar_Pprint.op_Hat_Slash_Hat uu____2772 uu____2775 in
           FStar_Pprint.group uu____2771)
    | FStar_Parser_AST.TryWith (e1,branches) ->
        let uu____2793 =
          let uu____2794 =
            let uu____2795 = str "try" in
            let uu____2796 = p_noSeqTerm e1 in prefix2 uu____2795 uu____2796 in
          let uu____2797 =
            let uu____2798 = str "with" in
            let uu____2799 =
              FStar_Pprint.separate_map FStar_Pprint.hardline p_patternBranch
                branches in
            FStar_Pprint.op_Hat_Slash_Hat uu____2798 uu____2799 in
          FStar_Pprint.op_Hat_Slash_Hat uu____2794 uu____2797 in
        FStar_Pprint.group uu____2793
    | FStar_Parser_AST.Match (e1,branches) ->
        let uu____2816 =
          let uu____2817 =
            let uu____2818 = str "match" in
            let uu____2819 = p_noSeqTerm e1 in
            let uu____2820 = str "with" in
            FStar_Pprint.surround (Prims.parse_int "2") (Prims.parse_int "1")
              uu____2818 uu____2819 uu____2820 in
          let uu____2821 =
            FStar_Pprint.separate_map FStar_Pprint.hardline p_patternBranch
              branches in
          FStar_Pprint.op_Hat_Slash_Hat uu____2817 uu____2821 in
        FStar_Pprint.group uu____2816
    | FStar_Parser_AST.LetOpen (uid,e1) ->
        let uu____2828 =
          let uu____2829 =
            let uu____2830 = str "let open" in
            let uu____2831 = p_quident uid in
            let uu____2832 = str "in" in
            FStar_Pprint.surround (Prims.parse_int "2") (Prims.parse_int "1")
              uu____2830 uu____2831 uu____2832 in
          let uu____2833 = p_term e1 in
          FStar_Pprint.op_Hat_Slash_Hat uu____2829 uu____2833 in
        FStar_Pprint.group uu____2828
    | FStar_Parser_AST.Let (q,lbs,e1) ->
        let let_doc =
          let uu____2844 = str "let" in
          let uu____2845 = p_letqualifier q in
          FStar_Pprint.op_Hat_Hat uu____2844 uu____2845 in
        let uu____2846 =
          let uu____2847 =
            let uu____2848 =
              let uu____2849 = str "and" in
              precede_break_separate_map let_doc uu____2849 p_letbinding lbs in
            let uu____2852 = str "in" in
            FStar_Pprint.op_Hat_Slash_Hat uu____2848 uu____2852 in
          FStar_Pprint.group uu____2847 in
        let uu____2853 = p_term e1 in
        FStar_Pprint.op_Hat_Slash_Hat uu____2846 uu____2853
    | FStar_Parser_AST.Abs
        ({ FStar_Parser_AST.pat = FStar_Parser_AST.PatVar (x,typ_opt);
           FStar_Parser_AST.prange = uu____2856;_}::[],{
                                                         FStar_Parser_AST.tm
                                                           =
                                                           FStar_Parser_AST.Match
                                                           (maybe_x,branches);
                                                         FStar_Parser_AST.range
                                                           = uu____2859;
                                                         FStar_Parser_AST.level
                                                           = uu____2860;_})
        when matches_var maybe_x x ->
        let uu____2874 =
          let uu____2875 = str "function" in
          let uu____2876 =
            FStar_Pprint.separate_map FStar_Pprint.hardline p_patternBranch
              branches in
          FStar_Pprint.op_Hat_Slash_Hat uu____2875 uu____2876 in
        FStar_Pprint.group uu____2874
    | FStar_Parser_AST.Assign (id,e1) ->
        let uu____2883 =
          let uu____2884 = p_lident id in
          let uu____2885 =
            let uu____2886 = p_noSeqTerm e1 in
            FStar_Pprint.op_Hat_Slash_Hat FStar_Pprint.larrow uu____2886 in
          FStar_Pprint.op_Hat_Slash_Hat uu____2884 uu____2885 in
        FStar_Pprint.group uu____2883
    | uu____2887 -> p_typ e
and p_typ: FStar_Parser_AST.term -> FStar_Pprint.document =
  fun e  -> with_comment p_typ' e e.FStar_Parser_AST.range
and p_typ': FStar_Parser_AST.term -> FStar_Pprint.document =
  fun e  ->
    let uu____2890 =
      let uu____2891 = unparen e in uu____2891.FStar_Parser_AST.tm in
    match uu____2890 with
    | FStar_Parser_AST.QForall (bs,trigger,e1)|FStar_Parser_AST.QExists
      (bs,trigger,e1) ->
        let uu____2907 =
          let uu____2908 =
            let uu____2909 = p_quantifier e in
            FStar_Pprint.op_Hat_Hat uu____2909 FStar_Pprint.space in
          let uu____2910 = p_binders true bs in
          FStar_Pprint.soft_surround (Prims.parse_int "2")
            (Prims.parse_int "0") uu____2908 uu____2910 FStar_Pprint.dot in
        let uu____2911 =
          let uu____2912 = p_trigger trigger in
          let uu____2913 = p_noSeqTerm e1 in
          FStar_Pprint.op_Hat_Hat uu____2912 uu____2913 in
        prefix2 uu____2907 uu____2911
    | uu____2914 -> p_simpleTerm e
and p_quantifier: FStar_Parser_AST.term -> FStar_Pprint.document =
  fun e  ->
    let uu____2916 =
      let uu____2917 = unparen e in uu____2917.FStar_Parser_AST.tm in
    match uu____2916 with
    | FStar_Parser_AST.QForall uu____2918 -> str "forall"
    | FStar_Parser_AST.QExists uu____2925 -> str "exists"
    | uu____2932 ->
        failwith "Imposible : p_quantifier called on a non-quantifier term"
and p_trigger:
  FStar_Parser_AST.term Prims.list Prims.list -> FStar_Pprint.document =
  fun uu___133_2933  ->
    match uu___133_2933 with
    | [] -> FStar_Pprint.empty
    | pats ->
        let uu____2940 =
          let uu____2941 =
            let uu____2942 = str "pattern" in
            let uu____2943 =
              let uu____2944 =
                let uu____2945 = p_disjunctivePats pats in jump2 uu____2945 in
              let uu____2946 =
                FStar_Pprint.op_Hat_Hat FStar_Pprint.rbrace break1 in
              FStar_Pprint.op_Hat_Slash_Hat uu____2944 uu____2946 in
            FStar_Pprint.op_Hat_Slash_Hat uu____2942 uu____2943 in
          FStar_Pprint.op_Hat_Hat FStar_Pprint.colon uu____2941 in
        FStar_Pprint.op_Hat_Hat FStar_Pprint.lbrace uu____2940
and p_disjunctivePats:
  FStar_Parser_AST.term Prims.list Prims.list -> FStar_Pprint.document =
  fun pats  ->
    let uu____2950 = str "\\/" in
    FStar_Pprint.separate_map uu____2950 p_conjunctivePats pats
and p_conjunctivePats:
  FStar_Parser_AST.term Prims.list -> FStar_Pprint.document =
  fun pats  ->
    let uu____2954 =
      FStar_Pprint.separate_map FStar_Pprint.semi p_appTerm pats in
    FStar_Pprint.group uu____2954
and p_simpleTerm: FStar_Parser_AST.term -> FStar_Pprint.document =
  fun e  ->
    let uu____2956 =
      let uu____2957 = unparen e in uu____2957.FStar_Parser_AST.tm in
    match uu____2956 with
    | FStar_Parser_AST.Abs (pats,e1) ->
        let uu____2962 =
          let uu____2963 = str "fun" in
          let uu____2964 =
            let uu____2965 =
              FStar_Pprint.separate_map break1 p_atomicPattern pats in
            FStar_Pprint.op_Hat_Slash_Hat uu____2965 FStar_Pprint.rarrow in
          op_Hat_Slash_Plus_Hat uu____2963 uu____2964 in
        let uu____2966 = p_term e1 in
        op_Hat_Slash_Plus_Hat uu____2962 uu____2966
    | uu____2967 -> p_tmIff e
and p_maybeFocusArrow: Prims.bool -> FStar_Pprint.document =
  fun b  -> if b then str "~>" else FStar_Pprint.rarrow
and p_patternBranch:
  (FStar_Parser_AST.pattern* FStar_Parser_AST.term Prims.option*
    FStar_Parser_AST.term) -> FStar_Pprint.document
  =
  fun uu____2970  ->
    match uu____2970 with
    | (pat,when_opt,e) ->
        let maybe_paren =
          let uu____2983 =
            let uu____2984 = unparen e in uu____2984.FStar_Parser_AST.tm in
          match uu____2983 with
          | FStar_Parser_AST.Match _|FStar_Parser_AST.TryWith _ ->
              soft_begin_end_with_nesting
          | FStar_Parser_AST.Abs
              ({
                 FStar_Parser_AST.pat = FStar_Parser_AST.PatVar
                   (x,uu____2990);
                 FStar_Parser_AST.prange = uu____2991;_}::[],{
                                                               FStar_Parser_AST.tm
                                                                 =
                                                                 FStar_Parser_AST.Match
                                                                 (maybe_x,uu____2993);
                                                               FStar_Parser_AST.range
                                                                 = uu____2994;
                                                               FStar_Parser_AST.level
                                                                 = uu____2995;_})
              when matches_var maybe_x x -> soft_begin_end_with_nesting
          | uu____3009 -> (fun x  -> x) in
        let uu____3011 =
          let uu____3012 =
            let uu____3013 =
              let uu____3014 =
                let uu____3015 =
                  let uu____3016 = p_disjunctivePattern pat in
                  let uu____3017 =
                    let uu____3018 = p_maybeWhen when_opt in
                    FStar_Pprint.op_Hat_Hat uu____3018 FStar_Pprint.rarrow in
                  op_Hat_Slash_Plus_Hat uu____3016 uu____3017 in
                FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____3015 in
              FStar_Pprint.op_Hat_Hat FStar_Pprint.bar uu____3014 in
            FStar_Pprint.group uu____3013 in
          let uu____3019 =
            let uu____3020 = p_term e in maybe_paren uu____3020 in
          op_Hat_Slash_Plus_Hat uu____3012 uu____3019 in
        FStar_Pprint.group uu____3011
and p_maybeWhen: FStar_Parser_AST.term Prims.option -> FStar_Pprint.document
  =
  fun uu___134_3021  ->
    match uu___134_3021 with
    | None  -> FStar_Pprint.empty
    | Some e ->
        let uu____3024 = str "when" in
        let uu____3025 =
          let uu____3026 = p_tmFormula e in
          FStar_Pprint.op_Hat_Hat uu____3026 FStar_Pprint.space in
        op_Hat_Slash_Plus_Hat uu____3024 uu____3025
and p_tmIff: FStar_Parser_AST.term -> FStar_Pprint.document =
  fun e  ->
    let uu____3028 =
      let uu____3029 = unparen e in uu____3029.FStar_Parser_AST.tm in
    match uu____3028 with
    | FStar_Parser_AST.Op
        ({ FStar_Ident.idText = "<==>"; FStar_Ident.idRange = uu____3030;_},e1::e2::[])
        ->
        let uu____3034 = str "<==>" in
        let uu____3035 = p_tmImplies e1 in
        let uu____3036 = p_tmIff e2 in
        infix0 uu____3034 uu____3035 uu____3036
    | uu____3037 -> p_tmImplies e
and p_tmImplies: FStar_Parser_AST.term -> FStar_Pprint.document =
  fun e  ->
    let uu____3039 =
      let uu____3040 = unparen e in uu____3040.FStar_Parser_AST.tm in
    match uu____3039 with
    | FStar_Parser_AST.Op
        ({ FStar_Ident.idText = "==>"; FStar_Ident.idRange = uu____3041;_},e1::e2::[])
        ->
        let uu____3045 = str "==>" in
        let uu____3046 = p_tmArrow p_tmFormula e1 in
        let uu____3047 = p_tmImplies e2 in
        infix0 uu____3045 uu____3046 uu____3047
    | uu____3048 -> p_tmArrow p_tmFormula e
and p_tmArrow:
  (FStar_Parser_AST.term -> FStar_Pprint.document) ->
    FStar_Parser_AST.term -> FStar_Pprint.document
  =
  fun p_Tm  ->
    fun e  ->
      let uu____3053 =
        let uu____3054 = unparen e in uu____3054.FStar_Parser_AST.tm in
      match uu____3053 with
      | FStar_Parser_AST.Product (bs,tgt) ->
          let uu____3059 =
            let uu____3060 =
              FStar_Pprint.concat_map
                (fun b  ->
                   let uu____3062 = p_binder false b in
                   let uu____3063 =
                     let uu____3064 =
                       FStar_Pprint.op_Hat_Hat FStar_Pprint.rarrow break1 in
                     FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____3064 in
                   FStar_Pprint.op_Hat_Hat uu____3062 uu____3063) bs in
            let uu____3065 = p_tmArrow p_Tm tgt in
            FStar_Pprint.op_Hat_Hat uu____3060 uu____3065 in
          FStar_Pprint.group uu____3059
      | uu____3066 -> p_Tm e
and p_tmFormula: FStar_Parser_AST.term -> FStar_Pprint.document =
  fun e  ->
    let uu____3068 =
      let uu____3069 = unparen e in uu____3069.FStar_Parser_AST.tm in
    match uu____3068 with
    | FStar_Parser_AST.Op
        ({ FStar_Ident.idText = "\\/"; FStar_Ident.idRange = uu____3070;_},e1::e2::[])
        ->
        let uu____3074 = str "\\/" in
        let uu____3075 = p_tmFormula e1 in
        let uu____3076 = p_tmConjunction e2 in
        infix0 uu____3074 uu____3075 uu____3076
    | uu____3077 -> p_tmConjunction e
and p_tmConjunction: FStar_Parser_AST.term -> FStar_Pprint.document =
  fun e  ->
    let uu____3079 =
      let uu____3080 = unparen e in uu____3080.FStar_Parser_AST.tm in
    match uu____3079 with
    | FStar_Parser_AST.Op
        ({ FStar_Ident.idText = "/\\"; FStar_Ident.idRange = uu____3081;_},e1::e2::[])
        ->
        let uu____3085 = str "/\\" in
        let uu____3086 = p_tmConjunction e1 in
        let uu____3087 = p_tmTuple e2 in
        infix0 uu____3085 uu____3086 uu____3087
    | uu____3088 -> p_tmTuple e
and p_tmTuple: FStar_Parser_AST.term -> FStar_Pprint.document =
  fun e  -> with_comment p_tmTuple' e e.FStar_Parser_AST.range
and p_tmTuple': FStar_Parser_AST.term -> FStar_Pprint.document =
  fun e  ->
    let uu____3091 =
      let uu____3092 = unparen e in uu____3092.FStar_Parser_AST.tm in
    match uu____3091 with
    | FStar_Parser_AST.Construct (lid,args) when is_tuple_constructor lid ->
        let uu____3101 = FStar_Pprint.op_Hat_Hat FStar_Pprint.comma break1 in
        FStar_Pprint.separate_map uu____3101
          (fun uu____3104  ->
             match uu____3104 with | (e1,uu____3108) -> p_tmEq e1) args
    | uu____3109 -> p_tmEq e
and paren_if:
  Prims.int -> Prims.int -> FStar_Pprint.document -> FStar_Pprint.document =
  fun curr  ->
    fun mine  ->
      fun doc1  ->
        if mine <= curr
        then doc1
        else
          (let uu____3114 =
             let uu____3115 =
               FStar_Pprint.op_Hat_Hat doc1 FStar_Pprint.rparen in
             FStar_Pprint.op_Hat_Hat FStar_Pprint.lparen uu____3115 in
           FStar_Pprint.group uu____3114)
and p_tmEq: FStar_Parser_AST.term -> FStar_Pprint.document =
  fun e  ->
    let n1 =
      max_level
        (FStar_List.append [colon_equals (); pipe_right ()]
           (operatorInfix0ad12 ())) in
    p_tmEq' n1 e
and p_tmEq': Prims.int -> FStar_Parser_AST.term -> FStar_Pprint.document =
  fun curr  ->
    fun e  ->
      let uu____3140 =
        let uu____3141 = unparen e in uu____3141.FStar_Parser_AST.tm in
      match uu____3140 with
      | FStar_Parser_AST.Op (op,e1::e2::[]) when
          ((is_operatorInfix0ad12 op) || ((FStar_Ident.text_of_id op) = "="))
            || ((FStar_Ident.text_of_id op) = "|>")
          ->
          let op1 = FStar_Ident.text_of_id op in
          let uu____3147 = levels op1 in
          (match uu____3147 with
           | (left1,mine,right1) ->
               let uu____3154 =
                 let uu____3155 = FStar_All.pipe_left str op1 in
                 let uu____3156 = p_tmEq' left1 e1 in
                 let uu____3157 = p_tmEq' right1 e2 in
                 infix0 uu____3155 uu____3156 uu____3157 in
               paren_if curr mine uu____3154)
      | FStar_Parser_AST.Op
          ({ FStar_Ident.idText = ":="; FStar_Ident.idRange = uu____3158;_},e1::e2::[])
          ->
          let uu____3162 =
            let uu____3163 = p_tmEq e1 in
            let uu____3164 =
              let uu____3165 =
                let uu____3166 =
                  let uu____3167 = p_tmEq e2 in
                  op_Hat_Slash_Plus_Hat FStar_Pprint.equals uu____3167 in
                FStar_Pprint.op_Hat_Hat FStar_Pprint.colon uu____3166 in
              FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____3165 in
            FStar_Pprint.op_Hat_Hat uu____3163 uu____3164 in
          FStar_Pprint.group uu____3162
      | uu____3168 -> p_tmNoEq e
and p_tmNoEq: FStar_Parser_AST.term -> FStar_Pprint.document =
  fun e  ->
    let n1 = max_level [colon_colon (); amp (); opinfix3 (); opinfix4 ()] in
    p_tmNoEq' n1 e
and p_tmNoEq': Prims.int -> FStar_Parser_AST.term -> FStar_Pprint.document =
  fun curr  ->
    fun e  ->
      let uu____3198 =
        let uu____3199 = unparen e in uu____3199.FStar_Parser_AST.tm in
      match uu____3198 with
      | FStar_Parser_AST.Construct (lid,(e1,uu____3202)::(e2,uu____3204)::[])
          when
          (FStar_Ident.lid_equals lid FStar_Syntax_Const.cons_lid) &&
            (let uu____3214 = is_list e in Prims.op_Negation uu____3214)
          ->
          let op = "::" in
          let uu____3216 = levels op in
          (match uu____3216 with
           | (left1,mine,right1) ->
               let uu____3223 =
                 let uu____3224 = str op in
                 let uu____3225 = p_tmNoEq' left1 e1 in
                 let uu____3226 = p_tmNoEq' right1 e2 in
                 infix0 uu____3224 uu____3225 uu____3226 in
               paren_if curr mine uu____3223)
      | FStar_Parser_AST.Sum (binders,res) ->
          let op = "&" in
          let uu____3232 = levels op in
          (match uu____3232 with
           | (left1,mine,right1) ->
               let p_dsumfst b =
                 let uu____3243 = p_binder false b in
                 let uu____3244 =
                   let uu____3245 =
                     let uu____3246 = str op in
                     FStar_Pprint.op_Hat_Hat uu____3246 break1 in
                   FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____3245 in
                 FStar_Pprint.op_Hat_Hat uu____3243 uu____3244 in
               let uu____3247 =
                 let uu____3248 = FStar_Pprint.concat_map p_dsumfst binders in
                 let uu____3249 = p_tmNoEq' right1 res in
                 FStar_Pprint.op_Hat_Hat uu____3248 uu____3249 in
               paren_if curr mine uu____3247)
      | FStar_Parser_AST.Op (op,e1::e2::[]) when is_operatorInfix34 op ->
          let op1 = FStar_Ident.text_of_id op in
          let uu____3255 = levels op1 in
          (match uu____3255 with
           | (left1,mine,right1) ->
               let uu____3262 =
                 let uu____3263 = str op1 in
                 let uu____3264 = p_tmNoEq' left1 e1 in
                 let uu____3265 = p_tmNoEq' right1 e2 in
                 infix0 uu____3263 uu____3264 uu____3265 in
               paren_if curr mine uu____3262)
      | FStar_Parser_AST.Op
          ({ FStar_Ident.idText = "-"; FStar_Ident.idRange = uu____3266;_},e1::[])
          ->
          let uu____3269 = levels "-" in
          (match uu____3269 with
           | (left1,mine,right1) ->
               let uu____3276 = p_tmNoEq' mine e1 in
               FStar_Pprint.op_Hat_Slash_Hat FStar_Pprint.minus uu____3276)
      | FStar_Parser_AST.NamedTyp (lid,e1) ->
          let uu____3279 =
            let uu____3280 = p_lidentOrUnderscore lid in
            let uu____3281 =
              let uu____3282 = p_appTerm e1 in
              FStar_Pprint.op_Hat_Slash_Hat FStar_Pprint.colon uu____3282 in
            FStar_Pprint.op_Hat_Slash_Hat uu____3280 uu____3281 in
          FStar_Pprint.group uu____3279
      | FStar_Parser_AST.Refine (b,phi) -> p_refinedBinder b phi
      | FStar_Parser_AST.Record (with_opt,record_fields) ->
          let uu____3295 =
            let uu____3296 =
              default_or_map FStar_Pprint.empty p_with_clause with_opt in
            let uu____3297 =
              let uu____3298 =
                FStar_Pprint.op_Hat_Hat FStar_Pprint.semi break1 in
              FStar_Pprint.separate_map uu____3298 p_simpleDef record_fields in
            FStar_Pprint.op_Hat_Hat uu____3296 uu____3297 in
          braces_with_nesting uu____3295
      | FStar_Parser_AST.Op
          ({ FStar_Ident.idText = "~"; FStar_Ident.idRange = uu____3301;_},e1::[])
          ->
          let uu____3304 =
            let uu____3305 = str "~" in
            let uu____3306 = p_atomicTerm e1 in
            FStar_Pprint.op_Hat_Hat uu____3305 uu____3306 in
          FStar_Pprint.group uu____3304
      | uu____3307 -> p_appTerm e
and p_with_clause: FStar_Parser_AST.term -> FStar_Pprint.document =
  fun e  ->
    let uu____3309 = p_appTerm e in
    let uu____3310 =
      let uu____3311 =
        let uu____3312 = str "with" in
        FStar_Pprint.op_Hat_Hat uu____3312 break1 in
      FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____3311 in
    FStar_Pprint.op_Hat_Hat uu____3309 uu____3310
and p_refinedBinder:
  FStar_Parser_AST.binder -> FStar_Parser_AST.term -> FStar_Pprint.document =
  fun b  ->
    fun phi  ->
      match b.FStar_Parser_AST.b with
      | FStar_Parser_AST.Annotated (lid,t) ->
          let uu____3317 =
            let uu____3318 = p_lident lid in
            p_refinement b.FStar_Parser_AST.aqual uu____3318 t phi in
          soft_parens_with_nesting uu____3317
      | FStar_Parser_AST.TAnnotated uu____3319 ->
          failwith "Is this still used ?"
      | FStar_Parser_AST.Variable _
        |FStar_Parser_AST.TVariable _|FStar_Parser_AST.NoName _ ->
          let uu____3325 =
            let uu____3326 = FStar_Parser_AST.binder_to_string b in
            FStar_Util.format1
              "Imposible : a refined binder ought to be annotated %s"
              uu____3326 in
          failwith uu____3325
and p_simpleDef:
  (FStar_Ident.lid* FStar_Parser_AST.term) -> FStar_Pprint.document =
  fun uu____3327  ->
    match uu____3327 with
    | (lid,e) ->
        let uu____3332 =
          let uu____3333 = p_qlident lid in
          let uu____3334 =
            let uu____3335 = p_tmIff e in
            FStar_Pprint.op_Hat_Slash_Hat FStar_Pprint.equals uu____3335 in
          FStar_Pprint.op_Hat_Slash_Hat uu____3333 uu____3334 in
        FStar_Pprint.group uu____3332
and p_appTerm: FStar_Parser_AST.term -> FStar_Pprint.document =
  fun e  ->
    let uu____3337 =
      let uu____3338 = unparen e in uu____3338.FStar_Parser_AST.tm in
    match uu____3337 with
    | FStar_Parser_AST.App uu____3339 when is_general_application e ->
        let uu____3343 = head_and_args e in
        (match uu____3343 with
         | (head1,args) ->
             let uu____3357 =
               let uu____3363 = FStar_ST.read should_print_fs_typ_app in
               if uu____3363
               then
                 let uu____3371 =
                   FStar_Util.take
                     (fun uu____3382  ->
                        match uu____3382 with
                        | (uu____3385,aq) -> aq = FStar_Parser_AST.FsTypApp)
                     args in
                 match uu____3371 with
                 | (fs_typ_args,args1) ->
                     let uu____3406 =
                       let uu____3407 = p_indexingTerm head1 in
                       let uu____3408 =
                         let uu____3409 =
                           FStar_Pprint.op_Hat_Hat FStar_Pprint.comma break1 in
                         soft_surround_separate_map (Prims.parse_int "2")
                           (Prims.parse_int "0") FStar_Pprint.empty
                           FStar_Pprint.langle uu____3409 FStar_Pprint.rangle
                           p_fsTypArg fs_typ_args in
                       FStar_Pprint.op_Hat_Hat uu____3407 uu____3408 in
                     (uu____3406, args1)
               else
                 (let uu____3416 = p_indexingTerm head1 in (uu____3416, args)) in
             (match uu____3357 with
              | (head_doc,args1) ->
                  let uu____3428 =
                    let uu____3429 =
                      FStar_Pprint.op_Hat_Hat head_doc FStar_Pprint.space in
                    soft_surround_separate_map (Prims.parse_int "2")
                      (Prims.parse_int "0") head_doc uu____3429 break1
                      FStar_Pprint.empty p_argTerm args1 in
                  FStar_Pprint.group uu____3428))
    | FStar_Parser_AST.Construct (lid,args) when
        (is_general_construction e) &&
          (Prims.op_Negation (is_dtuple_constructor lid))
        ->
        (match args with
         | [] -> p_quident lid
         | arg::[] ->
             let uu____3449 =
               let uu____3450 = p_quident lid in
               let uu____3451 = p_argTerm arg in
               FStar_Pprint.op_Hat_Slash_Hat uu____3450 uu____3451 in
             FStar_Pprint.group uu____3449
         | hd1::tl1 ->
             let uu____3461 =
               let uu____3462 =
                 let uu____3463 =
                   let uu____3464 = p_quident lid in
                   let uu____3465 = p_argTerm hd1 in
                   prefix2 uu____3464 uu____3465 in
                 FStar_Pprint.group uu____3463 in
               let uu____3466 =
                 let uu____3467 =
                   FStar_Pprint.separate_map break1 p_argTerm tl1 in
                 jump2 uu____3467 in
               FStar_Pprint.op_Hat_Hat uu____3462 uu____3466 in
             FStar_Pprint.group uu____3461)
    | uu____3470 -> p_indexingTerm e
and p_argTerm:
  (FStar_Parser_AST.term* FStar_Parser_AST.imp) -> FStar_Pprint.document =
  fun arg_imp  ->
    match arg_imp with
    | ({ FStar_Parser_AST.tm = FStar_Parser_AST.Uvar uu____3474;
         FStar_Parser_AST.range = uu____3475;
         FStar_Parser_AST.level = uu____3476;_},FStar_Parser_AST.UnivApp
       ) -> p_univar (Prims.fst arg_imp)
    | (u,FStar_Parser_AST.UnivApp ) -> p_universe u
    | (e,FStar_Parser_AST.FsTypApp ) ->
        (FStar_Util.print_warning
           "Unexpected FsTypApp, output might not be formatted correctly.\n";
         (let uu____3480 = p_indexingTerm e in
          FStar_Pprint.surround (Prims.parse_int "2") (Prims.parse_int "1")
            FStar_Pprint.langle uu____3480 FStar_Pprint.rangle))
    | (e,FStar_Parser_AST.Hash ) ->
        let uu____3482 = str "#" in
        let uu____3483 = p_indexingTerm e in
        FStar_Pprint.op_Hat_Hat uu____3482 uu____3483
    | (e,FStar_Parser_AST.Nothing ) -> p_indexingTerm e
and p_fsTypArg:
  (FStar_Parser_AST.term* FStar_Parser_AST.imp) -> FStar_Pprint.document =
  fun uu____3485  ->
    match uu____3485 with | (e,uu____3489) -> p_indexingTerm e
and p_indexingTerm_aux:
  (FStar_Parser_AST.term -> FStar_Pprint.document) ->
    FStar_Parser_AST.term -> FStar_Pprint.document
  =
  fun exit1  ->
    fun e  ->
      let uu____3494 =
        let uu____3495 = unparen e in uu____3495.FStar_Parser_AST.tm in
      match uu____3494 with
      | FStar_Parser_AST.Op
          ({ FStar_Ident.idText = ".()"; FStar_Ident.idRange = uu____3496;_},e1::e2::[])
          ->
          let uu____3500 =
            let uu____3501 = p_indexingTerm_aux p_atomicTermNotQUident e1 in
            let uu____3502 =
              let uu____3503 =
                let uu____3504 = p_term e2 in
                soft_parens_with_nesting uu____3504 in
              FStar_Pprint.op_Hat_Hat FStar_Pprint.dot uu____3503 in
            FStar_Pprint.op_Hat_Hat uu____3501 uu____3502 in
          FStar_Pprint.group uu____3500
      | FStar_Parser_AST.Op
          ({ FStar_Ident.idText = ".[]"; FStar_Ident.idRange = uu____3505;_},e1::e2::[])
          ->
          let uu____3509 =
            let uu____3510 = p_indexingTerm_aux p_atomicTermNotQUident e1 in
            let uu____3511 =
              let uu____3512 =
                let uu____3513 = p_term e2 in
                soft_brackets_with_nesting uu____3513 in
              FStar_Pprint.op_Hat_Hat FStar_Pprint.dot uu____3512 in
            FStar_Pprint.op_Hat_Hat uu____3510 uu____3511 in
          FStar_Pprint.group uu____3509
      | uu____3514 -> exit1 e
and p_indexingTerm: FStar_Parser_AST.term -> FStar_Pprint.document =
  fun e  -> p_indexingTerm_aux p_atomicTerm e
and p_atomicTerm: FStar_Parser_AST.term -> FStar_Pprint.document =
  fun e  ->
    let uu____3517 =
      let uu____3518 = unparen e in uu____3518.FStar_Parser_AST.tm in
    match uu____3517 with
    | FStar_Parser_AST.LetOpen (lid,e1) ->
        let uu____3521 = p_quident lid in
        let uu____3522 =
          let uu____3523 =
            let uu____3524 = p_term e1 in soft_parens_with_nesting uu____3524 in
          FStar_Pprint.op_Hat_Hat FStar_Pprint.dot uu____3523 in
        FStar_Pprint.op_Hat_Hat uu____3521 uu____3522
    | FStar_Parser_AST.Name lid -> p_quident lid
    | FStar_Parser_AST.Op (op,e1::[]) when is_general_prefix_op op ->
        let uu____3529 = str (FStar_Ident.text_of_id op) in
        let uu____3530 = p_atomicTerm e1 in
        FStar_Pprint.op_Hat_Hat uu____3529 uu____3530
    | uu____3531 -> p_atomicTermNotQUident e
and p_atomicTermNotQUident: FStar_Parser_AST.term -> FStar_Pprint.document =
  fun e  ->
    let uu____3533 =
      let uu____3534 = unparen e in uu____3534.FStar_Parser_AST.tm in
    match uu____3533 with
    | FStar_Parser_AST.Wild  -> FStar_Pprint.underscore
    | FStar_Parser_AST.Var lid when
        FStar_Ident.lid_equals lid FStar_Syntax_Const.assert_lid ->
        str "assert"
    | FStar_Parser_AST.Tvar tv -> p_tvar tv
    | FStar_Parser_AST.Const c -> p_constant c
    | FStar_Parser_AST.Name lid when
        FStar_Ident.lid_equals lid FStar_Syntax_Const.true_lid -> str "True"
    | FStar_Parser_AST.Name lid when
        FStar_Ident.lid_equals lid FStar_Syntax_Const.false_lid ->
        str "False"
    | FStar_Parser_AST.Op (op,e1::[]) when is_general_prefix_op op ->
        let uu____3543 = str (FStar_Ident.text_of_id op) in
        let uu____3544 = p_atomicTermNotQUident e1 in
        FStar_Pprint.op_Hat_Hat uu____3543 uu____3544
    | FStar_Parser_AST.Op (op,[]) ->
        let uu____3547 =
          let uu____3548 =
            let uu____3549 = str (FStar_Ident.text_of_id op) in
            let uu____3550 =
              FStar_Pprint.op_Hat_Hat FStar_Pprint.space FStar_Pprint.rparen in
            FStar_Pprint.op_Hat_Hat uu____3549 uu____3550 in
          FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____3548 in
        FStar_Pprint.op_Hat_Hat FStar_Pprint.lparen uu____3547
    | FStar_Parser_AST.Construct (lid,args) when is_dtuple_constructor lid ->
        let uu____3559 =
          FStar_Pprint.op_Hat_Hat FStar_Pprint.lparen FStar_Pprint.bar in
        let uu____3560 =
          let uu____3561 = FStar_Pprint.op_Hat_Hat FStar_Pprint.comma break1 in
          let uu____3562 = FStar_List.map Prims.fst args in
          FStar_Pprint.separate_map uu____3561 p_tmEq uu____3562 in
        let uu____3566 =
          FStar_Pprint.op_Hat_Hat FStar_Pprint.bar FStar_Pprint.rparen in
        FStar_Pprint.surround (Prims.parse_int "2") (Prims.parse_int "1")
          uu____3559 uu____3560 uu____3566
    | FStar_Parser_AST.Project (e1,lid) ->
        let uu____3569 =
          let uu____3570 = p_atomicTermNotQUident e1 in
          let uu____3571 =
            let uu____3572 = p_qlident lid in
            FStar_Pprint.op_Hat_Hat FStar_Pprint.dot uu____3572 in
          FStar_Pprint.prefix (Prims.parse_int "2") (Prims.parse_int "0")
            uu____3570 uu____3571 in
        FStar_Pprint.group uu____3569
    | uu____3573 -> p_projectionLHS e
and p_projectionLHS: FStar_Parser_AST.term -> FStar_Pprint.document =
  fun e  ->
    let uu____3575 =
      let uu____3576 = unparen e in uu____3576.FStar_Parser_AST.tm in
    match uu____3575 with
    | FStar_Parser_AST.Var lid -> p_qlident lid
    | FStar_Parser_AST.Projector (constr_lid,field_lid) ->
        let uu____3580 = p_quident constr_lid in
        let uu____3581 =
          let uu____3582 =
            let uu____3583 = p_lident field_lid in
            FStar_Pprint.op_Hat_Hat FStar_Pprint.dot uu____3583 in
          FStar_Pprint.op_Hat_Hat FStar_Pprint.qmark uu____3582 in
        FStar_Pprint.op_Hat_Hat uu____3580 uu____3581
    | FStar_Parser_AST.Discrim constr_lid ->
        let uu____3585 = p_quident constr_lid in
        FStar_Pprint.op_Hat_Hat uu____3585 FStar_Pprint.qmark
    | FStar_Parser_AST.Paren e1 ->
        let uu____3587 = p_term e1 in soft_parens_with_nesting uu____3587
    | uu____3588 when is_array e ->
        let es = extract_from_list e in
        let uu____3591 =
          FStar_Pprint.op_Hat_Hat FStar_Pprint.lbracket FStar_Pprint.bar in
        let uu____3592 =
          let uu____3593 = FStar_Pprint.op_Hat_Hat FStar_Pprint.semi break1 in
          separate_map_or_flow uu____3593 p_noSeqTerm es in
        let uu____3594 =
          FStar_Pprint.op_Hat_Hat FStar_Pprint.bar FStar_Pprint.rbracket in
        FStar_Pprint.surround (Prims.parse_int "2") (Prims.parse_int "0")
          uu____3591 uu____3592 uu____3594
    | uu____3595 when is_list e ->
        let uu____3596 =
          let uu____3597 = FStar_Pprint.op_Hat_Hat FStar_Pprint.semi break1 in
          let uu____3598 = extract_from_list e in
          separate_map_or_flow uu____3597 p_noSeqTerm uu____3598 in
        FStar_Pprint.surround (Prims.parse_int "2") (Prims.parse_int "0")
          FStar_Pprint.lbracket uu____3596 FStar_Pprint.rbracket
    | uu____3600 when is_lex_list e ->
        let uu____3601 =
          FStar_Pprint.op_Hat_Hat FStar_Pprint.percent FStar_Pprint.lbracket in
        let uu____3602 =
          let uu____3603 = FStar_Pprint.op_Hat_Hat FStar_Pprint.semi break1 in
          let uu____3604 = extract_from_list e in
          separate_map_or_flow uu____3603 p_noSeqTerm uu____3604 in
        FStar_Pprint.surround (Prims.parse_int "2") (Prims.parse_int "1")
          uu____3601 uu____3602 FStar_Pprint.rbracket
    | uu____3606 when is_ref_set e ->
        let es = extract_from_ref_set e in
        let uu____3609 =
          FStar_Pprint.op_Hat_Hat FStar_Pprint.bang FStar_Pprint.lbrace in
        let uu____3610 =
          let uu____3611 = FStar_Pprint.op_Hat_Hat FStar_Pprint.comma break1 in
          separate_map_or_flow uu____3611 p_appTerm es in
        FStar_Pprint.surround (Prims.parse_int "2") (Prims.parse_int "0")
          uu____3609 uu____3610 FStar_Pprint.rbrace
    | FStar_Parser_AST.Op (op,args) when
        let uu____3616 = handleable_op op args in
        Prims.op_Negation uu____3616 ->
        let uu____3617 =
          let uu____3618 =
            let uu____3619 =
              let uu____3620 =
                let uu____3621 =
                  FStar_Util.string_of_int (FStar_List.length args) in
                Prims.strcat uu____3621
                  " arguments couldn't be handled by the pretty printer" in
              Prims.strcat " with " uu____3620 in
            Prims.strcat (FStar_Ident.text_of_id op) uu____3619 in
          Prims.strcat "Operation " uu____3618 in
        failwith uu____3617
    | FStar_Parser_AST.Uvar uu____3625 ->
        failwith "Unexpected universe variable out of universe context"
    | FStar_Parser_AST.Labeled uu____3626 -> failwith "Not valid in universe"
    | FStar_Parser_AST.Wild 
      |FStar_Parser_AST.Const _
       |FStar_Parser_AST.Op _
        |FStar_Parser_AST.Tvar _
         |FStar_Parser_AST.Var _
          |FStar_Parser_AST.Name _
           |FStar_Parser_AST.Construct _
            |FStar_Parser_AST.Abs _
             |FStar_Parser_AST.App _
              |FStar_Parser_AST.Let _
               |FStar_Parser_AST.LetOpen _
                |FStar_Parser_AST.Seq _
                 |FStar_Parser_AST.Bind _
                  |FStar_Parser_AST.If _
                   |FStar_Parser_AST.Match _
                    |FStar_Parser_AST.TryWith _
                     |FStar_Parser_AST.Ascribed _
                      |FStar_Parser_AST.Record _
                       |FStar_Parser_AST.Project _
                        |FStar_Parser_AST.Product _
                         |FStar_Parser_AST.Sum _
                          |FStar_Parser_AST.QForall _
                           |FStar_Parser_AST.QExists _
                            |FStar_Parser_AST.Refine _
                             |FStar_Parser_AST.NamedTyp _
                              |FStar_Parser_AST.Requires _
                               |FStar_Parser_AST.Ensures _
                                |FStar_Parser_AST.Assign _
                                 |FStar_Parser_AST.Attributes _
        -> let uu____3658 = p_term e in soft_parens_with_nesting uu____3658
and p_constant: FStar_Const.sconst -> FStar_Pprint.document =
  fun uu___137_3659  ->
    match uu___137_3659 with
    | FStar_Const.Const_effect  -> str "Effect"
    | FStar_Const.Const_unit  -> str "()"
    | FStar_Const.Const_bool b -> FStar_Pprint.doc_of_bool b
    | FStar_Const.Const_float x -> str (FStar_Util.string_of_float x)
    | FStar_Const.Const_char x ->
        let uu____3663 = FStar_Pprint.doc_of_char x in
        FStar_Pprint.squotes uu____3663
    | FStar_Const.Const_string (bytes,uu____3665) ->
        let uu____3668 = str (FStar_Util.string_of_bytes bytes) in
        FStar_Pprint.dquotes uu____3668
    | FStar_Const.Const_bytearray (bytes,uu____3670) ->
        let uu____3673 =
          let uu____3674 = str (FStar_Util.string_of_bytes bytes) in
          FStar_Pprint.dquotes uu____3674 in
        let uu____3675 = str "B" in
        FStar_Pprint.op_Hat_Hat uu____3673 uu____3675
    | FStar_Const.Const_int (repr,sign_width_opt) ->
        let signedness uu___135_3687 =
          match uu___135_3687 with
          | FStar_Const.Unsigned  -> str "u"
          | FStar_Const.Signed  -> FStar_Pprint.empty in
        let width uu___136_3691 =
          match uu___136_3691 with
          | FStar_Const.Int8  -> str "y"
          | FStar_Const.Int16  -> str "s"
          | FStar_Const.Int32  -> str "l"
          | FStar_Const.Int64  -> str "L" in
        let ending =
          default_or_map FStar_Pprint.empty
            (fun uu____3695  ->
               match uu____3695 with
               | (s,w) ->
                   let uu____3700 = signedness s in
                   let uu____3701 = width w in
                   FStar_Pprint.op_Hat_Hat uu____3700 uu____3701)
            sign_width_opt in
        let uu____3702 = str repr in
        FStar_Pprint.op_Hat_Hat uu____3702 ending
    | FStar_Const.Const_range r ->
        let uu____3704 = FStar_Range.string_of_range r in str uu____3704
    | FStar_Const.Const_reify  -> str "reify"
    | FStar_Const.Const_reflect lid ->
        let uu____3706 = p_quident lid in
        let uu____3707 =
          let uu____3708 =
            let uu____3709 = str "reflect" in
            FStar_Pprint.op_Hat_Hat FStar_Pprint.dot uu____3709 in
          FStar_Pprint.op_Hat_Hat FStar_Pprint.qmark uu____3708 in
        FStar_Pprint.op_Hat_Hat uu____3706 uu____3707
and p_universe: FStar_Parser_AST.term -> FStar_Pprint.document =
  fun u  ->
    let uu____3711 = str "u#" in
    let uu____3712 = p_atomicUniverse u in
    FStar_Pprint.op_Hat_Hat uu____3711 uu____3712
and p_universeFrom: FStar_Parser_AST.term -> FStar_Pprint.document =
  fun u  ->
    let uu____3714 =
      let uu____3715 = unparen u in uu____3715.FStar_Parser_AST.tm in
    match uu____3714 with
    | FStar_Parser_AST.Op
        ({ FStar_Ident.idText = "+"; FStar_Ident.idRange = uu____3716;_},u1::u2::[])
        ->
        let uu____3720 =
          let uu____3721 = p_universeFrom u1 in
          let uu____3722 =
            let uu____3723 = p_universeFrom u2 in
            FStar_Pprint.op_Hat_Slash_Hat FStar_Pprint.plus uu____3723 in
          FStar_Pprint.op_Hat_Slash_Hat uu____3721 uu____3722 in
        FStar_Pprint.group uu____3720
    | FStar_Parser_AST.App uu____3724 ->
        let uu____3728 = head_and_args u in
        (match uu____3728 with
         | (head1,args) ->
             let uu____3742 =
               let uu____3743 = unparen head1 in
               uu____3743.FStar_Parser_AST.tm in
             (match uu____3742 with
              | FStar_Parser_AST.Var maybe_max_lid when
                  FStar_Ident.lid_equals maybe_max_lid
                    FStar_Syntax_Const.max_lid
                  ->
                  let uu____3745 =
                    let uu____3746 = p_qlident FStar_Syntax_Const.max_lid in
                    let uu____3747 =
                      FStar_Pprint.separate_map FStar_Pprint.space
                        (fun uu____3750  ->
                           match uu____3750 with
                           | (u1,uu____3754) -> p_atomicUniverse u1) args in
                    op_Hat_Slash_Plus_Hat uu____3746 uu____3747 in
                  FStar_Pprint.group uu____3745
              | uu____3755 ->
                  let uu____3756 =
                    let uu____3757 = FStar_Parser_AST.term_to_string u in
                    FStar_Util.format1 "Invalid term in universe context %s"
                      uu____3757 in
                  failwith uu____3756))
    | uu____3758 -> p_atomicUniverse u
and p_atomicUniverse: FStar_Parser_AST.term -> FStar_Pprint.document =
  fun u  ->
    let uu____3760 =
      let uu____3761 = unparen u in uu____3761.FStar_Parser_AST.tm in
    match uu____3760 with
    | FStar_Parser_AST.Wild  -> FStar_Pprint.underscore
    | FStar_Parser_AST.Const (FStar_Const.Const_int (r,sw)) ->
        p_constant (FStar_Const.Const_int (r, sw))
    | FStar_Parser_AST.Uvar uu____3773 -> p_univar u
    | FStar_Parser_AST.Paren u1 ->
        let uu____3775 = p_universeFrom u1 in
        soft_parens_with_nesting uu____3775
    | FStar_Parser_AST.Op
      ({ FStar_Ident.idText = "+"; FStar_Ident.idRange = _;_},_::_::[])
      |FStar_Parser_AST.App _ ->
        let uu____3781 = p_universeFrom u in
        soft_parens_with_nesting uu____3781
    | uu____3782 ->
        let uu____3783 =
          let uu____3784 = FStar_Parser_AST.term_to_string u in
          FStar_Util.format1 "Invalid term in universe context %s" uu____3784 in
        failwith uu____3783
and p_univar: FStar_Parser_AST.term -> FStar_Pprint.document =
  fun u  ->
    let uu____3786 =
      let uu____3787 = unparen u in uu____3787.FStar_Parser_AST.tm in
    match uu____3786 with
    | FStar_Parser_AST.Uvar id -> str (FStar_Ident.text_of_id id)
    | uu____3789 ->
        let uu____3790 =
          let uu____3791 = FStar_Parser_AST.term_to_string u in
          FStar_Util.format1 "Not a universe variable %s" uu____3791 in
        failwith uu____3790
let term_to_document: FStar_Parser_AST.term -> FStar_Pprint.document =
  fun e  -> p_term e
let decl_to_document: FStar_Parser_AST.decl -> FStar_Pprint.document =
  fun e  -> p_decl e
let modul_to_document: FStar_Parser_AST.modul -> FStar_Pprint.document =
  fun m  ->
    FStar_ST.write should_print_fs_typ_app false;
    (let res =
       match m with
       | FStar_Parser_AST.Module (_,decls)|FStar_Parser_AST.Interface
         (_,decls,_) ->
           let uu____3813 =
             FStar_All.pipe_right decls (FStar_List.map decl_to_document) in
           FStar_All.pipe_right uu____3813
             (FStar_Pprint.separate FStar_Pprint.hardline) in
     FStar_ST.write should_print_fs_typ_app false; res)
let comments_to_document:
  (Prims.string* FStar_Range.range) Prims.list -> FStar_Pprint.document =
  fun comments  ->
    FStar_Pprint.separate_map FStar_Pprint.hardline
      (fun uu____3832  ->
         match uu____3832 with | (comment,range) -> str comment) comments
let modul_with_comments_to_document:
  FStar_Parser_AST.modul ->
    (Prims.string* FStar_Range.range) Prims.list ->
      (FStar_Pprint.document* (Prims.string* FStar_Range.range) Prims.list)
  =
  fun m  ->
    fun comments  ->
      let decls =
        match m with
        | FStar_Parser_AST.Module (_,decls)|FStar_Parser_AST.Interface
          (_,decls,_) -> decls in
      FStar_ST.write should_print_fs_typ_app false;
      (match decls with
       | [] -> (FStar_Pprint.empty, comments)
       | d::ds ->
           let uu____3879 =
             match ds with
             | {
                 FStar_Parser_AST.d = FStar_Parser_AST.Pragma
                   (FStar_Parser_AST.LightOff );
                 FStar_Parser_AST.drange = uu____3886;
                 FStar_Parser_AST.doc = uu____3887;
                 FStar_Parser_AST.quals = uu____3888;
                 FStar_Parser_AST.attrs = uu____3889;_}::uu____3890 ->
                 let d0 = FStar_List.hd ds in
                 let uu____3894 =
                   let uu____3896 =
                     let uu____3898 = FStar_List.tl ds in d :: uu____3898 in
                   d0 :: uu____3896 in
                 (uu____3894, (d0.FStar_Parser_AST.drange))
             | uu____3901 -> ((d :: ds), (d.FStar_Parser_AST.drange)) in
           (match uu____3879 with
            | (decls1,first_range) ->
                let extract_decl_range d1 = d1.FStar_Parser_AST.drange in
                (FStar_ST.write comment_stack comments;
                 (let initial_comment =
                    let uu____3924 = FStar_Range.start_of_range first_range in
                    place_comments_until_pos (Prims.parse_int "0")
                      (Prims.parse_int "1") uu____3924 FStar_Pprint.empty in
                  let doc1 =
                    separate_map_with_comments FStar_Pprint.empty
                      FStar_Pprint.empty decl_to_document decls1
                      extract_decl_range in
                  let comments1 = FStar_ST.read comment_stack in
                  FStar_ST.write comment_stack [];
                  FStar_ST.write should_print_fs_typ_app false;
                  (let uu____3946 =
                     FStar_Pprint.op_Hat_Hat initial_comment doc1 in
                   (uu____3946, comments1))))))