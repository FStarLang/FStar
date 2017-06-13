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
    (let uu____302 = FStar_Pprint.separate_map sep f xs in
     FStar_Pprint.soft_surround n1 b opening uu____302 closing)
let doc_of_fsdoc:
  (Prims.string* (Prims.string* Prims.string) Prims.list) ->
    FStar_Pprint.document
  =
  fun uu____310  ->
    match uu____310 with
    | (comment,keywords1) ->
        let uu____324 =
          let uu____325 =
            let uu____327 = str comment in
            let uu____328 =
              let uu____330 =
                let uu____332 =
                  FStar_Pprint.separate_map FStar_Pprint.comma
                    (fun uu____335  ->
                       match uu____335 with
                       | (k,v1) ->
                           let uu____340 =
                             let uu____342 = str k in
                             let uu____343 =
                               let uu____345 =
                                 let uu____347 = str v1 in [uu____347] in
                               FStar_Pprint.rarrow :: uu____345 in
                             uu____342 :: uu____343 in
                           FStar_Pprint.concat uu____340) keywords1 in
                [uu____332] in
              FStar_Pprint.space :: uu____330 in
            uu____327 :: uu____328 in
          FStar_Pprint.concat uu____325 in
        FStar_Pprint.group uu____324
let is_unit: FStar_Parser_AST.term -> Prims.bool =
  fun e  ->
    let uu____351 =
      let uu____352 = unparen e in uu____352.FStar_Parser_AST.tm in
    match uu____351 with
    | FStar_Parser_AST.Const (FStar_Const.Const_unit ) -> true
    | uu____353 -> false
let matches_var: FStar_Parser_AST.term -> FStar_Ident.ident -> Prims.bool =
  fun t  ->
    fun x  ->
      let uu____360 =
        let uu____361 = unparen t in uu____361.FStar_Parser_AST.tm in
      match uu____360 with
      | FStar_Parser_AST.Var y ->
          x.FStar_Ident.idText = (FStar_Ident.text_of_lid y)
      | uu____363 -> false
let is_tuple_constructor: FStar_Ident.lident -> Prims.bool =
  FStar_Parser_Const.is_tuple_data_lid'
let is_dtuple_constructor: FStar_Ident.lident -> Prims.bool =
  FStar_Parser_Const.is_dtuple_data_lid'
let is_list_structure:
  FStar_Ident.lident ->
    FStar_Ident.lident -> FStar_Parser_AST.term -> Prims.bool
  =
  fun cons_lid1  ->
    fun nil_lid1  ->
      let rec aux e =
        let uu____380 =
          let uu____381 = unparen e in uu____381.FStar_Parser_AST.tm in
        match uu____380 with
        | FStar_Parser_AST.Construct (lid,[]) ->
            FStar_Ident.lid_equals lid nil_lid1
        | FStar_Parser_AST.Construct (lid,uu____389::(e2,uu____391)::[]) ->
            (FStar_Ident.lid_equals lid cons_lid1) && (aux e2)
        | uu____403 -> false in
      aux
let is_list: FStar_Parser_AST.term -> Prims.bool =
  is_list_structure FStar_Parser_Const.cons_lid FStar_Parser_Const.nil_lid
let is_lex_list: FStar_Parser_AST.term -> Prims.bool =
  is_list_structure FStar_Parser_Const.lexcons_lid
    FStar_Parser_Const.lextop_lid
let rec extract_from_list:
  FStar_Parser_AST.term -> FStar_Parser_AST.term Prims.list =
  fun e  ->
    let uu____412 =
      let uu____413 = unparen e in uu____413.FStar_Parser_AST.tm in
    match uu____412 with
    | FStar_Parser_AST.Construct (uu____415,[]) -> []
    | FStar_Parser_AST.Construct
        (uu____421,(e1,FStar_Parser_AST.Nothing )::(e2,FStar_Parser_AST.Nothing
                                                    )::[])
        -> let uu____433 = extract_from_list e2 in e1 :: uu____433
    | uu____435 ->
        let uu____436 =
          let uu____437 = FStar_Parser_AST.term_to_string e in
          FStar_Util.format1 "Not a list %s" uu____437 in
        failwith uu____436
let is_array: FStar_Parser_AST.term -> Prims.bool =
  fun e  ->
    let uu____442 =
      let uu____443 = unparen e in uu____443.FStar_Parser_AST.tm in
    match uu____442 with
    | FStar_Parser_AST.App
        ({ FStar_Parser_AST.tm = FStar_Parser_AST.Var lid;
           FStar_Parser_AST.range = uu____445;
           FStar_Parser_AST.level = uu____446;_},l,FStar_Parser_AST.Nothing
         )
        ->
        (FStar_Ident.lid_equals lid FStar_Parser_Const.array_mk_array_lid) &&
          (is_list l)
    | uu____448 -> false
let rec is_ref_set: FStar_Parser_AST.term -> Prims.bool =
  fun e  ->
    let uu____452 =
      let uu____453 = unparen e in uu____453.FStar_Parser_AST.tm in
    match uu____452 with
    | FStar_Parser_AST.Var maybe_empty_lid ->
        FStar_Ident.lid_equals maybe_empty_lid FStar_Parser_Const.tset_empty
    | FStar_Parser_AST.App
        ({ FStar_Parser_AST.tm = FStar_Parser_AST.Var maybe_singleton_lid;
           FStar_Parser_AST.range = uu____456;
           FStar_Parser_AST.level = uu____457;_},{
                                                   FStar_Parser_AST.tm =
                                                     FStar_Parser_AST.App
                                                     ({
                                                        FStar_Parser_AST.tm =
                                                          FStar_Parser_AST.Var
                                                          maybe_ref_lid;
                                                        FStar_Parser_AST.range
                                                          = uu____459;
                                                        FStar_Parser_AST.level
                                                          = uu____460;_},e1,FStar_Parser_AST.Nothing
                                                      );
                                                   FStar_Parser_AST.range =
                                                     uu____462;
                                                   FStar_Parser_AST.level =
                                                     uu____463;_},FStar_Parser_AST.Nothing
         )
        ->
        (FStar_Ident.lid_equals maybe_singleton_lid
           FStar_Parser_Const.tset_singleton)
          &&
          (FStar_Ident.lid_equals maybe_ref_lid FStar_Parser_Const.heap_ref)
    | FStar_Parser_AST.App
        ({
           FStar_Parser_AST.tm = FStar_Parser_AST.App
             ({ FStar_Parser_AST.tm = FStar_Parser_AST.Var maybe_union_lid;
                FStar_Parser_AST.range = uu____465;
                FStar_Parser_AST.level = uu____466;_},e1,FStar_Parser_AST.Nothing
              );
           FStar_Parser_AST.range = uu____468;
           FStar_Parser_AST.level = uu____469;_},e2,FStar_Parser_AST.Nothing
         )
        ->
        ((FStar_Ident.lid_equals maybe_union_lid
            FStar_Parser_Const.tset_union)
           && (is_ref_set e1))
          && (is_ref_set e2)
    | uu____471 -> false
let rec extract_from_ref_set:
  FStar_Parser_AST.term -> FStar_Parser_AST.term Prims.list =
  fun e  ->
    let uu____476 =
      let uu____477 = unparen e in uu____477.FStar_Parser_AST.tm in
    match uu____476 with
    | FStar_Parser_AST.Var uu____479 -> []
    | FStar_Parser_AST.App
        ({ FStar_Parser_AST.tm = FStar_Parser_AST.Var uu____480;
           FStar_Parser_AST.range = uu____481;
           FStar_Parser_AST.level = uu____482;_},{
                                                   FStar_Parser_AST.tm =
                                                     FStar_Parser_AST.App
                                                     ({
                                                        FStar_Parser_AST.tm =
                                                          FStar_Parser_AST.Var
                                                          uu____483;
                                                        FStar_Parser_AST.range
                                                          = uu____484;
                                                        FStar_Parser_AST.level
                                                          = uu____485;_},e1,FStar_Parser_AST.Nothing
                                                      );
                                                   FStar_Parser_AST.range =
                                                     uu____487;
                                                   FStar_Parser_AST.level =
                                                     uu____488;_},FStar_Parser_AST.Nothing
         )
        -> [e1]
    | FStar_Parser_AST.App
        ({
           FStar_Parser_AST.tm = FStar_Parser_AST.App
             ({ FStar_Parser_AST.tm = FStar_Parser_AST.Var uu____489;
                FStar_Parser_AST.range = uu____490;
                FStar_Parser_AST.level = uu____491;_},e1,FStar_Parser_AST.Nothing
              );
           FStar_Parser_AST.range = uu____493;
           FStar_Parser_AST.level = uu____494;_},e2,FStar_Parser_AST.Nothing
         )
        ->
        let uu____496 = extract_from_ref_set e1 in
        let uu____498 = extract_from_ref_set e2 in
        FStar_List.append uu____496 uu____498
    | uu____500 ->
        let uu____501 =
          let uu____502 = FStar_Parser_AST.term_to_string e in
          FStar_Util.format1 "Not a ref set %s" uu____502 in
        failwith uu____501
let is_general_application: FStar_Parser_AST.term -> Prims.bool =
  fun e  ->
    let uu____507 = (is_array e) || (is_ref_set e) in
    Prims.op_Negation uu____507
let is_general_construction: FStar_Parser_AST.term -> Prims.bool =
  fun e  ->
    let uu____511 = (is_list e) || (is_lex_list e) in
    Prims.op_Negation uu____511
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
      let uu____542 =
        let uu____543 = unparen e1 in uu____543.FStar_Parser_AST.tm in
      match uu____542 with
      | FStar_Parser_AST.App (head1,arg,imp) -> aux head1 ((arg, imp) :: acc)
      | uu____554 -> (e1, acc) in
    aux e []
type associativity =
  | Left
  | Right
  | NonAssoc
let uu___is_Left: associativity -> Prims.bool =
  fun projectee  -> match projectee with | Left  -> true | uu____563 -> false
let uu___is_Right: associativity -> Prims.bool =
  fun projectee  ->
    match projectee with | Right  -> true | uu____567 -> false
let uu___is_NonAssoc: associativity -> Prims.bool =
  fun projectee  ->
    match projectee with | NonAssoc  -> true | uu____571 -> false
type token = (FStar_Char.char,Prims.string) FStar_Util.either
type associativity_level = (associativity* token Prims.list)
let token_to_string:
  (FStar_BaseTypes.char,Prims.string) FStar_Util.either -> Prims.string =
  fun uu___95_581  ->
    match uu___95_581 with
    | FStar_Util.Inl c -> Prims.strcat (FStar_Util.string_of_char c) ".*"
    | FStar_Util.Inr s -> s
let matches_token:
  Prims.string ->
    (FStar_Char.char,Prims.string) FStar_Util.either -> Prims.bool
  =
  fun s  ->
    fun uu___96_593  ->
      match uu___96_593 with
      | FStar_Util.Inl c ->
          let uu____597 = FStar_String.get s (Prims.parse_int "0") in
          uu____597 = c
      | FStar_Util.Inr s' -> s = s'
let matches_level s uu____615 =
  match uu____615 with
  | (assoc_levels,tokens) ->
      let uu____629 = FStar_List.tryFind (matches_token s) tokens in
      uu____629 <> None
let opinfix4 uu____647 = (Right, [FStar_Util.Inr "**"])
let opinfix3 uu____662 =
  (Left, [FStar_Util.Inl '*'; FStar_Util.Inl '/'; FStar_Util.Inl '%'])
let opinfix2 uu____681 = (Left, [FStar_Util.Inl '+'; FStar_Util.Inl '-'])
let minus_lvl uu____698 = (Left, [FStar_Util.Inr "-"])
let opinfix1 uu____713 = (Right, [FStar_Util.Inl '@'; FStar_Util.Inl '^'])
let pipe_right uu____730 = (Left, [FStar_Util.Inr "|>"])
let opinfix0d uu____745 = (Left, [FStar_Util.Inl '$'])
let opinfix0c uu____760 =
  (Left, [FStar_Util.Inl '='; FStar_Util.Inl '<'; FStar_Util.Inl '>'])
let equal uu____779 = (Left, [FStar_Util.Inr "="])
let opinfix0b uu____794 = (Left, [FStar_Util.Inl '&'])
let opinfix0a uu____809 = (Left, [FStar_Util.Inl '|'])
let colon_equals uu____824 = (NonAssoc, [FStar_Util.Inr ":="])
let amp uu____839 = (Right, [FStar_Util.Inr "&"])
let colon_colon uu____854 = (Right, [FStar_Util.Inr "::"])
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
  let levels_from_associativity l uu___97_951 =
    match uu___97_951 with
    | Left  -> (l, l, (l - (Prims.parse_int "1")))
    | Right  -> ((l - (Prims.parse_int "1")), l, l)
    | NonAssoc  -> (l, l, l) in
  FStar_List.mapi
    (fun i  ->
       fun uu____969  ->
         match uu____969 with
         | (assoc1,tokens) -> ((levels_from_associativity i assoc1), tokens))
    level_associativity_spec
let assign_levels:
  associativity_level Prims.list ->
    Prims.string -> (Prims.int* Prims.int* Prims.int)
  =
  fun token_associativity_spec  ->
    fun s  ->
      let uu____1011 = FStar_List.tryFind (matches_level s) level_table in
      match uu____1011 with
      | Some (assoc_levels,uu____1036) -> assoc_levels
      | uu____1057 -> failwith (Prims.strcat "Unrecognized operator " s)
let max: Prims.int -> Prims.int -> Prims.int =
  fun k1  -> fun k2  -> if k1 > k2 then k1 else k2
let max_level l =
  let find_level_and_max n1 level =
    let uu____1113 =
      FStar_List.tryFind
        (fun uu____1131  ->
           match uu____1131 with
           | (uu____1140,tokens) -> tokens = (snd level)) level_table in
    match uu____1113 with
    | Some ((uu____1160,l1,uu____1162),uu____1163) -> max n1 l1
    | None  ->
        let uu____1189 =
          let uu____1190 =
            let uu____1191 = FStar_List.map token_to_string (snd level) in
            FStar_String.concat "," uu____1191 in
          FStar_Util.format1 "Undefined associativity level %s" uu____1190 in
        failwith uu____1189 in
  FStar_List.fold_left find_level_and_max (Prims.parse_int "0") l
let levels: Prims.string -> (Prims.int* Prims.int* Prims.int) =
  assign_levels level_associativity_spec
let operatorInfix0ad12 uu____1216 =
  [opinfix0a ();
  opinfix0b ();
  opinfix0c ();
  opinfix0d ();
  opinfix1 ();
  opinfix2 ()]
let is_operatorInfix0ad12: FStar_Ident.ident -> Prims.bool =
  fun op  ->
    let uu____1255 =
      let uu____1262 =
        FStar_All.pipe_left matches_level (FStar_Ident.text_of_id op) in
      FStar_List.tryFind uu____1262 (operatorInfix0ad12 ()) in
    uu____1255 <> None
let is_operatorInfix34: FStar_Ident.ident -> Prims.bool =
  let opinfix34 = [opinfix3 (); opinfix4 ()] in
  fun op  ->
    let uu____1318 =
      let uu____1325 =
        FStar_All.pipe_left matches_level (FStar_Ident.text_of_id op) in
      FStar_List.tryFind uu____1325 opinfix34 in
    uu____1318 <> None
let handleable_args_length: FStar_Ident.ident -> Prims.int =
  fun op  ->
    let op_s = FStar_Ident.text_of_id op in
    let uu____1360 =
      (is_general_prefix_op op) || (FStar_List.mem op_s ["-"; "~"]) in
    if uu____1360
    then Prims.parse_int "1"
    else
      (let uu____1362 =
         ((is_operatorInfix0ad12 op) || (is_operatorInfix34 op)) ||
           (FStar_List.mem op_s
              ["<==>"; "==>"; "\\/"; "/\\"; "="; "|>"; ":="; ".()"; ".[]"]) in
       if uu____1362
       then Prims.parse_int "2"
       else
         if FStar_List.mem op_s [".()<-"; ".[]<-"]
         then Prims.parse_int "3"
         else Prims.parse_int "0")
let handleable_op op args =
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
  | uu____1381 -> false
let comment_stack: (Prims.string* FStar_Range.range) Prims.list FStar_ST.ref
  = FStar_Util.mk_ref []
let with_comment printer tm tmrange =
  let rec comments_before_pos acc print_pos lookahead_pos =
    let uu____1427 = FStar_ST.read comment_stack in
    match uu____1427 with
    | [] -> (acc, false)
    | (comment,crange)::cs ->
        let uu____1448 = FStar_Range.range_before_pos crange print_pos in
        if uu____1448
        then
          (FStar_ST.write comment_stack cs;
           (let uu____1457 =
              let uu____1458 =
                let uu____1459 = str comment in
                FStar_Pprint.op_Hat_Hat uu____1459 FStar_Pprint.hardline in
              FStar_Pprint.op_Hat_Hat acc uu____1458 in
            comments_before_pos uu____1457 print_pos lookahead_pos))
        else
          (let uu____1461 = FStar_Range.range_before_pos crange lookahead_pos in
           (acc, uu____1461)) in
  let uu____1462 =
    let uu____1465 =
      let uu____1466 = FStar_Range.start_of_range tmrange in
      FStar_Range.end_of_line uu____1466 in
    let uu____1467 = FStar_Range.end_of_range tmrange in
    comments_before_pos FStar_Pprint.empty uu____1465 uu____1467 in
  match uu____1462 with
  | (comments,has_lookahead) ->
      let printed_e = printer tm in
      let comments1 =
        if has_lookahead
        then
          let pos = FStar_Range.end_of_range tmrange in
          let uu____1473 = comments_before_pos comments pos pos in
          fst uu____1473
        else comments in
      let uu____1477 = FStar_Pprint.op_Hat_Hat comments1 printed_e in
      FStar_Pprint.group uu____1477
let rec place_comments_until_pos:
  Prims.int ->
    Prims.int ->
      FStar_Range.pos -> FStar_Pprint.document -> FStar_Pprint.document
  =
  fun k  ->
    fun lbegin  ->
      fun pos_end  ->
        fun doc1  ->
          let uu____1490 = FStar_ST.read comment_stack in
          match uu____1490 with
          | (comment,crange)::cs when
              FStar_Range.range_before_pos crange pos_end ->
              (FStar_ST.write comment_stack cs;
               (let lnum =
                  let uu____1514 =
                    let uu____1515 =
                      let uu____1516 = FStar_Range.start_of_range crange in
                      FStar_Range.line_of_pos uu____1516 in
                    uu____1515 - lbegin in
                  max k uu____1514 in
                let doc2 =
                  let uu____1518 =
                    let uu____1519 =
                      FStar_Pprint.repeat lnum FStar_Pprint.hardline in
                    let uu____1520 = str comment in
                    FStar_Pprint.op_Hat_Hat uu____1519 uu____1520 in
                  FStar_Pprint.op_Hat_Hat doc1 uu____1518 in
                let uu____1521 =
                  let uu____1522 = FStar_Range.end_of_range crange in
                  FStar_Range.line_of_pos uu____1522 in
                place_comments_until_pos (Prims.parse_int "1") uu____1521
                  pos_end doc2))
          | uu____1523 ->
              let lnum =
                let uu____1528 =
                  let uu____1529 = FStar_Range.line_of_pos pos_end in
                  uu____1529 - lbegin in
                max (Prims.parse_int "1") uu____1528 in
              let uu____1530 = FStar_Pprint.repeat lnum FStar_Pprint.hardline in
              FStar_Pprint.op_Hat_Hat doc1 uu____1530
let separate_map_with_comments prefix1 sep f xs extract_range =
  let fold_fun uu____1579 x =
    match uu____1579 with
    | (last_line,doc1) ->
        let r = extract_range x in
        let doc2 =
          let uu____1589 = FStar_Range.start_of_range r in
          place_comments_until_pos (Prims.parse_int "1") last_line uu____1589
            doc1 in
        let uu____1590 =
          let uu____1591 = FStar_Range.end_of_range r in
          FStar_Range.line_of_pos uu____1591 in
        let uu____1592 =
          let uu____1593 =
            let uu____1594 = f x in FStar_Pprint.op_Hat_Hat sep uu____1594 in
          FStar_Pprint.op_Hat_Hat doc2 uu____1593 in
        (uu____1590, uu____1592) in
  let uu____1595 =
    let uu____1599 = FStar_List.hd xs in
    let uu____1600 = FStar_List.tl xs in (uu____1599, uu____1600) in
  match uu____1595 with
  | (x,xs1) ->
      let init1 =
        let uu____1610 =
          let uu____1611 =
            let uu____1612 = extract_range x in
            FStar_Range.end_of_range uu____1612 in
          FStar_Range.line_of_pos uu____1611 in
        let uu____1613 =
          let uu____1614 = f x in FStar_Pprint.op_Hat_Hat prefix1 uu____1614 in
        (uu____1610, uu____1613) in
      let uu____1615 = FStar_List.fold_left fold_fun init1 xs1 in
      snd uu____1615
let rec p_decl: FStar_Parser_AST.decl -> FStar_Pprint.document =
  fun d  ->
    let uu____1861 =
      let uu____1862 = FStar_Pprint.optional p_fsdoc d.FStar_Parser_AST.doc in
      let uu____1863 =
        let uu____1864 = p_attributes d.FStar_Parser_AST.attrs in
        let uu____1865 =
          let uu____1866 = p_qualifiers d.FStar_Parser_AST.quals in
          let uu____1867 =
            let uu____1868 = p_rawDecl d in
            FStar_Pprint.op_Hat_Hat
              (if d.FStar_Parser_AST.quals = []
               then FStar_Pprint.empty
               else break1) uu____1868 in
          FStar_Pprint.op_Hat_Hat uu____1866 uu____1867 in
        FStar_Pprint.op_Hat_Hat uu____1864 uu____1865 in
      FStar_Pprint.op_Hat_Hat uu____1862 uu____1863 in
    FStar_Pprint.group uu____1861
and p_attributes: FStar_Parser_AST.attributes_ -> FStar_Pprint.document =
  fun attrs  ->
    let uu____1871 =
      let uu____1872 = str "@" in
      FStar_Pprint.op_Hat_Hat FStar_Pprint.lbracket uu____1872 in
    let uu____1873 =
      FStar_Pprint.op_Hat_Hat FStar_Pprint.rbracket FStar_Pprint.hardline in
    soft_surround_separate_map (Prims.parse_int "0") (Prims.parse_int "2")
      FStar_Pprint.empty uu____1871 FStar_Pprint.space uu____1873
      p_atomicTerm attrs
and p_fsdoc: FStar_Parser_AST.fsdoc -> FStar_Pprint.document =
  fun uu____1874  ->
    match uu____1874 with
    | (doc1,kwd_args) ->
        let kwd_args_doc =
          match kwd_args with
          | [] -> FStar_Pprint.empty
          | kwd_args1 ->
              let process_kwd_arg uu____1895 =
                match uu____1895 with
                | (kwd1,arg) ->
                    let uu____1900 = str "@" in
                    let uu____1901 =
                      let uu____1902 = str kwd1 in
                      let uu____1903 =
                        let uu____1904 = str arg in
                        FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____1904 in
                      FStar_Pprint.op_Hat_Hat uu____1902 uu____1903 in
                    FStar_Pprint.op_Hat_Hat uu____1900 uu____1901 in
              let uu____1905 =
                let uu____1906 =
                  FStar_Pprint.separate_map FStar_Pprint.hardline
                    process_kwd_arg kwd_args1 in
                FStar_Pprint.op_Hat_Hat uu____1906 FStar_Pprint.hardline in
              FStar_Pprint.op_Hat_Hat FStar_Pprint.hardline uu____1905 in
        let uu____1909 =
          let uu____1910 =
            let uu____1911 =
              let uu____1912 =
                let uu____1913 = str doc1 in
                let uu____1914 =
                  let uu____1915 =
                    let uu____1916 =
                      FStar_Pprint.op_Hat_Hat FStar_Pprint.rparen
                        FStar_Pprint.hardline in
                    FStar_Pprint.op_Hat_Hat FStar_Pprint.star uu____1916 in
                  FStar_Pprint.op_Hat_Hat kwd_args_doc uu____1915 in
                FStar_Pprint.op_Hat_Hat uu____1913 uu____1914 in
              FStar_Pprint.op_Hat_Hat FStar_Pprint.star uu____1912 in
            FStar_Pprint.op_Hat_Hat FStar_Pprint.star uu____1911 in
          FStar_Pprint.op_Hat_Hat FStar_Pprint.lparen uu____1910 in
        FStar_Pprint.op_Hat_Hat FStar_Pprint.hardline uu____1909
and p_rawDecl: FStar_Parser_AST.decl -> FStar_Pprint.document =
  fun d  ->
    match d.FStar_Parser_AST.d with
    | FStar_Parser_AST.Open uid ->
        let uu____1919 =
          let uu____1920 = str "open" in
          let uu____1921 = p_quident uid in
          FStar_Pprint.op_Hat_Slash_Hat uu____1920 uu____1921 in
        FStar_Pprint.group uu____1919
    | FStar_Parser_AST.Include uid ->
        let uu____1923 =
          let uu____1924 = str "include" in
          let uu____1925 = p_quident uid in
          FStar_Pprint.op_Hat_Slash_Hat uu____1924 uu____1925 in
        FStar_Pprint.group uu____1923
    | FStar_Parser_AST.ModuleAbbrev (uid1,uid2) ->
        let uu____1928 =
          let uu____1929 = str "module" in
          let uu____1930 =
            let uu____1931 =
              let uu____1932 = p_uident uid1 in
              let uu____1933 =
                FStar_Pprint.op_Hat_Hat FStar_Pprint.space
                  FStar_Pprint.equals in
              FStar_Pprint.op_Hat_Hat uu____1932 uu____1933 in
            FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____1931 in
          FStar_Pprint.op_Hat_Hat uu____1929 uu____1930 in
        let uu____1934 = p_quident uid2 in
        op_Hat_Slash_Plus_Hat uu____1928 uu____1934
    | FStar_Parser_AST.TopLevelModule uid ->
        let uu____1936 =
          let uu____1937 = str "module" in
          let uu____1938 =
            let uu____1939 = p_quident uid in
            FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____1939 in
          FStar_Pprint.op_Hat_Hat uu____1937 uu____1938 in
        FStar_Pprint.group uu____1936
    | FStar_Parser_AST.Tycon
        (true ,(FStar_Parser_AST.TyconAbbrev (uid,tpars,None ,t),None )::[])
        ->
        let effect_prefix_doc =
          let uu____1958 = str "effect" in
          let uu____1959 =
            let uu____1960 = p_uident uid in
            FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____1960 in
          FStar_Pprint.op_Hat_Hat uu____1958 uu____1959 in
        let uu____1961 =
          let uu____1962 = p_typars tpars in
          FStar_Pprint.surround (Prims.parse_int "2") (Prims.parse_int "1")
            effect_prefix_doc uu____1962 FStar_Pprint.equals in
        let uu____1963 = p_typ t in
        op_Hat_Slash_Plus_Hat uu____1961 uu____1963
    | FStar_Parser_AST.Tycon (false ,tcdefs) ->
        let uu____1973 = str "type" in
        let uu____1974 = str "and" in
        precede_break_separate_map uu____1973 uu____1974 p_fsdocTypeDeclPairs
          tcdefs
    | FStar_Parser_AST.TopLevelLet (q,lbs) ->
        let let_doc =
          let uu____1987 = str "let" in
          let uu____1988 =
            let uu____1989 = p_letqualifier q in
            FStar_Pprint.op_Hat_Hat uu____1989 FStar_Pprint.space in
          FStar_Pprint.op_Hat_Hat uu____1987 uu____1988 in
        let uu____1990 =
          let uu____1991 = str "and" in
          FStar_Pprint.op_Hat_Hat uu____1991 FStar_Pprint.space in
        separate_map_with_comments let_doc uu____1990 p_letbinding lbs
          (fun uu____1994  ->
             match uu____1994 with
             | (p,t) ->
                 FStar_Range.union_ranges p.FStar_Parser_AST.prange
                   t.FStar_Parser_AST.range)
    | FStar_Parser_AST.Val (lid,t) ->
        let uu____2001 =
          let uu____2002 = str "val" in
          let uu____2003 =
            let uu____2004 =
              let uu____2005 = p_lident lid in
              let uu____2006 =
                FStar_Pprint.op_Hat_Hat FStar_Pprint.space FStar_Pprint.colon in
              FStar_Pprint.op_Hat_Hat uu____2005 uu____2006 in
            FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____2004 in
          FStar_Pprint.op_Hat_Hat uu____2002 uu____2003 in
        let uu____2007 = p_typ t in
        op_Hat_Slash_Plus_Hat uu____2001 uu____2007
    | FStar_Parser_AST.Assume (id,t) ->
        let decl_keyword =
          let uu____2011 =
            let uu____2012 =
              FStar_Util.char_at id.FStar_Ident.idText (Prims.parse_int "0") in
            FStar_All.pipe_right uu____2012 FStar_Util.is_upper in
          if uu____2011
          then FStar_Pprint.empty
          else
            (let uu____2014 = str "val" in
             FStar_Pprint.op_Hat_Hat uu____2014 FStar_Pprint.space) in
        let uu____2015 =
          let uu____2016 =
            let uu____2017 = p_ident id in
            let uu____2018 =
              FStar_Pprint.op_Hat_Hat FStar_Pprint.space FStar_Pprint.colon in
            FStar_Pprint.op_Hat_Hat uu____2017 uu____2018 in
          FStar_Pprint.op_Hat_Hat decl_keyword uu____2016 in
        let uu____2019 = p_typ t in
        op_Hat_Slash_Plus_Hat uu____2015 uu____2019
    | FStar_Parser_AST.Exception (uid,t_opt) ->
        let uu____2024 = str "exception" in
        let uu____2025 =
          let uu____2026 =
            let uu____2027 = p_uident uid in
            let uu____2028 =
              FStar_Pprint.optional
                (fun t  ->
                   let uu____2030 = str "of" in
                   let uu____2031 = p_typ t in
                   op_Hat_Slash_Plus_Hat uu____2030 uu____2031) t_opt in
            FStar_Pprint.op_Hat_Hat uu____2027 uu____2028 in
          FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____2026 in
        FStar_Pprint.op_Hat_Hat uu____2024 uu____2025
    | FStar_Parser_AST.NewEffect ne ->
        let uu____2033 = str "new_effect" in
        let uu____2034 =
          let uu____2035 = p_newEffect ne in
          FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____2035 in
        FStar_Pprint.op_Hat_Hat uu____2033 uu____2034
    | FStar_Parser_AST.SubEffect se ->
        let uu____2037 = str "sub_effect" in
        let uu____2038 =
          let uu____2039 = p_subEffect se in
          FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____2039 in
        FStar_Pprint.op_Hat_Hat uu____2037 uu____2038
    | FStar_Parser_AST.Pragma p -> p_pragma p
    | FStar_Parser_AST.Fsdoc doc1 ->
        let uu____2042 = p_fsdoc doc1 in
        FStar_Pprint.op_Hat_Hat uu____2042 FStar_Pprint.hardline
    | FStar_Parser_AST.Main uu____2043 ->
        failwith "*Main declaration* : Is that really still in use ??"
    | FStar_Parser_AST.Tycon (true ,uu____2044) ->
        failwith
          "Effect abbreviation is expected to be defined by an abbreviation"
and p_pragma: FStar_Parser_AST.pragma -> FStar_Pprint.document =
  fun uu___98_2053  ->
    match uu___98_2053 with
    | FStar_Parser_AST.SetOptions s ->
        let uu____2055 = str "#set-options" in
        let uu____2056 =
          let uu____2057 =
            let uu____2058 = str s in FStar_Pprint.dquotes uu____2058 in
          FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____2057 in
        FStar_Pprint.op_Hat_Hat uu____2055 uu____2056
    | FStar_Parser_AST.ResetOptions s_opt ->
        let uu____2061 = str "#reset-options" in
        let uu____2062 =
          FStar_Pprint.optional
            (fun s  ->
               let uu____2064 =
                 let uu____2065 = str s in FStar_Pprint.dquotes uu____2065 in
               FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____2064) s_opt in
        FStar_Pprint.op_Hat_Hat uu____2061 uu____2062
    | FStar_Parser_AST.LightOff  ->
        (FStar_ST.write should_print_fs_typ_app true; str "#light \"off\"")
and p_typars: FStar_Parser_AST.binder Prims.list -> FStar_Pprint.document =
  fun bs  -> p_binders true bs
and p_fsdocTypeDeclPairs:
  (FStar_Parser_AST.tycon* FStar_Parser_AST.fsdoc option) ->
    FStar_Pprint.document
  =
  fun uu____2071  ->
    match uu____2071 with
    | (typedecl,fsdoc_opt) ->
        let uu____2079 = FStar_Pprint.optional p_fsdoc fsdoc_opt in
        let uu____2080 = p_typeDecl typedecl in
        FStar_Pprint.op_Hat_Hat uu____2079 uu____2080
and p_typeDecl: FStar_Parser_AST.tycon -> FStar_Pprint.document =
  fun uu___99_2081  ->
    match uu___99_2081 with
    | FStar_Parser_AST.TyconAbstract (lid,bs,typ_opt) ->
        let empty' uu____2092 = FStar_Pprint.empty in
        p_typeDeclPrefix lid bs typ_opt empty'
    | FStar_Parser_AST.TyconAbbrev (lid,bs,typ_opt,t) ->
        let f uu____2104 =
          let uu____2105 = p_typ t in prefix2 FStar_Pprint.equals uu____2105 in
        p_typeDeclPrefix lid bs typ_opt f
    | FStar_Parser_AST.TyconRecord (lid,bs,typ_opt,record_field_decls) ->
        let p_recordFieldAndComments uu____2131 =
          match uu____2131 with
          | (lid1,t,doc_opt) ->
              let uu____2141 =
                FStar_Range.extend_to_end_of_line t.FStar_Parser_AST.range in
              with_comment p_recordFieldDecl (lid1, t, doc_opt) uu____2141 in
        let p_fields uu____2150 =
          let uu____2151 =
            let uu____2152 =
              let uu____2153 =
                let uu____2154 =
                  FStar_Pprint.op_Hat_Hat FStar_Pprint.semi break1 in
                FStar_Pprint.separate_map uu____2154 p_recordFieldAndComments
                  record_field_decls in
              braces_with_nesting uu____2153 in
            FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____2152 in
          FStar_Pprint.op_Hat_Hat FStar_Pprint.equals uu____2151 in
        p_typeDeclPrefix lid bs typ_opt p_fields
    | FStar_Parser_AST.TyconVariant (lid,bs,typ_opt,ct_decls) ->
        let p_constructorBranchAndComments uu____2190 =
          match uu____2190 with
          | (uid,t_opt,doc_opt,use_of) ->
              let range =
                let uu____2206 =
                  let uu____2207 =
                    FStar_Util.map_opt t_opt
                      (fun t  -> t.FStar_Parser_AST.range) in
                  FStar_Util.dflt uid.FStar_Ident.idRange uu____2207 in
                FStar_Range.extend_to_end_of_line uu____2206 in
              let p_constructorBranch decl =
                let uu____2226 =
                  let uu____2227 =
                    let uu____2228 = p_constructorDecl decl in
                    FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____2228 in
                  FStar_Pprint.op_Hat_Hat FStar_Pprint.bar uu____2227 in
                FStar_Pprint.group uu____2226 in
              with_comment p_constructorBranch (uid, t_opt, doc_opt, use_of)
                range in
        let datacon_doc uu____2240 =
          let uu____2241 =
            FStar_Pprint.separate_map break1 p_constructorBranchAndComments
              ct_decls in
          FStar_Pprint.group uu____2241 in
        p_typeDeclPrefix lid bs typ_opt
          (fun uu____2248  ->
             let uu____2249 = datacon_doc () in
             prefix2 FStar_Pprint.equals uu____2249)
and p_typeDeclPrefix:
  FStar_Ident.ident ->
    FStar_Parser_AST.binder Prims.list ->
      FStar_Parser_AST.knd option ->
        (Prims.unit -> FStar_Pprint.document) -> FStar_Pprint.document
  =
  fun lid  ->
    fun bs  ->
      fun typ_opt  ->
        fun cont  ->
          if (bs = []) && (typ_opt = None)
          then
            let uu____2260 = p_ident lid in
            let uu____2261 =
              let uu____2262 = cont () in
              FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____2262 in
            FStar_Pprint.op_Hat_Hat uu____2260 uu____2261
          else
            (let binders_doc =
               let uu____2265 = p_typars bs in
               let uu____2266 =
                 FStar_Pprint.optional
                   (fun t  ->
                      let uu____2268 =
                        let uu____2269 =
                          let uu____2270 = p_typ t in
                          FStar_Pprint.op_Hat_Hat FStar_Pprint.space
                            uu____2270 in
                        FStar_Pprint.op_Hat_Hat FStar_Pprint.colon uu____2269 in
                      FStar_Pprint.op_Hat_Hat break1 uu____2268) typ_opt in
               FStar_Pprint.op_Hat_Hat uu____2265 uu____2266 in
             let uu____2271 = p_ident lid in
             let uu____2272 = cont () in
             FStar_Pprint.surround (Prims.parse_int "2")
               (Prims.parse_int "1") uu____2271 binders_doc uu____2272)
and p_recordFieldDecl:
  (FStar_Ident.ident* FStar_Parser_AST.term* FStar_Parser_AST.fsdoc option)
    -> FStar_Pprint.document
  =
  fun uu____2273  ->
    match uu____2273 with
    | (lid,t,doc_opt) ->
        let uu____2283 =
          let uu____2284 = FStar_Pprint.optional p_fsdoc doc_opt in
          let uu____2285 =
            let uu____2286 = p_lident lid in
            let uu____2287 =
              let uu____2288 = p_typ t in
              FStar_Pprint.op_Hat_Hat FStar_Pprint.colon uu____2288 in
            FStar_Pprint.op_Hat_Hat uu____2286 uu____2287 in
          FStar_Pprint.op_Hat_Hat uu____2284 uu____2285 in
        FStar_Pprint.group uu____2283
and p_constructorDecl:
  (FStar_Ident.ident* FStar_Parser_AST.term option* FStar_Parser_AST.fsdoc
    option* Prims.bool) -> FStar_Pprint.document
  =
  fun uu____2289  ->
    match uu____2289 with
    | (uid,t_opt,doc_opt,use_of) ->
        let sep = if use_of then str "of" else FStar_Pprint.colon in
        let uid_doc = p_uident uid in
        let uu____2307 = FStar_Pprint.optional p_fsdoc doc_opt in
        let uu____2308 =
          let uu____2309 = FStar_Pprint.break_ (Prims.parse_int "0") in
          let uu____2310 =
            default_or_map uid_doc
              (fun t  ->
                 let uu____2312 =
                   let uu____2313 =
                     FStar_Pprint.op_Hat_Hat FStar_Pprint.space sep in
                   FStar_Pprint.op_Hat_Hat uid_doc uu____2313 in
                 let uu____2314 = p_typ t in
                 op_Hat_Slash_Plus_Hat uu____2312 uu____2314) t_opt in
          FStar_Pprint.op_Hat_Hat uu____2309 uu____2310 in
        FStar_Pprint.op_Hat_Hat uu____2307 uu____2308
and p_letbinding:
  (FStar_Parser_AST.pattern* FStar_Parser_AST.term) -> FStar_Pprint.document
  =
  fun uu____2315  ->
    match uu____2315 with
    | (pat,e) ->
        let pat_doc =
          let uu____2321 =
            match pat.FStar_Parser_AST.pat with
            | FStar_Parser_AST.PatAscribed (pat1,t) ->
                let uu____2328 =
                  let uu____2329 =
                    let uu____2330 =
                      let uu____2331 =
                        let uu____2332 = p_tmArrow p_tmNoEq t in
                        FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____2332 in
                      FStar_Pprint.op_Hat_Hat FStar_Pprint.colon uu____2331 in
                    FStar_Pprint.group uu____2330 in
                  FStar_Pprint.op_Hat_Hat break1 uu____2329 in
                (pat1, uu____2328)
            | uu____2333 -> (pat, FStar_Pprint.empty) in
          match uu____2321 with
          | (pat1,ascr_doc) ->
              (match pat1.FStar_Parser_AST.pat with
               | FStar_Parser_AST.PatApp
                   ({
                      FStar_Parser_AST.pat = FStar_Parser_AST.PatVar
                        (x,uu____2337);
                      FStar_Parser_AST.prange = uu____2338;_},pats)
                   ->
                   let uu____2344 = p_lident x in
                   let uu____2345 =
                     let uu____2346 =
                       FStar_Pprint.separate_map break1 p_atomicPattern pats in
                     FStar_Pprint.op_Hat_Hat uu____2346 ascr_doc in
                   FStar_Pprint.surround (Prims.parse_int "2")
                     (Prims.parse_int "1") uu____2344 uu____2345
                     FStar_Pprint.equals
               | uu____2347 ->
                   let uu____2348 =
                     let uu____2349 = p_tuplePattern pat1 in
                     let uu____2350 =
                       FStar_Pprint.op_Hat_Slash_Hat ascr_doc
                         FStar_Pprint.equals in
                     FStar_Pprint.op_Hat_Hat uu____2349 uu____2350 in
                   FStar_Pprint.group uu____2348) in
        let uu____2351 = p_term e in prefix2 pat_doc uu____2351
and p_newEffect: FStar_Parser_AST.effect_decl -> FStar_Pprint.document =
  fun uu___100_2352  ->
    match uu___100_2352 with
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
        let uu____2370 = p_uident uid in
        let uu____2371 = p_binders true bs in
        let uu____2372 =
          let uu____2373 = p_simpleTerm t in
          prefix2 FStar_Pprint.equals uu____2373 in
        FStar_Pprint.surround (Prims.parse_int "2") (Prims.parse_int "1")
          uu____2370 uu____2371 uu____2372
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
          let uu____2380 =
            let uu____2381 =
              let uu____2382 =
                let uu____2383 = p_uident uid in
                let uu____2384 = p_binders true bs in
                let uu____2385 =
                  let uu____2386 = p_typ t in
                  prefix2 FStar_Pprint.colon uu____2386 in
                FStar_Pprint.surround (Prims.parse_int "2")
                  (Prims.parse_int "1") uu____2383 uu____2384 uu____2385 in
              FStar_Pprint.group uu____2382 in
            let uu____2387 =
              let uu____2388 = str "with" in
              let uu____2389 =
                separate_break_map FStar_Pprint.semi p_effectDecl eff_decls in
              prefix2 uu____2388 uu____2389 in
            FStar_Pprint.op_Hat_Slash_Hat uu____2381 uu____2387 in
          braces_with_nesting uu____2380
and p_effectDecl: FStar_Parser_AST.decl -> FStar_Pprint.document =
  fun d  ->
    match d.FStar_Parser_AST.d with
    | FStar_Parser_AST.Tycon
        (false ,(FStar_Parser_AST.TyconAbbrev (lid,[],None ,e),None )::[]) ->
        let uu____2406 =
          let uu____2407 = p_lident lid in
          let uu____2408 =
            FStar_Pprint.op_Hat_Hat FStar_Pprint.space FStar_Pprint.equals in
          FStar_Pprint.op_Hat_Hat uu____2407 uu____2408 in
        let uu____2409 = p_simpleTerm e in prefix2 uu____2406 uu____2409
    | uu____2410 ->
        let uu____2411 =
          let uu____2412 = FStar_Parser_AST.decl_to_string d in
          FStar_Util.format1
            "Not a declaration of an effect member... or at least I hope so : %s"
            uu____2412 in
        failwith uu____2411
and p_subEffect: FStar_Parser_AST.lift -> FStar_Pprint.document =
  fun lift  ->
    let lift_op_doc =
      let lifts =
        match lift.FStar_Parser_AST.lift_op with
        | FStar_Parser_AST.NonReifiableLift t -> [("lift_wp", t)]
        | FStar_Parser_AST.ReifiableLift (t1,t2) ->
            [("lif_wp", t1); ("lift", t2)]
        | FStar_Parser_AST.LiftForFree t -> [("lift", t)] in
      let p_lift uu____2445 =
        match uu____2445 with
        | (kwd1,t) ->
            let uu____2450 =
              let uu____2451 = str kwd1 in
              let uu____2452 =
                FStar_Pprint.op_Hat_Hat FStar_Pprint.space
                  FStar_Pprint.equals in
              FStar_Pprint.op_Hat_Hat uu____2451 uu____2452 in
            let uu____2453 = p_simpleTerm t in prefix2 uu____2450 uu____2453 in
      separate_break_map FStar_Pprint.semi p_lift lifts in
    let uu____2456 =
      let uu____2457 =
        let uu____2458 = p_quident lift.FStar_Parser_AST.msource in
        let uu____2459 =
          let uu____2460 = str "~>" in
          FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____2460 in
        FStar_Pprint.op_Hat_Hat uu____2458 uu____2459 in
      let uu____2461 = p_quident lift.FStar_Parser_AST.mdest in
      prefix2 uu____2457 uu____2461 in
    let uu____2462 =
      let uu____2463 = braces_with_nesting lift_op_doc in
      FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____2463 in
    FStar_Pprint.op_Hat_Hat uu____2456 uu____2462
and p_qualifier: FStar_Parser_AST.qualifier -> FStar_Pprint.document =
  fun uu___101_2464  ->
    match uu___101_2464 with
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
    let uu____2466 = FStar_Pprint.separate_map break1 p_qualifier qs in
    FStar_Pprint.group uu____2466
and p_letqualifier: FStar_Parser_AST.let_qualifier -> FStar_Pprint.document =
  fun uu___102_2467  ->
    match uu___102_2467 with
    | FStar_Parser_AST.Rec  ->
        let uu____2468 = str "rec" in
        FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____2468
    | FStar_Parser_AST.Mutable  ->
        let uu____2469 = str "mutable" in
        FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____2469
    | FStar_Parser_AST.NoLetQualifier  -> FStar_Pprint.empty
and p_aqual: FStar_Parser_AST.arg_qualifier -> FStar_Pprint.document =
  fun uu___103_2470  ->
    match uu___103_2470 with
    | FStar_Parser_AST.Implicit  -> str "#"
    | FStar_Parser_AST.Equality  -> str "$"
and p_disjunctivePattern: FStar_Parser_AST.pattern -> FStar_Pprint.document =
  fun p  ->
    match p.FStar_Parser_AST.pat with
    | FStar_Parser_AST.PatOr pats ->
        let uu____2474 =
          let uu____2475 =
            let uu____2476 =
              FStar_Pprint.op_Hat_Hat FStar_Pprint.bar FStar_Pprint.space in
            FStar_Pprint.op_Hat_Hat break1 uu____2476 in
          FStar_Pprint.separate_map uu____2475 p_tuplePattern pats in
        FStar_Pprint.group uu____2474
    | uu____2477 -> p_tuplePattern p
and p_tuplePattern: FStar_Parser_AST.pattern -> FStar_Pprint.document =
  fun p  ->
    match p.FStar_Parser_AST.pat with
    | FStar_Parser_AST.PatTuple (pats,false ) ->
        let uu____2482 =
          let uu____2483 = FStar_Pprint.op_Hat_Hat FStar_Pprint.comma break1 in
          FStar_Pprint.separate_map uu____2483 p_constructorPattern pats in
        FStar_Pprint.group uu____2482
    | uu____2484 -> p_constructorPattern p
and p_constructorPattern: FStar_Parser_AST.pattern -> FStar_Pprint.document =
  fun p  ->
    match p.FStar_Parser_AST.pat with
    | FStar_Parser_AST.PatApp
        ({ FStar_Parser_AST.pat = FStar_Parser_AST.PatName maybe_cons_lid;
           FStar_Parser_AST.prange = uu____2487;_},hd1::tl1::[])
        when
        FStar_Ident.lid_equals maybe_cons_lid FStar_Parser_Const.cons_lid ->
        let uu____2491 =
          FStar_Pprint.op_Hat_Hat FStar_Pprint.colon FStar_Pprint.colon in
        let uu____2492 = p_constructorPattern hd1 in
        let uu____2493 = p_constructorPattern tl1 in
        infix0 uu____2491 uu____2492 uu____2493
    | FStar_Parser_AST.PatApp
        ({ FStar_Parser_AST.pat = FStar_Parser_AST.PatName uid;
           FStar_Parser_AST.prange = uu____2495;_},pats)
        ->
        let uu____2499 = p_quident uid in
        let uu____2500 =
          FStar_Pprint.separate_map break1 p_atomicPattern pats in
        prefix2 uu____2499 uu____2500
    | uu____2501 -> p_atomicPattern p
and p_atomicPattern: FStar_Parser_AST.pattern -> FStar_Pprint.document =
  fun p  ->
    match p.FStar_Parser_AST.pat with
    | FStar_Parser_AST.PatAscribed (pat,t) ->
        let uu____2505 =
          let uu____2508 =
            let uu____2509 = unparen t in uu____2509.FStar_Parser_AST.tm in
          ((pat.FStar_Parser_AST.pat), uu____2508) in
        (match uu____2505 with
         | (FStar_Parser_AST.PatVar (lid,aqual),FStar_Parser_AST.Refine
            ({ FStar_Parser_AST.b = FStar_Parser_AST.Annotated (lid',t1);
               FStar_Parser_AST.brange = uu____2514;
               FStar_Parser_AST.blevel = uu____2515;
               FStar_Parser_AST.aqual = uu____2516;_},phi))
             when lid.FStar_Ident.idText = lid'.FStar_Ident.idText ->
             let uu____2520 =
               let uu____2521 = p_ident lid in
               p_refinement aqual uu____2521 t1 phi in
             soft_parens_with_nesting uu____2520
         | (FStar_Parser_AST.PatWild ,FStar_Parser_AST.Refine
            ({ FStar_Parser_AST.b = FStar_Parser_AST.NoName t1;
               FStar_Parser_AST.brange = uu____2523;
               FStar_Parser_AST.blevel = uu____2524;
               FStar_Parser_AST.aqual = uu____2525;_},phi))
             ->
             let uu____2527 =
               p_refinement None FStar_Pprint.underscore t1 phi in
             soft_parens_with_nesting uu____2527
         | uu____2528 ->
             let uu____2531 =
               let uu____2532 = p_tuplePattern pat in
               let uu____2533 =
                 let uu____2534 = FStar_Pprint.break_ (Prims.parse_int "0") in
                 let uu____2535 =
                   let uu____2536 = p_typ t in
                   FStar_Pprint.op_Hat_Hat FStar_Pprint.colon uu____2536 in
                 FStar_Pprint.op_Hat_Hat uu____2534 uu____2535 in
               FStar_Pprint.op_Hat_Hat uu____2532 uu____2533 in
             soft_parens_with_nesting uu____2531)
    | FStar_Parser_AST.PatList pats ->
        let uu____2539 =
          separate_break_map FStar_Pprint.semi p_tuplePattern pats in
        FStar_Pprint.surround (Prims.parse_int "2") (Prims.parse_int "0")
          FStar_Pprint.lbracket uu____2539 FStar_Pprint.rbracket
    | FStar_Parser_AST.PatRecord pats ->
        let p_recordFieldPat uu____2549 =
          match uu____2549 with
          | (lid,pat) ->
              let uu____2554 = p_qlident lid in
              let uu____2555 = p_tuplePattern pat in
              infix2 FStar_Pprint.equals uu____2554 uu____2555 in
        let uu____2556 =
          separate_break_map FStar_Pprint.semi p_recordFieldPat pats in
        soft_braces_with_nesting uu____2556
    | FStar_Parser_AST.PatTuple (pats,true ) ->
        let uu____2562 =
          FStar_Pprint.op_Hat_Hat FStar_Pprint.lparen FStar_Pprint.bar in
        let uu____2563 =
          separate_break_map FStar_Pprint.comma p_constructorPattern pats in
        let uu____2564 =
          FStar_Pprint.op_Hat_Hat FStar_Pprint.bar FStar_Pprint.rparen in
        FStar_Pprint.surround (Prims.parse_int "2") (Prims.parse_int "1")
          uu____2562 uu____2563 uu____2564
    | FStar_Parser_AST.PatTvar (tv,arg_qualifier_opt) -> p_tvar tv
    | FStar_Parser_AST.PatOp op ->
        let uu____2571 =
          let uu____2572 =
            let uu____2573 = str (FStar_Ident.text_of_id op) in
            let uu____2574 =
              FStar_Pprint.op_Hat_Hat FStar_Pprint.space FStar_Pprint.rparen in
            FStar_Pprint.op_Hat_Hat uu____2573 uu____2574 in
          FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____2572 in
        FStar_Pprint.op_Hat_Hat FStar_Pprint.lparen uu____2571
    | FStar_Parser_AST.PatWild  -> FStar_Pprint.underscore
    | FStar_Parser_AST.PatConst c -> p_constant c
    | FStar_Parser_AST.PatVar (lid,aqual) ->
        let uu____2580 = FStar_Pprint.optional p_aqual aqual in
        let uu____2581 = p_lident lid in
        FStar_Pprint.op_Hat_Hat uu____2580 uu____2581
    | FStar_Parser_AST.PatName uid -> p_quident uid
    | FStar_Parser_AST.PatOr uu____2583 -> failwith "Inner or pattern !"
    | FStar_Parser_AST.PatApp
        ({ FStar_Parser_AST.pat = FStar_Parser_AST.PatName uu____2585;
           FStar_Parser_AST.prange = uu____2586;_},uu____2587)
        ->
        let uu____2590 = p_tuplePattern p in
        soft_parens_with_nesting uu____2590
    | FStar_Parser_AST.PatTuple (uu____2591,false ) ->
        let uu____2594 = p_tuplePattern p in
        soft_parens_with_nesting uu____2594
    | uu____2595 ->
        let uu____2596 =
          let uu____2597 = FStar_Parser_AST.pat_to_string p in
          FStar_Util.format1 "Invalid pattern %s" uu____2597 in
        failwith uu____2596
and p_binder: Prims.bool -> FStar_Parser_AST.binder -> FStar_Pprint.document
  =
  fun is_atomic  ->
    fun b  ->
      match b.FStar_Parser_AST.b with
      | FStar_Parser_AST.Variable lid ->
          let uu____2601 =
            FStar_Pprint.optional p_aqual b.FStar_Parser_AST.aqual in
          let uu____2602 = p_lident lid in
          FStar_Pprint.op_Hat_Hat uu____2601 uu____2602
      | FStar_Parser_AST.TVariable lid -> p_lident lid
      | FStar_Parser_AST.Annotated (lid,t) ->
          let doc1 =
            let uu____2607 =
              let uu____2608 = unparen t in uu____2608.FStar_Parser_AST.tm in
            match uu____2607 with
            | FStar_Parser_AST.Refine
                ({ FStar_Parser_AST.b = FStar_Parser_AST.Annotated (lid',t1);
                   FStar_Parser_AST.brange = uu____2611;
                   FStar_Parser_AST.blevel = uu____2612;
                   FStar_Parser_AST.aqual = uu____2613;_},phi)
                when lid.FStar_Ident.idText = lid'.FStar_Ident.idText ->
                let uu____2615 = p_ident lid in
                p_refinement b.FStar_Parser_AST.aqual uu____2615 t1 phi
            | uu____2616 ->
                let uu____2617 =
                  FStar_Pprint.optional p_aqual b.FStar_Parser_AST.aqual in
                let uu____2618 =
                  let uu____2619 = p_lident lid in
                  let uu____2620 =
                    let uu____2621 =
                      let uu____2622 =
                        FStar_Pprint.break_ (Prims.parse_int "0") in
                      let uu____2623 = p_tmFormula t in
                      FStar_Pprint.op_Hat_Hat uu____2622 uu____2623 in
                    FStar_Pprint.op_Hat_Hat FStar_Pprint.colon uu____2621 in
                  FStar_Pprint.op_Hat_Hat uu____2619 uu____2620 in
                FStar_Pprint.op_Hat_Hat uu____2617 uu____2618 in
          if is_atomic
          then
            let uu____2624 =
              let uu____2625 =
                FStar_Pprint.op_Hat_Hat doc1 FStar_Pprint.rparen in
              FStar_Pprint.op_Hat_Hat FStar_Pprint.lparen uu____2625 in
            FStar_Pprint.group uu____2624
          else FStar_Pprint.group doc1
      | FStar_Parser_AST.TAnnotated uu____2627 ->
          failwith "Is this still used ?"
      | FStar_Parser_AST.NoName t ->
          let uu____2631 =
            let uu____2632 = unparen t in uu____2632.FStar_Parser_AST.tm in
          (match uu____2631 with
           | FStar_Parser_AST.Refine
               ({ FStar_Parser_AST.b = FStar_Parser_AST.NoName t1;
                  FStar_Parser_AST.brange = uu____2634;
                  FStar_Parser_AST.blevel = uu____2635;
                  FStar_Parser_AST.aqual = uu____2636;_},phi)
               ->
               if is_atomic
               then
                 let uu____2638 =
                   let uu____2639 =
                     let uu____2640 =
                       p_refinement b.FStar_Parser_AST.aqual
                         FStar_Pprint.underscore t1 phi in
                     FStar_Pprint.op_Hat_Hat uu____2640 FStar_Pprint.rparen in
                   FStar_Pprint.op_Hat_Hat FStar_Pprint.lparen uu____2639 in
                 FStar_Pprint.group uu____2638
               else
                 (let uu____2642 =
                    p_refinement b.FStar_Parser_AST.aqual
                      FStar_Pprint.underscore t1 phi in
                  FStar_Pprint.group uu____2642)
           | uu____2643 -> if is_atomic then p_atomicTerm t else p_appTerm t)
and p_refinement:
  FStar_Parser_AST.arg_qualifier option ->
    FStar_Pprint.document ->
      FStar_Parser_AST.term -> FStar_Parser_AST.term -> FStar_Pprint.document
  =
  fun aqual_opt  ->
    fun binder  ->
      fun t  ->
        fun phi  ->
          let uu____2650 = FStar_Pprint.optional p_aqual aqual_opt in
          let uu____2651 =
            let uu____2652 =
              let uu____2653 =
                let uu____2654 = p_appTerm t in
                let uu____2655 =
                  let uu____2656 = p_noSeqTerm phi in
                  soft_braces_with_nesting uu____2656 in
                FStar_Pprint.op_Hat_Hat uu____2654 uu____2655 in
              FStar_Pprint.op_Hat_Hat FStar_Pprint.colon uu____2653 in
            FStar_Pprint.op_Hat_Hat binder uu____2652 in
          FStar_Pprint.op_Hat_Hat uu____2650 uu____2651
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
    let uu____2669 =
      let uu____2670 = unparen e in uu____2670.FStar_Parser_AST.tm in
    match uu____2669 with
    | FStar_Parser_AST.Seq (e1,e2) ->
        let uu____2673 =
          let uu____2674 =
            let uu____2675 = p_noSeqTerm e1 in
            FStar_Pprint.op_Hat_Hat uu____2675 FStar_Pprint.semi in
          FStar_Pprint.group uu____2674 in
        let uu____2676 = p_term e2 in
        FStar_Pprint.op_Hat_Slash_Hat uu____2673 uu____2676
    | FStar_Parser_AST.Bind (x,e1,e2) ->
        let uu____2680 =
          let uu____2681 =
            let uu____2682 =
              let uu____2683 = p_lident x in
              let uu____2684 =
                FStar_Pprint.op_Hat_Hat FStar_Pprint.space
                  FStar_Pprint.long_left_arrow in
              FStar_Pprint.op_Hat_Hat uu____2683 uu____2684 in
            let uu____2685 =
              let uu____2686 = p_noSeqTerm e1 in
              let uu____2687 =
                FStar_Pprint.op_Hat_Hat FStar_Pprint.space FStar_Pprint.semi in
              FStar_Pprint.op_Hat_Hat uu____2686 uu____2687 in
            op_Hat_Slash_Plus_Hat uu____2682 uu____2685 in
          FStar_Pprint.group uu____2681 in
        let uu____2688 = p_term e2 in
        FStar_Pprint.op_Hat_Slash_Hat uu____2680 uu____2688
    | uu____2689 ->
        let uu____2690 = p_noSeqTerm e in FStar_Pprint.group uu____2690
and p_noSeqTerm: FStar_Parser_AST.term -> FStar_Pprint.document =
  fun e  -> with_comment p_noSeqTerm' e e.FStar_Parser_AST.range
and p_noSeqTerm': FStar_Parser_AST.term -> FStar_Pprint.document =
  fun e  ->
    let uu____2693 =
      let uu____2694 = unparen e in uu____2694.FStar_Parser_AST.tm in
    match uu____2693 with
    | FStar_Parser_AST.Ascribed (e1,t,None ) ->
        let uu____2698 =
          let uu____2699 = p_tmIff e1 in
          let uu____2700 =
            let uu____2701 =
              let uu____2702 = p_typ t in
              FStar_Pprint.op_Hat_Slash_Hat FStar_Pprint.colon uu____2702 in
            FStar_Pprint.op_Hat_Hat FStar_Pprint.langle uu____2701 in
          FStar_Pprint.op_Hat_Slash_Hat uu____2699 uu____2700 in
        FStar_Pprint.group uu____2698
    | FStar_Parser_AST.Ascribed (e1,t,Some tac) ->
        let uu____2707 =
          let uu____2708 = p_tmIff e1 in
          let uu____2709 =
            let uu____2710 =
              let uu____2711 =
                let uu____2712 = p_typ t in
                let uu____2713 =
                  let uu____2714 = str "by" in
                  let uu____2715 = p_typ tac in
                  FStar_Pprint.op_Hat_Slash_Hat uu____2714 uu____2715 in
                FStar_Pprint.op_Hat_Slash_Hat uu____2712 uu____2713 in
              FStar_Pprint.op_Hat_Slash_Hat FStar_Pprint.colon uu____2711 in
            FStar_Pprint.op_Hat_Hat FStar_Pprint.langle uu____2710 in
          FStar_Pprint.op_Hat_Slash_Hat uu____2708 uu____2709 in
        FStar_Pprint.group uu____2707
    | FStar_Parser_AST.Op
        ({ FStar_Ident.idText = ".()<-"; FStar_Ident.idRange = uu____2716;_},e1::e2::e3::[])
        ->
        let uu____2721 =
          let uu____2722 =
            let uu____2723 =
              let uu____2724 = p_atomicTermNotQUident e1 in
              let uu____2725 =
                let uu____2726 =
                  let uu____2727 =
                    let uu____2728 = p_term e2 in
                    soft_parens_with_nesting uu____2728 in
                  let uu____2729 =
                    FStar_Pprint.op_Hat_Hat FStar_Pprint.space
                      FStar_Pprint.larrow in
                  FStar_Pprint.op_Hat_Hat uu____2727 uu____2729 in
                FStar_Pprint.op_Hat_Hat FStar_Pprint.dot uu____2726 in
              FStar_Pprint.op_Hat_Hat uu____2724 uu____2725 in
            FStar_Pprint.group uu____2723 in
          let uu____2730 =
            let uu____2731 = p_noSeqTerm e3 in jump2 uu____2731 in
          FStar_Pprint.op_Hat_Hat uu____2722 uu____2730 in
        FStar_Pprint.group uu____2721
    | FStar_Parser_AST.Op
        ({ FStar_Ident.idText = ".[]<-"; FStar_Ident.idRange = uu____2732;_},e1::e2::e3::[])
        ->
        let uu____2737 =
          let uu____2738 =
            let uu____2739 =
              let uu____2740 = p_atomicTermNotQUident e1 in
              let uu____2741 =
                let uu____2742 =
                  let uu____2743 =
                    let uu____2744 = p_term e2 in
                    soft_brackets_with_nesting uu____2744 in
                  let uu____2745 =
                    FStar_Pprint.op_Hat_Hat FStar_Pprint.space
                      FStar_Pprint.larrow in
                  FStar_Pprint.op_Hat_Hat uu____2743 uu____2745 in
                FStar_Pprint.op_Hat_Hat FStar_Pprint.dot uu____2742 in
              FStar_Pprint.op_Hat_Hat uu____2740 uu____2741 in
            FStar_Pprint.group uu____2739 in
          let uu____2746 =
            let uu____2747 = p_noSeqTerm e3 in jump2 uu____2747 in
          FStar_Pprint.op_Hat_Hat uu____2738 uu____2746 in
        FStar_Pprint.group uu____2737
    | FStar_Parser_AST.Requires (e1,wtf) ->
        let uu____2753 =
          let uu____2754 = str "requires" in
          let uu____2755 = p_typ e1 in
          FStar_Pprint.op_Hat_Slash_Hat uu____2754 uu____2755 in
        FStar_Pprint.group uu____2753
    | FStar_Parser_AST.Ensures (e1,wtf) ->
        let uu____2761 =
          let uu____2762 = str "ensures" in
          let uu____2763 = p_typ e1 in
          FStar_Pprint.op_Hat_Slash_Hat uu____2762 uu____2763 in
        FStar_Pprint.group uu____2761
    | FStar_Parser_AST.Attributes es ->
        let uu____2766 =
          let uu____2767 = str "attributes" in
          let uu____2768 = FStar_Pprint.separate_map break1 p_atomicTerm es in
          FStar_Pprint.op_Hat_Slash_Hat uu____2767 uu____2768 in
        FStar_Pprint.group uu____2766
    | FStar_Parser_AST.If (e1,e2,e3) ->
        let uu____2772 = is_unit e3 in
        if uu____2772
        then
          let uu____2773 =
            let uu____2774 =
              let uu____2775 = str "if" in
              let uu____2776 = p_noSeqTerm e1 in
              op_Hat_Slash_Plus_Hat uu____2775 uu____2776 in
            let uu____2777 =
              let uu____2778 = str "then" in
              let uu____2779 = p_noSeqTerm e2 in
              op_Hat_Slash_Plus_Hat uu____2778 uu____2779 in
            FStar_Pprint.op_Hat_Slash_Hat uu____2774 uu____2777 in
          FStar_Pprint.group uu____2773
        else
          (let e2_doc =
             let uu____2782 =
               let uu____2783 = unparen e2 in uu____2783.FStar_Parser_AST.tm in
             match uu____2782 with
             | FStar_Parser_AST.If (uu____2784,uu____2785,e31) when
                 is_unit e31 ->
                 let uu____2787 = p_noSeqTerm e2 in
                 soft_parens_with_nesting uu____2787
             | uu____2788 -> p_noSeqTerm e2 in
           let uu____2789 =
             let uu____2790 =
               let uu____2791 = str "if" in
               let uu____2792 = p_noSeqTerm e1 in
               op_Hat_Slash_Plus_Hat uu____2791 uu____2792 in
             let uu____2793 =
               let uu____2794 =
                 let uu____2795 = str "then" in
                 op_Hat_Slash_Plus_Hat uu____2795 e2_doc in
               let uu____2796 =
                 let uu____2797 = str "else" in
                 let uu____2798 = p_noSeqTerm e3 in
                 op_Hat_Slash_Plus_Hat uu____2797 uu____2798 in
               FStar_Pprint.op_Hat_Slash_Hat uu____2794 uu____2796 in
             FStar_Pprint.op_Hat_Slash_Hat uu____2790 uu____2793 in
           FStar_Pprint.group uu____2789)
    | FStar_Parser_AST.TryWith (e1,branches) ->
        let uu____2811 =
          let uu____2812 =
            let uu____2813 = str "try" in
            let uu____2814 = p_noSeqTerm e1 in prefix2 uu____2813 uu____2814 in
          let uu____2815 =
            let uu____2816 = str "with" in
            let uu____2817 =
              FStar_Pprint.separate_map FStar_Pprint.hardline p_patternBranch
                branches in
            FStar_Pprint.op_Hat_Slash_Hat uu____2816 uu____2817 in
          FStar_Pprint.op_Hat_Slash_Hat uu____2812 uu____2815 in
        FStar_Pprint.group uu____2811
    | FStar_Parser_AST.Match (e1,branches) ->
        let uu____2834 =
          let uu____2835 =
            let uu____2836 = str "match" in
            let uu____2837 = p_noSeqTerm e1 in
            let uu____2838 = str "with" in
            FStar_Pprint.surround (Prims.parse_int "2") (Prims.parse_int "1")
              uu____2836 uu____2837 uu____2838 in
          let uu____2839 =
            FStar_Pprint.separate_map FStar_Pprint.hardline p_patternBranch
              branches in
          FStar_Pprint.op_Hat_Slash_Hat uu____2835 uu____2839 in
        FStar_Pprint.group uu____2834
    | FStar_Parser_AST.LetOpen (uid,e1) ->
        let uu____2846 =
          let uu____2847 =
            let uu____2848 = str "let open" in
            let uu____2849 = p_quident uid in
            let uu____2850 = str "in" in
            FStar_Pprint.surround (Prims.parse_int "2") (Prims.parse_int "1")
              uu____2848 uu____2849 uu____2850 in
          let uu____2851 = p_term e1 in
          FStar_Pprint.op_Hat_Slash_Hat uu____2847 uu____2851 in
        FStar_Pprint.group uu____2846
    | FStar_Parser_AST.Let (q,lbs,e1) ->
        let let_doc =
          let uu____2862 = str "let" in
          let uu____2863 = p_letqualifier q in
          FStar_Pprint.op_Hat_Hat uu____2862 uu____2863 in
        let uu____2864 =
          let uu____2865 =
            let uu____2866 =
              let uu____2867 = str "and" in
              precede_break_separate_map let_doc uu____2867 p_letbinding lbs in
            let uu____2870 = str "in" in
            FStar_Pprint.op_Hat_Slash_Hat uu____2866 uu____2870 in
          FStar_Pprint.group uu____2865 in
        let uu____2871 = p_term e1 in
        FStar_Pprint.op_Hat_Slash_Hat uu____2864 uu____2871
    | FStar_Parser_AST.Abs
        ({ FStar_Parser_AST.pat = FStar_Parser_AST.PatVar (x,typ_opt);
           FStar_Parser_AST.prange = uu____2874;_}::[],{
                                                         FStar_Parser_AST.tm
                                                           =
                                                           FStar_Parser_AST.Match
                                                           (maybe_x,branches);
                                                         FStar_Parser_AST.range
                                                           = uu____2877;
                                                         FStar_Parser_AST.level
                                                           = uu____2878;_})
        when matches_var maybe_x x ->
        let uu____2892 =
          let uu____2893 = str "function" in
          let uu____2894 =
            FStar_Pprint.separate_map FStar_Pprint.hardline p_patternBranch
              branches in
          FStar_Pprint.op_Hat_Slash_Hat uu____2893 uu____2894 in
        FStar_Pprint.group uu____2892
    | FStar_Parser_AST.Assign (id,e1) ->
        let uu____2901 =
          let uu____2902 = p_lident id in
          let uu____2903 =
            let uu____2904 = p_noSeqTerm e1 in
            FStar_Pprint.op_Hat_Slash_Hat FStar_Pprint.larrow uu____2904 in
          FStar_Pprint.op_Hat_Slash_Hat uu____2902 uu____2903 in
        FStar_Pprint.group uu____2901
    | uu____2905 -> p_typ e
and p_typ: FStar_Parser_AST.term -> FStar_Pprint.document =
  fun e  -> with_comment p_typ' e e.FStar_Parser_AST.range
and p_typ': FStar_Parser_AST.term -> FStar_Pprint.document =
  fun e  ->
    let uu____2908 =
      let uu____2909 = unparen e in uu____2909.FStar_Parser_AST.tm in
    match uu____2908 with
    | FStar_Parser_AST.QForall (bs,trigger,e1) ->
        let uu____2919 =
          let uu____2920 =
            let uu____2921 = p_quantifier e in
            FStar_Pprint.op_Hat_Hat uu____2921 FStar_Pprint.space in
          let uu____2922 = p_binders true bs in
          FStar_Pprint.soft_surround (Prims.parse_int "2")
            (Prims.parse_int "0") uu____2920 uu____2922 FStar_Pprint.dot in
        let uu____2923 =
          let uu____2924 = p_trigger trigger in
          let uu____2925 = p_noSeqTerm e1 in
          FStar_Pprint.op_Hat_Hat uu____2924 uu____2925 in
        prefix2 uu____2919 uu____2923
    | FStar_Parser_AST.QExists (bs,trigger,e1) ->
        let uu____2935 =
          let uu____2936 =
            let uu____2937 = p_quantifier e in
            FStar_Pprint.op_Hat_Hat uu____2937 FStar_Pprint.space in
          let uu____2938 = p_binders true bs in
          FStar_Pprint.soft_surround (Prims.parse_int "2")
            (Prims.parse_int "0") uu____2936 uu____2938 FStar_Pprint.dot in
        let uu____2939 =
          let uu____2940 = p_trigger trigger in
          let uu____2941 = p_noSeqTerm e1 in
          FStar_Pprint.op_Hat_Hat uu____2940 uu____2941 in
        prefix2 uu____2935 uu____2939
    | uu____2942 -> p_simpleTerm e
and p_quantifier: FStar_Parser_AST.term -> FStar_Pprint.document =
  fun e  ->
    let uu____2944 =
      let uu____2945 = unparen e in uu____2945.FStar_Parser_AST.tm in
    match uu____2944 with
    | FStar_Parser_AST.QForall uu____2946 -> str "forall"
    | FStar_Parser_AST.QExists uu____2953 -> str "exists"
    | uu____2960 ->
        failwith "Imposible : p_quantifier called on a non-quantifier term"
and p_trigger:
  FStar_Parser_AST.term Prims.list Prims.list -> FStar_Pprint.document =
  fun uu___104_2961  ->
    match uu___104_2961 with
    | [] -> FStar_Pprint.empty
    | pats ->
        let uu____2968 =
          let uu____2969 =
            let uu____2970 = str "pattern" in
            let uu____2971 =
              let uu____2972 =
                let uu____2973 = p_disjunctivePats pats in jump2 uu____2973 in
              let uu____2974 =
                FStar_Pprint.op_Hat_Hat FStar_Pprint.rbrace break1 in
              FStar_Pprint.op_Hat_Slash_Hat uu____2972 uu____2974 in
            FStar_Pprint.op_Hat_Slash_Hat uu____2970 uu____2971 in
          FStar_Pprint.op_Hat_Hat FStar_Pprint.colon uu____2969 in
        FStar_Pprint.op_Hat_Hat FStar_Pprint.lbrace uu____2968
and p_disjunctivePats:
  FStar_Parser_AST.term Prims.list Prims.list -> FStar_Pprint.document =
  fun pats  ->
    let uu____2978 = str "\\/" in
    FStar_Pprint.separate_map uu____2978 p_conjunctivePats pats
and p_conjunctivePats:
  FStar_Parser_AST.term Prims.list -> FStar_Pprint.document =
  fun pats  ->
    let uu____2982 =
      FStar_Pprint.separate_map FStar_Pprint.semi p_appTerm pats in
    FStar_Pprint.group uu____2982
and p_simpleTerm: FStar_Parser_AST.term -> FStar_Pprint.document =
  fun e  ->
    let uu____2984 =
      let uu____2985 = unparen e in uu____2985.FStar_Parser_AST.tm in
    match uu____2984 with
    | FStar_Parser_AST.Abs (pats,e1) ->
        let uu____2990 =
          let uu____2991 = str "fun" in
          let uu____2992 =
            let uu____2993 =
              FStar_Pprint.separate_map break1 p_atomicPattern pats in
            FStar_Pprint.op_Hat_Slash_Hat uu____2993 FStar_Pprint.rarrow in
          op_Hat_Slash_Plus_Hat uu____2991 uu____2992 in
        let uu____2994 = p_term e1 in
        op_Hat_Slash_Plus_Hat uu____2990 uu____2994
    | uu____2995 -> p_tmIff e
and p_maybeFocusArrow: Prims.bool -> FStar_Pprint.document =
  fun b  -> if b then str "~>" else FStar_Pprint.rarrow
and p_patternBranch:
  (FStar_Parser_AST.pattern* FStar_Parser_AST.term option*
    FStar_Parser_AST.term) -> FStar_Pprint.document
  =
  fun uu____2998  ->
    match uu____2998 with
    | (pat,when_opt,e) ->
        let maybe_paren =
          let uu____3011 =
            let uu____3012 = unparen e in uu____3012.FStar_Parser_AST.tm in
          match uu____3011 with
          | FStar_Parser_AST.Match uu____3015 -> soft_begin_end_with_nesting
          | FStar_Parser_AST.TryWith uu____3023 ->
              soft_begin_end_with_nesting
          | FStar_Parser_AST.Abs
              ({
                 FStar_Parser_AST.pat = FStar_Parser_AST.PatVar
                   (x,uu____3032);
                 FStar_Parser_AST.prange = uu____3033;_}::[],{
                                                               FStar_Parser_AST.tm
                                                                 =
                                                                 FStar_Parser_AST.Match
                                                                 (maybe_x,uu____3035);
                                                               FStar_Parser_AST.range
                                                                 = uu____3036;
                                                               FStar_Parser_AST.level
                                                                 = uu____3037;_})
              when matches_var maybe_x x -> soft_begin_end_with_nesting
          | uu____3051 -> (fun x  -> x) in
        let uu____3053 =
          let uu____3054 =
            let uu____3055 =
              let uu____3056 =
                let uu____3057 =
                  let uu____3058 = p_disjunctivePattern pat in
                  let uu____3059 =
                    let uu____3060 = p_maybeWhen when_opt in
                    FStar_Pprint.op_Hat_Hat uu____3060 FStar_Pprint.rarrow in
                  op_Hat_Slash_Plus_Hat uu____3058 uu____3059 in
                FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____3057 in
              FStar_Pprint.op_Hat_Hat FStar_Pprint.bar uu____3056 in
            FStar_Pprint.group uu____3055 in
          let uu____3061 =
            let uu____3062 = p_term e in maybe_paren uu____3062 in
          op_Hat_Slash_Plus_Hat uu____3054 uu____3061 in
        FStar_Pprint.group uu____3053
and p_maybeWhen: FStar_Parser_AST.term option -> FStar_Pprint.document =
  fun uu___105_3063  ->
    match uu___105_3063 with
    | None  -> FStar_Pprint.empty
    | Some e ->
        let uu____3066 = str "when" in
        let uu____3067 =
          let uu____3068 = p_tmFormula e in
          FStar_Pprint.op_Hat_Hat uu____3068 FStar_Pprint.space in
        op_Hat_Slash_Plus_Hat uu____3066 uu____3067
and p_tmIff: FStar_Parser_AST.term -> FStar_Pprint.document =
  fun e  ->
    let uu____3070 =
      let uu____3071 = unparen e in uu____3071.FStar_Parser_AST.tm in
    match uu____3070 with
    | FStar_Parser_AST.Op
        ({ FStar_Ident.idText = "<==>"; FStar_Ident.idRange = uu____3072;_},e1::e2::[])
        ->
        let uu____3076 = str "<==>" in
        let uu____3077 = p_tmImplies e1 in
        let uu____3078 = p_tmIff e2 in
        infix0 uu____3076 uu____3077 uu____3078
    | uu____3079 -> p_tmImplies e
and p_tmImplies: FStar_Parser_AST.term -> FStar_Pprint.document =
  fun e  ->
    let uu____3081 =
      let uu____3082 = unparen e in uu____3082.FStar_Parser_AST.tm in
    match uu____3081 with
    | FStar_Parser_AST.Op
        ({ FStar_Ident.idText = "==>"; FStar_Ident.idRange = uu____3083;_},e1::e2::[])
        ->
        let uu____3087 = str "==>" in
        let uu____3088 = p_tmArrow p_tmFormula e1 in
        let uu____3089 = p_tmImplies e2 in
        infix0 uu____3087 uu____3088 uu____3089
    | uu____3090 -> p_tmArrow p_tmFormula e
and p_tmArrow:
  (FStar_Parser_AST.term -> FStar_Pprint.document) ->
    FStar_Parser_AST.term -> FStar_Pprint.document
  =
  fun p_Tm  ->
    fun e  ->
      let uu____3095 =
        let uu____3096 = unparen e in uu____3096.FStar_Parser_AST.tm in
      match uu____3095 with
      | FStar_Parser_AST.Product (bs,tgt) ->
          let uu____3101 =
            let uu____3102 =
              FStar_Pprint.concat_map
                (fun b  ->
                   let uu____3104 = p_binder false b in
                   let uu____3105 =
                     let uu____3106 =
                       FStar_Pprint.op_Hat_Hat FStar_Pprint.rarrow break1 in
                     FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____3106 in
                   FStar_Pprint.op_Hat_Hat uu____3104 uu____3105) bs in
            let uu____3107 = p_tmArrow p_Tm tgt in
            FStar_Pprint.op_Hat_Hat uu____3102 uu____3107 in
          FStar_Pprint.group uu____3101
      | uu____3108 -> p_Tm e
and p_tmFormula: FStar_Parser_AST.term -> FStar_Pprint.document =
  fun e  ->
    let uu____3110 =
      let uu____3111 = unparen e in uu____3111.FStar_Parser_AST.tm in
    match uu____3110 with
    | FStar_Parser_AST.Op
        ({ FStar_Ident.idText = "\\/"; FStar_Ident.idRange = uu____3112;_},e1::e2::[])
        ->
        let uu____3116 = str "\\/" in
        let uu____3117 = p_tmFormula e1 in
        let uu____3118 = p_tmConjunction e2 in
        infix0 uu____3116 uu____3117 uu____3118
    | uu____3119 -> p_tmConjunction e
and p_tmConjunction: FStar_Parser_AST.term -> FStar_Pprint.document =
  fun e  ->
    let uu____3121 =
      let uu____3122 = unparen e in uu____3122.FStar_Parser_AST.tm in
    match uu____3121 with
    | FStar_Parser_AST.Op
        ({ FStar_Ident.idText = "/\\"; FStar_Ident.idRange = uu____3123;_},e1::e2::[])
        ->
        let uu____3127 = str "/\\" in
        let uu____3128 = p_tmConjunction e1 in
        let uu____3129 = p_tmTuple e2 in
        infix0 uu____3127 uu____3128 uu____3129
    | uu____3130 -> p_tmTuple e
and p_tmTuple: FStar_Parser_AST.term -> FStar_Pprint.document =
  fun e  -> with_comment p_tmTuple' e e.FStar_Parser_AST.range
and p_tmTuple': FStar_Parser_AST.term -> FStar_Pprint.document =
  fun e  ->
    let uu____3133 =
      let uu____3134 = unparen e in uu____3134.FStar_Parser_AST.tm in
    match uu____3133 with
    | FStar_Parser_AST.Construct (lid,args) when is_tuple_constructor lid ->
        let uu____3143 = FStar_Pprint.op_Hat_Hat FStar_Pprint.comma break1 in
        FStar_Pprint.separate_map uu____3143
          (fun uu____3146  ->
             match uu____3146 with | (e1,uu____3150) -> p_tmEq e1) args
    | uu____3151 -> p_tmEq e
and paren_if:
  Prims.int -> Prims.int -> FStar_Pprint.document -> FStar_Pprint.document =
  fun curr  ->
    fun mine  ->
      fun doc1  ->
        if mine <= curr
        then doc1
        else
          (let uu____3156 =
             let uu____3157 =
               FStar_Pprint.op_Hat_Hat doc1 FStar_Pprint.rparen in
             FStar_Pprint.op_Hat_Hat FStar_Pprint.lparen uu____3157 in
           FStar_Pprint.group uu____3156)
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
      let uu____3182 =
        let uu____3183 = unparen e in uu____3183.FStar_Parser_AST.tm in
      match uu____3182 with
      | FStar_Parser_AST.Op (op,e1::e2::[]) when
          ((is_operatorInfix0ad12 op) || ((FStar_Ident.text_of_id op) = "="))
            || ((FStar_Ident.text_of_id op) = "|>")
          ->
          let op1 = FStar_Ident.text_of_id op in
          let uu____3189 = levels op1 in
          (match uu____3189 with
           | (left1,mine,right1) ->
               let uu____3196 =
                 let uu____3197 = FStar_All.pipe_left str op1 in
                 let uu____3198 = p_tmEq' left1 e1 in
                 let uu____3199 = p_tmEq' right1 e2 in
                 infix0 uu____3197 uu____3198 uu____3199 in
               paren_if curr mine uu____3196)
      | FStar_Parser_AST.Op
          ({ FStar_Ident.idText = ":="; FStar_Ident.idRange = uu____3200;_},e1::e2::[])
          ->
          let uu____3204 =
            let uu____3205 = p_tmEq e1 in
            let uu____3206 =
              let uu____3207 =
                let uu____3208 =
                  let uu____3209 = p_tmEq e2 in
                  op_Hat_Slash_Plus_Hat FStar_Pprint.equals uu____3209 in
                FStar_Pprint.op_Hat_Hat FStar_Pprint.colon uu____3208 in
              FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____3207 in
            FStar_Pprint.op_Hat_Hat uu____3205 uu____3206 in
          FStar_Pprint.group uu____3204
      | FStar_Parser_AST.Op
          ({ FStar_Ident.idText = "-"; FStar_Ident.idRange = uu____3210;_},e1::[])
          ->
          let uu____3213 = levels "-" in
          (match uu____3213 with
           | (left1,mine,right1) ->
               let uu____3220 = p_tmEq' mine e1 in
               FStar_Pprint.op_Hat_Slash_Hat FStar_Pprint.minus uu____3220)
      | uu____3221 -> p_tmNoEq e
and p_tmNoEq: FStar_Parser_AST.term -> FStar_Pprint.document =
  fun e  ->
    let n1 = max_level [colon_colon (); amp (); opinfix3 (); opinfix4 ()] in
    p_tmNoEq' n1 e
and p_tmNoEq': Prims.int -> FStar_Parser_AST.term -> FStar_Pprint.document =
  fun curr  ->
    fun e  ->
      let uu____3251 =
        let uu____3252 = unparen e in uu____3252.FStar_Parser_AST.tm in
      match uu____3251 with
      | FStar_Parser_AST.Construct (lid,(e1,uu____3255)::(e2,uu____3257)::[])
          when
          (FStar_Ident.lid_equals lid FStar_Parser_Const.cons_lid) &&
            (let uu____3267 = is_list e in Prims.op_Negation uu____3267)
          ->
          let op = "::" in
          let uu____3269 = levels op in
          (match uu____3269 with
           | (left1,mine,right1) ->
               let uu____3276 =
                 let uu____3277 = str op in
                 let uu____3278 = p_tmNoEq' left1 e1 in
                 let uu____3279 = p_tmNoEq' right1 e2 in
                 infix0 uu____3277 uu____3278 uu____3279 in
               paren_if curr mine uu____3276)
      | FStar_Parser_AST.Sum (binders,res) ->
          let op = "&" in
          let uu____3285 = levels op in
          (match uu____3285 with
           | (left1,mine,right1) ->
               let p_dsumfst b =
                 let uu____3296 = p_binder false b in
                 let uu____3297 =
                   let uu____3298 =
                     let uu____3299 = str op in
                     FStar_Pprint.op_Hat_Hat uu____3299 break1 in
                   FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____3298 in
                 FStar_Pprint.op_Hat_Hat uu____3296 uu____3297 in
               let uu____3300 =
                 let uu____3301 = FStar_Pprint.concat_map p_dsumfst binders in
                 let uu____3302 = p_tmNoEq' right1 res in
                 FStar_Pprint.op_Hat_Hat uu____3301 uu____3302 in
               paren_if curr mine uu____3300)
      | FStar_Parser_AST.Op (op,e1::e2::[]) when is_operatorInfix34 op ->
          let op1 = FStar_Ident.text_of_id op in
          let uu____3308 = levels op1 in
          (match uu____3308 with
           | (left1,mine,right1) ->
               let uu____3315 =
                 let uu____3316 = str op1 in
                 let uu____3317 = p_tmNoEq' left1 e1 in
                 let uu____3318 = p_tmNoEq' right1 e2 in
                 infix0 uu____3316 uu____3317 uu____3318 in
               paren_if curr mine uu____3315)
      | FStar_Parser_AST.NamedTyp (lid,e1) ->
          let uu____3321 =
            let uu____3322 = p_lidentOrUnderscore lid in
            let uu____3323 =
              let uu____3324 = p_appTerm e1 in
              FStar_Pprint.op_Hat_Slash_Hat FStar_Pprint.colon uu____3324 in
            FStar_Pprint.op_Hat_Slash_Hat uu____3322 uu____3323 in
          FStar_Pprint.group uu____3321
      | FStar_Parser_AST.Refine (b,phi) -> p_refinedBinder b phi
      | FStar_Parser_AST.Record (with_opt,record_fields) ->
          let uu____3337 =
            let uu____3338 =
              default_or_map FStar_Pprint.empty p_with_clause with_opt in
            let uu____3339 =
              let uu____3340 =
                FStar_Pprint.op_Hat_Hat FStar_Pprint.semi break1 in
              FStar_Pprint.separate_map uu____3340 p_simpleDef record_fields in
            FStar_Pprint.op_Hat_Hat uu____3338 uu____3339 in
          braces_with_nesting uu____3337
      | FStar_Parser_AST.Op
          ({ FStar_Ident.idText = "~"; FStar_Ident.idRange = uu____3343;_},e1::[])
          ->
          let uu____3346 =
            let uu____3347 = str "~" in
            let uu____3348 = p_atomicTerm e1 in
            FStar_Pprint.op_Hat_Hat uu____3347 uu____3348 in
          FStar_Pprint.group uu____3346
      | uu____3349 -> p_appTerm e
and p_with_clause: FStar_Parser_AST.term -> FStar_Pprint.document =
  fun e  ->
    let uu____3351 = p_appTerm e in
    let uu____3352 =
      let uu____3353 =
        let uu____3354 = str "with" in
        FStar_Pprint.op_Hat_Hat uu____3354 break1 in
      FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____3353 in
    FStar_Pprint.op_Hat_Hat uu____3351 uu____3352
and p_refinedBinder:
  FStar_Parser_AST.binder -> FStar_Parser_AST.term -> FStar_Pprint.document =
  fun b  ->
    fun phi  ->
      match b.FStar_Parser_AST.b with
      | FStar_Parser_AST.Annotated (lid,t) ->
          let uu____3359 =
            let uu____3360 = p_lident lid in
            p_refinement b.FStar_Parser_AST.aqual uu____3360 t phi in
          soft_parens_with_nesting uu____3359
      | FStar_Parser_AST.TAnnotated uu____3361 ->
          failwith "Is this still used ?"
      | FStar_Parser_AST.Variable uu____3364 ->
          let uu____3365 =
            let uu____3366 = FStar_Parser_AST.binder_to_string b in
            FStar_Util.format1
              "Imposible : a refined binder ought to be annotated %s"
              uu____3366 in
          failwith uu____3365
      | FStar_Parser_AST.TVariable uu____3367 ->
          let uu____3368 =
            let uu____3369 = FStar_Parser_AST.binder_to_string b in
            FStar_Util.format1
              "Imposible : a refined binder ought to be annotated %s"
              uu____3369 in
          failwith uu____3368
      | FStar_Parser_AST.NoName uu____3370 ->
          let uu____3371 =
            let uu____3372 = FStar_Parser_AST.binder_to_string b in
            FStar_Util.format1
              "Imposible : a refined binder ought to be annotated %s"
              uu____3372 in
          failwith uu____3371
and p_simpleDef:
  (FStar_Ident.lid* FStar_Parser_AST.term) -> FStar_Pprint.document =
  fun uu____3373  ->
    match uu____3373 with
    | (lid,e) ->
        let uu____3378 =
          let uu____3379 = p_qlident lid in
          let uu____3380 =
            let uu____3381 = p_tmIff e in
            FStar_Pprint.op_Hat_Slash_Hat FStar_Pprint.equals uu____3381 in
          FStar_Pprint.op_Hat_Slash_Hat uu____3379 uu____3380 in
        FStar_Pprint.group uu____3378
and p_appTerm: FStar_Parser_AST.term -> FStar_Pprint.document =
  fun e  ->
    let uu____3383 =
      let uu____3384 = unparen e in uu____3384.FStar_Parser_AST.tm in
    match uu____3383 with
    | FStar_Parser_AST.App uu____3385 when is_general_application e ->
        let uu____3389 = head_and_args e in
        (match uu____3389 with
         | (head1,args) ->
             let uu____3403 =
               let uu____3409 = FStar_ST.read should_print_fs_typ_app in
               if uu____3409
               then
                 let uu____3417 =
                   FStar_Util.take
                     (fun uu____3428  ->
                        match uu____3428 with
                        | (uu____3431,aq) -> aq = FStar_Parser_AST.FsTypApp)
                     args in
                 match uu____3417 with
                 | (fs_typ_args,args1) ->
                     let uu____3452 =
                       let uu____3453 = p_indexingTerm head1 in
                       let uu____3454 =
                         let uu____3455 =
                           FStar_Pprint.op_Hat_Hat FStar_Pprint.comma break1 in
                         soft_surround_separate_map (Prims.parse_int "2")
                           (Prims.parse_int "0") FStar_Pprint.empty
                           FStar_Pprint.langle uu____3455 FStar_Pprint.rangle
                           p_fsTypArg fs_typ_args in
                       FStar_Pprint.op_Hat_Hat uu____3453 uu____3454 in
                     (uu____3452, args1)
               else
                 (let uu____3462 = p_indexingTerm head1 in (uu____3462, args)) in
             (match uu____3403 with
              | (head_doc,args1) ->
                  let uu____3474 =
                    let uu____3475 =
                      FStar_Pprint.op_Hat_Hat head_doc FStar_Pprint.space in
                    soft_surround_separate_map (Prims.parse_int "2")
                      (Prims.parse_int "0") head_doc uu____3475 break1
                      FStar_Pprint.empty p_argTerm args1 in
                  FStar_Pprint.group uu____3474))
    | FStar_Parser_AST.Construct (lid,args) when
        (is_general_construction e) &&
          (Prims.op_Negation (is_dtuple_constructor lid))
        ->
        (match args with
         | [] -> p_quident lid
         | arg::[] ->
             let uu____3495 =
               let uu____3496 = p_quident lid in
               let uu____3497 = p_argTerm arg in
               FStar_Pprint.op_Hat_Slash_Hat uu____3496 uu____3497 in
             FStar_Pprint.group uu____3495
         | hd1::tl1 ->
             let uu____3507 =
               let uu____3508 =
                 let uu____3509 =
                   let uu____3510 = p_quident lid in
                   let uu____3511 = p_argTerm hd1 in
                   prefix2 uu____3510 uu____3511 in
                 FStar_Pprint.group uu____3509 in
               let uu____3512 =
                 let uu____3513 =
                   FStar_Pprint.separate_map break1 p_argTerm tl1 in
                 jump2 uu____3513 in
               FStar_Pprint.op_Hat_Hat uu____3508 uu____3512 in
             FStar_Pprint.group uu____3507)
    | uu____3516 -> p_indexingTerm e
and p_argTerm:
  (FStar_Parser_AST.term* FStar_Parser_AST.imp) -> FStar_Pprint.document =
  fun arg_imp  ->
    match arg_imp with
    | ({ FStar_Parser_AST.tm = FStar_Parser_AST.Uvar uu____3520;
         FStar_Parser_AST.range = uu____3521;
         FStar_Parser_AST.level = uu____3522;_},FStar_Parser_AST.UnivApp
       ) -> p_univar (fst arg_imp)
    | (u,FStar_Parser_AST.UnivApp ) -> p_universe u
    | (e,FStar_Parser_AST.FsTypApp ) ->
        (FStar_Util.print_warning
           "Unexpected FsTypApp, output might not be formatted correctly.\n";
         (let uu____3526 = p_indexingTerm e in
          FStar_Pprint.surround (Prims.parse_int "2") (Prims.parse_int "1")
            FStar_Pprint.langle uu____3526 FStar_Pprint.rangle))
    | (e,FStar_Parser_AST.Hash ) ->
        let uu____3528 = str "#" in
        let uu____3529 = p_indexingTerm e in
        FStar_Pprint.op_Hat_Hat uu____3528 uu____3529
    | (e,FStar_Parser_AST.Nothing ) -> p_indexingTerm e
and p_fsTypArg:
  (FStar_Parser_AST.term* FStar_Parser_AST.imp) -> FStar_Pprint.document =
  fun uu____3531  ->
    match uu____3531 with | (e,uu____3535) -> p_indexingTerm e
and p_indexingTerm_aux:
  (FStar_Parser_AST.term -> FStar_Pprint.document) ->
    FStar_Parser_AST.term -> FStar_Pprint.document
  =
  fun exit1  ->
    fun e  ->
      let uu____3540 =
        let uu____3541 = unparen e in uu____3541.FStar_Parser_AST.tm in
      match uu____3540 with
      | FStar_Parser_AST.Op
          ({ FStar_Ident.idText = ".()"; FStar_Ident.idRange = uu____3542;_},e1::e2::[])
          ->
          let uu____3546 =
            let uu____3547 = p_indexingTerm_aux p_atomicTermNotQUident e1 in
            let uu____3548 =
              let uu____3549 =
                let uu____3550 = p_term e2 in
                soft_parens_with_nesting uu____3550 in
              FStar_Pprint.op_Hat_Hat FStar_Pprint.dot uu____3549 in
            FStar_Pprint.op_Hat_Hat uu____3547 uu____3548 in
          FStar_Pprint.group uu____3546
      | FStar_Parser_AST.Op
          ({ FStar_Ident.idText = ".[]"; FStar_Ident.idRange = uu____3551;_},e1::e2::[])
          ->
          let uu____3555 =
            let uu____3556 = p_indexingTerm_aux p_atomicTermNotQUident e1 in
            let uu____3557 =
              let uu____3558 =
                let uu____3559 = p_term e2 in
                soft_brackets_with_nesting uu____3559 in
              FStar_Pprint.op_Hat_Hat FStar_Pprint.dot uu____3558 in
            FStar_Pprint.op_Hat_Hat uu____3556 uu____3557 in
          FStar_Pprint.group uu____3555
      | uu____3560 -> exit1 e
and p_indexingTerm: FStar_Parser_AST.term -> FStar_Pprint.document =
  fun e  -> p_indexingTerm_aux p_atomicTerm e
and p_atomicTerm: FStar_Parser_AST.term -> FStar_Pprint.document =
  fun e  ->
    let uu____3563 =
      let uu____3564 = unparen e in uu____3564.FStar_Parser_AST.tm in
    match uu____3563 with
    | FStar_Parser_AST.LetOpen (lid,e1) ->
        let uu____3567 = p_quident lid in
        let uu____3568 =
          let uu____3569 =
            let uu____3570 = p_term e1 in soft_parens_with_nesting uu____3570 in
          FStar_Pprint.op_Hat_Hat FStar_Pprint.dot uu____3569 in
        FStar_Pprint.op_Hat_Hat uu____3567 uu____3568
    | FStar_Parser_AST.Name lid -> p_quident lid
    | FStar_Parser_AST.Op (op,e1::[]) when is_general_prefix_op op ->
        let uu____3575 = str (FStar_Ident.text_of_id op) in
        let uu____3576 = p_atomicTerm e1 in
        FStar_Pprint.op_Hat_Hat uu____3575 uu____3576
    | uu____3577 -> p_atomicTermNotQUident e
and p_atomicTermNotQUident: FStar_Parser_AST.term -> FStar_Pprint.document =
  fun e  ->
    let uu____3579 =
      let uu____3580 = unparen e in uu____3580.FStar_Parser_AST.tm in
    match uu____3579 with
    | FStar_Parser_AST.Wild  -> FStar_Pprint.underscore
    | FStar_Parser_AST.Var lid when
        FStar_Ident.lid_equals lid FStar_Parser_Const.assert_lid ->
        str "assert"
    | FStar_Parser_AST.Tvar tv -> p_tvar tv
    | FStar_Parser_AST.Const c ->
        (match c with
         | FStar_Const.Const_char x when x = '\n' -> str "0x0Az"
         | uu____3585 -> p_constant c)
    | FStar_Parser_AST.Name lid when
        FStar_Ident.lid_equals lid FStar_Parser_Const.true_lid -> str "True"
    | FStar_Parser_AST.Name lid when
        FStar_Ident.lid_equals lid FStar_Parser_Const.false_lid ->
        str "False"
    | FStar_Parser_AST.Op (op,e1::[]) when is_general_prefix_op op ->
        let uu____3591 = str (FStar_Ident.text_of_id op) in
        let uu____3592 = p_atomicTermNotQUident e1 in
        FStar_Pprint.op_Hat_Hat uu____3591 uu____3592
    | FStar_Parser_AST.Op (op,[]) ->
        let uu____3595 =
          let uu____3596 =
            let uu____3597 = str (FStar_Ident.text_of_id op) in
            let uu____3598 =
              FStar_Pprint.op_Hat_Hat FStar_Pprint.space FStar_Pprint.rparen in
            FStar_Pprint.op_Hat_Hat uu____3597 uu____3598 in
          FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____3596 in
        FStar_Pprint.op_Hat_Hat FStar_Pprint.lparen uu____3595
    | FStar_Parser_AST.Construct (lid,args) when is_dtuple_constructor lid ->
        let uu____3607 =
          FStar_Pprint.op_Hat_Hat FStar_Pprint.lparen FStar_Pprint.bar in
        let uu____3608 =
          let uu____3609 = FStar_Pprint.op_Hat_Hat FStar_Pprint.comma break1 in
          let uu____3610 = FStar_List.map FStar_Pervasives.fst args in
          FStar_Pprint.separate_map uu____3609 p_tmEq uu____3610 in
        let uu____3614 =
          FStar_Pprint.op_Hat_Hat FStar_Pprint.bar FStar_Pprint.rparen in
        FStar_Pprint.surround (Prims.parse_int "2") (Prims.parse_int "1")
          uu____3607 uu____3608 uu____3614
    | FStar_Parser_AST.Project (e1,lid) ->
        let uu____3617 =
          let uu____3618 = p_atomicTermNotQUident e1 in
          let uu____3619 =
            let uu____3620 = p_qlident lid in
            FStar_Pprint.op_Hat_Hat FStar_Pprint.dot uu____3620 in
          FStar_Pprint.prefix (Prims.parse_int "2") (Prims.parse_int "0")
            uu____3618 uu____3619 in
        FStar_Pprint.group uu____3617
    | uu____3621 -> p_projectionLHS e
and p_projectionLHS: FStar_Parser_AST.term -> FStar_Pprint.document =
  fun e  ->
    let uu____3623 =
      let uu____3624 = unparen e in uu____3624.FStar_Parser_AST.tm in
    match uu____3623 with
    | FStar_Parser_AST.Var lid -> p_qlident lid
    | FStar_Parser_AST.Projector (constr_lid,field_lid) ->
        let uu____3628 = p_quident constr_lid in
        let uu____3629 =
          let uu____3630 =
            let uu____3631 = p_lident field_lid in
            FStar_Pprint.op_Hat_Hat FStar_Pprint.dot uu____3631 in
          FStar_Pprint.op_Hat_Hat FStar_Pprint.qmark uu____3630 in
        FStar_Pprint.op_Hat_Hat uu____3628 uu____3629
    | FStar_Parser_AST.Discrim constr_lid ->
        let uu____3633 = p_quident constr_lid in
        FStar_Pprint.op_Hat_Hat uu____3633 FStar_Pprint.qmark
    | FStar_Parser_AST.Paren e1 ->
        let uu____3635 = p_term e1 in soft_parens_with_nesting uu____3635
    | uu____3636 when is_array e ->
        let es = extract_from_list e in
        let uu____3639 =
          FStar_Pprint.op_Hat_Hat FStar_Pprint.lbracket FStar_Pprint.bar in
        let uu____3640 =
          let uu____3641 = FStar_Pprint.op_Hat_Hat FStar_Pprint.semi break1 in
          separate_map_or_flow uu____3641 p_noSeqTerm es in
        let uu____3642 =
          FStar_Pprint.op_Hat_Hat FStar_Pprint.bar FStar_Pprint.rbracket in
        FStar_Pprint.surround (Prims.parse_int "2") (Prims.parse_int "0")
          uu____3639 uu____3640 uu____3642
    | uu____3643 when is_list e ->
        let uu____3644 =
          let uu____3645 = FStar_Pprint.op_Hat_Hat FStar_Pprint.semi break1 in
          let uu____3646 = extract_from_list e in
          separate_map_or_flow uu____3645 p_noSeqTerm uu____3646 in
        FStar_Pprint.surround (Prims.parse_int "2") (Prims.parse_int "0")
          FStar_Pprint.lbracket uu____3644 FStar_Pprint.rbracket
    | uu____3648 when is_lex_list e ->
        let uu____3649 =
          FStar_Pprint.op_Hat_Hat FStar_Pprint.percent FStar_Pprint.lbracket in
        let uu____3650 =
          let uu____3651 = FStar_Pprint.op_Hat_Hat FStar_Pprint.semi break1 in
          let uu____3652 = extract_from_list e in
          separate_map_or_flow uu____3651 p_noSeqTerm uu____3652 in
        FStar_Pprint.surround (Prims.parse_int "2") (Prims.parse_int "1")
          uu____3649 uu____3650 FStar_Pprint.rbracket
    | uu____3654 when is_ref_set e ->
        let es = extract_from_ref_set e in
        let uu____3657 =
          FStar_Pprint.op_Hat_Hat FStar_Pprint.bang FStar_Pprint.lbrace in
        let uu____3658 =
          let uu____3659 = FStar_Pprint.op_Hat_Hat FStar_Pprint.comma break1 in
          separate_map_or_flow uu____3659 p_appTerm es in
        FStar_Pprint.surround (Prims.parse_int "2") (Prims.parse_int "0")
          uu____3657 uu____3658 FStar_Pprint.rbrace
    | FStar_Parser_AST.Labeled (e1,s,b) ->
        let uu____3663 = FStar_Pprint.break_ (Prims.parse_int "0") in
        let uu____3664 =
          let uu____3665 = str (Prims.strcat "(*" (Prims.strcat s "*)")) in
          let uu____3666 = p_term e1 in
          FStar_Pprint.op_Hat_Slash_Hat uu____3665 uu____3666 in
        FStar_Pprint.op_Hat_Hat uu____3663 uu____3664
    | FStar_Parser_AST.Op (op,args) when
        let uu____3671 = handleable_op op args in
        Prims.op_Negation uu____3671 ->
        let uu____3672 =
          let uu____3673 =
            let uu____3674 =
              let uu____3675 =
                let uu____3676 =
                  FStar_Util.string_of_int (FStar_List.length args) in
                Prims.strcat uu____3676
                  " arguments couldn't be handled by the pretty printer" in
              Prims.strcat " with " uu____3675 in
            Prims.strcat (FStar_Ident.text_of_id op) uu____3674 in
          Prims.strcat "Operation " uu____3673 in
        failwith uu____3672
    | FStar_Parser_AST.Uvar uu____3683 ->
        failwith "Unexpected universe variable out of universe context"
    | FStar_Parser_AST.Wild  ->
        let uu____3684 = p_term e in soft_parens_with_nesting uu____3684
    | FStar_Parser_AST.Const uu____3685 ->
        let uu____3686 = p_term e in soft_parens_with_nesting uu____3686
    | FStar_Parser_AST.Op uu____3687 ->
        let uu____3691 = p_term e in soft_parens_with_nesting uu____3691
    | FStar_Parser_AST.Tvar uu____3692 ->
        let uu____3693 = p_term e in soft_parens_with_nesting uu____3693
    | FStar_Parser_AST.Var uu____3694 ->
        let uu____3695 = p_term e in soft_parens_with_nesting uu____3695
    | FStar_Parser_AST.Name uu____3696 ->
        let uu____3697 = p_term e in soft_parens_with_nesting uu____3697
    | FStar_Parser_AST.Construct uu____3698 ->
        let uu____3704 = p_term e in soft_parens_with_nesting uu____3704
    | FStar_Parser_AST.Abs uu____3705 ->
        let uu____3709 = p_term e in soft_parens_with_nesting uu____3709
    | FStar_Parser_AST.App uu____3710 ->
        let uu____3714 = p_term e in soft_parens_with_nesting uu____3714
    | FStar_Parser_AST.Let uu____3715 ->
        let uu____3722 = p_term e in soft_parens_with_nesting uu____3722
    | FStar_Parser_AST.LetOpen uu____3723 ->
        let uu____3726 = p_term e in soft_parens_with_nesting uu____3726
    | FStar_Parser_AST.Seq uu____3727 ->
        let uu____3730 = p_term e in soft_parens_with_nesting uu____3730
    | FStar_Parser_AST.Bind uu____3731 ->
        let uu____3735 = p_term e in soft_parens_with_nesting uu____3735
    | FStar_Parser_AST.If uu____3736 ->
        let uu____3740 = p_term e in soft_parens_with_nesting uu____3740
    | FStar_Parser_AST.Match uu____3741 ->
        let uu____3749 = p_term e in soft_parens_with_nesting uu____3749
    | FStar_Parser_AST.TryWith uu____3750 ->
        let uu____3758 = p_term e in soft_parens_with_nesting uu____3758
    | FStar_Parser_AST.Ascribed uu____3759 ->
        let uu____3764 = p_term e in soft_parens_with_nesting uu____3764
    | FStar_Parser_AST.Record uu____3765 ->
        let uu____3772 = p_term e in soft_parens_with_nesting uu____3772
    | FStar_Parser_AST.Project uu____3773 ->
        let uu____3776 = p_term e in soft_parens_with_nesting uu____3776
    | FStar_Parser_AST.Product uu____3777 ->
        let uu____3781 = p_term e in soft_parens_with_nesting uu____3781
    | FStar_Parser_AST.Sum uu____3782 ->
        let uu____3786 = p_term e in soft_parens_with_nesting uu____3786
    | FStar_Parser_AST.QForall uu____3787 ->
        let uu____3794 = p_term e in soft_parens_with_nesting uu____3794
    | FStar_Parser_AST.QExists uu____3795 ->
        let uu____3802 = p_term e in soft_parens_with_nesting uu____3802
    | FStar_Parser_AST.Refine uu____3803 ->
        let uu____3806 = p_term e in soft_parens_with_nesting uu____3806
    | FStar_Parser_AST.NamedTyp uu____3807 ->
        let uu____3810 = p_term e in soft_parens_with_nesting uu____3810
    | FStar_Parser_AST.Requires uu____3811 ->
        let uu____3815 = p_term e in soft_parens_with_nesting uu____3815
    | FStar_Parser_AST.Ensures uu____3816 ->
        let uu____3820 = p_term e in soft_parens_with_nesting uu____3820
    | FStar_Parser_AST.Assign uu____3821 ->
        let uu____3824 = p_term e in soft_parens_with_nesting uu____3824
    | FStar_Parser_AST.Attributes uu____3825 ->
        let uu____3827 = p_term e in soft_parens_with_nesting uu____3827
and p_constant: FStar_Const.sconst -> FStar_Pprint.document =
  fun uu___108_3828  ->
    match uu___108_3828 with
    | FStar_Const.Const_effect  -> str "Effect"
    | FStar_Const.Const_unit  -> str "()"
    | FStar_Const.Const_bool b -> FStar_Pprint.doc_of_bool b
    | FStar_Const.Const_float x -> str (FStar_Util.string_of_float x)
    | FStar_Const.Const_char x ->
        let uu____3832 = FStar_Pprint.doc_of_char x in
        FStar_Pprint.squotes uu____3832
    | FStar_Const.Const_string (bytes,uu____3834) ->
        let uu____3837 = str (FStar_Util.string_of_bytes bytes) in
        FStar_Pprint.dquotes uu____3837
    | FStar_Const.Const_bytearray (bytes,uu____3839) ->
        let uu____3842 =
          let uu____3843 = str (FStar_Util.string_of_bytes bytes) in
          FStar_Pprint.dquotes uu____3843 in
        let uu____3844 = str "B" in
        FStar_Pprint.op_Hat_Hat uu____3842 uu____3844
    | FStar_Const.Const_int (repr,sign_width_opt) ->
        let signedness uu___106_3856 =
          match uu___106_3856 with
          | FStar_Const.Unsigned  -> str "u"
          | FStar_Const.Signed  -> FStar_Pprint.empty in
        let width uu___107_3860 =
          match uu___107_3860 with
          | FStar_Const.Int8  -> str "y"
          | FStar_Const.Int16  -> str "s"
          | FStar_Const.Int32  -> str "l"
          | FStar_Const.Int64  -> str "L" in
        let ending =
          default_or_map FStar_Pprint.empty
            (fun uu____3864  ->
               match uu____3864 with
               | (s,w) ->
                   let uu____3869 = signedness s in
                   let uu____3870 = width w in
                   FStar_Pprint.op_Hat_Hat uu____3869 uu____3870)
            sign_width_opt in
        let uu____3871 = str repr in
        FStar_Pprint.op_Hat_Hat uu____3871 ending
    | FStar_Const.Const_range r ->
        let uu____3873 = FStar_Range.string_of_range r in str uu____3873
    | FStar_Const.Const_reify  -> str "reify"
    | FStar_Const.Const_reflect lid ->
        let uu____3875 = p_quident lid in
        let uu____3876 =
          let uu____3877 =
            let uu____3878 = str "reflect" in
            FStar_Pprint.op_Hat_Hat FStar_Pprint.dot uu____3878 in
          FStar_Pprint.op_Hat_Hat FStar_Pprint.qmark uu____3877 in
        FStar_Pprint.op_Hat_Hat uu____3875 uu____3876
and p_universe: FStar_Parser_AST.term -> FStar_Pprint.document =
  fun u  ->
    let uu____3880 = str "u#" in
    let uu____3881 = p_atomicUniverse u in
    FStar_Pprint.op_Hat_Hat uu____3880 uu____3881
and p_universeFrom: FStar_Parser_AST.term -> FStar_Pprint.document =
  fun u  ->
    let uu____3883 =
      let uu____3884 = unparen u in uu____3884.FStar_Parser_AST.tm in
    match uu____3883 with
    | FStar_Parser_AST.Op
        ({ FStar_Ident.idText = "+"; FStar_Ident.idRange = uu____3885;_},u1::u2::[])
        ->
        let uu____3889 =
          let uu____3890 = p_universeFrom u1 in
          let uu____3891 =
            let uu____3892 = p_universeFrom u2 in
            FStar_Pprint.op_Hat_Slash_Hat FStar_Pprint.plus uu____3892 in
          FStar_Pprint.op_Hat_Slash_Hat uu____3890 uu____3891 in
        FStar_Pprint.group uu____3889
    | FStar_Parser_AST.App uu____3893 ->
        let uu____3897 = head_and_args u in
        (match uu____3897 with
         | (head1,args) ->
             let uu____3911 =
               let uu____3912 = unparen head1 in
               uu____3912.FStar_Parser_AST.tm in
             (match uu____3911 with
              | FStar_Parser_AST.Var maybe_max_lid when
                  FStar_Ident.lid_equals maybe_max_lid
                    FStar_Parser_Const.max_lid
                  ->
                  let uu____3914 =
                    let uu____3915 = p_qlident FStar_Parser_Const.max_lid in
                    let uu____3916 =
                      FStar_Pprint.separate_map FStar_Pprint.space
                        (fun uu____3919  ->
                           match uu____3919 with
                           | (u1,uu____3923) -> p_atomicUniverse u1) args in
                    op_Hat_Slash_Plus_Hat uu____3915 uu____3916 in
                  FStar_Pprint.group uu____3914
              | uu____3924 ->
                  let uu____3925 =
                    let uu____3926 = FStar_Parser_AST.term_to_string u in
                    FStar_Util.format1 "Invalid term in universe context %s"
                      uu____3926 in
                  failwith uu____3925))
    | uu____3927 -> p_atomicUniverse u
and p_atomicUniverse: FStar_Parser_AST.term -> FStar_Pprint.document =
  fun u  ->
    let uu____3929 =
      let uu____3930 = unparen u in uu____3930.FStar_Parser_AST.tm in
    match uu____3929 with
    | FStar_Parser_AST.Wild  -> FStar_Pprint.underscore
    | FStar_Parser_AST.Const (FStar_Const.Const_int (r,sw)) ->
        p_constant (FStar_Const.Const_int (r, sw))
    | FStar_Parser_AST.Uvar uu____3942 -> p_univar u
    | FStar_Parser_AST.Paren u1 ->
        let uu____3944 = p_universeFrom u1 in
        soft_parens_with_nesting uu____3944
    | FStar_Parser_AST.Op
        ({ FStar_Ident.idText = "+"; FStar_Ident.idRange = uu____3945;_},uu____3946::uu____3947::[])
        ->
        let uu____3949 = p_universeFrom u in
        soft_parens_with_nesting uu____3949
    | FStar_Parser_AST.App uu____3950 ->
        let uu____3954 = p_universeFrom u in
        soft_parens_with_nesting uu____3954
    | uu____3955 ->
        let uu____3956 =
          let uu____3957 = FStar_Parser_AST.term_to_string u in
          FStar_Util.format1 "Invalid term in universe context %s" uu____3957 in
        failwith uu____3956
and p_univar: FStar_Parser_AST.term -> FStar_Pprint.document =
  fun u  ->
    let uu____3959 =
      let uu____3960 = unparen u in uu____3960.FStar_Parser_AST.tm in
    match uu____3959 with
    | FStar_Parser_AST.Uvar id -> str (FStar_Ident.text_of_id id)
    | uu____3962 ->
        let uu____3963 =
          let uu____3964 = FStar_Parser_AST.term_to_string u in
          FStar_Util.format1 "Not a universe variable %s" uu____3964 in
        failwith uu____3963
let term_to_document: FStar_Parser_AST.term -> FStar_Pprint.document =
  fun e  -> p_term e
let decl_to_document: FStar_Parser_AST.decl -> FStar_Pprint.document =
  fun e  -> p_decl e
let pat_to_document: FStar_Parser_AST.pattern -> FStar_Pprint.document =
  fun p  -> p_disjunctivePattern p
let binder_to_document: FStar_Parser_AST.binder -> FStar_Pprint.document =
  fun b  -> p_binder true b
let modul_to_document: FStar_Parser_AST.modul -> FStar_Pprint.document =
  fun m  ->
    FStar_ST.write should_print_fs_typ_app false;
    (let res =
       match m with
       | FStar_Parser_AST.Module (uu____3984,decls) ->
           let uu____3988 =
             FStar_All.pipe_right decls (FStar_List.map decl_to_document) in
           FStar_All.pipe_right uu____3988
             (FStar_Pprint.separate FStar_Pprint.hardline)
       | FStar_Parser_AST.Interface (uu____3993,decls,uu____3995) ->
           let uu____3998 =
             FStar_All.pipe_right decls (FStar_List.map decl_to_document) in
           FStar_All.pipe_right uu____3998
             (FStar_Pprint.separate FStar_Pprint.hardline) in
     FStar_ST.write should_print_fs_typ_app false; res)
let comments_to_document:
  (Prims.string* FStar_Range.range) Prims.list -> FStar_Pprint.document =
  fun comments  ->
    FStar_Pprint.separate_map FStar_Pprint.hardline
      (fun uu____4017  ->
         match uu____4017 with | (comment,range) -> str comment) comments
let modul_with_comments_to_document:
  FStar_Parser_AST.modul ->
    (Prims.string* FStar_Range.range) Prims.list ->
      (FStar_Pprint.document* (Prims.string* FStar_Range.range) Prims.list)
  =
  fun m  ->
    fun comments  ->
      let decls =
        match m with
        | FStar_Parser_AST.Module (uu____4042,decls) -> decls
        | FStar_Parser_AST.Interface (uu____4046,decls,uu____4048) -> decls in
      FStar_ST.write should_print_fs_typ_app false;
      (match decls with
       | [] -> (FStar_Pprint.empty, comments)
       | d::ds ->
           let uu____4065 =
             match ds with
             | {
                 FStar_Parser_AST.d = FStar_Parser_AST.Pragma
                   (FStar_Parser_AST.LightOff );
                 FStar_Parser_AST.drange = uu____4072;
                 FStar_Parser_AST.doc = uu____4073;
                 FStar_Parser_AST.quals = uu____4074;
                 FStar_Parser_AST.attrs = uu____4075;_}::uu____4076 ->
                 let d0 = FStar_List.hd ds in
                 let uu____4080 =
                   let uu____4082 =
                     let uu____4084 = FStar_List.tl ds in d :: uu____4084 in
                   d0 :: uu____4082 in
                 (uu____4080, (d0.FStar_Parser_AST.drange))
             | uu____4087 -> ((d :: ds), (d.FStar_Parser_AST.drange)) in
           (match uu____4065 with
            | (decls1,first_range) ->
                let extract_decl_range d1 = d1.FStar_Parser_AST.drange in
                (FStar_ST.write comment_stack comments;
                 (let initial_comment =
                    let uu____4110 = FStar_Range.start_of_range first_range in
                    place_comments_until_pos (Prims.parse_int "0")
                      (Prims.parse_int "1") uu____4110 FStar_Pprint.empty in
                  let doc1 =
                    separate_map_with_comments FStar_Pprint.empty
                      FStar_Pprint.empty decl_to_document decls1
                      extract_decl_range in
                  let comments1 = FStar_ST.read comment_stack in
                  FStar_ST.write comment_stack [];
                  FStar_ST.write should_print_fs_typ_app false;
                  (let uu____4132 =
                     FStar_Pprint.op_Hat_Hat initial_comment doc1 in
                   (uu____4132, comments1))))))