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
  is_list_structure FStar_Parser_Const.cons_lid FStar_Parser_Const.nil_lid
let is_lex_list: FStar_Parser_AST.term -> Prims.bool =
  is_list_structure FStar_Parser_Const.lexcons_lid
    FStar_Parser_Const.lextop_lid
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
        (FStar_Ident.lid_equals lid FStar_Parser_Const.array_mk_array_lid) &&
          (is_list l)
    | uu____445 -> false
let rec is_ref_set: FStar_Parser_AST.term -> Prims.bool =
  fun e  ->
    let uu____449 =
      let uu____450 = unparen e in uu____450.FStar_Parser_AST.tm in
    match uu____449 with
    | FStar_Parser_AST.Var maybe_empty_lid ->
        FStar_Ident.lid_equals maybe_empty_lid FStar_Parser_Const.tset_empty
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
           FStar_Parser_Const.tset_singleton)
          &&
          (FStar_Ident.lid_equals maybe_ref_lid FStar_Parser_Const.heap_ref)
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
            FStar_Parser_Const.tset_union)
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
  fun uu___95_578  ->
    match uu___95_578 with
    | FStar_Util.Inl c -> Prims.strcat (FStar_Util.string_of_char c) ".*"
    | FStar_Util.Inr s -> s
let matches_token:
  Prims.string ->
    (FStar_Char.char,Prims.string) FStar_Util.either -> Prims.bool
  =
  fun s  ->
    fun uu___96_590  ->
      match uu___96_590 with
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
  let levels_from_associativity l uu___97_948 =
    match uu___97_948 with
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
           | (uu____1137,tokens) -> tokens = (snd level)) level_table in
    match uu____1110 with
    | Some ((uu____1157,l1,uu____1159),uu____1160) -> max n1 l1
    | None  ->
        let uu____1186 =
          let uu____1187 =
            let uu____1188 = FStar_List.map token_to_string (snd level) in
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
let handleable_args_length: FStar_Ident.ident -> Prims.int =
  fun op  ->
    let op_s = FStar_Ident.text_of_id op in
    let uu____1357 =
      (is_general_prefix_op op) || (FStar_List.mem op_s ["-"; "~"]) in
    if uu____1357
    then Prims.parse_int "1"
    else
      (let uu____1359 =
         ((is_operatorInfix0ad12 op) || (is_operatorInfix34 op)) ||
           (FStar_List.mem op_s
              ["<==>"; "==>"; "\\/"; "/\\"; "="; "|>"; ":="; ".()"; ".[]"]) in
       if uu____1359
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
  | uu____1377 -> false
let comment_stack: (Prims.string* FStar_Range.range) Prims.list FStar_ST.ref
  = FStar_Util.mk_ref []
let with_comment printer tm tmrange =
  let rec comments_before_pos acc print_pos lookahead_pos =
    let uu____1423 = FStar_ST.read comment_stack in
    match uu____1423 with
    | [] -> (acc, false)
    | (comment,crange)::cs ->
        let uu____1444 = FStar_Range.range_before_pos crange print_pos in
        if uu____1444
        then
          (FStar_ST.write comment_stack cs;
           (let uu____1453 =
              let uu____1454 =
                let uu____1455 = str comment in
                FStar_Pprint.op_Hat_Hat uu____1455 FStar_Pprint.hardline in
              FStar_Pprint.op_Hat_Hat acc uu____1454 in
            comments_before_pos uu____1453 print_pos lookahead_pos))
        else
          (let uu____1457 = FStar_Range.range_before_pos crange lookahead_pos in
           (acc, uu____1457)) in
  let uu____1458 =
    let uu____1461 =
      let uu____1462 = FStar_Range.start_of_range tmrange in
      FStar_Range.end_of_line uu____1462 in
    let uu____1463 = FStar_Range.end_of_range tmrange in
    comments_before_pos FStar_Pprint.empty uu____1461 uu____1463 in
  match uu____1458 with
  | (comments,has_lookahead) ->
      let printed_e = printer tm in
      let comments1 =
        if has_lookahead
        then
          let pos = FStar_Range.end_of_range tmrange in
          let uu____1469 = comments_before_pos comments pos pos in
          fst uu____1469
        else comments in
      let uu____1473 = FStar_Pprint.op_Hat_Hat comments1 printed_e in
      FStar_Pprint.group uu____1473
let rec place_comments_until_pos:
  Prims.int ->
    Prims.int ->
      FStar_Range.pos -> FStar_Pprint.document -> FStar_Pprint.document
  =
  fun k  ->
    fun lbegin  ->
      fun pos_end  ->
        fun doc1  ->
          let uu____1486 = FStar_ST.read comment_stack in
          match uu____1486 with
          | (comment,crange)::cs when
              FStar_Range.range_before_pos crange pos_end ->
              (FStar_ST.write comment_stack cs;
               (let lnum =
                  let uu____1510 =
                    let uu____1511 =
                      let uu____1512 = FStar_Range.start_of_range crange in
                      FStar_Range.line_of_pos uu____1512 in
                    uu____1511 - lbegin in
                  max k uu____1510 in
                let doc2 =
                  let uu____1514 =
                    let uu____1515 =
                      FStar_Pprint.repeat lnum FStar_Pprint.hardline in
                    let uu____1516 = str comment in
                    FStar_Pprint.op_Hat_Hat uu____1515 uu____1516 in
                  FStar_Pprint.op_Hat_Hat doc1 uu____1514 in
                let uu____1517 =
                  let uu____1518 = FStar_Range.end_of_range crange in
                  FStar_Range.line_of_pos uu____1518 in
                place_comments_until_pos (Prims.parse_int "1") uu____1517
                  pos_end doc2))
          | uu____1519 ->
              let lnum =
                let uu____1524 =
                  let uu____1525 = FStar_Range.line_of_pos pos_end in
                  uu____1525 - lbegin in
                max (Prims.parse_int "1") uu____1524 in
              let uu____1526 = FStar_Pprint.repeat lnum FStar_Pprint.hardline in
              FStar_Pprint.op_Hat_Hat doc1 uu____1526
let separate_map_with_comments prefix1 sep f xs extract_range =
  let fold_fun uu____1575 x =
    match uu____1575 with
    | (last_line,doc1) ->
        let r = extract_range x in
        let doc2 =
          let uu____1585 = FStar_Range.start_of_range r in
          place_comments_until_pos (Prims.parse_int "1") last_line uu____1585
            doc1 in
        let uu____1586 =
          let uu____1587 = FStar_Range.end_of_range r in
          FStar_Range.line_of_pos uu____1587 in
        let uu____1588 =
          let uu____1589 =
            let uu____1590 = f x in FStar_Pprint.op_Hat_Hat sep uu____1590 in
          FStar_Pprint.op_Hat_Hat doc2 uu____1589 in
        (uu____1586, uu____1588) in
  let uu____1591 =
    let uu____1595 = FStar_List.hd xs in
    let uu____1596 = FStar_List.tl xs in (uu____1595, uu____1596) in
  match uu____1591 with
  | (x,xs1) ->
      let init1 =
        let uu____1606 =
          let uu____1607 =
            let uu____1608 = extract_range x in
            FStar_Range.end_of_range uu____1608 in
          FStar_Range.line_of_pos uu____1607 in
        let uu____1609 =
          let uu____1610 = f x in FStar_Pprint.op_Hat_Hat prefix1 uu____1610 in
        (uu____1606, uu____1609) in
      let uu____1611 = FStar_List.fold_left fold_fun init1 xs1 in
      snd uu____1611
let rec p_decl: FStar_Parser_AST.decl -> FStar_Pprint.document =
  fun d  ->
    let uu____1857 =
      let uu____1858 = FStar_Pprint.optional p_fsdoc d.FStar_Parser_AST.doc in
      let uu____1859 =
        let uu____1860 = p_attributes d.FStar_Parser_AST.attrs in
        let uu____1861 =
          let uu____1862 = p_qualifiers d.FStar_Parser_AST.quals in
          let uu____1863 =
            let uu____1864 = p_rawDecl d in
            FStar_Pprint.op_Hat_Hat
              (if d.FStar_Parser_AST.quals = []
               then FStar_Pprint.empty
               else break1) uu____1864 in
          FStar_Pprint.op_Hat_Hat uu____1862 uu____1863 in
        FStar_Pprint.op_Hat_Hat uu____1860 uu____1861 in
      FStar_Pprint.op_Hat_Hat uu____1858 uu____1859 in
    FStar_Pprint.group uu____1857
and p_attributes: FStar_Parser_AST.attributes_ -> FStar_Pprint.document =
  fun attrs  ->
    let uu____1867 =
      let uu____1868 = str "@" in
      FStar_Pprint.op_Hat_Hat FStar_Pprint.lbracket uu____1868 in
    let uu____1869 =
      FStar_Pprint.op_Hat_Hat FStar_Pprint.rbracket FStar_Pprint.hardline in
    soft_surround_separate_map (Prims.parse_int "0") (Prims.parse_int "2")
      FStar_Pprint.empty uu____1867 FStar_Pprint.space uu____1869
      p_atomicTerm attrs
and p_fsdoc: FStar_Parser_AST.fsdoc -> FStar_Pprint.document =
  fun uu____1870  ->
    match uu____1870 with
    | (doc1,kwd_args) ->
        let kwd_args_doc =
          match kwd_args with
          | [] -> FStar_Pprint.empty
          | kwd_args1 ->
              let process_kwd_arg uu____1891 =
                match uu____1891 with
                | (kwd1,arg) ->
                    let uu____1896 = str "@" in
                    let uu____1897 =
                      let uu____1898 = str kwd1 in
                      let uu____1899 =
                        let uu____1900 = str arg in
                        FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____1900 in
                      FStar_Pprint.op_Hat_Hat uu____1898 uu____1899 in
                    FStar_Pprint.op_Hat_Hat uu____1896 uu____1897 in
              let uu____1901 =
                let uu____1902 =
                  FStar_Pprint.separate_map FStar_Pprint.hardline
                    process_kwd_arg kwd_args1 in
                FStar_Pprint.op_Hat_Hat uu____1902 FStar_Pprint.hardline in
              FStar_Pprint.op_Hat_Hat FStar_Pprint.hardline uu____1901 in
        let uu____1905 =
          let uu____1906 =
            let uu____1907 =
              let uu____1908 =
                let uu____1909 = str doc1 in
                let uu____1910 =
                  let uu____1911 =
                    let uu____1912 =
                      FStar_Pprint.op_Hat_Hat FStar_Pprint.rparen
                        FStar_Pprint.hardline in
                    FStar_Pprint.op_Hat_Hat FStar_Pprint.star uu____1912 in
                  FStar_Pprint.op_Hat_Hat kwd_args_doc uu____1911 in
                FStar_Pprint.op_Hat_Hat uu____1909 uu____1910 in
              FStar_Pprint.op_Hat_Hat FStar_Pprint.star uu____1908 in
            FStar_Pprint.op_Hat_Hat FStar_Pprint.star uu____1907 in
          FStar_Pprint.op_Hat_Hat FStar_Pprint.lparen uu____1906 in
        FStar_Pprint.op_Hat_Hat FStar_Pprint.hardline uu____1905
and p_rawDecl: FStar_Parser_AST.decl -> FStar_Pprint.document =
  fun d  ->
    match d.FStar_Parser_AST.d with
    | FStar_Parser_AST.Open uid ->
        let uu____1915 =
          let uu____1916 = str "open" in
          let uu____1917 = p_quident uid in
          FStar_Pprint.op_Hat_Slash_Hat uu____1916 uu____1917 in
        FStar_Pprint.group uu____1915
    | FStar_Parser_AST.Include uid ->
        let uu____1919 =
          let uu____1920 = str "include" in
          let uu____1921 = p_quident uid in
          FStar_Pprint.op_Hat_Slash_Hat uu____1920 uu____1921 in
        FStar_Pprint.group uu____1919
    | FStar_Parser_AST.ModuleAbbrev (uid1,uid2) ->
        let uu____1924 =
          let uu____1925 = str "module" in
          let uu____1926 =
            let uu____1927 =
              let uu____1928 = p_uident uid1 in
              let uu____1929 =
                FStar_Pprint.op_Hat_Hat FStar_Pprint.space
                  FStar_Pprint.equals in
              FStar_Pprint.op_Hat_Hat uu____1928 uu____1929 in
            FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____1927 in
          FStar_Pprint.op_Hat_Hat uu____1925 uu____1926 in
        let uu____1930 = p_quident uid2 in
        op_Hat_Slash_Plus_Hat uu____1924 uu____1930
    | FStar_Parser_AST.TopLevelModule uid ->
        let uu____1932 =
          let uu____1933 = str "module" in
          let uu____1934 =
            let uu____1935 = p_quident uid in
            FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____1935 in
          FStar_Pprint.op_Hat_Hat uu____1933 uu____1934 in
        FStar_Pprint.group uu____1932
    | FStar_Parser_AST.Tycon
        (true ,(FStar_Parser_AST.TyconAbbrev (uid,tpars,None ,t),None )::[])
        ->
        let effect_prefix_doc =
          let uu____1954 = str "effect" in
          let uu____1955 =
            let uu____1956 = p_uident uid in
            FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____1956 in
          FStar_Pprint.op_Hat_Hat uu____1954 uu____1955 in
        let uu____1957 =
          let uu____1958 = p_typars tpars in
          FStar_Pprint.surround (Prims.parse_int "2") (Prims.parse_int "1")
            effect_prefix_doc uu____1958 FStar_Pprint.equals in
        let uu____1959 = p_typ t in
        op_Hat_Slash_Plus_Hat uu____1957 uu____1959
    | FStar_Parser_AST.Tycon (false ,tcdefs) ->
        let uu____1969 = str "type" in
        let uu____1970 = str "and" in
        precede_break_separate_map uu____1969 uu____1970 p_fsdocTypeDeclPairs
          tcdefs
    | FStar_Parser_AST.TopLevelLet (q,lbs) ->
        let let_doc =
          let uu____1983 = str "let" in
          let uu____1984 =
            let uu____1985 = p_letqualifier q in
            FStar_Pprint.op_Hat_Hat uu____1985 FStar_Pprint.space in
          FStar_Pprint.op_Hat_Hat uu____1983 uu____1984 in
        let uu____1986 =
          let uu____1987 = str "and" in
          FStar_Pprint.op_Hat_Hat uu____1987 FStar_Pprint.space in
        separate_map_with_comments let_doc uu____1986 p_letbinding lbs
          (fun uu____1990  ->
             match uu____1990 with
             | (p,t) ->
                 FStar_Range.union_ranges p.FStar_Parser_AST.prange
                   t.FStar_Parser_AST.range)
    | FStar_Parser_AST.Val (lid,t) ->
        let uu____1997 =
          let uu____1998 = str "val" in
          let uu____1999 =
            let uu____2000 =
              let uu____2001 = p_lident lid in
              let uu____2002 =
                FStar_Pprint.op_Hat_Hat FStar_Pprint.space FStar_Pprint.colon in
              FStar_Pprint.op_Hat_Hat uu____2001 uu____2002 in
            FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____2000 in
          FStar_Pprint.op_Hat_Hat uu____1998 uu____1999 in
        let uu____2003 = p_typ t in
        op_Hat_Slash_Plus_Hat uu____1997 uu____2003
    | FStar_Parser_AST.Assume (id,t) ->
        let decl_keyword =
          let uu____2007 =
            let uu____2008 =
              FStar_Util.char_at id.FStar_Ident.idText (Prims.parse_int "0") in
            FStar_All.pipe_right uu____2008 FStar_Util.is_upper in
          if uu____2007
          then FStar_Pprint.empty
          else
            (let uu____2010 = str "val" in
             FStar_Pprint.op_Hat_Hat uu____2010 FStar_Pprint.space) in
        let uu____2011 =
          let uu____2012 =
            let uu____2013 = p_ident id in
            let uu____2014 =
              FStar_Pprint.op_Hat_Hat FStar_Pprint.space FStar_Pprint.colon in
            FStar_Pprint.op_Hat_Hat uu____2013 uu____2014 in
          FStar_Pprint.op_Hat_Hat decl_keyword uu____2012 in
        let uu____2015 = p_typ t in
        op_Hat_Slash_Plus_Hat uu____2011 uu____2015
    | FStar_Parser_AST.Exception (uid,t_opt) ->
        let uu____2020 = str "exception" in
        let uu____2021 =
          let uu____2022 =
            let uu____2023 = p_uident uid in
            let uu____2024 =
              FStar_Pprint.optional
                (fun t  ->
                   let uu____2026 = str "of" in
                   let uu____2027 = p_typ t in
                   op_Hat_Slash_Plus_Hat uu____2026 uu____2027) t_opt in
            FStar_Pprint.op_Hat_Hat uu____2023 uu____2024 in
          FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____2022 in
        FStar_Pprint.op_Hat_Hat uu____2020 uu____2021
    | FStar_Parser_AST.NewEffect ne ->
        let uu____2029 = str "new_effect" in
        let uu____2030 =
          let uu____2031 = p_newEffect ne in
          FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____2031 in
        FStar_Pprint.op_Hat_Hat uu____2029 uu____2030
    | FStar_Parser_AST.SubEffect se ->
        let uu____2033 = str "sub_effect" in
        let uu____2034 =
          let uu____2035 = p_subEffect se in
          FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____2035 in
        FStar_Pprint.op_Hat_Hat uu____2033 uu____2034
    | FStar_Parser_AST.Pragma p -> p_pragma p
    | FStar_Parser_AST.Fsdoc doc1 ->
        let uu____2038 = p_fsdoc doc1 in
        FStar_Pprint.op_Hat_Hat uu____2038 FStar_Pprint.hardline
    | FStar_Parser_AST.Main uu____2039 ->
        failwith "*Main declaration* : Is that really still in use ??"
    | FStar_Parser_AST.Tycon (true ,uu____2040) ->
        failwith
          "Effect abbreviation is expected to be defined by an abbreviation"
and p_pragma: FStar_Parser_AST.pragma -> FStar_Pprint.document =
  fun uu___98_2049  ->
    match uu___98_2049 with
    | FStar_Parser_AST.SetOptions s ->
        let uu____2051 = str "#set-options" in
        let uu____2052 =
          let uu____2053 =
            let uu____2054 = str s in FStar_Pprint.dquotes uu____2054 in
          FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____2053 in
        FStar_Pprint.op_Hat_Hat uu____2051 uu____2052
    | FStar_Parser_AST.ResetOptions s_opt ->
        let uu____2057 = str "#reset-options" in
        let uu____2058 =
          FStar_Pprint.optional
            (fun s  ->
               let uu____2060 =
                 let uu____2061 = str s in FStar_Pprint.dquotes uu____2061 in
               FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____2060) s_opt in
        FStar_Pprint.op_Hat_Hat uu____2057 uu____2058
    | FStar_Parser_AST.LightOff  ->
        (FStar_ST.write should_print_fs_typ_app true; str "#light \"off\"")
and p_typars: FStar_Parser_AST.binder Prims.list -> FStar_Pprint.document =
  fun bs  -> p_binders true bs
and p_fsdocTypeDeclPairs:
  (FStar_Parser_AST.tycon* FStar_Parser_AST.fsdoc option) ->
    FStar_Pprint.document
  =
  fun uu____2067  ->
    match uu____2067 with
    | (typedecl,fsdoc_opt) ->
        let uu____2075 = FStar_Pprint.optional p_fsdoc fsdoc_opt in
        let uu____2076 = p_typeDecl typedecl in
        FStar_Pprint.op_Hat_Hat uu____2075 uu____2076
and p_typeDecl: FStar_Parser_AST.tycon -> FStar_Pprint.document =
  fun uu___99_2077  ->
    match uu___99_2077 with
    | FStar_Parser_AST.TyconAbstract (lid,bs,typ_opt) ->
        let empty' uu____2088 = FStar_Pprint.empty in
        p_typeDeclPrefix lid bs typ_opt empty'
    | FStar_Parser_AST.TyconAbbrev (lid,bs,typ_opt,t) ->
        let f uu____2100 =
          let uu____2101 = p_typ t in prefix2 FStar_Pprint.equals uu____2101 in
        p_typeDeclPrefix lid bs typ_opt f
    | FStar_Parser_AST.TyconRecord (lid,bs,typ_opt,record_field_decls) ->
        let p_recordFieldAndComments uu____2127 =
          match uu____2127 with
          | (lid1,t,doc_opt) ->
              let uu____2137 =
                FStar_Range.extend_to_end_of_line t.FStar_Parser_AST.range in
              with_comment p_recordFieldDecl (lid1, t, doc_opt) uu____2137 in
        let p_fields uu____2146 =
          let uu____2147 =
            let uu____2148 =
              let uu____2149 =
                let uu____2150 =
                  FStar_Pprint.op_Hat_Hat FStar_Pprint.semi break1 in
                FStar_Pprint.separate_map uu____2150 p_recordFieldAndComments
                  record_field_decls in
              braces_with_nesting uu____2149 in
            FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____2148 in
          FStar_Pprint.op_Hat_Hat FStar_Pprint.equals uu____2147 in
        p_typeDeclPrefix lid bs typ_opt p_fields
    | FStar_Parser_AST.TyconVariant (lid,bs,typ_opt,ct_decls) ->
        let p_constructorBranchAndComments uu____2186 =
          match uu____2186 with
          | (uid,t_opt,doc_opt,use_of) ->
              let range =
                let uu____2202 =
                  let uu____2203 =
                    FStar_Util.map_opt t_opt
                      (fun t  -> t.FStar_Parser_AST.range) in
                  FStar_Util.dflt uid.FStar_Ident.idRange uu____2203 in
                FStar_Range.extend_to_end_of_line uu____2202 in
              let p_constructorBranch decl =
                let uu____2222 =
                  let uu____2223 =
                    let uu____2224 = p_constructorDecl decl in
                    FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____2224 in
                  FStar_Pprint.op_Hat_Hat FStar_Pprint.bar uu____2223 in
                FStar_Pprint.group uu____2222 in
              with_comment p_constructorBranch (uid, t_opt, doc_opt, use_of)
                range in
        let datacon_doc uu____2236 =
          let uu____2237 =
            FStar_Pprint.separate_map break1 p_constructorBranchAndComments
              ct_decls in
          FStar_Pprint.group uu____2237 in
        p_typeDeclPrefix lid bs typ_opt
          (fun uu____2244  ->
             let uu____2245 = datacon_doc () in
             prefix2 FStar_Pprint.equals uu____2245)
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
            let uu____2256 = p_ident lid in
            let uu____2257 =
              let uu____2258 = cont () in
              FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____2258 in
            FStar_Pprint.op_Hat_Hat uu____2256 uu____2257
          else
            (let binders_doc =
               let uu____2261 = p_typars bs in
               let uu____2262 =
                 FStar_Pprint.optional
                   (fun t  ->
                      let uu____2264 =
                        let uu____2265 =
                          let uu____2266 = p_typ t in
                          FStar_Pprint.op_Hat_Hat FStar_Pprint.space
                            uu____2266 in
                        FStar_Pprint.op_Hat_Hat FStar_Pprint.colon uu____2265 in
                      FStar_Pprint.op_Hat_Hat break1 uu____2264) typ_opt in
               FStar_Pprint.op_Hat_Hat uu____2261 uu____2262 in
             let uu____2267 = p_ident lid in
             let uu____2268 = cont () in
             FStar_Pprint.surround (Prims.parse_int "2")
               (Prims.parse_int "1") uu____2267 binders_doc uu____2268)
and p_recordFieldDecl:
  (FStar_Ident.ident* FStar_Parser_AST.term* FStar_Parser_AST.fsdoc option)
    -> FStar_Pprint.document
  =
  fun uu____2269  ->
    match uu____2269 with
    | (lid,t,doc_opt) ->
        let uu____2279 =
          let uu____2280 = FStar_Pprint.optional p_fsdoc doc_opt in
          let uu____2281 =
            let uu____2282 = p_lident lid in
            let uu____2283 =
              let uu____2284 = p_typ t in
              FStar_Pprint.op_Hat_Hat FStar_Pprint.colon uu____2284 in
            FStar_Pprint.op_Hat_Hat uu____2282 uu____2283 in
          FStar_Pprint.op_Hat_Hat uu____2280 uu____2281 in
        FStar_Pprint.group uu____2279
and p_constructorDecl:
  (FStar_Ident.ident* FStar_Parser_AST.term option* FStar_Parser_AST.fsdoc
    option* Prims.bool) -> FStar_Pprint.document
  =
  fun uu____2285  ->
    match uu____2285 with
    | (uid,t_opt,doc_opt,use_of) ->
        let sep = if use_of then str "of" else FStar_Pprint.colon in
        let uid_doc = p_uident uid in
        let uu____2303 = FStar_Pprint.optional p_fsdoc doc_opt in
        let uu____2304 =
          let uu____2305 = FStar_Pprint.break_ (Prims.parse_int "0") in
          let uu____2306 =
            default_or_map uid_doc
              (fun t  ->
                 let uu____2308 =
                   let uu____2309 =
                     FStar_Pprint.op_Hat_Hat FStar_Pprint.space sep in
                   FStar_Pprint.op_Hat_Hat uid_doc uu____2309 in
                 let uu____2310 = p_typ t in
                 op_Hat_Slash_Plus_Hat uu____2308 uu____2310) t_opt in
          FStar_Pprint.op_Hat_Hat uu____2305 uu____2306 in
        FStar_Pprint.op_Hat_Hat uu____2303 uu____2304
and p_letbinding:
  (FStar_Parser_AST.pattern* FStar_Parser_AST.term) -> FStar_Pprint.document
  =
  fun uu____2311  ->
    match uu____2311 with
    | (pat,e) ->
        let pat_doc =
          let uu____2317 =
            match pat.FStar_Parser_AST.pat with
            | FStar_Parser_AST.PatAscribed (pat1,t) ->
                let uu____2324 =
                  let uu____2325 =
                    let uu____2326 =
                      let uu____2327 =
                        let uu____2328 = p_tmArrow p_tmNoEq t in
                        FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____2328 in
                      FStar_Pprint.op_Hat_Hat FStar_Pprint.colon uu____2327 in
                    FStar_Pprint.group uu____2326 in
                  FStar_Pprint.op_Hat_Hat break1 uu____2325 in
                (pat1, uu____2324)
            | uu____2329 -> (pat, FStar_Pprint.empty) in
          match uu____2317 with
          | (pat1,ascr_doc) ->
              (match pat1.FStar_Parser_AST.pat with
               | FStar_Parser_AST.PatApp
                   ({
                      FStar_Parser_AST.pat = FStar_Parser_AST.PatVar
                        (x,uu____2333);
                      FStar_Parser_AST.prange = uu____2334;_},pats)
                   ->
                   let uu____2340 = p_lident x in
                   let uu____2341 =
                     let uu____2342 =
                       FStar_Pprint.separate_map break1 p_atomicPattern pats in
                     FStar_Pprint.op_Hat_Hat uu____2342 ascr_doc in
                   FStar_Pprint.surround (Prims.parse_int "2")
                     (Prims.parse_int "1") uu____2340 uu____2341
                     FStar_Pprint.equals
               | uu____2343 ->
                   let uu____2344 =
                     let uu____2345 = p_tuplePattern pat1 in
                     let uu____2346 =
                       FStar_Pprint.op_Hat_Slash_Hat ascr_doc
                         FStar_Pprint.equals in
                     FStar_Pprint.op_Hat_Hat uu____2345 uu____2346 in
                   FStar_Pprint.group uu____2344) in
        let uu____2347 = p_term e in prefix2 pat_doc uu____2347
and p_newEffect: FStar_Parser_AST.effect_decl -> FStar_Pprint.document =
  fun uu___100_2348  ->
    match uu___100_2348 with
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
        let uu____2366 = p_uident uid in
        let uu____2367 = p_binders true bs in
        let uu____2368 =
          let uu____2369 = p_simpleTerm t in
          prefix2 FStar_Pprint.equals uu____2369 in
        FStar_Pprint.surround (Prims.parse_int "2") (Prims.parse_int "1")
          uu____2366 uu____2367 uu____2368
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
          let uu____2376 =
            let uu____2377 =
              let uu____2378 =
                let uu____2379 = p_uident uid in
                let uu____2380 = p_binders true bs in
                let uu____2381 =
                  let uu____2382 = p_typ t in
                  prefix2 FStar_Pprint.colon uu____2382 in
                FStar_Pprint.surround (Prims.parse_int "2")
                  (Prims.parse_int "1") uu____2379 uu____2380 uu____2381 in
              FStar_Pprint.group uu____2378 in
            let uu____2383 =
              let uu____2384 = str "with" in
              let uu____2385 =
                separate_break_map FStar_Pprint.semi p_effectDecl eff_decls in
              prefix2 uu____2384 uu____2385 in
            FStar_Pprint.op_Hat_Slash_Hat uu____2377 uu____2383 in
          braces_with_nesting uu____2376
and p_effectDecl: FStar_Parser_AST.decl -> FStar_Pprint.document =
  fun d  ->
    match d.FStar_Parser_AST.d with
    | FStar_Parser_AST.Tycon
        (false ,(FStar_Parser_AST.TyconAbbrev (lid,[],None ,e),None )::[]) ->
        let uu____2402 =
          let uu____2403 = p_lident lid in
          let uu____2404 =
            FStar_Pprint.op_Hat_Hat FStar_Pprint.space FStar_Pprint.equals in
          FStar_Pprint.op_Hat_Hat uu____2403 uu____2404 in
        let uu____2405 = p_simpleTerm e in prefix2 uu____2402 uu____2405
    | uu____2406 ->
        let uu____2407 =
          let uu____2408 = FStar_Parser_AST.decl_to_string d in
          FStar_Util.format1
            "Not a declaration of an effect member... or at least I hope so : %s"
            uu____2408 in
        failwith uu____2407
and p_subEffect: FStar_Parser_AST.lift -> FStar_Pprint.document =
  fun lift  ->
    let lift_op_doc =
      let lifts =
        match lift.FStar_Parser_AST.lift_op with
        | FStar_Parser_AST.NonReifiableLift t -> [("lift_wp", t)]
        | FStar_Parser_AST.ReifiableLift (t1,t2) ->
            [("lif_wp", t1); ("lift", t2)]
        | FStar_Parser_AST.LiftForFree t -> [("lift", t)] in
      let p_lift uu____2441 =
        match uu____2441 with
        | (kwd1,t) ->
            let uu____2446 =
              let uu____2447 = str kwd1 in
              let uu____2448 =
                FStar_Pprint.op_Hat_Hat FStar_Pprint.space
                  FStar_Pprint.equals in
              FStar_Pprint.op_Hat_Hat uu____2447 uu____2448 in
            let uu____2449 = p_simpleTerm t in prefix2 uu____2446 uu____2449 in
      separate_break_map FStar_Pprint.semi p_lift lifts in
    let uu____2452 =
      let uu____2453 =
        let uu____2454 = p_quident lift.FStar_Parser_AST.msource in
        let uu____2455 =
          let uu____2456 = str "~>" in
          FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____2456 in
        FStar_Pprint.op_Hat_Hat uu____2454 uu____2455 in
      let uu____2457 = p_quident lift.FStar_Parser_AST.mdest in
      prefix2 uu____2453 uu____2457 in
    let uu____2458 =
      let uu____2459 = braces_with_nesting lift_op_doc in
      FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____2459 in
    FStar_Pprint.op_Hat_Hat uu____2452 uu____2458
and p_qualifier: FStar_Parser_AST.qualifier -> FStar_Pprint.document =
  fun uu___101_2460  ->
    match uu___101_2460 with
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
    let uu____2462 = FStar_Pprint.separate_map break1 p_qualifier qs in
    FStar_Pprint.group uu____2462
and p_letqualifier: FStar_Parser_AST.let_qualifier -> FStar_Pprint.document =
  fun uu___102_2463  ->
    match uu___102_2463 with
    | FStar_Parser_AST.Rec  ->
        let uu____2464 = str "rec" in
        FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____2464
    | FStar_Parser_AST.Mutable  ->
        let uu____2465 = str "mutable" in
        FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____2465
    | FStar_Parser_AST.NoLetQualifier  -> FStar_Pprint.empty
and p_aqual: FStar_Parser_AST.arg_qualifier -> FStar_Pprint.document =
  fun uu___103_2466  ->
    match uu___103_2466 with
    | FStar_Parser_AST.Implicit  -> str "#"
    | FStar_Parser_AST.Equality  -> str "$"
and p_disjunctivePattern: FStar_Parser_AST.pattern -> FStar_Pprint.document =
  fun p  ->
    match p.FStar_Parser_AST.pat with
    | FStar_Parser_AST.PatOr pats ->
        let uu____2470 =
          let uu____2471 =
            let uu____2472 =
              FStar_Pprint.op_Hat_Hat FStar_Pprint.bar FStar_Pprint.space in
            FStar_Pprint.op_Hat_Hat break1 uu____2472 in
          FStar_Pprint.separate_map uu____2471 p_tuplePattern pats in
        FStar_Pprint.group uu____2470
    | uu____2473 -> p_tuplePattern p
and p_tuplePattern: FStar_Parser_AST.pattern -> FStar_Pprint.document =
  fun p  ->
    match p.FStar_Parser_AST.pat with
    | FStar_Parser_AST.PatTuple (pats,false ) ->
        let uu____2478 =
          let uu____2479 = FStar_Pprint.op_Hat_Hat FStar_Pprint.comma break1 in
          FStar_Pprint.separate_map uu____2479 p_constructorPattern pats in
        FStar_Pprint.group uu____2478
    | uu____2480 -> p_constructorPattern p
and p_constructorPattern: FStar_Parser_AST.pattern -> FStar_Pprint.document =
  fun p  ->
    match p.FStar_Parser_AST.pat with
    | FStar_Parser_AST.PatApp
        ({ FStar_Parser_AST.pat = FStar_Parser_AST.PatName maybe_cons_lid;
           FStar_Parser_AST.prange = uu____2483;_},hd1::tl1::[])
        when
        FStar_Ident.lid_equals maybe_cons_lid FStar_Parser_Const.cons_lid ->
        let uu____2487 =
          FStar_Pprint.op_Hat_Hat FStar_Pprint.colon FStar_Pprint.colon in
        let uu____2488 = p_constructorPattern hd1 in
        let uu____2489 = p_constructorPattern tl1 in
        infix0 uu____2487 uu____2488 uu____2489
    | FStar_Parser_AST.PatApp
        ({ FStar_Parser_AST.pat = FStar_Parser_AST.PatName uid;
           FStar_Parser_AST.prange = uu____2491;_},pats)
        ->
        let uu____2495 = p_quident uid in
        let uu____2496 =
          FStar_Pprint.separate_map break1 p_atomicPattern pats in
        prefix2 uu____2495 uu____2496
    | uu____2497 -> p_atomicPattern p
and p_atomicPattern: FStar_Parser_AST.pattern -> FStar_Pprint.document =
  fun p  ->
    match p.FStar_Parser_AST.pat with
    | FStar_Parser_AST.PatAscribed (pat,t) ->
        let uu____2501 =
          let uu____2504 =
            let uu____2505 = unparen t in uu____2505.FStar_Parser_AST.tm in
          ((pat.FStar_Parser_AST.pat), uu____2504) in
        (match uu____2501 with
         | (FStar_Parser_AST.PatVar (lid,aqual),FStar_Parser_AST.Refine
            ({ FStar_Parser_AST.b = FStar_Parser_AST.Annotated (lid',t1);
               FStar_Parser_AST.brange = uu____2510;
               FStar_Parser_AST.blevel = uu____2511;
               FStar_Parser_AST.aqual = uu____2512;_},phi))
             when lid.FStar_Ident.idText = lid'.FStar_Ident.idText ->
             let uu____2516 =
               let uu____2517 = p_ident lid in
               p_refinement aqual uu____2517 t1 phi in
             soft_parens_with_nesting uu____2516
         | (FStar_Parser_AST.PatWild ,FStar_Parser_AST.Refine
            ({ FStar_Parser_AST.b = FStar_Parser_AST.NoName t1;
               FStar_Parser_AST.brange = uu____2519;
               FStar_Parser_AST.blevel = uu____2520;
               FStar_Parser_AST.aqual = uu____2521;_},phi))
             ->
             let uu____2523 =
               p_refinement None FStar_Pprint.underscore t1 phi in
             soft_parens_with_nesting uu____2523
         | uu____2524 ->
             let uu____2527 =
               let uu____2528 = p_tuplePattern pat in
               let uu____2529 =
                 let uu____2530 = FStar_Pprint.break_ (Prims.parse_int "0") in
                 let uu____2531 =
                   let uu____2532 = p_typ t in
                   FStar_Pprint.op_Hat_Hat FStar_Pprint.colon uu____2532 in
                 FStar_Pprint.op_Hat_Hat uu____2530 uu____2531 in
               FStar_Pprint.op_Hat_Hat uu____2528 uu____2529 in
             soft_parens_with_nesting uu____2527)
    | FStar_Parser_AST.PatList pats ->
        let uu____2535 =
          separate_break_map FStar_Pprint.semi p_tuplePattern pats in
        FStar_Pprint.surround (Prims.parse_int "2") (Prims.parse_int "0")
          FStar_Pprint.lbracket uu____2535 FStar_Pprint.rbracket
    | FStar_Parser_AST.PatRecord pats ->
        let p_recordFieldPat uu____2545 =
          match uu____2545 with
          | (lid,pat) ->
              let uu____2550 = p_qlident lid in
              let uu____2551 = p_tuplePattern pat in
              infix2 FStar_Pprint.equals uu____2550 uu____2551 in
        let uu____2552 =
          separate_break_map FStar_Pprint.semi p_recordFieldPat pats in
        soft_braces_with_nesting uu____2552
    | FStar_Parser_AST.PatTuple (pats,true ) ->
        let uu____2558 =
          FStar_Pprint.op_Hat_Hat FStar_Pprint.lparen FStar_Pprint.bar in
        let uu____2559 =
          separate_break_map FStar_Pprint.comma p_constructorPattern pats in
        let uu____2560 =
          FStar_Pprint.op_Hat_Hat FStar_Pprint.bar FStar_Pprint.rparen in
        FStar_Pprint.surround (Prims.parse_int "2") (Prims.parse_int "1")
          uu____2558 uu____2559 uu____2560
    | FStar_Parser_AST.PatTvar (tv,arg_qualifier_opt) -> p_tvar tv
    | FStar_Parser_AST.PatOp op ->
        let uu____2567 =
          let uu____2568 =
            let uu____2569 = str (FStar_Ident.text_of_id op) in
            let uu____2570 =
              FStar_Pprint.op_Hat_Hat FStar_Pprint.space FStar_Pprint.rparen in
            FStar_Pprint.op_Hat_Hat uu____2569 uu____2570 in
          FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____2568 in
        FStar_Pprint.op_Hat_Hat FStar_Pprint.lparen uu____2567
    | FStar_Parser_AST.PatWild  -> FStar_Pprint.underscore
    | FStar_Parser_AST.PatConst c -> p_constant c
    | FStar_Parser_AST.PatVar (lid,aqual) ->
        let uu____2576 = FStar_Pprint.optional p_aqual aqual in
        let uu____2577 = p_lident lid in
        FStar_Pprint.op_Hat_Hat uu____2576 uu____2577
    | FStar_Parser_AST.PatName uid -> p_quident uid
    | FStar_Parser_AST.PatOr uu____2579 -> failwith "Inner or pattern !"
    | FStar_Parser_AST.PatApp
        ({ FStar_Parser_AST.pat = FStar_Parser_AST.PatName uu____2581;
           FStar_Parser_AST.prange = uu____2582;_},uu____2583)
        ->
        let uu____2586 = p_tuplePattern p in
        soft_parens_with_nesting uu____2586
    | FStar_Parser_AST.PatTuple (uu____2587,false ) ->
        let uu____2590 = p_tuplePattern p in
        soft_parens_with_nesting uu____2590
    | uu____2591 ->
        let uu____2592 =
          let uu____2593 = FStar_Parser_AST.pat_to_string p in
          FStar_Util.format1 "Invalid pattern %s" uu____2593 in
        failwith uu____2592
and p_binder: Prims.bool -> FStar_Parser_AST.binder -> FStar_Pprint.document
  =
  fun is_atomic  ->
    fun b  ->
      match b.FStar_Parser_AST.b with
      | FStar_Parser_AST.Variable lid ->
          let uu____2597 =
            FStar_Pprint.optional p_aqual b.FStar_Parser_AST.aqual in
          let uu____2598 = p_lident lid in
          FStar_Pprint.op_Hat_Hat uu____2597 uu____2598
      | FStar_Parser_AST.TVariable lid -> p_lident lid
      | FStar_Parser_AST.Annotated (lid,t) ->
          let doc1 =
            let uu____2603 =
              let uu____2604 = unparen t in uu____2604.FStar_Parser_AST.tm in
            match uu____2603 with
            | FStar_Parser_AST.Refine
                ({ FStar_Parser_AST.b = FStar_Parser_AST.Annotated (lid',t1);
                   FStar_Parser_AST.brange = uu____2607;
                   FStar_Parser_AST.blevel = uu____2608;
                   FStar_Parser_AST.aqual = uu____2609;_},phi)
                when lid.FStar_Ident.idText = lid'.FStar_Ident.idText ->
                let uu____2611 = p_ident lid in
                p_refinement b.FStar_Parser_AST.aqual uu____2611 t1 phi
            | uu____2612 ->
                let uu____2613 =
                  FStar_Pprint.optional p_aqual b.FStar_Parser_AST.aqual in
                let uu____2614 =
                  let uu____2615 = p_lident lid in
                  let uu____2616 =
                    let uu____2617 =
                      let uu____2618 =
                        FStar_Pprint.break_ (Prims.parse_int "0") in
                      let uu____2619 = p_tmFormula t in
                      FStar_Pprint.op_Hat_Hat uu____2618 uu____2619 in
                    FStar_Pprint.op_Hat_Hat FStar_Pprint.colon uu____2617 in
                  FStar_Pprint.op_Hat_Hat uu____2615 uu____2616 in
                FStar_Pprint.op_Hat_Hat uu____2613 uu____2614 in
          if is_atomic
          then
            let uu____2620 =
              let uu____2621 =
                FStar_Pprint.op_Hat_Hat doc1 FStar_Pprint.rparen in
              FStar_Pprint.op_Hat_Hat FStar_Pprint.lparen uu____2621 in
            FStar_Pprint.group uu____2620
          else FStar_Pprint.group doc1
      | FStar_Parser_AST.TAnnotated uu____2623 ->
          failwith "Is this still used ?"
      | FStar_Parser_AST.NoName t ->
          let uu____2627 =
            let uu____2628 = unparen t in uu____2628.FStar_Parser_AST.tm in
          (match uu____2627 with
           | FStar_Parser_AST.Refine
               ({ FStar_Parser_AST.b = FStar_Parser_AST.NoName t1;
                  FStar_Parser_AST.brange = uu____2630;
                  FStar_Parser_AST.blevel = uu____2631;
                  FStar_Parser_AST.aqual = uu____2632;_},phi)
               ->
               if is_atomic
               then
                 let uu____2634 =
                   let uu____2635 =
                     let uu____2636 =
                       p_refinement b.FStar_Parser_AST.aqual
                         FStar_Pprint.underscore t1 phi in
                     FStar_Pprint.op_Hat_Hat uu____2636 FStar_Pprint.rparen in
                   FStar_Pprint.op_Hat_Hat FStar_Pprint.lparen uu____2635 in
                 FStar_Pprint.group uu____2634
               else
                 (let uu____2638 =
                    p_refinement b.FStar_Parser_AST.aqual
                      FStar_Pprint.underscore t1 phi in
                  FStar_Pprint.group uu____2638)
           | uu____2639 -> if is_atomic then p_atomicTerm t else p_appTerm t)
and p_refinement:
  FStar_Parser_AST.arg_qualifier option ->
    FStar_Pprint.document ->
      FStar_Parser_AST.term -> FStar_Parser_AST.term -> FStar_Pprint.document
  =
  fun aqual_opt  ->
    fun binder  ->
      fun t  ->
        fun phi  ->
          let uu____2646 = FStar_Pprint.optional p_aqual aqual_opt in
          let uu____2647 =
            let uu____2648 =
              let uu____2649 =
                let uu____2650 = p_appTerm t in
                let uu____2651 =
                  let uu____2652 = p_noSeqTerm phi in
                  soft_braces_with_nesting uu____2652 in
                FStar_Pprint.op_Hat_Hat uu____2650 uu____2651 in
              FStar_Pprint.op_Hat_Hat FStar_Pprint.colon uu____2649 in
            FStar_Pprint.op_Hat_Hat binder uu____2648 in
          FStar_Pprint.op_Hat_Hat uu____2646 uu____2647
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
    let uu____2665 =
      let uu____2666 = unparen e in uu____2666.FStar_Parser_AST.tm in
    match uu____2665 with
    | FStar_Parser_AST.Seq (e1,e2) ->
        let uu____2669 =
          let uu____2670 =
            let uu____2671 = p_noSeqTerm e1 in
            FStar_Pprint.op_Hat_Hat uu____2671 FStar_Pprint.semi in
          FStar_Pprint.group uu____2670 in
        let uu____2672 = p_term e2 in
        FStar_Pprint.op_Hat_Slash_Hat uu____2669 uu____2672
    | FStar_Parser_AST.Bind (x,e1,e2) ->
        let uu____2676 =
          let uu____2677 =
            let uu____2678 =
              let uu____2679 = p_lident x in
              let uu____2680 =
                FStar_Pprint.op_Hat_Hat FStar_Pprint.space
                  FStar_Pprint.long_left_arrow in
              FStar_Pprint.op_Hat_Hat uu____2679 uu____2680 in
            let uu____2681 =
              let uu____2682 = p_noSeqTerm e1 in
              let uu____2683 =
                FStar_Pprint.op_Hat_Hat FStar_Pprint.space FStar_Pprint.semi in
              FStar_Pprint.op_Hat_Hat uu____2682 uu____2683 in
            op_Hat_Slash_Plus_Hat uu____2678 uu____2681 in
          FStar_Pprint.group uu____2677 in
        let uu____2684 = p_term e2 in
        FStar_Pprint.op_Hat_Slash_Hat uu____2676 uu____2684
    | uu____2685 ->
        let uu____2686 = p_noSeqTerm e in FStar_Pprint.group uu____2686
and p_noSeqTerm: FStar_Parser_AST.term -> FStar_Pprint.document =
  fun e  -> with_comment p_noSeqTerm' e e.FStar_Parser_AST.range
and p_noSeqTerm': FStar_Parser_AST.term -> FStar_Pprint.document =
  fun e  ->
    let uu____2689 =
      let uu____2690 = unparen e in uu____2690.FStar_Parser_AST.tm in
    match uu____2689 with
    | FStar_Parser_AST.Ascribed (e1,t,None ) ->
        let uu____2694 =
          let uu____2695 = p_tmIff e1 in
          let uu____2696 =
            let uu____2697 =
              let uu____2698 = p_typ t in
              FStar_Pprint.op_Hat_Slash_Hat FStar_Pprint.colon uu____2698 in
            FStar_Pprint.op_Hat_Hat FStar_Pprint.langle uu____2697 in
          FStar_Pprint.op_Hat_Slash_Hat uu____2695 uu____2696 in
        FStar_Pprint.group uu____2694
    | FStar_Parser_AST.Ascribed (e1,t,Some tac) ->
        let uu____2703 =
          let uu____2704 = p_tmIff e1 in
          let uu____2705 =
            let uu____2706 =
              let uu____2707 =
                let uu____2708 = p_typ t in
                let uu____2709 =
                  let uu____2710 = str "by" in
                  let uu____2711 = p_typ tac in
                  FStar_Pprint.op_Hat_Slash_Hat uu____2710 uu____2711 in
                FStar_Pprint.op_Hat_Slash_Hat uu____2708 uu____2709 in
              FStar_Pprint.op_Hat_Slash_Hat FStar_Pprint.colon uu____2707 in
            FStar_Pprint.op_Hat_Hat FStar_Pprint.langle uu____2706 in
          FStar_Pprint.op_Hat_Slash_Hat uu____2704 uu____2705 in
        FStar_Pprint.group uu____2703
    | FStar_Parser_AST.Op
        ({ FStar_Ident.idText = ".()<-"; FStar_Ident.idRange = uu____2712;_},e1::e2::e3::[])
        ->
        let uu____2717 =
          let uu____2718 =
            let uu____2719 =
              let uu____2720 = p_atomicTermNotQUident e1 in
              let uu____2721 =
                let uu____2722 =
                  let uu____2723 =
                    let uu____2724 = p_term e2 in
                    soft_parens_with_nesting uu____2724 in
                  let uu____2725 =
                    FStar_Pprint.op_Hat_Hat FStar_Pprint.space
                      FStar_Pprint.larrow in
                  FStar_Pprint.op_Hat_Hat uu____2723 uu____2725 in
                FStar_Pprint.op_Hat_Hat FStar_Pprint.dot uu____2722 in
              FStar_Pprint.op_Hat_Hat uu____2720 uu____2721 in
            FStar_Pprint.group uu____2719 in
          let uu____2726 =
            let uu____2727 = p_noSeqTerm e3 in jump2 uu____2727 in
          FStar_Pprint.op_Hat_Hat uu____2718 uu____2726 in
        FStar_Pprint.group uu____2717
    | FStar_Parser_AST.Op
        ({ FStar_Ident.idText = ".[]<-"; FStar_Ident.idRange = uu____2728;_},e1::e2::e3::[])
        ->
        let uu____2733 =
          let uu____2734 =
            let uu____2735 =
              let uu____2736 = p_atomicTermNotQUident e1 in
              let uu____2737 =
                let uu____2738 =
                  let uu____2739 =
                    let uu____2740 = p_term e2 in
                    soft_brackets_with_nesting uu____2740 in
                  let uu____2741 =
                    FStar_Pprint.op_Hat_Hat FStar_Pprint.space
                      FStar_Pprint.larrow in
                  FStar_Pprint.op_Hat_Hat uu____2739 uu____2741 in
                FStar_Pprint.op_Hat_Hat FStar_Pprint.dot uu____2738 in
              FStar_Pprint.op_Hat_Hat uu____2736 uu____2737 in
            FStar_Pprint.group uu____2735 in
          let uu____2742 =
            let uu____2743 = p_noSeqTerm e3 in jump2 uu____2743 in
          FStar_Pprint.op_Hat_Hat uu____2734 uu____2742 in
        FStar_Pprint.group uu____2733
    | FStar_Parser_AST.Requires (e1,wtf) ->
        let uu____2749 =
          let uu____2750 = str "requires" in
          let uu____2751 = p_typ e1 in
          FStar_Pprint.op_Hat_Slash_Hat uu____2750 uu____2751 in
        FStar_Pprint.group uu____2749
    | FStar_Parser_AST.Ensures (e1,wtf) ->
        let uu____2757 =
          let uu____2758 = str "ensures" in
          let uu____2759 = p_typ e1 in
          FStar_Pprint.op_Hat_Slash_Hat uu____2758 uu____2759 in
        FStar_Pprint.group uu____2757
    | FStar_Parser_AST.Attributes es ->
        let uu____2762 =
          let uu____2763 = str "attributes" in
          let uu____2764 = FStar_Pprint.separate_map break1 p_atomicTerm es in
          FStar_Pprint.op_Hat_Slash_Hat uu____2763 uu____2764 in
        FStar_Pprint.group uu____2762
    | FStar_Parser_AST.If (e1,e2,e3) ->
        let uu____2768 = is_unit e3 in
        if uu____2768
        then
          let uu____2769 =
            let uu____2770 =
              let uu____2771 = str "if" in
              let uu____2772 = p_noSeqTerm e1 in
              op_Hat_Slash_Plus_Hat uu____2771 uu____2772 in
            let uu____2773 =
              let uu____2774 = str "then" in
              let uu____2775 = p_noSeqTerm e2 in
              op_Hat_Slash_Plus_Hat uu____2774 uu____2775 in
            FStar_Pprint.op_Hat_Slash_Hat uu____2770 uu____2773 in
          FStar_Pprint.group uu____2769
        else
          (let e2_doc =
             let uu____2778 =
               let uu____2779 = unparen e2 in uu____2779.FStar_Parser_AST.tm in
             match uu____2778 with
             | FStar_Parser_AST.If (uu____2780,uu____2781,e31) when
                 is_unit e31 ->
                 let uu____2783 = p_noSeqTerm e2 in
                 soft_parens_with_nesting uu____2783
             | uu____2784 -> p_noSeqTerm e2 in
           let uu____2785 =
             let uu____2786 =
               let uu____2787 = str "if" in
               let uu____2788 = p_noSeqTerm e1 in
               op_Hat_Slash_Plus_Hat uu____2787 uu____2788 in
             let uu____2789 =
               let uu____2790 =
                 let uu____2791 = str "then" in
                 op_Hat_Slash_Plus_Hat uu____2791 e2_doc in
               let uu____2792 =
                 let uu____2793 = str "else" in
                 let uu____2794 = p_noSeqTerm e3 in
                 op_Hat_Slash_Plus_Hat uu____2793 uu____2794 in
               FStar_Pprint.op_Hat_Slash_Hat uu____2790 uu____2792 in
             FStar_Pprint.op_Hat_Slash_Hat uu____2786 uu____2789 in
           FStar_Pprint.group uu____2785)
    | FStar_Parser_AST.TryWith (e1,branches) ->
        let uu____2807 =
          let uu____2808 =
            let uu____2809 = str "try" in
            let uu____2810 = p_noSeqTerm e1 in prefix2 uu____2809 uu____2810 in
          let uu____2811 =
            let uu____2812 = str "with" in
            let uu____2813 =
              FStar_Pprint.separate_map FStar_Pprint.hardline p_patternBranch
                branches in
            FStar_Pprint.op_Hat_Slash_Hat uu____2812 uu____2813 in
          FStar_Pprint.op_Hat_Slash_Hat uu____2808 uu____2811 in
        FStar_Pprint.group uu____2807
    | FStar_Parser_AST.Match (e1,branches) ->
        let uu____2830 =
          let uu____2831 =
            let uu____2832 = str "match" in
            let uu____2833 = p_noSeqTerm e1 in
            let uu____2834 = str "with" in
            FStar_Pprint.surround (Prims.parse_int "2") (Prims.parse_int "1")
              uu____2832 uu____2833 uu____2834 in
          let uu____2835 =
            FStar_Pprint.separate_map FStar_Pprint.hardline p_patternBranch
              branches in
          FStar_Pprint.op_Hat_Slash_Hat uu____2831 uu____2835 in
        FStar_Pprint.group uu____2830
    | FStar_Parser_AST.LetOpen (uid,e1) ->
        let uu____2842 =
          let uu____2843 =
            let uu____2844 = str "let open" in
            let uu____2845 = p_quident uid in
            let uu____2846 = str "in" in
            FStar_Pprint.surround (Prims.parse_int "2") (Prims.parse_int "1")
              uu____2844 uu____2845 uu____2846 in
          let uu____2847 = p_term e1 in
          FStar_Pprint.op_Hat_Slash_Hat uu____2843 uu____2847 in
        FStar_Pprint.group uu____2842
    | FStar_Parser_AST.Let (q,lbs,e1) ->
        let let_doc =
          let uu____2858 = str "let" in
          let uu____2859 = p_letqualifier q in
          FStar_Pprint.op_Hat_Hat uu____2858 uu____2859 in
        let uu____2860 =
          let uu____2861 =
            let uu____2862 =
              let uu____2863 = str "and" in
              precede_break_separate_map let_doc uu____2863 p_letbinding lbs in
            let uu____2866 = str "in" in
            FStar_Pprint.op_Hat_Slash_Hat uu____2862 uu____2866 in
          FStar_Pprint.group uu____2861 in
        let uu____2867 = p_term e1 in
        FStar_Pprint.op_Hat_Slash_Hat uu____2860 uu____2867
    | FStar_Parser_AST.Abs
        ({ FStar_Parser_AST.pat = FStar_Parser_AST.PatVar (x,typ_opt);
           FStar_Parser_AST.prange = uu____2870;_}::[],{
                                                         FStar_Parser_AST.tm
                                                           =
                                                           FStar_Parser_AST.Match
                                                           (maybe_x,branches);
                                                         FStar_Parser_AST.range
                                                           = uu____2873;
                                                         FStar_Parser_AST.level
                                                           = uu____2874;_})
        when matches_var maybe_x x ->
        let uu____2888 =
          let uu____2889 = str "function" in
          let uu____2890 =
            FStar_Pprint.separate_map FStar_Pprint.hardline p_patternBranch
              branches in
          FStar_Pprint.op_Hat_Slash_Hat uu____2889 uu____2890 in
        FStar_Pprint.group uu____2888
    | FStar_Parser_AST.Assign (id,e1) ->
        let uu____2897 =
          let uu____2898 = p_lident id in
          let uu____2899 =
            let uu____2900 = p_noSeqTerm e1 in
            FStar_Pprint.op_Hat_Slash_Hat FStar_Pprint.larrow uu____2900 in
          FStar_Pprint.op_Hat_Slash_Hat uu____2898 uu____2899 in
        FStar_Pprint.group uu____2897
    | uu____2901 -> p_typ e
and p_typ: FStar_Parser_AST.term -> FStar_Pprint.document =
  fun e  -> with_comment p_typ' e e.FStar_Parser_AST.range
and p_typ': FStar_Parser_AST.term -> FStar_Pprint.document =
  fun e  ->
    let uu____2904 =
      let uu____2905 = unparen e in uu____2905.FStar_Parser_AST.tm in
    match uu____2904 with
    | FStar_Parser_AST.QForall (bs,trigger,e1) ->
        let uu____2915 =
          let uu____2916 =
            let uu____2917 = p_quantifier e in
            FStar_Pprint.op_Hat_Hat uu____2917 FStar_Pprint.space in
          let uu____2918 = p_binders true bs in
          FStar_Pprint.soft_surround (Prims.parse_int "2")
            (Prims.parse_int "0") uu____2916 uu____2918 FStar_Pprint.dot in
        let uu____2919 =
          let uu____2920 = p_trigger trigger in
          let uu____2921 = p_noSeqTerm e1 in
          FStar_Pprint.op_Hat_Hat uu____2920 uu____2921 in
        prefix2 uu____2915 uu____2919
    | FStar_Parser_AST.QExists (bs,trigger,e1) ->
        let uu____2931 =
          let uu____2932 =
            let uu____2933 = p_quantifier e in
            FStar_Pprint.op_Hat_Hat uu____2933 FStar_Pprint.space in
          let uu____2934 = p_binders true bs in
          FStar_Pprint.soft_surround (Prims.parse_int "2")
            (Prims.parse_int "0") uu____2932 uu____2934 FStar_Pprint.dot in
        let uu____2935 =
          let uu____2936 = p_trigger trigger in
          let uu____2937 = p_noSeqTerm e1 in
          FStar_Pprint.op_Hat_Hat uu____2936 uu____2937 in
        prefix2 uu____2931 uu____2935
    | uu____2938 -> p_simpleTerm e
and p_quantifier: FStar_Parser_AST.term -> FStar_Pprint.document =
  fun e  ->
    let uu____2940 =
      let uu____2941 = unparen e in uu____2941.FStar_Parser_AST.tm in
    match uu____2940 with
    | FStar_Parser_AST.QForall uu____2942 -> str "forall"
    | FStar_Parser_AST.QExists uu____2949 -> str "exists"
    | uu____2956 ->
        failwith "Imposible : p_quantifier called on a non-quantifier term"
and p_trigger:
  FStar_Parser_AST.term Prims.list Prims.list -> FStar_Pprint.document =
  fun uu___104_2957  ->
    match uu___104_2957 with
    | [] -> FStar_Pprint.empty
    | pats ->
        let uu____2964 =
          let uu____2965 =
            let uu____2966 = str "pattern" in
            let uu____2967 =
              let uu____2968 =
                let uu____2969 = p_disjunctivePats pats in jump2 uu____2969 in
              let uu____2970 =
                FStar_Pprint.op_Hat_Hat FStar_Pprint.rbrace break1 in
              FStar_Pprint.op_Hat_Slash_Hat uu____2968 uu____2970 in
            FStar_Pprint.op_Hat_Slash_Hat uu____2966 uu____2967 in
          FStar_Pprint.op_Hat_Hat FStar_Pprint.colon uu____2965 in
        FStar_Pprint.op_Hat_Hat FStar_Pprint.lbrace uu____2964
and p_disjunctivePats:
  FStar_Parser_AST.term Prims.list Prims.list -> FStar_Pprint.document =
  fun pats  ->
    let uu____2974 = str "\\/" in
    FStar_Pprint.separate_map uu____2974 p_conjunctivePats pats
and p_conjunctivePats:
  FStar_Parser_AST.term Prims.list -> FStar_Pprint.document =
  fun pats  ->
    let uu____2978 =
      FStar_Pprint.separate_map FStar_Pprint.semi p_appTerm pats in
    FStar_Pprint.group uu____2978
and p_simpleTerm: FStar_Parser_AST.term -> FStar_Pprint.document =
  fun e  ->
    let uu____2980 =
      let uu____2981 = unparen e in uu____2981.FStar_Parser_AST.tm in
    match uu____2980 with
    | FStar_Parser_AST.Abs (pats,e1) ->
        let uu____2986 =
          let uu____2987 = str "fun" in
          let uu____2988 =
            let uu____2989 =
              FStar_Pprint.separate_map break1 p_atomicPattern pats in
            FStar_Pprint.op_Hat_Slash_Hat uu____2989 FStar_Pprint.rarrow in
          op_Hat_Slash_Plus_Hat uu____2987 uu____2988 in
        let uu____2990 = p_term e1 in
        op_Hat_Slash_Plus_Hat uu____2986 uu____2990
    | uu____2991 -> p_tmIff e
and p_maybeFocusArrow: Prims.bool -> FStar_Pprint.document =
  fun b  -> if b then str "~>" else FStar_Pprint.rarrow
and p_patternBranch:
  (FStar_Parser_AST.pattern* FStar_Parser_AST.term option*
    FStar_Parser_AST.term) -> FStar_Pprint.document
  =
  fun uu____2994  ->
    match uu____2994 with
    | (pat,when_opt,e) ->
        let maybe_paren =
          let uu____3007 =
            let uu____3008 = unparen e in uu____3008.FStar_Parser_AST.tm in
          match uu____3007 with
          | FStar_Parser_AST.Match uu____3011 -> soft_begin_end_with_nesting
          | FStar_Parser_AST.TryWith uu____3019 ->
              soft_begin_end_with_nesting
          | FStar_Parser_AST.Abs
              ({
                 FStar_Parser_AST.pat = FStar_Parser_AST.PatVar
                   (x,uu____3028);
                 FStar_Parser_AST.prange = uu____3029;_}::[],{
                                                               FStar_Parser_AST.tm
                                                                 =
                                                                 FStar_Parser_AST.Match
                                                                 (maybe_x,uu____3031);
                                                               FStar_Parser_AST.range
                                                                 = uu____3032;
                                                               FStar_Parser_AST.level
                                                                 = uu____3033;_})
              when matches_var maybe_x x -> soft_begin_end_with_nesting
          | uu____3047 -> (fun x  -> x) in
        let uu____3049 =
          let uu____3050 =
            let uu____3051 =
              let uu____3052 =
                let uu____3053 =
                  let uu____3054 = p_disjunctivePattern pat in
                  let uu____3055 =
                    let uu____3056 = p_maybeWhen when_opt in
                    FStar_Pprint.op_Hat_Hat uu____3056 FStar_Pprint.rarrow in
                  op_Hat_Slash_Plus_Hat uu____3054 uu____3055 in
                FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____3053 in
              FStar_Pprint.op_Hat_Hat FStar_Pprint.bar uu____3052 in
            FStar_Pprint.group uu____3051 in
          let uu____3057 =
            let uu____3058 = p_term e in maybe_paren uu____3058 in
          op_Hat_Slash_Plus_Hat uu____3050 uu____3057 in
        FStar_Pprint.group uu____3049
and p_maybeWhen: FStar_Parser_AST.term option -> FStar_Pprint.document =
  fun uu___105_3059  ->
    match uu___105_3059 with
    | None  -> FStar_Pprint.empty
    | Some e ->
        let uu____3062 = str "when" in
        let uu____3063 =
          let uu____3064 = p_tmFormula e in
          FStar_Pprint.op_Hat_Hat uu____3064 FStar_Pprint.space in
        op_Hat_Slash_Plus_Hat uu____3062 uu____3063
and p_tmIff: FStar_Parser_AST.term -> FStar_Pprint.document =
  fun e  ->
    let uu____3066 =
      let uu____3067 = unparen e in uu____3067.FStar_Parser_AST.tm in
    match uu____3066 with
    | FStar_Parser_AST.Op
        ({ FStar_Ident.idText = "<==>"; FStar_Ident.idRange = uu____3068;_},e1::e2::[])
        ->
        let uu____3072 = str "<==>" in
        let uu____3073 = p_tmImplies e1 in
        let uu____3074 = p_tmIff e2 in
        infix0 uu____3072 uu____3073 uu____3074
    | uu____3075 -> p_tmImplies e
and p_tmImplies: FStar_Parser_AST.term -> FStar_Pprint.document =
  fun e  ->
    let uu____3077 =
      let uu____3078 = unparen e in uu____3078.FStar_Parser_AST.tm in
    match uu____3077 with
    | FStar_Parser_AST.Op
        ({ FStar_Ident.idText = "==>"; FStar_Ident.idRange = uu____3079;_},e1::e2::[])
        ->
        let uu____3083 = str "==>" in
        let uu____3084 = p_tmArrow p_tmFormula e1 in
        let uu____3085 = p_tmImplies e2 in
        infix0 uu____3083 uu____3084 uu____3085
    | uu____3086 -> p_tmArrow p_tmFormula e
and p_tmArrow:
  (FStar_Parser_AST.term -> FStar_Pprint.document) ->
    FStar_Parser_AST.term -> FStar_Pprint.document
  =
  fun p_Tm  ->
    fun e  ->
      let uu____3091 =
        let uu____3092 = unparen e in uu____3092.FStar_Parser_AST.tm in
      match uu____3091 with
      | FStar_Parser_AST.Product (bs,tgt) ->
          let uu____3097 =
            let uu____3098 =
              FStar_Pprint.concat_map
                (fun b  ->
                   let uu____3100 = p_binder false b in
                   let uu____3101 =
                     let uu____3102 =
                       FStar_Pprint.op_Hat_Hat FStar_Pprint.rarrow break1 in
                     FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____3102 in
                   FStar_Pprint.op_Hat_Hat uu____3100 uu____3101) bs in
            let uu____3103 = p_tmArrow p_Tm tgt in
            FStar_Pprint.op_Hat_Hat uu____3098 uu____3103 in
          FStar_Pprint.group uu____3097
      | uu____3104 -> p_Tm e
and p_tmFormula: FStar_Parser_AST.term -> FStar_Pprint.document =
  fun e  ->
    let uu____3106 =
      let uu____3107 = unparen e in uu____3107.FStar_Parser_AST.tm in
    match uu____3106 with
    | FStar_Parser_AST.Op
        ({ FStar_Ident.idText = "\\/"; FStar_Ident.idRange = uu____3108;_},e1::e2::[])
        ->
        let uu____3112 = str "\\/" in
        let uu____3113 = p_tmFormula e1 in
        let uu____3114 = p_tmConjunction e2 in
        infix0 uu____3112 uu____3113 uu____3114
    | uu____3115 -> p_tmConjunction e
and p_tmConjunction: FStar_Parser_AST.term -> FStar_Pprint.document =
  fun e  ->
    let uu____3117 =
      let uu____3118 = unparen e in uu____3118.FStar_Parser_AST.tm in
    match uu____3117 with
    | FStar_Parser_AST.Op
        ({ FStar_Ident.idText = "/\\"; FStar_Ident.idRange = uu____3119;_},e1::e2::[])
        ->
        let uu____3123 = str "/\\" in
        let uu____3124 = p_tmConjunction e1 in
        let uu____3125 = p_tmTuple e2 in
        infix0 uu____3123 uu____3124 uu____3125
    | uu____3126 -> p_tmTuple e
and p_tmTuple: FStar_Parser_AST.term -> FStar_Pprint.document =
  fun e  -> with_comment p_tmTuple' e e.FStar_Parser_AST.range
and p_tmTuple': FStar_Parser_AST.term -> FStar_Pprint.document =
  fun e  ->
    let uu____3129 =
      let uu____3130 = unparen e in uu____3130.FStar_Parser_AST.tm in
    match uu____3129 with
    | FStar_Parser_AST.Construct (lid,args) when is_tuple_constructor lid ->
        let uu____3139 = FStar_Pprint.op_Hat_Hat FStar_Pprint.comma break1 in
        FStar_Pprint.separate_map uu____3139
          (fun uu____3142  ->
             match uu____3142 with | (e1,uu____3146) -> p_tmEq e1) args
    | uu____3147 -> p_tmEq e
and paren_if:
  Prims.int -> Prims.int -> FStar_Pprint.document -> FStar_Pprint.document =
  fun curr  ->
    fun mine  ->
      fun doc1  ->
        if mine <= curr
        then doc1
        else
          (let uu____3152 =
             let uu____3153 =
               FStar_Pprint.op_Hat_Hat doc1 FStar_Pprint.rparen in
             FStar_Pprint.op_Hat_Hat FStar_Pprint.lparen uu____3153 in
           FStar_Pprint.group uu____3152)
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
      let uu____3178 =
        let uu____3179 = unparen e in uu____3179.FStar_Parser_AST.tm in
      match uu____3178 with
      | FStar_Parser_AST.Op (op,e1::e2::[]) when
          ((is_operatorInfix0ad12 op) || ((FStar_Ident.text_of_id op) = "="))
            || ((FStar_Ident.text_of_id op) = "|>")
          ->
          let op1 = FStar_Ident.text_of_id op in
          let uu____3185 = levels op1 in
          (match uu____3185 with
           | (left1,mine,right1) ->
               let uu____3192 =
                 let uu____3193 = FStar_All.pipe_left str op1 in
                 let uu____3194 = p_tmEq' left1 e1 in
                 let uu____3195 = p_tmEq' right1 e2 in
                 infix0 uu____3193 uu____3194 uu____3195 in
               paren_if curr mine uu____3192)
      | FStar_Parser_AST.Op
          ({ FStar_Ident.idText = ":="; FStar_Ident.idRange = uu____3196;_},e1::e2::[])
          ->
          let uu____3200 =
            let uu____3201 = p_tmEq e1 in
            let uu____3202 =
              let uu____3203 =
                let uu____3204 =
                  let uu____3205 = p_tmEq e2 in
                  op_Hat_Slash_Plus_Hat FStar_Pprint.equals uu____3205 in
                FStar_Pprint.op_Hat_Hat FStar_Pprint.colon uu____3204 in
              FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____3203 in
            FStar_Pprint.op_Hat_Hat uu____3201 uu____3202 in
          FStar_Pprint.group uu____3200
      | FStar_Parser_AST.Op
          ({ FStar_Ident.idText = "-"; FStar_Ident.idRange = uu____3206;_},e1::[])
          ->
          let uu____3209 = levels "-" in
          (match uu____3209 with
           | (left1,mine,right1) ->
               let uu____3216 = p_tmEq' mine e1 in
               FStar_Pprint.op_Hat_Slash_Hat FStar_Pprint.minus uu____3216)
      | uu____3217 -> p_tmNoEq e
and p_tmNoEq: FStar_Parser_AST.term -> FStar_Pprint.document =
  fun e  ->
    let n1 = max_level [colon_colon (); amp (); opinfix3 (); opinfix4 ()] in
    p_tmNoEq' n1 e
and p_tmNoEq': Prims.int -> FStar_Parser_AST.term -> FStar_Pprint.document =
  fun curr  ->
    fun e  ->
      let uu____3247 =
        let uu____3248 = unparen e in uu____3248.FStar_Parser_AST.tm in
      match uu____3247 with
      | FStar_Parser_AST.Construct (lid,(e1,uu____3251)::(e2,uu____3253)::[])
          when
          (FStar_Ident.lid_equals lid FStar_Parser_Const.cons_lid) &&
            (let uu____3263 = is_list e in Prims.op_Negation uu____3263)
          ->
          let op = "::" in
          let uu____3265 = levels op in
          (match uu____3265 with
           | (left1,mine,right1) ->
               let uu____3272 =
                 let uu____3273 = str op in
                 let uu____3274 = p_tmNoEq' left1 e1 in
                 let uu____3275 = p_tmNoEq' right1 e2 in
                 infix0 uu____3273 uu____3274 uu____3275 in
               paren_if curr mine uu____3272)
      | FStar_Parser_AST.Sum (binders,res) ->
          let op = "&" in
          let uu____3281 = levels op in
          (match uu____3281 with
           | (left1,mine,right1) ->
               let p_dsumfst b =
                 let uu____3292 = p_binder false b in
                 let uu____3293 =
                   let uu____3294 =
                     let uu____3295 = str op in
                     FStar_Pprint.op_Hat_Hat uu____3295 break1 in
                   FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____3294 in
                 FStar_Pprint.op_Hat_Hat uu____3292 uu____3293 in
               let uu____3296 =
                 let uu____3297 = FStar_Pprint.concat_map p_dsumfst binders in
                 let uu____3298 = p_tmNoEq' right1 res in
                 FStar_Pprint.op_Hat_Hat uu____3297 uu____3298 in
               paren_if curr mine uu____3296)
      | FStar_Parser_AST.Op (op,e1::e2::[]) when is_operatorInfix34 op ->
          let op1 = FStar_Ident.text_of_id op in
          let uu____3304 = levels op1 in
          (match uu____3304 with
           | (left1,mine,right1) ->
               let uu____3311 =
                 let uu____3312 = str op1 in
                 let uu____3313 = p_tmNoEq' left1 e1 in
                 let uu____3314 = p_tmNoEq' right1 e2 in
                 infix0 uu____3312 uu____3313 uu____3314 in
               paren_if curr mine uu____3311)
      | FStar_Parser_AST.NamedTyp (lid,e1) ->
          let uu____3317 =
            let uu____3318 = p_lidentOrUnderscore lid in
            let uu____3319 =
              let uu____3320 = p_appTerm e1 in
              FStar_Pprint.op_Hat_Slash_Hat FStar_Pprint.colon uu____3320 in
            FStar_Pprint.op_Hat_Slash_Hat uu____3318 uu____3319 in
          FStar_Pprint.group uu____3317
      | FStar_Parser_AST.Refine (b,phi) -> p_refinedBinder b phi
      | FStar_Parser_AST.Record (with_opt,record_fields) ->
          let uu____3333 =
            let uu____3334 =
              default_or_map FStar_Pprint.empty p_with_clause with_opt in
            let uu____3335 =
              let uu____3336 =
                FStar_Pprint.op_Hat_Hat FStar_Pprint.semi break1 in
              FStar_Pprint.separate_map uu____3336 p_simpleDef record_fields in
            FStar_Pprint.op_Hat_Hat uu____3334 uu____3335 in
          braces_with_nesting uu____3333
      | FStar_Parser_AST.Op
          ({ FStar_Ident.idText = "~"; FStar_Ident.idRange = uu____3339;_},e1::[])
          ->
          let uu____3342 =
            let uu____3343 = str "~" in
            let uu____3344 = p_atomicTerm e1 in
            FStar_Pprint.op_Hat_Hat uu____3343 uu____3344 in
          FStar_Pprint.group uu____3342
      | uu____3345 -> p_appTerm e
and p_with_clause: FStar_Parser_AST.term -> FStar_Pprint.document =
  fun e  ->
    let uu____3347 = p_appTerm e in
    let uu____3348 =
      let uu____3349 =
        let uu____3350 = str "with" in
        FStar_Pprint.op_Hat_Hat uu____3350 break1 in
      FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____3349 in
    FStar_Pprint.op_Hat_Hat uu____3347 uu____3348
and p_refinedBinder:
  FStar_Parser_AST.binder -> FStar_Parser_AST.term -> FStar_Pprint.document =
  fun b  ->
    fun phi  ->
      match b.FStar_Parser_AST.b with
      | FStar_Parser_AST.Annotated (lid,t) ->
          let uu____3355 =
            let uu____3356 = p_lident lid in
            p_refinement b.FStar_Parser_AST.aqual uu____3356 t phi in
          soft_parens_with_nesting uu____3355
      | FStar_Parser_AST.TAnnotated uu____3357 ->
          failwith "Is this still used ?"
      | FStar_Parser_AST.Variable uu____3360 ->
          let uu____3361 =
            let uu____3362 = FStar_Parser_AST.binder_to_string b in
            FStar_Util.format1
              "Imposible : a refined binder ought to be annotated %s"
              uu____3362 in
          failwith uu____3361
      | FStar_Parser_AST.TVariable uu____3363 ->
          let uu____3364 =
            let uu____3365 = FStar_Parser_AST.binder_to_string b in
            FStar_Util.format1
              "Imposible : a refined binder ought to be annotated %s"
              uu____3365 in
          failwith uu____3364
      | FStar_Parser_AST.NoName uu____3366 ->
          let uu____3367 =
            let uu____3368 = FStar_Parser_AST.binder_to_string b in
            FStar_Util.format1
              "Imposible : a refined binder ought to be annotated %s"
              uu____3368 in
          failwith uu____3367
and p_simpleDef:
  (FStar_Ident.lid* FStar_Parser_AST.term) -> FStar_Pprint.document =
  fun uu____3369  ->
    match uu____3369 with
    | (lid,e) ->
        let uu____3374 =
          let uu____3375 = p_qlident lid in
          let uu____3376 =
            let uu____3377 = p_tmIff e in
            FStar_Pprint.op_Hat_Slash_Hat FStar_Pprint.equals uu____3377 in
          FStar_Pprint.op_Hat_Slash_Hat uu____3375 uu____3376 in
        FStar_Pprint.group uu____3374
and p_appTerm: FStar_Parser_AST.term -> FStar_Pprint.document =
  fun e  ->
    let uu____3379 =
      let uu____3380 = unparen e in uu____3380.FStar_Parser_AST.tm in
    match uu____3379 with
    | FStar_Parser_AST.App uu____3381 when is_general_application e ->
        let uu____3385 = head_and_args e in
        (match uu____3385 with
         | (head1,args) ->
             let uu____3399 =
               let uu____3405 = FStar_ST.read should_print_fs_typ_app in
               if uu____3405
               then
                 let uu____3413 =
                   FStar_Util.take
                     (fun uu____3424  ->
                        match uu____3424 with
                        | (uu____3427,aq) -> aq = FStar_Parser_AST.FsTypApp)
                     args in
                 match uu____3413 with
                 | (fs_typ_args,args1) ->
                     let uu____3448 =
                       let uu____3449 = p_indexingTerm head1 in
                       let uu____3450 =
                         let uu____3451 =
                           FStar_Pprint.op_Hat_Hat FStar_Pprint.comma break1 in
                         soft_surround_separate_map (Prims.parse_int "2")
                           (Prims.parse_int "0") FStar_Pprint.empty
                           FStar_Pprint.langle uu____3451 FStar_Pprint.rangle
                           p_fsTypArg fs_typ_args in
                       FStar_Pprint.op_Hat_Hat uu____3449 uu____3450 in
                     (uu____3448, args1)
               else
                 (let uu____3458 = p_indexingTerm head1 in (uu____3458, args)) in
             (match uu____3399 with
              | (head_doc,args1) ->
                  let uu____3470 =
                    let uu____3471 =
                      FStar_Pprint.op_Hat_Hat head_doc FStar_Pprint.space in
                    soft_surround_separate_map (Prims.parse_int "2")
                      (Prims.parse_int "0") head_doc uu____3471 break1
                      FStar_Pprint.empty p_argTerm args1 in
                  FStar_Pprint.group uu____3470))
    | FStar_Parser_AST.Construct (lid,args) when
        (is_general_construction e) &&
          (Prims.op_Negation (is_dtuple_constructor lid))
        ->
        (match args with
         | [] -> p_quident lid
         | arg::[] ->
             let uu____3491 =
               let uu____3492 = p_quident lid in
               let uu____3493 = p_argTerm arg in
               FStar_Pprint.op_Hat_Slash_Hat uu____3492 uu____3493 in
             FStar_Pprint.group uu____3491
         | hd1::tl1 ->
             let uu____3503 =
               let uu____3504 =
                 let uu____3505 =
                   let uu____3506 = p_quident lid in
                   let uu____3507 = p_argTerm hd1 in
                   prefix2 uu____3506 uu____3507 in
                 FStar_Pprint.group uu____3505 in
               let uu____3508 =
                 let uu____3509 =
                   FStar_Pprint.separate_map break1 p_argTerm tl1 in
                 jump2 uu____3509 in
               FStar_Pprint.op_Hat_Hat uu____3504 uu____3508 in
             FStar_Pprint.group uu____3503)
    | uu____3512 -> p_indexingTerm e
and p_argTerm:
  (FStar_Parser_AST.term* FStar_Parser_AST.imp) -> FStar_Pprint.document =
  fun arg_imp  ->
    match arg_imp with
    | ({ FStar_Parser_AST.tm = FStar_Parser_AST.Uvar uu____3516;
         FStar_Parser_AST.range = uu____3517;
         FStar_Parser_AST.level = uu____3518;_},FStar_Parser_AST.UnivApp
       ) -> p_univar (fst arg_imp)
    | (u,FStar_Parser_AST.UnivApp ) -> p_universe u
    | (e,FStar_Parser_AST.FsTypApp ) ->
        (FStar_Util.print_warning
           "Unexpected FsTypApp, output might not be formatted correctly.\n";
         (let uu____3522 = p_indexingTerm e in
          FStar_Pprint.surround (Prims.parse_int "2") (Prims.parse_int "1")
            FStar_Pprint.langle uu____3522 FStar_Pprint.rangle))
    | (e,FStar_Parser_AST.Hash ) ->
        let uu____3524 = str "#" in
        let uu____3525 = p_indexingTerm e in
        FStar_Pprint.op_Hat_Hat uu____3524 uu____3525
    | (e,FStar_Parser_AST.Nothing ) -> p_indexingTerm e
and p_fsTypArg:
  (FStar_Parser_AST.term* FStar_Parser_AST.imp) -> FStar_Pprint.document =
  fun uu____3527  ->
    match uu____3527 with | (e,uu____3531) -> p_indexingTerm e
and p_indexingTerm_aux:
  (FStar_Parser_AST.term -> FStar_Pprint.document) ->
    FStar_Parser_AST.term -> FStar_Pprint.document
  =
  fun exit1  ->
    fun e  ->
      let uu____3536 =
        let uu____3537 = unparen e in uu____3537.FStar_Parser_AST.tm in
      match uu____3536 with
      | FStar_Parser_AST.Op
          ({ FStar_Ident.idText = ".()"; FStar_Ident.idRange = uu____3538;_},e1::e2::[])
          ->
          let uu____3542 =
            let uu____3543 = p_indexingTerm_aux p_atomicTermNotQUident e1 in
            let uu____3544 =
              let uu____3545 =
                let uu____3546 = p_term e2 in
                soft_parens_with_nesting uu____3546 in
              FStar_Pprint.op_Hat_Hat FStar_Pprint.dot uu____3545 in
            FStar_Pprint.op_Hat_Hat uu____3543 uu____3544 in
          FStar_Pprint.group uu____3542
      | FStar_Parser_AST.Op
          ({ FStar_Ident.idText = ".[]"; FStar_Ident.idRange = uu____3547;_},e1::e2::[])
          ->
          let uu____3551 =
            let uu____3552 = p_indexingTerm_aux p_atomicTermNotQUident e1 in
            let uu____3553 =
              let uu____3554 =
                let uu____3555 = p_term e2 in
                soft_brackets_with_nesting uu____3555 in
              FStar_Pprint.op_Hat_Hat FStar_Pprint.dot uu____3554 in
            FStar_Pprint.op_Hat_Hat uu____3552 uu____3553 in
          FStar_Pprint.group uu____3551
      | uu____3556 -> exit1 e
and p_indexingTerm: FStar_Parser_AST.term -> FStar_Pprint.document =
  fun e  -> p_indexingTerm_aux p_atomicTerm e
and p_atomicTerm: FStar_Parser_AST.term -> FStar_Pprint.document =
  fun e  ->
    let uu____3559 =
      let uu____3560 = unparen e in uu____3560.FStar_Parser_AST.tm in
    match uu____3559 with
    | FStar_Parser_AST.LetOpen (lid,e1) ->
        let uu____3563 = p_quident lid in
        let uu____3564 =
          let uu____3565 =
            let uu____3566 = p_term e1 in soft_parens_with_nesting uu____3566 in
          FStar_Pprint.op_Hat_Hat FStar_Pprint.dot uu____3565 in
        FStar_Pprint.op_Hat_Hat uu____3563 uu____3564
    | FStar_Parser_AST.Name lid -> p_quident lid
    | FStar_Parser_AST.Op (op,e1::[]) when is_general_prefix_op op ->
        let uu____3571 = str (FStar_Ident.text_of_id op) in
        let uu____3572 = p_atomicTerm e1 in
        FStar_Pprint.op_Hat_Hat uu____3571 uu____3572
    | uu____3573 -> p_atomicTermNotQUident e
and p_atomicTermNotQUident: FStar_Parser_AST.term -> FStar_Pprint.document =
  fun e  ->
    let uu____3575 =
      let uu____3576 = unparen e in uu____3576.FStar_Parser_AST.tm in
    match uu____3575 with
    | FStar_Parser_AST.Wild  -> FStar_Pprint.underscore
    | FStar_Parser_AST.Var lid when
        FStar_Ident.lid_equals lid FStar_Parser_Const.assert_lid ->
        str "assert"
    | FStar_Parser_AST.Tvar tv -> p_tvar tv
    | FStar_Parser_AST.Const c ->
        (match c with
         | FStar_Const.Const_char x when x = '\n' -> str "0x0Az"
         | uu____3581 -> p_constant c)
    | FStar_Parser_AST.Name lid when
        FStar_Ident.lid_equals lid FStar_Parser_Const.true_lid -> str "True"
    | FStar_Parser_AST.Name lid when
        FStar_Ident.lid_equals lid FStar_Parser_Const.false_lid ->
        str "False"
    | FStar_Parser_AST.Op (op,e1::[]) when is_general_prefix_op op ->
        let uu____3587 = str (FStar_Ident.text_of_id op) in
        let uu____3588 = p_atomicTermNotQUident e1 in
        FStar_Pprint.op_Hat_Hat uu____3587 uu____3588
    | FStar_Parser_AST.Op (op,[]) ->
        let uu____3591 =
          let uu____3592 =
            let uu____3593 = str (FStar_Ident.text_of_id op) in
            let uu____3594 =
              FStar_Pprint.op_Hat_Hat FStar_Pprint.space FStar_Pprint.rparen in
            FStar_Pprint.op_Hat_Hat uu____3593 uu____3594 in
          FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____3592 in
        FStar_Pprint.op_Hat_Hat FStar_Pprint.lparen uu____3591
    | FStar_Parser_AST.Construct (lid,args) when is_dtuple_constructor lid ->
        let uu____3603 =
          FStar_Pprint.op_Hat_Hat FStar_Pprint.lparen FStar_Pprint.bar in
        let uu____3604 =
          let uu____3605 = FStar_Pprint.op_Hat_Hat FStar_Pprint.comma break1 in
          let uu____3606 = FStar_List.map FStar_Pervasives.fst args in
          FStar_Pprint.separate_map uu____3605 p_tmEq uu____3606 in
        let uu____3610 =
          FStar_Pprint.op_Hat_Hat FStar_Pprint.bar FStar_Pprint.rparen in
        FStar_Pprint.surround (Prims.parse_int "2") (Prims.parse_int "1")
          uu____3603 uu____3604 uu____3610
    | FStar_Parser_AST.Project (e1,lid) ->
        let uu____3613 =
          let uu____3614 = p_atomicTermNotQUident e1 in
          let uu____3615 =
            let uu____3616 = p_qlident lid in
            FStar_Pprint.op_Hat_Hat FStar_Pprint.dot uu____3616 in
          FStar_Pprint.prefix (Prims.parse_int "2") (Prims.parse_int "0")
            uu____3614 uu____3615 in
        FStar_Pprint.group uu____3613
    | uu____3617 -> p_projectionLHS e
and p_projectionLHS: FStar_Parser_AST.term -> FStar_Pprint.document =
  fun e  ->
    let uu____3619 =
      let uu____3620 = unparen e in uu____3620.FStar_Parser_AST.tm in
    match uu____3619 with
    | FStar_Parser_AST.Var lid -> p_qlident lid
    | FStar_Parser_AST.Projector (constr_lid,field_lid) ->
        let uu____3624 = p_quident constr_lid in
        let uu____3625 =
          let uu____3626 =
            let uu____3627 = p_lident field_lid in
            FStar_Pprint.op_Hat_Hat FStar_Pprint.dot uu____3627 in
          FStar_Pprint.op_Hat_Hat FStar_Pprint.qmark uu____3626 in
        FStar_Pprint.op_Hat_Hat uu____3624 uu____3625
    | FStar_Parser_AST.Discrim constr_lid ->
        let uu____3629 = p_quident constr_lid in
        FStar_Pprint.op_Hat_Hat uu____3629 FStar_Pprint.qmark
    | FStar_Parser_AST.Paren e1 ->
        let uu____3631 = p_term e1 in soft_parens_with_nesting uu____3631
    | uu____3632 when is_array e ->
        let es = extract_from_list e in
        let uu____3635 =
          FStar_Pprint.op_Hat_Hat FStar_Pprint.lbracket FStar_Pprint.bar in
        let uu____3636 =
          let uu____3637 = FStar_Pprint.op_Hat_Hat FStar_Pprint.semi break1 in
          separate_map_or_flow uu____3637 p_noSeqTerm es in
        let uu____3638 =
          FStar_Pprint.op_Hat_Hat FStar_Pprint.bar FStar_Pprint.rbracket in
        FStar_Pprint.surround (Prims.parse_int "2") (Prims.parse_int "0")
          uu____3635 uu____3636 uu____3638
    | uu____3639 when is_list e ->
        let uu____3640 =
          let uu____3641 = FStar_Pprint.op_Hat_Hat FStar_Pprint.semi break1 in
          let uu____3642 = extract_from_list e in
          separate_map_or_flow uu____3641 p_noSeqTerm uu____3642 in
        FStar_Pprint.surround (Prims.parse_int "2") (Prims.parse_int "0")
          FStar_Pprint.lbracket uu____3640 FStar_Pprint.rbracket
    | uu____3644 when is_lex_list e ->
        let uu____3645 =
          FStar_Pprint.op_Hat_Hat FStar_Pprint.percent FStar_Pprint.lbracket in
        let uu____3646 =
          let uu____3647 = FStar_Pprint.op_Hat_Hat FStar_Pprint.semi break1 in
          let uu____3648 = extract_from_list e in
          separate_map_or_flow uu____3647 p_noSeqTerm uu____3648 in
        FStar_Pprint.surround (Prims.parse_int "2") (Prims.parse_int "1")
          uu____3645 uu____3646 FStar_Pprint.rbracket
    | uu____3650 when is_ref_set e ->
        let es = extract_from_ref_set e in
        let uu____3653 =
          FStar_Pprint.op_Hat_Hat FStar_Pprint.bang FStar_Pprint.lbrace in
        let uu____3654 =
          let uu____3655 = FStar_Pprint.op_Hat_Hat FStar_Pprint.comma break1 in
          separate_map_or_flow uu____3655 p_appTerm es in
        FStar_Pprint.surround (Prims.parse_int "2") (Prims.parse_int "0")
          uu____3653 uu____3654 FStar_Pprint.rbrace
    | FStar_Parser_AST.Labeled (e1,s,b) ->
        let uu____3659 = FStar_Pprint.break_ (Prims.parse_int "0") in
        let uu____3660 =
          let uu____3661 = str (Prims.strcat "(*" (Prims.strcat s "*)")) in
          let uu____3662 = p_term e1 in
          FStar_Pprint.op_Hat_Slash_Hat uu____3661 uu____3662 in
        FStar_Pprint.op_Hat_Hat uu____3659 uu____3660
    | FStar_Parser_AST.Op (op,args) when
        let uu____3667 = handleable_op op args in
        Prims.op_Negation uu____3667 ->
        let uu____3668 =
          let uu____3669 =
            let uu____3670 =
              let uu____3671 =
                let uu____3672 =
                  FStar_Util.string_of_int (FStar_List.length args) in
                Prims.strcat uu____3672
                  " arguments couldn't be handled by the pretty printer" in
              Prims.strcat " with " uu____3671 in
            Prims.strcat (FStar_Ident.text_of_id op) uu____3670 in
          Prims.strcat "Operation " uu____3669 in
        failwith uu____3668
    | FStar_Parser_AST.Uvar uu____3676 ->
        failwith "Unexpected universe variable out of universe context"
    | FStar_Parser_AST.Wild  ->
        let uu____3677 = p_term e in soft_parens_with_nesting uu____3677
    | FStar_Parser_AST.Const uu____3678 ->
        let uu____3679 = p_term e in soft_parens_with_nesting uu____3679
    | FStar_Parser_AST.Op uu____3680 ->
        let uu____3684 = p_term e in soft_parens_with_nesting uu____3684
    | FStar_Parser_AST.Tvar uu____3685 ->
        let uu____3686 = p_term e in soft_parens_with_nesting uu____3686
    | FStar_Parser_AST.Var uu____3687 ->
        let uu____3688 = p_term e in soft_parens_with_nesting uu____3688
    | FStar_Parser_AST.Name uu____3689 ->
        let uu____3690 = p_term e in soft_parens_with_nesting uu____3690
    | FStar_Parser_AST.Construct uu____3691 ->
        let uu____3697 = p_term e in soft_parens_with_nesting uu____3697
    | FStar_Parser_AST.Abs uu____3698 ->
        let uu____3702 = p_term e in soft_parens_with_nesting uu____3702
    | FStar_Parser_AST.App uu____3703 ->
        let uu____3707 = p_term e in soft_parens_with_nesting uu____3707
    | FStar_Parser_AST.Let uu____3708 ->
        let uu____3715 = p_term e in soft_parens_with_nesting uu____3715
    | FStar_Parser_AST.LetOpen uu____3716 ->
        let uu____3719 = p_term e in soft_parens_with_nesting uu____3719
    | FStar_Parser_AST.Seq uu____3720 ->
        let uu____3723 = p_term e in soft_parens_with_nesting uu____3723
    | FStar_Parser_AST.Bind uu____3724 ->
        let uu____3728 = p_term e in soft_parens_with_nesting uu____3728
    | FStar_Parser_AST.If uu____3729 ->
        let uu____3733 = p_term e in soft_parens_with_nesting uu____3733
    | FStar_Parser_AST.Match uu____3734 ->
        let uu____3742 = p_term e in soft_parens_with_nesting uu____3742
    | FStar_Parser_AST.TryWith uu____3743 ->
        let uu____3751 = p_term e in soft_parens_with_nesting uu____3751
    | FStar_Parser_AST.Ascribed uu____3752 ->
        let uu____3757 = p_term e in soft_parens_with_nesting uu____3757
    | FStar_Parser_AST.Record uu____3758 ->
        let uu____3765 = p_term e in soft_parens_with_nesting uu____3765
    | FStar_Parser_AST.Project uu____3766 ->
        let uu____3769 = p_term e in soft_parens_with_nesting uu____3769
    | FStar_Parser_AST.Product uu____3770 ->
        let uu____3774 = p_term e in soft_parens_with_nesting uu____3774
    | FStar_Parser_AST.Sum uu____3775 ->
        let uu____3779 = p_term e in soft_parens_with_nesting uu____3779
    | FStar_Parser_AST.QForall uu____3780 ->
        let uu____3787 = p_term e in soft_parens_with_nesting uu____3787
    | FStar_Parser_AST.QExists uu____3788 ->
        let uu____3795 = p_term e in soft_parens_with_nesting uu____3795
    | FStar_Parser_AST.Refine uu____3796 ->
        let uu____3799 = p_term e in soft_parens_with_nesting uu____3799
    | FStar_Parser_AST.NamedTyp uu____3800 ->
        let uu____3803 = p_term e in soft_parens_with_nesting uu____3803
    | FStar_Parser_AST.Requires uu____3804 ->
        let uu____3808 = p_term e in soft_parens_with_nesting uu____3808
    | FStar_Parser_AST.Ensures uu____3809 ->
        let uu____3813 = p_term e in soft_parens_with_nesting uu____3813
    | FStar_Parser_AST.Assign uu____3814 ->
        let uu____3817 = p_term e in soft_parens_with_nesting uu____3817
    | FStar_Parser_AST.Attributes uu____3818 ->
        let uu____3820 = p_term e in soft_parens_with_nesting uu____3820
and p_constant: FStar_Const.sconst -> FStar_Pprint.document =
  fun uu___108_3821  ->
    match uu___108_3821 with
    | FStar_Const.Const_effect  -> str "Effect"
    | FStar_Const.Const_unit  -> str "()"
    | FStar_Const.Const_bool b -> FStar_Pprint.doc_of_bool b
    | FStar_Const.Const_float x -> str (FStar_Util.string_of_float x)
    | FStar_Const.Const_char x ->
        let uu____3825 = FStar_Pprint.doc_of_char x in
        FStar_Pprint.squotes uu____3825
    | FStar_Const.Const_string (bytes,uu____3827) ->
        let uu____3830 = str (FStar_Util.string_of_bytes bytes) in
        FStar_Pprint.dquotes uu____3830
    | FStar_Const.Const_bytearray (bytes,uu____3832) ->
        let uu____3835 =
          let uu____3836 = str (FStar_Util.string_of_bytes bytes) in
          FStar_Pprint.dquotes uu____3836 in
        let uu____3837 = str "B" in
        FStar_Pprint.op_Hat_Hat uu____3835 uu____3837
    | FStar_Const.Const_int (repr,sign_width_opt) ->
        let signedness uu___106_3849 =
          match uu___106_3849 with
          | FStar_Const.Unsigned  -> str "u"
          | FStar_Const.Signed  -> FStar_Pprint.empty in
        let width uu___107_3853 =
          match uu___107_3853 with
          | FStar_Const.Int8  -> str "y"
          | FStar_Const.Int16  -> str "s"
          | FStar_Const.Int32  -> str "l"
          | FStar_Const.Int64  -> str "L" in
        let ending =
          default_or_map FStar_Pprint.empty
            (fun uu____3857  ->
               match uu____3857 with
               | (s,w) ->
                   let uu____3862 = signedness s in
                   let uu____3863 = width w in
                   FStar_Pprint.op_Hat_Hat uu____3862 uu____3863)
            sign_width_opt in
        let uu____3864 = str repr in
        FStar_Pprint.op_Hat_Hat uu____3864 ending
    | FStar_Const.Const_range r ->
        let uu____3866 = FStar_Range.string_of_range r in str uu____3866
    | FStar_Const.Const_reify  -> str "reify"
    | FStar_Const.Const_reflect lid ->
        let uu____3868 = p_quident lid in
        let uu____3869 =
          let uu____3870 =
            let uu____3871 = str "reflect" in
            FStar_Pprint.op_Hat_Hat FStar_Pprint.dot uu____3871 in
          FStar_Pprint.op_Hat_Hat FStar_Pprint.qmark uu____3870 in
        FStar_Pprint.op_Hat_Hat uu____3868 uu____3869
and p_universe: FStar_Parser_AST.term -> FStar_Pprint.document =
  fun u  ->
    let uu____3873 = str "u#" in
    let uu____3874 = p_atomicUniverse u in
    FStar_Pprint.op_Hat_Hat uu____3873 uu____3874
and p_universeFrom: FStar_Parser_AST.term -> FStar_Pprint.document =
  fun u  ->
    let uu____3876 =
      let uu____3877 = unparen u in uu____3877.FStar_Parser_AST.tm in
    match uu____3876 with
    | FStar_Parser_AST.Op
        ({ FStar_Ident.idText = "+"; FStar_Ident.idRange = uu____3878;_},u1::u2::[])
        ->
        let uu____3882 =
          let uu____3883 = p_universeFrom u1 in
          let uu____3884 =
            let uu____3885 = p_universeFrom u2 in
            FStar_Pprint.op_Hat_Slash_Hat FStar_Pprint.plus uu____3885 in
          FStar_Pprint.op_Hat_Slash_Hat uu____3883 uu____3884 in
        FStar_Pprint.group uu____3882
    | FStar_Parser_AST.App uu____3886 ->
        let uu____3890 = head_and_args u in
        (match uu____3890 with
         | (head1,args) ->
             let uu____3904 =
               let uu____3905 = unparen head1 in
               uu____3905.FStar_Parser_AST.tm in
             (match uu____3904 with
              | FStar_Parser_AST.Var maybe_max_lid when
                  FStar_Ident.lid_equals maybe_max_lid
                    FStar_Parser_Const.max_lid
                  ->
                  let uu____3907 =
                    let uu____3908 = p_qlident FStar_Parser_Const.max_lid in
                    let uu____3909 =
                      FStar_Pprint.separate_map FStar_Pprint.space
                        (fun uu____3912  ->
                           match uu____3912 with
                           | (u1,uu____3916) -> p_atomicUniverse u1) args in
                    op_Hat_Slash_Plus_Hat uu____3908 uu____3909 in
                  FStar_Pprint.group uu____3907
              | uu____3917 ->
                  let uu____3918 =
                    let uu____3919 = FStar_Parser_AST.term_to_string u in
                    FStar_Util.format1 "Invalid term in universe context %s"
                      uu____3919 in
                  failwith uu____3918))
    | uu____3920 -> p_atomicUniverse u
and p_atomicUniverse: FStar_Parser_AST.term -> FStar_Pprint.document =
  fun u  ->
    let uu____3922 =
      let uu____3923 = unparen u in uu____3923.FStar_Parser_AST.tm in
    match uu____3922 with
    | FStar_Parser_AST.Wild  -> FStar_Pprint.underscore
    | FStar_Parser_AST.Const (FStar_Const.Const_int (r,sw)) ->
        p_constant (FStar_Const.Const_int (r, sw))
    | FStar_Parser_AST.Uvar uu____3935 -> p_univar u
    | FStar_Parser_AST.Paren u1 ->
        let uu____3937 = p_universeFrom u1 in
        soft_parens_with_nesting uu____3937
    | FStar_Parser_AST.Op
        ({ FStar_Ident.idText = "+"; FStar_Ident.idRange = uu____3938;_},uu____3939::uu____3940::[])
        ->
        let uu____3942 = p_universeFrom u in
        soft_parens_with_nesting uu____3942
    | FStar_Parser_AST.App uu____3943 ->
        let uu____3947 = p_universeFrom u in
        soft_parens_with_nesting uu____3947
    | uu____3948 ->
        let uu____3949 =
          let uu____3950 = FStar_Parser_AST.term_to_string u in
          FStar_Util.format1 "Invalid term in universe context %s" uu____3950 in
        failwith uu____3949
and p_univar: FStar_Parser_AST.term -> FStar_Pprint.document =
  fun u  ->
    let uu____3952 =
      let uu____3953 = unparen u in uu____3953.FStar_Parser_AST.tm in
    match uu____3952 with
    | FStar_Parser_AST.Uvar id -> str (FStar_Ident.text_of_id id)
    | uu____3955 ->
        let uu____3956 =
          let uu____3957 = FStar_Parser_AST.term_to_string u in
          FStar_Util.format1 "Not a universe variable %s" uu____3957 in
        failwith uu____3956
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
       | FStar_Parser_AST.Module (uu____3977,decls) ->
           let uu____3981 =
             FStar_All.pipe_right decls (FStar_List.map decl_to_document) in
           FStar_All.pipe_right uu____3981
             (FStar_Pprint.separate FStar_Pprint.hardline)
       | FStar_Parser_AST.Interface (uu____3986,decls,uu____3988) ->
           let uu____3991 =
             FStar_All.pipe_right decls (FStar_List.map decl_to_document) in
           FStar_All.pipe_right uu____3991
             (FStar_Pprint.separate FStar_Pprint.hardline) in
     FStar_ST.write should_print_fs_typ_app false; res)
let comments_to_document:
  (Prims.string* FStar_Range.range) Prims.list -> FStar_Pprint.document =
  fun comments  ->
    FStar_Pprint.separate_map FStar_Pprint.hardline
      (fun uu____4010  ->
         match uu____4010 with | (comment,range) -> str comment) comments
let modul_with_comments_to_document:
  FStar_Parser_AST.modul ->
    (Prims.string* FStar_Range.range) Prims.list ->
      (FStar_Pprint.document* (Prims.string* FStar_Range.range) Prims.list)
  =
  fun m  ->
    fun comments  ->
      let decls =
        match m with
        | FStar_Parser_AST.Module (uu____4035,decls) -> decls
        | FStar_Parser_AST.Interface (uu____4039,decls,uu____4041) -> decls in
      FStar_ST.write should_print_fs_typ_app false;
      (match decls with
       | [] -> (FStar_Pprint.empty, comments)
       | d::ds ->
           let uu____4058 =
             match ds with
             | {
                 FStar_Parser_AST.d = FStar_Parser_AST.Pragma
                   (FStar_Parser_AST.LightOff );
                 FStar_Parser_AST.drange = uu____4065;
                 FStar_Parser_AST.doc = uu____4066;
                 FStar_Parser_AST.quals = uu____4067;
                 FStar_Parser_AST.attrs = uu____4068;_}::uu____4069 ->
                 let d0 = FStar_List.hd ds in
                 let uu____4073 =
                   let uu____4075 =
                     let uu____4077 = FStar_List.tl ds in d :: uu____4077 in
                   d0 :: uu____4075 in
                 (uu____4073, (d0.FStar_Parser_AST.drange))
             | uu____4080 -> ((d :: ds), (d.FStar_Parser_AST.drange)) in
           (match uu____4058 with
            | (decls1,first_range) ->
                let extract_decl_range d1 = d1.FStar_Parser_AST.drange in
                (FStar_ST.write comment_stack comments;
                 (let initial_comment =
                    let uu____4103 = FStar_Range.start_of_range first_range in
                    place_comments_until_pos (Prims.parse_int "0")
                      (Prims.parse_int "1") uu____4103 FStar_Pprint.empty in
                  let doc1 =
                    separate_map_with_comments FStar_Pprint.empty
                      FStar_Pprint.empty decl_to_document decls1
                      extract_decl_range in
                  let comments1 = FStar_ST.read comment_stack in
                  FStar_ST.write comment_stack [];
                  FStar_ST.write should_print_fs_typ_app false;
                  (let uu____4125 =
                     FStar_Pprint.op_Hat_Hat initial_comment doc1 in
                   (uu____4125, comments1))))))