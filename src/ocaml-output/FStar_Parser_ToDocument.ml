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
  | x when x = (Prims.parse_int "0") -> true
  | x when x = (Prims.parse_int "1") ->
      (is_general_prefix_op op) ||
        (FStar_List.mem (FStar_Ident.text_of_id op) ["-"; "~"])
  | x when x = (Prims.parse_int "2") ->
      ((is_operatorInfix0ad12 op) || (is_operatorInfix34 op)) ||
        (FStar_List.mem (FStar_Ident.text_of_id op)
           ["<==>"; "==>"; "\\/"; "/\\"; "="; "|>"; ":="; ".()"; ".[]"])
  | x when x = (Prims.parse_int "3") ->
      FStar_List.mem (FStar_Ident.text_of_id op) [".()<-"; ".[]<-"]
  | uu____1389 -> false
let comment_stack: (Prims.string* FStar_Range.range) Prims.list FStar_ST.ref
  = FStar_Util.mk_ref []
let with_comment printer tm tmrange =
  let rec comments_before_pos acc print_pos lookahead_pos =
    let uu____1435 = FStar_ST.read comment_stack in
    match uu____1435 with
    | [] -> (acc, false)
    | (comment,crange)::cs ->
        let uu____1456 = FStar_Range.range_before_pos crange print_pos in
        if uu____1456
        then
          (FStar_ST.write comment_stack cs;
           (let uu____1465 =
              let uu____1466 =
                let uu____1467 = str comment in
                FStar_Pprint.op_Hat_Hat uu____1467 FStar_Pprint.hardline in
              FStar_Pprint.op_Hat_Hat acc uu____1466 in
            comments_before_pos uu____1465 print_pos lookahead_pos))
        else
          (let uu____1469 = FStar_Range.range_before_pos crange lookahead_pos in
           (acc, uu____1469)) in
  let uu____1470 =
    let uu____1473 =
      let uu____1474 = FStar_Range.start_of_range tmrange in
      FStar_Range.end_of_line uu____1474 in
    let uu____1475 = FStar_Range.end_of_range tmrange in
    comments_before_pos FStar_Pprint.empty uu____1473 uu____1475 in
  match uu____1470 with
  | (comments,has_lookahead) ->
      let printed_e = printer tm in
      let comments1 =
        if has_lookahead
        then
          let pos = FStar_Range.end_of_range tmrange in
          let uu____1481 = comments_before_pos comments pos pos in
          fst uu____1481
        else comments in
      let uu____1485 = FStar_Pprint.op_Hat_Hat comments1 printed_e in
      FStar_Pprint.group uu____1485
let rec place_comments_until_pos:
  Prims.int ->
    Prims.int ->
      FStar_Range.pos -> FStar_Pprint.document -> FStar_Pprint.document
  =
  fun k  ->
    fun lbegin  ->
      fun pos_end  ->
        fun doc1  ->
          let uu____1498 = FStar_ST.read comment_stack in
          match uu____1498 with
          | (comment,crange)::cs when
              FStar_Range.range_before_pos crange pos_end ->
              (FStar_ST.write comment_stack cs;
               (let lnum =
                  let uu____1522 =
                    let uu____1523 =
                      let uu____1524 = FStar_Range.start_of_range crange in
                      FStar_Range.line_of_pos uu____1524 in
                    uu____1523 - lbegin in
                  max k uu____1522 in
                let doc2 =
                  let uu____1526 =
                    let uu____1527 =
                      FStar_Pprint.repeat lnum FStar_Pprint.hardline in
                    let uu____1528 = str comment in
                    FStar_Pprint.op_Hat_Hat uu____1527 uu____1528 in
                  FStar_Pprint.op_Hat_Hat doc1 uu____1526 in
                let uu____1529 =
                  let uu____1530 = FStar_Range.end_of_range crange in
                  FStar_Range.line_of_pos uu____1530 in
                place_comments_until_pos (Prims.parse_int "1") uu____1529
                  pos_end doc2))
          | uu____1531 ->
              let lnum =
                let uu____1536 =
                  let uu____1537 = FStar_Range.line_of_pos pos_end in
                  uu____1537 - lbegin in
                max (Prims.parse_int "1") uu____1536 in
              let uu____1538 = FStar_Pprint.repeat lnum FStar_Pprint.hardline in
              FStar_Pprint.op_Hat_Hat doc1 uu____1538
let separate_map_with_comments prefix1 sep f xs extract_range =
  let fold_fun uu____1587 x =
    match uu____1587 with
    | (last_line,doc1) ->
        let r = extract_range x in
        let doc2 =
          let uu____1597 = FStar_Range.start_of_range r in
          place_comments_until_pos (Prims.parse_int "1") last_line uu____1597
            doc1 in
        let uu____1598 =
          let uu____1599 = FStar_Range.end_of_range r in
          FStar_Range.line_of_pos uu____1599 in
        let uu____1600 =
          let uu____1601 =
            let uu____1602 = f x in FStar_Pprint.op_Hat_Hat sep uu____1602 in
          FStar_Pprint.op_Hat_Hat doc2 uu____1601 in
        (uu____1598, uu____1600) in
  let uu____1603 =
    let uu____1607 = FStar_List.hd xs in
    let uu____1608 = FStar_List.tl xs in (uu____1607, uu____1608) in
  match uu____1603 with
  | (x,xs1) ->
      let init1 =
        let uu____1618 =
          let uu____1619 =
            let uu____1620 = extract_range x in
            FStar_Range.end_of_range uu____1620 in
          FStar_Range.line_of_pos uu____1619 in
        let uu____1621 =
          let uu____1622 = f x in FStar_Pprint.op_Hat_Hat prefix1 uu____1622 in
        (uu____1618, uu____1621) in
      let uu____1623 = FStar_List.fold_left fold_fun init1 xs1 in
      snd uu____1623
let rec p_decl: FStar_Parser_AST.decl -> FStar_Pprint.document =
  fun d  ->
    let uu____1869 =
      let uu____1870 = FStar_Pprint.optional p_fsdoc d.FStar_Parser_AST.doc in
      let uu____1871 =
        let uu____1872 = p_attributes d.FStar_Parser_AST.attrs in
        let uu____1873 =
          let uu____1874 = p_qualifiers d.FStar_Parser_AST.quals in
          let uu____1875 =
            let uu____1876 = p_rawDecl d in
            FStar_Pprint.op_Hat_Hat
              (if d.FStar_Parser_AST.quals = []
               then FStar_Pprint.empty
               else break1) uu____1876 in
          FStar_Pprint.op_Hat_Hat uu____1874 uu____1875 in
        FStar_Pprint.op_Hat_Hat uu____1872 uu____1873 in
      FStar_Pprint.op_Hat_Hat uu____1870 uu____1871 in
    FStar_Pprint.group uu____1869
and p_attributes: FStar_Parser_AST.attributes_ -> FStar_Pprint.document =
  fun attrs  ->
    let uu____1879 =
      let uu____1880 = str "@" in
      FStar_Pprint.op_Hat_Hat FStar_Pprint.lbracket uu____1880 in
    let uu____1881 =
      FStar_Pprint.op_Hat_Hat FStar_Pprint.rbracket FStar_Pprint.hardline in
    soft_surround_separate_map (Prims.parse_int "0") (Prims.parse_int "2")
      FStar_Pprint.empty uu____1879 FStar_Pprint.space uu____1881
      p_atomicTerm attrs
and p_fsdoc: FStar_Parser_AST.fsdoc -> FStar_Pprint.document =
  fun uu____1882  ->
    match uu____1882 with
    | (doc1,kwd_args) ->
        let kwd_args_doc =
          match kwd_args with
          | [] -> FStar_Pprint.empty
          | kwd_args1 ->
              let process_kwd_arg uu____1903 =
                match uu____1903 with
                | (kwd1,arg) ->
                    let uu____1908 = str "@" in
                    let uu____1909 =
                      let uu____1910 = str kwd1 in
                      let uu____1911 =
                        let uu____1912 = str arg in
                        FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____1912 in
                      FStar_Pprint.op_Hat_Hat uu____1910 uu____1911 in
                    FStar_Pprint.op_Hat_Hat uu____1908 uu____1909 in
              let uu____1913 =
                let uu____1914 =
                  FStar_Pprint.separate_map FStar_Pprint.hardline
                    process_kwd_arg kwd_args1 in
                FStar_Pprint.op_Hat_Hat uu____1914 FStar_Pprint.hardline in
              FStar_Pprint.op_Hat_Hat FStar_Pprint.hardline uu____1913 in
        let uu____1917 =
          let uu____1918 =
            let uu____1919 =
              let uu____1920 =
                let uu____1921 = str doc1 in
                let uu____1922 =
                  let uu____1923 =
                    let uu____1924 =
                      FStar_Pprint.op_Hat_Hat FStar_Pprint.rparen
                        FStar_Pprint.hardline in
                    FStar_Pprint.op_Hat_Hat FStar_Pprint.star uu____1924 in
                  FStar_Pprint.op_Hat_Hat kwd_args_doc uu____1923 in
                FStar_Pprint.op_Hat_Hat uu____1921 uu____1922 in
              FStar_Pprint.op_Hat_Hat FStar_Pprint.star uu____1920 in
            FStar_Pprint.op_Hat_Hat FStar_Pprint.star uu____1919 in
          FStar_Pprint.op_Hat_Hat FStar_Pprint.lparen uu____1918 in
        FStar_Pprint.op_Hat_Hat FStar_Pprint.hardline uu____1917
and p_rawDecl: FStar_Parser_AST.decl -> FStar_Pprint.document =
  fun d  ->
    match d.FStar_Parser_AST.d with
    | FStar_Parser_AST.Open uid ->
        let uu____1927 =
          let uu____1928 = str "open" in
          let uu____1929 = p_quident uid in
          FStar_Pprint.op_Hat_Slash_Hat uu____1928 uu____1929 in
        FStar_Pprint.group uu____1927
    | FStar_Parser_AST.Include uid ->
        let uu____1931 =
          let uu____1932 = str "include" in
          let uu____1933 = p_quident uid in
          FStar_Pprint.op_Hat_Slash_Hat uu____1932 uu____1933 in
        FStar_Pprint.group uu____1931
    | FStar_Parser_AST.ModuleAbbrev (uid1,uid2) ->
        let uu____1936 =
          let uu____1937 = str "module" in
          let uu____1938 =
            let uu____1939 =
              let uu____1940 = p_uident uid1 in
              let uu____1941 =
                FStar_Pprint.op_Hat_Hat FStar_Pprint.space
                  FStar_Pprint.equals in
              FStar_Pprint.op_Hat_Hat uu____1940 uu____1941 in
            FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____1939 in
          FStar_Pprint.op_Hat_Hat uu____1937 uu____1938 in
        let uu____1942 = p_quident uid2 in
        op_Hat_Slash_Plus_Hat uu____1936 uu____1942
    | FStar_Parser_AST.TopLevelModule uid ->
        let uu____1944 =
          let uu____1945 = str "module" in
          let uu____1946 =
            let uu____1947 = p_quident uid in
            FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____1947 in
          FStar_Pprint.op_Hat_Hat uu____1945 uu____1946 in
        FStar_Pprint.group uu____1944
    | FStar_Parser_AST.Tycon
        (true ,(FStar_Parser_AST.TyconAbbrev (uid,tpars,None ,t),None )::[])
        ->
        let effect_prefix_doc =
          let uu____1966 = str "effect" in
          let uu____1967 =
            let uu____1968 = p_uident uid in
            FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____1968 in
          FStar_Pprint.op_Hat_Hat uu____1966 uu____1967 in
        let uu____1969 =
          let uu____1970 = p_typars tpars in
          FStar_Pprint.surround (Prims.parse_int "2") (Prims.parse_int "1")
            effect_prefix_doc uu____1970 FStar_Pprint.equals in
        let uu____1971 = p_typ t in
        op_Hat_Slash_Plus_Hat uu____1969 uu____1971
    | FStar_Parser_AST.Tycon (false ,tcdefs) ->
        let uu____1981 = str "type" in
        let uu____1982 = str "and" in
        precede_break_separate_map uu____1981 uu____1982 p_fsdocTypeDeclPairs
          tcdefs
    | FStar_Parser_AST.TopLevelLet (q,lbs) ->
        let let_doc =
          let uu____1995 = str "let" in
          let uu____1996 =
            let uu____1997 = p_letqualifier q in
            FStar_Pprint.op_Hat_Hat uu____1997 FStar_Pprint.space in
          FStar_Pprint.op_Hat_Hat uu____1995 uu____1996 in
        let uu____1998 =
          let uu____1999 = str "and" in
          FStar_Pprint.op_Hat_Hat uu____1999 FStar_Pprint.space in
        separate_map_with_comments let_doc uu____1998 p_letbinding lbs
          (fun uu____2002  ->
             match uu____2002 with
             | (p,t) ->
                 FStar_Range.union_ranges p.FStar_Parser_AST.prange
                   t.FStar_Parser_AST.range)
    | FStar_Parser_AST.Val (lid,t) ->
        let uu____2009 =
          let uu____2010 = str "val" in
          let uu____2011 =
            let uu____2012 =
              let uu____2013 = p_lident lid in
              let uu____2014 =
                FStar_Pprint.op_Hat_Hat FStar_Pprint.space FStar_Pprint.colon in
              FStar_Pprint.op_Hat_Hat uu____2013 uu____2014 in
            FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____2012 in
          FStar_Pprint.op_Hat_Hat uu____2010 uu____2011 in
        let uu____2015 = p_typ t in
        op_Hat_Slash_Plus_Hat uu____2009 uu____2015
    | FStar_Parser_AST.Assume (id,t) ->
        let decl_keyword =
          let uu____2019 =
            let uu____2020 =
              FStar_Util.char_at id.FStar_Ident.idText (Prims.parse_int "0") in
            FStar_All.pipe_right uu____2020 FStar_Util.is_upper in
          if uu____2019
          then FStar_Pprint.empty
          else
            (let uu____2022 = str "val" in
             FStar_Pprint.op_Hat_Hat uu____2022 FStar_Pprint.space) in
        let uu____2023 =
          let uu____2024 =
            let uu____2025 = p_ident id in
            let uu____2026 =
              FStar_Pprint.op_Hat_Hat FStar_Pprint.space FStar_Pprint.colon in
            FStar_Pprint.op_Hat_Hat uu____2025 uu____2026 in
          FStar_Pprint.op_Hat_Hat decl_keyword uu____2024 in
        let uu____2027 = p_typ t in
        op_Hat_Slash_Plus_Hat uu____2023 uu____2027
    | FStar_Parser_AST.Exception (uid,t_opt) ->
        let uu____2032 = str "exception" in
        let uu____2033 =
          let uu____2034 =
            let uu____2035 = p_uident uid in
            let uu____2036 =
              FStar_Pprint.optional
                (fun t  ->
                   let uu____2038 = str "of" in
                   let uu____2039 = p_typ t in
                   op_Hat_Slash_Plus_Hat uu____2038 uu____2039) t_opt in
            FStar_Pprint.op_Hat_Hat uu____2035 uu____2036 in
          FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____2034 in
        FStar_Pprint.op_Hat_Hat uu____2032 uu____2033
    | FStar_Parser_AST.NewEffect ne ->
        let uu____2041 = str "new_effect" in
        let uu____2042 =
          let uu____2043 = p_newEffect ne in
          FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____2043 in
        FStar_Pprint.op_Hat_Hat uu____2041 uu____2042
    | FStar_Parser_AST.SubEffect se ->
        let uu____2045 = str "sub_effect" in
        let uu____2046 =
          let uu____2047 = p_subEffect se in
          FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____2047 in
        FStar_Pprint.op_Hat_Hat uu____2045 uu____2046
    | FStar_Parser_AST.Pragma p -> p_pragma p
    | FStar_Parser_AST.Fsdoc doc1 ->
        let uu____2050 = p_fsdoc doc1 in
        FStar_Pprint.op_Hat_Hat uu____2050 FStar_Pprint.hardline
    | FStar_Parser_AST.Main uu____2051 ->
        failwith "*Main declaration* : Is that really still in use ??"
    | FStar_Parser_AST.Tycon (true ,uu____2052) ->
        failwith
          "Effect abbreviation is expected to be defined by an abbreviation"
and p_pragma: FStar_Parser_AST.pragma -> FStar_Pprint.document =
  fun uu___98_2061  ->
    match uu___98_2061 with
    | FStar_Parser_AST.SetOptions s ->
        let uu____2063 = str "#set-options" in
        let uu____2064 =
          let uu____2065 =
            let uu____2066 = str s in FStar_Pprint.dquotes uu____2066 in
          FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____2065 in
        FStar_Pprint.op_Hat_Hat uu____2063 uu____2064
    | FStar_Parser_AST.ResetOptions s_opt ->
        let uu____2069 = str "#reset-options" in
        let uu____2070 =
          FStar_Pprint.optional
            (fun s  ->
               let uu____2072 =
                 let uu____2073 = str s in FStar_Pprint.dquotes uu____2073 in
               FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____2072) s_opt in
        FStar_Pprint.op_Hat_Hat uu____2069 uu____2070
    | FStar_Parser_AST.LightOff  ->
        (FStar_ST.write should_print_fs_typ_app true; str "#light \"off\"")
and p_typars: FStar_Parser_AST.binder Prims.list -> FStar_Pprint.document =
  fun bs  -> p_binders true bs
and p_fsdocTypeDeclPairs:
  (FStar_Parser_AST.tycon* FStar_Parser_AST.fsdoc option) ->
    FStar_Pprint.document
  =
  fun uu____2079  ->
    match uu____2079 with
    | (typedecl,fsdoc_opt) ->
        let uu____2087 = FStar_Pprint.optional p_fsdoc fsdoc_opt in
        let uu____2088 = p_typeDecl typedecl in
        FStar_Pprint.op_Hat_Hat uu____2087 uu____2088
and p_typeDecl: FStar_Parser_AST.tycon -> FStar_Pprint.document =
  fun uu___99_2089  ->
    match uu___99_2089 with
    | FStar_Parser_AST.TyconAbstract (lid,bs,typ_opt) ->
        let empty' uu____2100 = FStar_Pprint.empty in
        p_typeDeclPrefix lid bs typ_opt empty'
    | FStar_Parser_AST.TyconAbbrev (lid,bs,typ_opt,t) ->
        let f uu____2112 =
          let uu____2113 = p_typ t in prefix2 FStar_Pprint.equals uu____2113 in
        p_typeDeclPrefix lid bs typ_opt f
    | FStar_Parser_AST.TyconRecord (lid,bs,typ_opt,record_field_decls) ->
        let p_recordFieldAndComments uu____2139 =
          match uu____2139 with
          | (lid1,t,doc_opt) ->
              let uu____2149 =
                FStar_Range.extend_to_end_of_line t.FStar_Parser_AST.range in
              with_comment p_recordFieldDecl (lid1, t, doc_opt) uu____2149 in
        let p_fields uu____2158 =
          let uu____2159 =
            let uu____2160 =
              let uu____2161 =
                let uu____2162 =
                  FStar_Pprint.op_Hat_Hat FStar_Pprint.semi break1 in
                FStar_Pprint.separate_map uu____2162 p_recordFieldAndComments
                  record_field_decls in
              braces_with_nesting uu____2161 in
            FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____2160 in
          FStar_Pprint.op_Hat_Hat FStar_Pprint.equals uu____2159 in
        p_typeDeclPrefix lid bs typ_opt p_fields
    | FStar_Parser_AST.TyconVariant (lid,bs,typ_opt,ct_decls) ->
        let p_constructorBranchAndComments uu____2198 =
          match uu____2198 with
          | (uid,t_opt,doc_opt,use_of) ->
              let range =
                let uu____2214 =
                  let uu____2215 =
                    FStar_Util.map_opt t_opt
                      (fun t  -> t.FStar_Parser_AST.range) in
                  FStar_Util.dflt uid.FStar_Ident.idRange uu____2215 in
                FStar_Range.extend_to_end_of_line uu____2214 in
              let p_constructorBranch decl =
                let uu____2234 =
                  let uu____2235 =
                    let uu____2236 = p_constructorDecl decl in
                    FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____2236 in
                  FStar_Pprint.op_Hat_Hat FStar_Pprint.bar uu____2235 in
                FStar_Pprint.group uu____2234 in
              with_comment p_constructorBranch (uid, t_opt, doc_opt, use_of)
                range in
        let datacon_doc uu____2248 =
          let uu____2249 =
            FStar_Pprint.separate_map break1 p_constructorBranchAndComments
              ct_decls in
          FStar_Pprint.group uu____2249 in
        p_typeDeclPrefix lid bs typ_opt
          (fun uu____2256  ->
             let uu____2257 = datacon_doc () in
             prefix2 FStar_Pprint.equals uu____2257)
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
            let uu____2268 = p_ident lid in
            let uu____2269 =
              let uu____2270 = cont () in
              FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____2270 in
            FStar_Pprint.op_Hat_Hat uu____2268 uu____2269
          else
            (let binders_doc =
               let uu____2273 = p_typars bs in
               let uu____2274 =
                 FStar_Pprint.optional
                   (fun t  ->
                      let uu____2276 =
                        let uu____2277 =
                          let uu____2278 = p_typ t in
                          FStar_Pprint.op_Hat_Hat FStar_Pprint.space
                            uu____2278 in
                        FStar_Pprint.op_Hat_Hat FStar_Pprint.colon uu____2277 in
                      FStar_Pprint.op_Hat_Hat break1 uu____2276) typ_opt in
               FStar_Pprint.op_Hat_Hat uu____2273 uu____2274 in
             let uu____2279 = p_ident lid in
             let uu____2280 = cont () in
             FStar_Pprint.surround (Prims.parse_int "2")
               (Prims.parse_int "1") uu____2279 binders_doc uu____2280)
and p_recordFieldDecl:
  (FStar_Ident.ident* FStar_Parser_AST.term* FStar_Parser_AST.fsdoc option)
    -> FStar_Pprint.document
  =
  fun uu____2281  ->
    match uu____2281 with
    | (lid,t,doc_opt) ->
        let uu____2291 =
          let uu____2292 = FStar_Pprint.optional p_fsdoc doc_opt in
          let uu____2293 =
            let uu____2294 = p_lident lid in
            let uu____2295 =
              let uu____2296 = p_typ t in
              FStar_Pprint.op_Hat_Hat FStar_Pprint.colon uu____2296 in
            FStar_Pprint.op_Hat_Hat uu____2294 uu____2295 in
          FStar_Pprint.op_Hat_Hat uu____2292 uu____2293 in
        FStar_Pprint.group uu____2291
and p_constructorDecl:
  (FStar_Ident.ident* FStar_Parser_AST.term option* FStar_Parser_AST.fsdoc
    option* Prims.bool) -> FStar_Pprint.document
  =
  fun uu____2297  ->
    match uu____2297 with
    | (uid,t_opt,doc_opt,use_of) ->
        let sep = if use_of then str "of" else FStar_Pprint.colon in
        let uid_doc = p_uident uid in
        let uu____2315 = FStar_Pprint.optional p_fsdoc doc_opt in
        let uu____2316 =
          let uu____2317 = FStar_Pprint.break_ (Prims.parse_int "0") in
          let uu____2318 =
            default_or_map uid_doc
              (fun t  ->
                 let uu____2320 =
                   let uu____2321 =
                     FStar_Pprint.op_Hat_Hat FStar_Pprint.space sep in
                   FStar_Pprint.op_Hat_Hat uid_doc uu____2321 in
                 let uu____2322 = p_typ t in
                 op_Hat_Slash_Plus_Hat uu____2320 uu____2322) t_opt in
          FStar_Pprint.op_Hat_Hat uu____2317 uu____2318 in
        FStar_Pprint.op_Hat_Hat uu____2315 uu____2316
and p_letbinding:
  (FStar_Parser_AST.pattern* FStar_Parser_AST.term) -> FStar_Pprint.document
  =
  fun uu____2323  ->
    match uu____2323 with
    | (pat,e) ->
        let pat_doc =
          let uu____2329 =
            match pat.FStar_Parser_AST.pat with
            | FStar_Parser_AST.PatAscribed (pat1,t) ->
                let uu____2336 =
                  let uu____2337 =
                    let uu____2338 =
                      let uu____2339 =
                        let uu____2340 = p_tmArrow p_tmNoEq t in
                        FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____2340 in
                      FStar_Pprint.op_Hat_Hat FStar_Pprint.colon uu____2339 in
                    FStar_Pprint.group uu____2338 in
                  FStar_Pprint.op_Hat_Hat break1 uu____2337 in
                (pat1, uu____2336)
            | uu____2341 -> (pat, FStar_Pprint.empty) in
          match uu____2329 with
          | (pat1,ascr_doc) ->
              (match pat1.FStar_Parser_AST.pat with
               | FStar_Parser_AST.PatApp
                   ({
                      FStar_Parser_AST.pat = FStar_Parser_AST.PatVar
                        (x,uu____2345);
                      FStar_Parser_AST.prange = uu____2346;_},pats)
                   ->
                   let uu____2352 = p_lident x in
                   let uu____2353 =
                     let uu____2354 =
                       FStar_Pprint.separate_map break1 p_atomicPattern pats in
                     FStar_Pprint.op_Hat_Hat uu____2354 ascr_doc in
                   FStar_Pprint.surround (Prims.parse_int "2")
                     (Prims.parse_int "1") uu____2352 uu____2353
                     FStar_Pprint.equals
               | uu____2355 ->
                   let uu____2356 =
                     let uu____2357 = p_tuplePattern pat1 in
                     let uu____2358 =
                       FStar_Pprint.op_Hat_Slash_Hat ascr_doc
                         FStar_Pprint.equals in
                     FStar_Pprint.op_Hat_Hat uu____2357 uu____2358 in
                   FStar_Pprint.group uu____2356) in
        let uu____2359 = p_term e in prefix2 pat_doc uu____2359
and p_newEffect: FStar_Parser_AST.effect_decl -> FStar_Pprint.document =
  fun uu___100_2360  ->
    match uu___100_2360 with
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
        let uu____2378 = p_uident uid in
        let uu____2379 = p_binders true bs in
        let uu____2380 =
          let uu____2381 = p_simpleTerm t in
          prefix2 FStar_Pprint.equals uu____2381 in
        FStar_Pprint.surround (Prims.parse_int "2") (Prims.parse_int "1")
          uu____2378 uu____2379 uu____2380
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
          let uu____2388 =
            let uu____2389 =
              let uu____2390 =
                let uu____2391 = p_uident uid in
                let uu____2392 = p_binders true bs in
                let uu____2393 =
                  let uu____2394 = p_typ t in
                  prefix2 FStar_Pprint.colon uu____2394 in
                FStar_Pprint.surround (Prims.parse_int "2")
                  (Prims.parse_int "1") uu____2391 uu____2392 uu____2393 in
              FStar_Pprint.group uu____2390 in
            let uu____2395 =
              let uu____2396 = str "with" in
              let uu____2397 =
                separate_break_map FStar_Pprint.semi p_effectDecl eff_decls in
              prefix2 uu____2396 uu____2397 in
            FStar_Pprint.op_Hat_Slash_Hat uu____2389 uu____2395 in
          braces_with_nesting uu____2388
and p_effectDecl: FStar_Parser_AST.decl -> FStar_Pprint.document =
  fun d  ->
    match d.FStar_Parser_AST.d with
    | FStar_Parser_AST.Tycon
        (false ,(FStar_Parser_AST.TyconAbbrev (lid,[],None ,e),None )::[]) ->
        let uu____2414 =
          let uu____2415 = p_lident lid in
          let uu____2416 =
            FStar_Pprint.op_Hat_Hat FStar_Pprint.space FStar_Pprint.equals in
          FStar_Pprint.op_Hat_Hat uu____2415 uu____2416 in
        let uu____2417 = p_simpleTerm e in prefix2 uu____2414 uu____2417
    | uu____2418 ->
        let uu____2419 =
          let uu____2420 = FStar_Parser_AST.decl_to_string d in
          FStar_Util.format1
            "Not a declaration of an effect member... or at least I hope so : %s"
            uu____2420 in
        failwith uu____2419
and p_subEffect: FStar_Parser_AST.lift -> FStar_Pprint.document =
  fun lift  ->
    let lift_op_doc =
      let lifts =
        match lift.FStar_Parser_AST.lift_op with
        | FStar_Parser_AST.NonReifiableLift t -> [("lift_wp", t)]
        | FStar_Parser_AST.ReifiableLift (t1,t2) ->
            [("lif_wp", t1); ("lift", t2)]
        | FStar_Parser_AST.LiftForFree t -> [("lift", t)] in
      let p_lift uu____2453 =
        match uu____2453 with
        | (kwd1,t) ->
            let uu____2458 =
              let uu____2459 = str kwd1 in
              let uu____2460 =
                FStar_Pprint.op_Hat_Hat FStar_Pprint.space
                  FStar_Pprint.equals in
              FStar_Pprint.op_Hat_Hat uu____2459 uu____2460 in
            let uu____2461 = p_simpleTerm t in prefix2 uu____2458 uu____2461 in
      separate_break_map FStar_Pprint.semi p_lift lifts in
    let uu____2464 =
      let uu____2465 =
        let uu____2466 = p_quident lift.FStar_Parser_AST.msource in
        let uu____2467 =
          let uu____2468 = str "~>" in
          FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____2468 in
        FStar_Pprint.op_Hat_Hat uu____2466 uu____2467 in
      let uu____2469 = p_quident lift.FStar_Parser_AST.mdest in
      prefix2 uu____2465 uu____2469 in
    let uu____2470 =
      let uu____2471 = braces_with_nesting lift_op_doc in
      FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____2471 in
    FStar_Pprint.op_Hat_Hat uu____2464 uu____2470
and p_qualifier: FStar_Parser_AST.qualifier -> FStar_Pprint.document =
  fun uu___101_2472  ->
    match uu___101_2472 with
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
    let uu____2474 = FStar_Pprint.separate_map break1 p_qualifier qs in
    FStar_Pprint.group uu____2474
and p_letqualifier: FStar_Parser_AST.let_qualifier -> FStar_Pprint.document =
  fun uu___102_2475  ->
    match uu___102_2475 with
    | FStar_Parser_AST.Rec  ->
        let uu____2476 = str "rec" in
        FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____2476
    | FStar_Parser_AST.Mutable  ->
        let uu____2477 = str "mutable" in
        FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____2477
    | FStar_Parser_AST.NoLetQualifier  -> FStar_Pprint.empty
and p_aqual: FStar_Parser_AST.arg_qualifier -> FStar_Pprint.document =
  fun uu___103_2478  ->
    match uu___103_2478 with
    | FStar_Parser_AST.Implicit  -> str "#"
    | FStar_Parser_AST.Equality  -> str "$"
and p_disjunctivePattern: FStar_Parser_AST.pattern -> FStar_Pprint.document =
  fun p  ->
    match p.FStar_Parser_AST.pat with
    | FStar_Parser_AST.PatOr pats ->
        let uu____2482 =
          let uu____2483 =
            let uu____2484 =
              FStar_Pprint.op_Hat_Hat FStar_Pprint.bar FStar_Pprint.space in
            FStar_Pprint.op_Hat_Hat break1 uu____2484 in
          FStar_Pprint.separate_map uu____2483 p_tuplePattern pats in
        FStar_Pprint.group uu____2482
    | uu____2485 -> p_tuplePattern p
and p_tuplePattern: FStar_Parser_AST.pattern -> FStar_Pprint.document =
  fun p  ->
    match p.FStar_Parser_AST.pat with
    | FStar_Parser_AST.PatTuple (pats,false ) ->
        let uu____2490 =
          let uu____2491 = FStar_Pprint.op_Hat_Hat FStar_Pprint.comma break1 in
          FStar_Pprint.separate_map uu____2491 p_constructorPattern pats in
        FStar_Pprint.group uu____2490
    | uu____2492 -> p_constructorPattern p
and p_constructorPattern: FStar_Parser_AST.pattern -> FStar_Pprint.document =
  fun p  ->
    match p.FStar_Parser_AST.pat with
    | FStar_Parser_AST.PatApp
        ({ FStar_Parser_AST.pat = FStar_Parser_AST.PatName maybe_cons_lid;
           FStar_Parser_AST.prange = uu____2495;_},hd1::tl1::[])
        when
        FStar_Ident.lid_equals maybe_cons_lid FStar_Parser_Const.cons_lid ->
        let uu____2499 =
          FStar_Pprint.op_Hat_Hat FStar_Pprint.colon FStar_Pprint.colon in
        let uu____2500 = p_constructorPattern hd1 in
        let uu____2501 = p_constructorPattern tl1 in
        infix0 uu____2499 uu____2500 uu____2501
    | FStar_Parser_AST.PatApp
        ({ FStar_Parser_AST.pat = FStar_Parser_AST.PatName uid;
           FStar_Parser_AST.prange = uu____2503;_},pats)
        ->
        let uu____2507 = p_quident uid in
        let uu____2508 =
          FStar_Pprint.separate_map break1 p_atomicPattern pats in
        prefix2 uu____2507 uu____2508
    | uu____2509 -> p_atomicPattern p
and p_atomicPattern: FStar_Parser_AST.pattern -> FStar_Pprint.document =
  fun p  ->
    match p.FStar_Parser_AST.pat with
    | FStar_Parser_AST.PatAscribed (pat,t) ->
        let uu____2513 =
          let uu____2516 =
            let uu____2517 = unparen t in uu____2517.FStar_Parser_AST.tm in
          ((pat.FStar_Parser_AST.pat), uu____2516) in
        (match uu____2513 with
         | (FStar_Parser_AST.PatVar (lid,aqual),FStar_Parser_AST.Refine
            ({ FStar_Parser_AST.b = FStar_Parser_AST.Annotated (lid',t1);
               FStar_Parser_AST.brange = uu____2522;
               FStar_Parser_AST.blevel = uu____2523;
               FStar_Parser_AST.aqual = uu____2524;_},phi))
             when lid.FStar_Ident.idText = lid'.FStar_Ident.idText ->
             let uu____2528 =
               let uu____2529 = p_ident lid in
               p_refinement aqual uu____2529 t1 phi in
             soft_parens_with_nesting uu____2528
         | (FStar_Parser_AST.PatWild ,FStar_Parser_AST.Refine
            ({ FStar_Parser_AST.b = FStar_Parser_AST.NoName t1;
               FStar_Parser_AST.brange = uu____2531;
               FStar_Parser_AST.blevel = uu____2532;
               FStar_Parser_AST.aqual = uu____2533;_},phi))
             ->
             let uu____2535 =
               p_refinement None FStar_Pprint.underscore t1 phi in
             soft_parens_with_nesting uu____2535
         | uu____2536 ->
             let uu____2539 =
               let uu____2540 = p_tuplePattern pat in
               let uu____2541 =
                 let uu____2542 = FStar_Pprint.break_ (Prims.parse_int "0") in
                 let uu____2543 =
                   let uu____2544 = p_typ t in
                   FStar_Pprint.op_Hat_Hat FStar_Pprint.colon uu____2544 in
                 FStar_Pprint.op_Hat_Hat uu____2542 uu____2543 in
               FStar_Pprint.op_Hat_Hat uu____2540 uu____2541 in
             soft_parens_with_nesting uu____2539)
    | FStar_Parser_AST.PatList pats ->
        let uu____2547 =
          separate_break_map FStar_Pprint.semi p_tuplePattern pats in
        FStar_Pprint.surround (Prims.parse_int "2") (Prims.parse_int "0")
          FStar_Pprint.lbracket uu____2547 FStar_Pprint.rbracket
    | FStar_Parser_AST.PatRecord pats ->
        let p_recordFieldPat uu____2557 =
          match uu____2557 with
          | (lid,pat) ->
              let uu____2562 = p_qlident lid in
              let uu____2563 = p_tuplePattern pat in
              infix2 FStar_Pprint.equals uu____2562 uu____2563 in
        let uu____2564 =
          separate_break_map FStar_Pprint.semi p_recordFieldPat pats in
        soft_braces_with_nesting uu____2564
    | FStar_Parser_AST.PatTuple (pats,true ) ->
        let uu____2570 =
          FStar_Pprint.op_Hat_Hat FStar_Pprint.lparen FStar_Pprint.bar in
        let uu____2571 =
          separate_break_map FStar_Pprint.comma p_constructorPattern pats in
        let uu____2572 =
          FStar_Pprint.op_Hat_Hat FStar_Pprint.bar FStar_Pprint.rparen in
        FStar_Pprint.surround (Prims.parse_int "2") (Prims.parse_int "1")
          uu____2570 uu____2571 uu____2572
    | FStar_Parser_AST.PatTvar (tv,arg_qualifier_opt) -> p_tvar tv
    | FStar_Parser_AST.PatOp op ->
        let uu____2579 =
          let uu____2580 =
            let uu____2581 = str (FStar_Ident.text_of_id op) in
            let uu____2582 =
              FStar_Pprint.op_Hat_Hat FStar_Pprint.space FStar_Pprint.rparen in
            FStar_Pprint.op_Hat_Hat uu____2581 uu____2582 in
          FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____2580 in
        FStar_Pprint.op_Hat_Hat FStar_Pprint.lparen uu____2579
    | FStar_Parser_AST.PatWild  -> FStar_Pprint.underscore
    | FStar_Parser_AST.PatConst c -> p_constant c
    | FStar_Parser_AST.PatVar (lid,aqual) ->
        let uu____2588 = FStar_Pprint.optional p_aqual aqual in
        let uu____2589 = p_lident lid in
        FStar_Pprint.op_Hat_Hat uu____2588 uu____2589
    | FStar_Parser_AST.PatName uid -> p_quident uid
    | FStar_Parser_AST.PatOr uu____2591 -> failwith "Inner or pattern !"
    | FStar_Parser_AST.PatApp
        ({ FStar_Parser_AST.pat = FStar_Parser_AST.PatName uu____2593;
           FStar_Parser_AST.prange = uu____2594;_},uu____2595)
        ->
        let uu____2598 = p_tuplePattern p in
        soft_parens_with_nesting uu____2598
    | FStar_Parser_AST.PatTuple (uu____2599,false ) ->
        let uu____2602 = p_tuplePattern p in
        soft_parens_with_nesting uu____2602
    | uu____2603 ->
        let uu____2604 =
          let uu____2605 = FStar_Parser_AST.pat_to_string p in
          FStar_Util.format1 "Invalid pattern %s" uu____2605 in
        failwith uu____2604
and p_binder: Prims.bool -> FStar_Parser_AST.binder -> FStar_Pprint.document
  =
  fun is_atomic  ->
    fun b  ->
      match b.FStar_Parser_AST.b with
      | FStar_Parser_AST.Variable lid ->
          let uu____2609 =
            FStar_Pprint.optional p_aqual b.FStar_Parser_AST.aqual in
          let uu____2610 = p_lident lid in
          FStar_Pprint.op_Hat_Hat uu____2609 uu____2610
      | FStar_Parser_AST.TVariable lid -> p_lident lid
      | FStar_Parser_AST.Annotated (lid,t) ->
          let doc1 =
            let uu____2615 =
              let uu____2616 = unparen t in uu____2616.FStar_Parser_AST.tm in
            match uu____2615 with
            | FStar_Parser_AST.Refine
                ({ FStar_Parser_AST.b = FStar_Parser_AST.Annotated (lid',t1);
                   FStar_Parser_AST.brange = uu____2619;
                   FStar_Parser_AST.blevel = uu____2620;
                   FStar_Parser_AST.aqual = uu____2621;_},phi)
                when lid.FStar_Ident.idText = lid'.FStar_Ident.idText ->
                let uu____2623 = p_ident lid in
                p_refinement b.FStar_Parser_AST.aqual uu____2623 t1 phi
            | uu____2624 ->
                let uu____2625 =
                  FStar_Pprint.optional p_aqual b.FStar_Parser_AST.aqual in
                let uu____2626 =
                  let uu____2627 = p_lident lid in
                  let uu____2628 =
                    let uu____2629 =
                      let uu____2630 =
                        FStar_Pprint.break_ (Prims.parse_int "0") in
                      let uu____2631 = p_tmFormula t in
                      FStar_Pprint.op_Hat_Hat uu____2630 uu____2631 in
                    FStar_Pprint.op_Hat_Hat FStar_Pprint.colon uu____2629 in
                  FStar_Pprint.op_Hat_Hat uu____2627 uu____2628 in
                FStar_Pprint.op_Hat_Hat uu____2625 uu____2626 in
          if is_atomic
          then
            let uu____2632 =
              let uu____2633 =
                FStar_Pprint.op_Hat_Hat doc1 FStar_Pprint.rparen in
              FStar_Pprint.op_Hat_Hat FStar_Pprint.lparen uu____2633 in
            FStar_Pprint.group uu____2632
          else FStar_Pprint.group doc1
      | FStar_Parser_AST.TAnnotated uu____2635 ->
          failwith "Is this still used ?"
      | FStar_Parser_AST.NoName t ->
          let uu____2639 =
            let uu____2640 = unparen t in uu____2640.FStar_Parser_AST.tm in
          (match uu____2639 with
           | FStar_Parser_AST.Refine
               ({ FStar_Parser_AST.b = FStar_Parser_AST.NoName t1;
                  FStar_Parser_AST.brange = uu____2642;
                  FStar_Parser_AST.blevel = uu____2643;
                  FStar_Parser_AST.aqual = uu____2644;_},phi)
               ->
               if is_atomic
               then
                 let uu____2646 =
                   let uu____2647 =
                     let uu____2648 =
                       p_refinement b.FStar_Parser_AST.aqual
                         FStar_Pprint.underscore t1 phi in
                     FStar_Pprint.op_Hat_Hat uu____2648 FStar_Pprint.rparen in
                   FStar_Pprint.op_Hat_Hat FStar_Pprint.lparen uu____2647 in
                 FStar_Pprint.group uu____2646
               else
                 (let uu____2650 =
                    p_refinement b.FStar_Parser_AST.aqual
                      FStar_Pprint.underscore t1 phi in
                  FStar_Pprint.group uu____2650)
           | uu____2651 -> if is_atomic then p_atomicTerm t else p_appTerm t)
and p_refinement:
  FStar_Parser_AST.arg_qualifier option ->
    FStar_Pprint.document ->
      FStar_Parser_AST.term -> FStar_Parser_AST.term -> FStar_Pprint.document
  =
  fun aqual_opt  ->
    fun binder  ->
      fun t  ->
        fun phi  ->
          let uu____2658 = FStar_Pprint.optional p_aqual aqual_opt in
          let uu____2659 =
            let uu____2660 =
              let uu____2661 =
                let uu____2662 = p_appTerm t in
                let uu____2663 =
                  let uu____2664 = p_noSeqTerm phi in
                  soft_braces_with_nesting uu____2664 in
                FStar_Pprint.op_Hat_Hat uu____2662 uu____2663 in
              FStar_Pprint.op_Hat_Hat FStar_Pprint.colon uu____2661 in
            FStar_Pprint.op_Hat_Hat binder uu____2660 in
          FStar_Pprint.op_Hat_Hat uu____2658 uu____2659
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
    let uu____2677 =
      let uu____2678 = unparen e in uu____2678.FStar_Parser_AST.tm in
    match uu____2677 with
    | FStar_Parser_AST.Seq (e1,e2) ->
        let uu____2681 =
          let uu____2682 =
            let uu____2683 = p_noSeqTerm e1 in
            FStar_Pprint.op_Hat_Hat uu____2683 FStar_Pprint.semi in
          FStar_Pprint.group uu____2682 in
        let uu____2684 = p_term e2 in
        FStar_Pprint.op_Hat_Slash_Hat uu____2681 uu____2684
    | FStar_Parser_AST.Bind (x,e1,e2) ->
        let uu____2688 =
          let uu____2689 =
            let uu____2690 =
              let uu____2691 = p_lident x in
              let uu____2692 =
                FStar_Pprint.op_Hat_Hat FStar_Pprint.space
                  FStar_Pprint.long_left_arrow in
              FStar_Pprint.op_Hat_Hat uu____2691 uu____2692 in
            let uu____2693 =
              let uu____2694 = p_noSeqTerm e1 in
              let uu____2695 =
                FStar_Pprint.op_Hat_Hat FStar_Pprint.space FStar_Pprint.semi in
              FStar_Pprint.op_Hat_Hat uu____2694 uu____2695 in
            op_Hat_Slash_Plus_Hat uu____2690 uu____2693 in
          FStar_Pprint.group uu____2689 in
        let uu____2696 = p_term e2 in
        FStar_Pprint.op_Hat_Slash_Hat uu____2688 uu____2696
    | uu____2697 ->
        let uu____2698 = p_noSeqTerm e in FStar_Pprint.group uu____2698
and p_noSeqTerm: FStar_Parser_AST.term -> FStar_Pprint.document =
  fun e  -> with_comment p_noSeqTerm' e e.FStar_Parser_AST.range
and p_noSeqTerm': FStar_Parser_AST.term -> FStar_Pprint.document =
  fun e  ->
    let uu____2701 =
      let uu____2702 = unparen e in uu____2702.FStar_Parser_AST.tm in
    match uu____2701 with
    | FStar_Parser_AST.Ascribed (e1,t,None ) ->
        let uu____2706 =
          let uu____2707 = p_tmIff e1 in
          let uu____2708 =
            let uu____2709 =
              let uu____2710 = p_typ t in
              FStar_Pprint.op_Hat_Slash_Hat FStar_Pprint.colon uu____2710 in
            FStar_Pprint.op_Hat_Hat FStar_Pprint.langle uu____2709 in
          FStar_Pprint.op_Hat_Slash_Hat uu____2707 uu____2708 in
        FStar_Pprint.group uu____2706
    | FStar_Parser_AST.Ascribed (e1,t,Some tac) ->
        let uu____2715 =
          let uu____2716 = p_tmIff e1 in
          let uu____2717 =
            let uu____2718 =
              let uu____2719 =
                let uu____2720 = p_typ t in
                let uu____2721 =
                  let uu____2722 = str "by" in
                  let uu____2723 = p_typ tac in
                  FStar_Pprint.op_Hat_Slash_Hat uu____2722 uu____2723 in
                FStar_Pprint.op_Hat_Slash_Hat uu____2720 uu____2721 in
              FStar_Pprint.op_Hat_Slash_Hat FStar_Pprint.colon uu____2719 in
            FStar_Pprint.op_Hat_Hat FStar_Pprint.langle uu____2718 in
          FStar_Pprint.op_Hat_Slash_Hat uu____2716 uu____2717 in
        FStar_Pprint.group uu____2715
    | FStar_Parser_AST.Op
        ({ FStar_Ident.idText = ".()<-"; FStar_Ident.idRange = uu____2724;_},e1::e2::e3::[])
        ->
        let uu____2729 =
          let uu____2730 =
            let uu____2731 =
              let uu____2732 = p_atomicTermNotQUident e1 in
              let uu____2733 =
                let uu____2734 =
                  let uu____2735 =
                    let uu____2736 = p_term e2 in
                    soft_parens_with_nesting uu____2736 in
                  let uu____2737 =
                    FStar_Pprint.op_Hat_Hat FStar_Pprint.space
                      FStar_Pprint.larrow in
                  FStar_Pprint.op_Hat_Hat uu____2735 uu____2737 in
                FStar_Pprint.op_Hat_Hat FStar_Pprint.dot uu____2734 in
              FStar_Pprint.op_Hat_Hat uu____2732 uu____2733 in
            FStar_Pprint.group uu____2731 in
          let uu____2738 =
            let uu____2739 = p_noSeqTerm e3 in jump2 uu____2739 in
          FStar_Pprint.op_Hat_Hat uu____2730 uu____2738 in
        FStar_Pprint.group uu____2729
    | FStar_Parser_AST.Op
        ({ FStar_Ident.idText = ".[]<-"; FStar_Ident.idRange = uu____2740;_},e1::e2::e3::[])
        ->
        let uu____2745 =
          let uu____2746 =
            let uu____2747 =
              let uu____2748 = p_atomicTermNotQUident e1 in
              let uu____2749 =
                let uu____2750 =
                  let uu____2751 =
                    let uu____2752 = p_term e2 in
                    soft_brackets_with_nesting uu____2752 in
                  let uu____2753 =
                    FStar_Pprint.op_Hat_Hat FStar_Pprint.space
                      FStar_Pprint.larrow in
                  FStar_Pprint.op_Hat_Hat uu____2751 uu____2753 in
                FStar_Pprint.op_Hat_Hat FStar_Pprint.dot uu____2750 in
              FStar_Pprint.op_Hat_Hat uu____2748 uu____2749 in
            FStar_Pprint.group uu____2747 in
          let uu____2754 =
            let uu____2755 = p_noSeqTerm e3 in jump2 uu____2755 in
          FStar_Pprint.op_Hat_Hat uu____2746 uu____2754 in
        FStar_Pprint.group uu____2745
    | FStar_Parser_AST.Requires (e1,wtf) ->
        let uu____2761 =
          let uu____2762 = str "requires" in
          let uu____2763 = p_typ e1 in
          FStar_Pprint.op_Hat_Slash_Hat uu____2762 uu____2763 in
        FStar_Pprint.group uu____2761
    | FStar_Parser_AST.Ensures (e1,wtf) ->
        let uu____2769 =
          let uu____2770 = str "ensures" in
          let uu____2771 = p_typ e1 in
          FStar_Pprint.op_Hat_Slash_Hat uu____2770 uu____2771 in
        FStar_Pprint.group uu____2769
    | FStar_Parser_AST.Attributes es ->
        let uu____2774 =
          let uu____2775 = str "attributes" in
          let uu____2776 = FStar_Pprint.separate_map break1 p_atomicTerm es in
          FStar_Pprint.op_Hat_Slash_Hat uu____2775 uu____2776 in
        FStar_Pprint.group uu____2774
    | FStar_Parser_AST.If (e1,e2,e3) ->
        let uu____2780 = is_unit e3 in
        if uu____2780
        then
          let uu____2781 =
            let uu____2782 =
              let uu____2783 = str "if" in
              let uu____2784 = p_noSeqTerm e1 in
              op_Hat_Slash_Plus_Hat uu____2783 uu____2784 in
            let uu____2785 =
              let uu____2786 = str "then" in
              let uu____2787 = p_noSeqTerm e2 in
              op_Hat_Slash_Plus_Hat uu____2786 uu____2787 in
            FStar_Pprint.op_Hat_Slash_Hat uu____2782 uu____2785 in
          FStar_Pprint.group uu____2781
        else
          (let e2_doc =
             let uu____2790 =
               let uu____2791 = unparen e2 in uu____2791.FStar_Parser_AST.tm in
             match uu____2790 with
             | FStar_Parser_AST.If (uu____2792,uu____2793,e31) when
                 is_unit e31 ->
                 let uu____2795 = p_noSeqTerm e2 in
                 soft_parens_with_nesting uu____2795
             | uu____2796 -> p_noSeqTerm e2 in
           let uu____2797 =
             let uu____2798 =
               let uu____2799 = str "if" in
               let uu____2800 = p_noSeqTerm e1 in
               op_Hat_Slash_Plus_Hat uu____2799 uu____2800 in
             let uu____2801 =
               let uu____2802 =
                 let uu____2803 = str "then" in
                 op_Hat_Slash_Plus_Hat uu____2803 e2_doc in
               let uu____2804 =
                 let uu____2805 = str "else" in
                 let uu____2806 = p_noSeqTerm e3 in
                 op_Hat_Slash_Plus_Hat uu____2805 uu____2806 in
               FStar_Pprint.op_Hat_Slash_Hat uu____2802 uu____2804 in
             FStar_Pprint.op_Hat_Slash_Hat uu____2798 uu____2801 in
           FStar_Pprint.group uu____2797)
    | FStar_Parser_AST.TryWith (e1,branches) ->
        let uu____2819 =
          let uu____2820 =
            let uu____2821 = str "try" in
            let uu____2822 = p_noSeqTerm e1 in prefix2 uu____2821 uu____2822 in
          let uu____2823 =
            let uu____2824 = str "with" in
            let uu____2825 =
              FStar_Pprint.separate_map FStar_Pprint.hardline p_patternBranch
                branches in
            FStar_Pprint.op_Hat_Slash_Hat uu____2824 uu____2825 in
          FStar_Pprint.op_Hat_Slash_Hat uu____2820 uu____2823 in
        FStar_Pprint.group uu____2819
    | FStar_Parser_AST.Match (e1,branches) ->
        let uu____2842 =
          let uu____2843 =
            let uu____2844 = str "match" in
            let uu____2845 = p_noSeqTerm e1 in
            let uu____2846 = str "with" in
            FStar_Pprint.surround (Prims.parse_int "2") (Prims.parse_int "1")
              uu____2844 uu____2845 uu____2846 in
          let uu____2847 =
            FStar_Pprint.separate_map FStar_Pprint.hardline p_patternBranch
              branches in
          FStar_Pprint.op_Hat_Slash_Hat uu____2843 uu____2847 in
        FStar_Pprint.group uu____2842
    | FStar_Parser_AST.LetOpen (uid,e1) ->
        let uu____2854 =
          let uu____2855 =
            let uu____2856 = str "let open" in
            let uu____2857 = p_quident uid in
            let uu____2858 = str "in" in
            FStar_Pprint.surround (Prims.parse_int "2") (Prims.parse_int "1")
              uu____2856 uu____2857 uu____2858 in
          let uu____2859 = p_term e1 in
          FStar_Pprint.op_Hat_Slash_Hat uu____2855 uu____2859 in
        FStar_Pprint.group uu____2854
    | FStar_Parser_AST.Let (q,lbs,e1) ->
        let let_doc =
          let uu____2870 = str "let" in
          let uu____2871 = p_letqualifier q in
          FStar_Pprint.op_Hat_Hat uu____2870 uu____2871 in
        let uu____2872 =
          let uu____2873 =
            let uu____2874 =
              let uu____2875 = str "and" in
              precede_break_separate_map let_doc uu____2875 p_letbinding lbs in
            let uu____2878 = str "in" in
            FStar_Pprint.op_Hat_Slash_Hat uu____2874 uu____2878 in
          FStar_Pprint.group uu____2873 in
        let uu____2879 = p_term e1 in
        FStar_Pprint.op_Hat_Slash_Hat uu____2872 uu____2879
    | FStar_Parser_AST.Abs
        ({ FStar_Parser_AST.pat = FStar_Parser_AST.PatVar (x,typ_opt);
           FStar_Parser_AST.prange = uu____2882;_}::[],{
                                                         FStar_Parser_AST.tm
                                                           =
                                                           FStar_Parser_AST.Match
                                                           (maybe_x,branches);
                                                         FStar_Parser_AST.range
                                                           = uu____2885;
                                                         FStar_Parser_AST.level
                                                           = uu____2886;_})
        when matches_var maybe_x x ->
        let uu____2900 =
          let uu____2901 = str "function" in
          let uu____2902 =
            FStar_Pprint.separate_map FStar_Pprint.hardline p_patternBranch
              branches in
          FStar_Pprint.op_Hat_Slash_Hat uu____2901 uu____2902 in
        FStar_Pprint.group uu____2900
    | FStar_Parser_AST.Assign (id,e1) ->
        let uu____2909 =
          let uu____2910 = p_lident id in
          let uu____2911 =
            let uu____2912 = p_noSeqTerm e1 in
            FStar_Pprint.op_Hat_Slash_Hat FStar_Pprint.larrow uu____2912 in
          FStar_Pprint.op_Hat_Slash_Hat uu____2910 uu____2911 in
        FStar_Pprint.group uu____2909
    | uu____2913 -> p_typ e
and p_typ: FStar_Parser_AST.term -> FStar_Pprint.document =
  fun e  -> with_comment p_typ' e e.FStar_Parser_AST.range
and p_typ': FStar_Parser_AST.term -> FStar_Pprint.document =
  fun e  ->
    let uu____2916 =
      let uu____2917 = unparen e in uu____2917.FStar_Parser_AST.tm in
    match uu____2916 with
    | FStar_Parser_AST.QForall (bs,trigger,e1) ->
        let uu____2927 =
          let uu____2928 =
            let uu____2929 = p_quantifier e in
            FStar_Pprint.op_Hat_Hat uu____2929 FStar_Pprint.space in
          let uu____2930 = p_binders true bs in
          FStar_Pprint.soft_surround (Prims.parse_int "2")
            (Prims.parse_int "0") uu____2928 uu____2930 FStar_Pprint.dot in
        let uu____2931 =
          let uu____2932 = p_trigger trigger in
          let uu____2933 = p_noSeqTerm e1 in
          FStar_Pprint.op_Hat_Hat uu____2932 uu____2933 in
        prefix2 uu____2927 uu____2931
    | FStar_Parser_AST.QExists (bs,trigger,e1) ->
        let uu____2943 =
          let uu____2944 =
            let uu____2945 = p_quantifier e in
            FStar_Pprint.op_Hat_Hat uu____2945 FStar_Pprint.space in
          let uu____2946 = p_binders true bs in
          FStar_Pprint.soft_surround (Prims.parse_int "2")
            (Prims.parse_int "0") uu____2944 uu____2946 FStar_Pprint.dot in
        let uu____2947 =
          let uu____2948 = p_trigger trigger in
          let uu____2949 = p_noSeqTerm e1 in
          FStar_Pprint.op_Hat_Hat uu____2948 uu____2949 in
        prefix2 uu____2943 uu____2947
    | uu____2950 -> p_simpleTerm e
and p_quantifier: FStar_Parser_AST.term -> FStar_Pprint.document =
  fun e  ->
    let uu____2952 =
      let uu____2953 = unparen e in uu____2953.FStar_Parser_AST.tm in
    match uu____2952 with
    | FStar_Parser_AST.QForall uu____2954 -> str "forall"
    | FStar_Parser_AST.QExists uu____2961 -> str "exists"
    | uu____2968 ->
        failwith "Imposible : p_quantifier called on a non-quantifier term"
and p_trigger:
  FStar_Parser_AST.term Prims.list Prims.list -> FStar_Pprint.document =
  fun uu___104_2969  ->
    match uu___104_2969 with
    | [] -> FStar_Pprint.empty
    | pats ->
        let uu____2976 =
          let uu____2977 =
            let uu____2978 = str "pattern" in
            let uu____2979 =
              let uu____2980 =
                let uu____2981 = p_disjunctivePats pats in jump2 uu____2981 in
              let uu____2982 =
                FStar_Pprint.op_Hat_Hat FStar_Pprint.rbrace break1 in
              FStar_Pprint.op_Hat_Slash_Hat uu____2980 uu____2982 in
            FStar_Pprint.op_Hat_Slash_Hat uu____2978 uu____2979 in
          FStar_Pprint.op_Hat_Hat FStar_Pprint.colon uu____2977 in
        FStar_Pprint.op_Hat_Hat FStar_Pprint.lbrace uu____2976
and p_disjunctivePats:
  FStar_Parser_AST.term Prims.list Prims.list -> FStar_Pprint.document =
  fun pats  ->
    let uu____2986 = str "\\/" in
    FStar_Pprint.separate_map uu____2986 p_conjunctivePats pats
and p_conjunctivePats:
  FStar_Parser_AST.term Prims.list -> FStar_Pprint.document =
  fun pats  ->
    let uu____2990 =
      FStar_Pprint.separate_map FStar_Pprint.semi p_appTerm pats in
    FStar_Pprint.group uu____2990
and p_simpleTerm: FStar_Parser_AST.term -> FStar_Pprint.document =
  fun e  ->
    let uu____2992 =
      let uu____2993 = unparen e in uu____2993.FStar_Parser_AST.tm in
    match uu____2992 with
    | FStar_Parser_AST.Abs (pats,e1) ->
        let uu____2998 =
          let uu____2999 = str "fun" in
          let uu____3000 =
            let uu____3001 =
              FStar_Pprint.separate_map break1 p_atomicPattern pats in
            FStar_Pprint.op_Hat_Slash_Hat uu____3001 FStar_Pprint.rarrow in
          op_Hat_Slash_Plus_Hat uu____2999 uu____3000 in
        let uu____3002 = p_term e1 in
        op_Hat_Slash_Plus_Hat uu____2998 uu____3002
    | uu____3003 -> p_tmIff e
and p_maybeFocusArrow: Prims.bool -> FStar_Pprint.document =
  fun b  -> if b then str "~>" else FStar_Pprint.rarrow
and p_patternBranch:
  (FStar_Parser_AST.pattern* FStar_Parser_AST.term option*
    FStar_Parser_AST.term) -> FStar_Pprint.document
  =
  fun uu____3006  ->
    match uu____3006 with
    | (pat,when_opt,e) ->
        let maybe_paren =
          let uu____3019 =
            let uu____3020 = unparen e in uu____3020.FStar_Parser_AST.tm in
          match uu____3019 with
          | FStar_Parser_AST.Match uu____3023 -> soft_begin_end_with_nesting
          | FStar_Parser_AST.TryWith uu____3031 ->
              soft_begin_end_with_nesting
          | FStar_Parser_AST.Abs
              ({
                 FStar_Parser_AST.pat = FStar_Parser_AST.PatVar
                   (x,uu____3040);
                 FStar_Parser_AST.prange = uu____3041;_}::[],{
                                                               FStar_Parser_AST.tm
                                                                 =
                                                                 FStar_Parser_AST.Match
                                                                 (maybe_x,uu____3043);
                                                               FStar_Parser_AST.range
                                                                 = uu____3044;
                                                               FStar_Parser_AST.level
                                                                 = uu____3045;_})
              when matches_var maybe_x x -> soft_begin_end_with_nesting
          | uu____3059 -> (fun x  -> x) in
        let uu____3061 =
          let uu____3062 =
            let uu____3063 =
              let uu____3064 =
                let uu____3065 =
                  let uu____3066 = p_disjunctivePattern pat in
                  let uu____3067 =
                    let uu____3068 = p_maybeWhen when_opt in
                    FStar_Pprint.op_Hat_Hat uu____3068 FStar_Pprint.rarrow in
                  op_Hat_Slash_Plus_Hat uu____3066 uu____3067 in
                FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____3065 in
              FStar_Pprint.op_Hat_Hat FStar_Pprint.bar uu____3064 in
            FStar_Pprint.group uu____3063 in
          let uu____3069 =
            let uu____3070 = p_term e in maybe_paren uu____3070 in
          op_Hat_Slash_Plus_Hat uu____3062 uu____3069 in
        FStar_Pprint.group uu____3061
and p_maybeWhen: FStar_Parser_AST.term option -> FStar_Pprint.document =
  fun uu___105_3071  ->
    match uu___105_3071 with
    | None  -> FStar_Pprint.empty
    | Some e ->
        let uu____3074 = str "when" in
        let uu____3075 =
          let uu____3076 = p_tmFormula e in
          FStar_Pprint.op_Hat_Hat uu____3076 FStar_Pprint.space in
        op_Hat_Slash_Plus_Hat uu____3074 uu____3075
and p_tmIff: FStar_Parser_AST.term -> FStar_Pprint.document =
  fun e  ->
    let uu____3078 =
      let uu____3079 = unparen e in uu____3079.FStar_Parser_AST.tm in
    match uu____3078 with
    | FStar_Parser_AST.Op
        ({ FStar_Ident.idText = "<==>"; FStar_Ident.idRange = uu____3080;_},e1::e2::[])
        ->
        let uu____3084 = str "<==>" in
        let uu____3085 = p_tmImplies e1 in
        let uu____3086 = p_tmIff e2 in
        infix0 uu____3084 uu____3085 uu____3086
    | uu____3087 -> p_tmImplies e
and p_tmImplies: FStar_Parser_AST.term -> FStar_Pprint.document =
  fun e  ->
    let uu____3089 =
      let uu____3090 = unparen e in uu____3090.FStar_Parser_AST.tm in
    match uu____3089 with
    | FStar_Parser_AST.Op
        ({ FStar_Ident.idText = "==>"; FStar_Ident.idRange = uu____3091;_},e1::e2::[])
        ->
        let uu____3095 = str "==>" in
        let uu____3096 = p_tmArrow p_tmFormula e1 in
        let uu____3097 = p_tmImplies e2 in
        infix0 uu____3095 uu____3096 uu____3097
    | uu____3098 -> p_tmArrow p_tmFormula e
and p_tmArrow:
  (FStar_Parser_AST.term -> FStar_Pprint.document) ->
    FStar_Parser_AST.term -> FStar_Pprint.document
  =
  fun p_Tm  ->
    fun e  ->
      let uu____3103 =
        let uu____3104 = unparen e in uu____3104.FStar_Parser_AST.tm in
      match uu____3103 with
      | FStar_Parser_AST.Product (bs,tgt) ->
          let uu____3109 =
            let uu____3110 =
              FStar_Pprint.concat_map
                (fun b  ->
                   let uu____3112 = p_binder false b in
                   let uu____3113 =
                     let uu____3114 =
                       FStar_Pprint.op_Hat_Hat FStar_Pprint.rarrow break1 in
                     FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____3114 in
                   FStar_Pprint.op_Hat_Hat uu____3112 uu____3113) bs in
            let uu____3115 = p_tmArrow p_Tm tgt in
            FStar_Pprint.op_Hat_Hat uu____3110 uu____3115 in
          FStar_Pprint.group uu____3109
      | uu____3116 -> p_Tm e
and p_tmFormula: FStar_Parser_AST.term -> FStar_Pprint.document =
  fun e  ->
    let uu____3118 =
      let uu____3119 = unparen e in uu____3119.FStar_Parser_AST.tm in
    match uu____3118 with
    | FStar_Parser_AST.Op
        ({ FStar_Ident.idText = "\\/"; FStar_Ident.idRange = uu____3120;_},e1::e2::[])
        ->
        let uu____3124 = str "\\/" in
        let uu____3125 = p_tmFormula e1 in
        let uu____3126 = p_tmConjunction e2 in
        infix0 uu____3124 uu____3125 uu____3126
    | uu____3127 -> p_tmConjunction e
and p_tmConjunction: FStar_Parser_AST.term -> FStar_Pprint.document =
  fun e  ->
    let uu____3129 =
      let uu____3130 = unparen e in uu____3130.FStar_Parser_AST.tm in
    match uu____3129 with
    | FStar_Parser_AST.Op
        ({ FStar_Ident.idText = "/\\"; FStar_Ident.idRange = uu____3131;_},e1::e2::[])
        ->
        let uu____3135 = str "/\\" in
        let uu____3136 = p_tmConjunction e1 in
        let uu____3137 = p_tmTuple e2 in
        infix0 uu____3135 uu____3136 uu____3137
    | uu____3138 -> p_tmTuple e
and p_tmTuple: FStar_Parser_AST.term -> FStar_Pprint.document =
  fun e  -> with_comment p_tmTuple' e e.FStar_Parser_AST.range
and p_tmTuple': FStar_Parser_AST.term -> FStar_Pprint.document =
  fun e  ->
    let uu____3141 =
      let uu____3142 = unparen e in uu____3142.FStar_Parser_AST.tm in
    match uu____3141 with
    | FStar_Parser_AST.Construct (lid,args) when is_tuple_constructor lid ->
        let uu____3151 = FStar_Pprint.op_Hat_Hat FStar_Pprint.comma break1 in
        FStar_Pprint.separate_map uu____3151
          (fun uu____3154  ->
             match uu____3154 with | (e1,uu____3158) -> p_tmEq e1) args
    | uu____3159 -> p_tmEq e
and paren_if:
  Prims.int -> Prims.int -> FStar_Pprint.document -> FStar_Pprint.document =
  fun curr  ->
    fun mine  ->
      fun doc1  ->
        if mine <= curr
        then doc1
        else
          (let uu____3164 =
             let uu____3165 =
               FStar_Pprint.op_Hat_Hat doc1 FStar_Pprint.rparen in
             FStar_Pprint.op_Hat_Hat FStar_Pprint.lparen uu____3165 in
           FStar_Pprint.group uu____3164)
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
      let uu____3190 =
        let uu____3191 = unparen e in uu____3191.FStar_Parser_AST.tm in
      match uu____3190 with
      | FStar_Parser_AST.Op (op,e1::e2::[]) when
          ((is_operatorInfix0ad12 op) || ((FStar_Ident.text_of_id op) = "="))
            || ((FStar_Ident.text_of_id op) = "|>")
          ->
          let op1 = FStar_Ident.text_of_id op in
          let uu____3197 = levels op1 in
          (match uu____3197 with
           | (left1,mine,right1) ->
               let uu____3204 =
                 let uu____3205 = FStar_All.pipe_left str op1 in
                 let uu____3206 = p_tmEq' left1 e1 in
                 let uu____3207 = p_tmEq' right1 e2 in
                 infix0 uu____3205 uu____3206 uu____3207 in
               paren_if curr mine uu____3204)
      | FStar_Parser_AST.Op
          ({ FStar_Ident.idText = ":="; FStar_Ident.idRange = uu____3208;_},e1::e2::[])
          ->
          let uu____3212 =
            let uu____3213 = p_tmEq e1 in
            let uu____3214 =
              let uu____3215 =
                let uu____3216 =
                  let uu____3217 = p_tmEq e2 in
                  op_Hat_Slash_Plus_Hat FStar_Pprint.equals uu____3217 in
                FStar_Pprint.op_Hat_Hat FStar_Pprint.colon uu____3216 in
              FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____3215 in
            FStar_Pprint.op_Hat_Hat uu____3213 uu____3214 in
          FStar_Pprint.group uu____3212
      | FStar_Parser_AST.Op
          ({ FStar_Ident.idText = "-"; FStar_Ident.idRange = uu____3218;_},e1::[])
          ->
          let uu____3221 = levels "-" in
          (match uu____3221 with
           | (left1,mine,right1) ->
               let uu____3228 = p_tmEq' mine e1 in
               FStar_Pprint.op_Hat_Slash_Hat FStar_Pprint.minus uu____3228)
      | uu____3229 -> p_tmNoEq e
and p_tmNoEq: FStar_Parser_AST.term -> FStar_Pprint.document =
  fun e  ->
    let n1 = max_level [colon_colon (); amp (); opinfix3 (); opinfix4 ()] in
    p_tmNoEq' n1 e
and p_tmNoEq': Prims.int -> FStar_Parser_AST.term -> FStar_Pprint.document =
  fun curr  ->
    fun e  ->
      let uu____3259 =
        let uu____3260 = unparen e in uu____3260.FStar_Parser_AST.tm in
      match uu____3259 with
      | FStar_Parser_AST.Construct (lid,(e1,uu____3263)::(e2,uu____3265)::[])
          when
          (FStar_Ident.lid_equals lid FStar_Parser_Const.cons_lid) &&
            (let uu____3275 = is_list e in Prims.op_Negation uu____3275)
          ->
          let op = "::" in
          let uu____3277 = levels op in
          (match uu____3277 with
           | (left1,mine,right1) ->
               let uu____3284 =
                 let uu____3285 = str op in
                 let uu____3286 = p_tmNoEq' left1 e1 in
                 let uu____3287 = p_tmNoEq' right1 e2 in
                 infix0 uu____3285 uu____3286 uu____3287 in
               paren_if curr mine uu____3284)
      | FStar_Parser_AST.Sum (binders,res) ->
          let op = "&" in
          let uu____3293 = levels op in
          (match uu____3293 with
           | (left1,mine,right1) ->
               let p_dsumfst b =
                 let uu____3304 = p_binder false b in
                 let uu____3305 =
                   let uu____3306 =
                     let uu____3307 = str op in
                     FStar_Pprint.op_Hat_Hat uu____3307 break1 in
                   FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____3306 in
                 FStar_Pprint.op_Hat_Hat uu____3304 uu____3305 in
               let uu____3308 =
                 let uu____3309 = FStar_Pprint.concat_map p_dsumfst binders in
                 let uu____3310 = p_tmNoEq' right1 res in
                 FStar_Pprint.op_Hat_Hat uu____3309 uu____3310 in
               paren_if curr mine uu____3308)
      | FStar_Parser_AST.Op (op,e1::e2::[]) when is_operatorInfix34 op ->
          let op1 = FStar_Ident.text_of_id op in
          let uu____3316 = levels op1 in
          (match uu____3316 with
           | (left1,mine,right1) ->
               let uu____3323 =
                 let uu____3324 = str op1 in
                 let uu____3325 = p_tmNoEq' left1 e1 in
                 let uu____3326 = p_tmNoEq' right1 e2 in
                 infix0 uu____3324 uu____3325 uu____3326 in
               paren_if curr mine uu____3323)
      | FStar_Parser_AST.NamedTyp (lid,e1) ->
          let uu____3329 =
            let uu____3330 = p_lidentOrUnderscore lid in
            let uu____3331 =
              let uu____3332 = p_appTerm e1 in
              FStar_Pprint.op_Hat_Slash_Hat FStar_Pprint.colon uu____3332 in
            FStar_Pprint.op_Hat_Slash_Hat uu____3330 uu____3331 in
          FStar_Pprint.group uu____3329
      | FStar_Parser_AST.Refine (b,phi) -> p_refinedBinder b phi
      | FStar_Parser_AST.Record (with_opt,record_fields) ->
          let uu____3345 =
            let uu____3346 =
              default_or_map FStar_Pprint.empty p_with_clause with_opt in
            let uu____3347 =
              let uu____3348 =
                FStar_Pprint.op_Hat_Hat FStar_Pprint.semi break1 in
              FStar_Pprint.separate_map uu____3348 p_simpleDef record_fields in
            FStar_Pprint.op_Hat_Hat uu____3346 uu____3347 in
          braces_with_nesting uu____3345
      | FStar_Parser_AST.Op
          ({ FStar_Ident.idText = "~"; FStar_Ident.idRange = uu____3351;_},e1::[])
          ->
          let uu____3354 =
            let uu____3355 = str "~" in
            let uu____3356 = p_atomicTerm e1 in
            FStar_Pprint.op_Hat_Hat uu____3355 uu____3356 in
          FStar_Pprint.group uu____3354
      | uu____3357 -> p_appTerm e
and p_with_clause: FStar_Parser_AST.term -> FStar_Pprint.document =
  fun e  ->
    let uu____3359 = p_appTerm e in
    let uu____3360 =
      let uu____3361 =
        let uu____3362 = str "with" in
        FStar_Pprint.op_Hat_Hat uu____3362 break1 in
      FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____3361 in
    FStar_Pprint.op_Hat_Hat uu____3359 uu____3360
and p_refinedBinder:
  FStar_Parser_AST.binder -> FStar_Parser_AST.term -> FStar_Pprint.document =
  fun b  ->
    fun phi  ->
      match b.FStar_Parser_AST.b with
      | FStar_Parser_AST.Annotated (lid,t) ->
          let uu____3367 =
            let uu____3368 = p_lident lid in
            p_refinement b.FStar_Parser_AST.aqual uu____3368 t phi in
          soft_parens_with_nesting uu____3367
      | FStar_Parser_AST.TAnnotated uu____3369 ->
          failwith "Is this still used ?"
      | FStar_Parser_AST.Variable uu____3372 ->
          let uu____3373 =
            let uu____3374 = FStar_Parser_AST.binder_to_string b in
            FStar_Util.format1
              "Imposible : a refined binder ought to be annotated %s"
              uu____3374 in
          failwith uu____3373
      | FStar_Parser_AST.TVariable uu____3375 ->
          let uu____3376 =
            let uu____3377 = FStar_Parser_AST.binder_to_string b in
            FStar_Util.format1
              "Imposible : a refined binder ought to be annotated %s"
              uu____3377 in
          failwith uu____3376
      | FStar_Parser_AST.NoName uu____3378 ->
          let uu____3379 =
            let uu____3380 = FStar_Parser_AST.binder_to_string b in
            FStar_Util.format1
              "Imposible : a refined binder ought to be annotated %s"
              uu____3380 in
          failwith uu____3379
and p_simpleDef:
  (FStar_Ident.lid* FStar_Parser_AST.term) -> FStar_Pprint.document =
  fun uu____3381  ->
    match uu____3381 with
    | (lid,e) ->
        let uu____3386 =
          let uu____3387 = p_qlident lid in
          let uu____3388 =
            let uu____3389 = p_tmIff e in
            FStar_Pprint.op_Hat_Slash_Hat FStar_Pprint.equals uu____3389 in
          FStar_Pprint.op_Hat_Slash_Hat uu____3387 uu____3388 in
        FStar_Pprint.group uu____3386
and p_appTerm: FStar_Parser_AST.term -> FStar_Pprint.document =
  fun e  ->
    let uu____3391 =
      let uu____3392 = unparen e in uu____3392.FStar_Parser_AST.tm in
    match uu____3391 with
    | FStar_Parser_AST.App uu____3393 when is_general_application e ->
        let uu____3397 = head_and_args e in
        (match uu____3397 with
         | (head1,args) ->
             let uu____3411 =
               let uu____3417 = FStar_ST.read should_print_fs_typ_app in
               if uu____3417
               then
                 let uu____3425 =
                   FStar_Util.take
                     (fun uu____3436  ->
                        match uu____3436 with
                        | (uu____3439,aq) -> aq = FStar_Parser_AST.FsTypApp)
                     args in
                 match uu____3425 with
                 | (fs_typ_args,args1) ->
                     let uu____3460 =
                       let uu____3461 = p_indexingTerm head1 in
                       let uu____3462 =
                         let uu____3463 =
                           FStar_Pprint.op_Hat_Hat FStar_Pprint.comma break1 in
                         soft_surround_separate_map (Prims.parse_int "2")
                           (Prims.parse_int "0") FStar_Pprint.empty
                           FStar_Pprint.langle uu____3463 FStar_Pprint.rangle
                           p_fsTypArg fs_typ_args in
                       FStar_Pprint.op_Hat_Hat uu____3461 uu____3462 in
                     (uu____3460, args1)
               else
                 (let uu____3470 = p_indexingTerm head1 in (uu____3470, args)) in
             (match uu____3411 with
              | (head_doc,args1) ->
                  let uu____3482 =
                    let uu____3483 =
                      FStar_Pprint.op_Hat_Hat head_doc FStar_Pprint.space in
                    soft_surround_separate_map (Prims.parse_int "2")
                      (Prims.parse_int "0") head_doc uu____3483 break1
                      FStar_Pprint.empty p_argTerm args1 in
                  FStar_Pprint.group uu____3482))
    | FStar_Parser_AST.Construct (lid,args) when
        (is_general_construction e) &&
          (Prims.op_Negation (is_dtuple_constructor lid))
        ->
        (match args with
         | [] -> p_quident lid
         | arg::[] ->
             let uu____3503 =
               let uu____3504 = p_quident lid in
               let uu____3505 = p_argTerm arg in
               FStar_Pprint.op_Hat_Slash_Hat uu____3504 uu____3505 in
             FStar_Pprint.group uu____3503
         | hd1::tl1 ->
             let uu____3515 =
               let uu____3516 =
                 let uu____3517 =
                   let uu____3518 = p_quident lid in
                   let uu____3519 = p_argTerm hd1 in
                   prefix2 uu____3518 uu____3519 in
                 FStar_Pprint.group uu____3517 in
               let uu____3520 =
                 let uu____3521 =
                   FStar_Pprint.separate_map break1 p_argTerm tl1 in
                 jump2 uu____3521 in
               FStar_Pprint.op_Hat_Hat uu____3516 uu____3520 in
             FStar_Pprint.group uu____3515)
    | uu____3524 -> p_indexingTerm e
and p_argTerm:
  (FStar_Parser_AST.term* FStar_Parser_AST.imp) -> FStar_Pprint.document =
  fun arg_imp  ->
    match arg_imp with
    | ({ FStar_Parser_AST.tm = FStar_Parser_AST.Uvar uu____3528;
         FStar_Parser_AST.range = uu____3529;
         FStar_Parser_AST.level = uu____3530;_},FStar_Parser_AST.UnivApp
       ) -> p_univar (fst arg_imp)
    | (u,FStar_Parser_AST.UnivApp ) -> p_universe u
    | (e,FStar_Parser_AST.FsTypApp ) ->
        (FStar_Util.print_warning
           "Unexpected FsTypApp, output might not be formatted correctly.\n";
         (let uu____3534 = p_indexingTerm e in
          FStar_Pprint.surround (Prims.parse_int "2") (Prims.parse_int "1")
            FStar_Pprint.langle uu____3534 FStar_Pprint.rangle))
    | (e,FStar_Parser_AST.Hash ) ->
        let uu____3536 = str "#" in
        let uu____3537 = p_indexingTerm e in
        FStar_Pprint.op_Hat_Hat uu____3536 uu____3537
    | (e,FStar_Parser_AST.Nothing ) -> p_indexingTerm e
and p_fsTypArg:
  (FStar_Parser_AST.term* FStar_Parser_AST.imp) -> FStar_Pprint.document =
  fun uu____3539  ->
    match uu____3539 with | (e,uu____3543) -> p_indexingTerm e
and p_indexingTerm_aux:
  (FStar_Parser_AST.term -> FStar_Pprint.document) ->
    FStar_Parser_AST.term -> FStar_Pprint.document
  =
  fun exit1  ->
    fun e  ->
      let uu____3548 =
        let uu____3549 = unparen e in uu____3549.FStar_Parser_AST.tm in
      match uu____3548 with
      | FStar_Parser_AST.Op
          ({ FStar_Ident.idText = ".()"; FStar_Ident.idRange = uu____3550;_},e1::e2::[])
          ->
          let uu____3554 =
            let uu____3555 = p_indexingTerm_aux p_atomicTermNotQUident e1 in
            let uu____3556 =
              let uu____3557 =
                let uu____3558 = p_term e2 in
                soft_parens_with_nesting uu____3558 in
              FStar_Pprint.op_Hat_Hat FStar_Pprint.dot uu____3557 in
            FStar_Pprint.op_Hat_Hat uu____3555 uu____3556 in
          FStar_Pprint.group uu____3554
      | FStar_Parser_AST.Op
          ({ FStar_Ident.idText = ".[]"; FStar_Ident.idRange = uu____3559;_},e1::e2::[])
          ->
          let uu____3563 =
            let uu____3564 = p_indexingTerm_aux p_atomicTermNotQUident e1 in
            let uu____3565 =
              let uu____3566 =
                let uu____3567 = p_term e2 in
                soft_brackets_with_nesting uu____3567 in
              FStar_Pprint.op_Hat_Hat FStar_Pprint.dot uu____3566 in
            FStar_Pprint.op_Hat_Hat uu____3564 uu____3565 in
          FStar_Pprint.group uu____3563
      | uu____3568 -> exit1 e
and p_indexingTerm: FStar_Parser_AST.term -> FStar_Pprint.document =
  fun e  -> p_indexingTerm_aux p_atomicTerm e
and p_atomicTerm: FStar_Parser_AST.term -> FStar_Pprint.document =
  fun e  ->
    let uu____3571 =
      let uu____3572 = unparen e in uu____3572.FStar_Parser_AST.tm in
    match uu____3571 with
    | FStar_Parser_AST.LetOpen (lid,e1) ->
        let uu____3575 = p_quident lid in
        let uu____3576 =
          let uu____3577 =
            let uu____3578 = p_term e1 in soft_parens_with_nesting uu____3578 in
          FStar_Pprint.op_Hat_Hat FStar_Pprint.dot uu____3577 in
        FStar_Pprint.op_Hat_Hat uu____3575 uu____3576
    | FStar_Parser_AST.Name lid -> p_quident lid
    | FStar_Parser_AST.Op (op,e1::[]) when is_general_prefix_op op ->
        let uu____3583 = str (FStar_Ident.text_of_id op) in
        let uu____3584 = p_atomicTerm e1 in
        FStar_Pprint.op_Hat_Hat uu____3583 uu____3584
    | uu____3585 -> p_atomicTermNotQUident e
and p_atomicTermNotQUident: FStar_Parser_AST.term -> FStar_Pprint.document =
  fun e  ->
    let uu____3587 =
      let uu____3588 = unparen e in uu____3588.FStar_Parser_AST.tm in
    match uu____3587 with
    | FStar_Parser_AST.Wild  -> FStar_Pprint.underscore
    | FStar_Parser_AST.Var lid when
        FStar_Ident.lid_equals lid FStar_Parser_Const.assert_lid ->
        str "assert"
    | FStar_Parser_AST.Tvar tv -> p_tvar tv
    | FStar_Parser_AST.Const c ->
        (match c with
         | FStar_Const.Const_char x when x = '\n' -> str "0x0Az"
         | uu____3593 -> p_constant c)
    | FStar_Parser_AST.Name lid when
        FStar_Ident.lid_equals lid FStar_Parser_Const.true_lid -> str "True"
    | FStar_Parser_AST.Name lid when
        FStar_Ident.lid_equals lid FStar_Parser_Const.false_lid ->
        str "False"
    | FStar_Parser_AST.Op (op,e1::[]) when is_general_prefix_op op ->
        let uu____3599 = str (FStar_Ident.text_of_id op) in
        let uu____3600 = p_atomicTermNotQUident e1 in
        FStar_Pprint.op_Hat_Hat uu____3599 uu____3600
    | FStar_Parser_AST.Op (op,[]) ->
        let uu____3603 =
          let uu____3604 =
            let uu____3605 = str (FStar_Ident.text_of_id op) in
            let uu____3606 =
              FStar_Pprint.op_Hat_Hat FStar_Pprint.space FStar_Pprint.rparen in
            FStar_Pprint.op_Hat_Hat uu____3605 uu____3606 in
          FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____3604 in
        FStar_Pprint.op_Hat_Hat FStar_Pprint.lparen uu____3603
    | FStar_Parser_AST.Construct (lid,args) when is_dtuple_constructor lid ->
        let uu____3615 =
          FStar_Pprint.op_Hat_Hat FStar_Pprint.lparen FStar_Pprint.bar in
        let uu____3616 =
          let uu____3617 = FStar_Pprint.op_Hat_Hat FStar_Pprint.comma break1 in
          let uu____3618 = FStar_List.map FStar_Pervasives.fst args in
          FStar_Pprint.separate_map uu____3617 p_tmEq uu____3618 in
        let uu____3622 =
          FStar_Pprint.op_Hat_Hat FStar_Pprint.bar FStar_Pprint.rparen in
        FStar_Pprint.surround (Prims.parse_int "2") (Prims.parse_int "1")
          uu____3615 uu____3616 uu____3622
    | FStar_Parser_AST.Project (e1,lid) ->
        let uu____3625 =
          let uu____3626 = p_atomicTermNotQUident e1 in
          let uu____3627 =
            let uu____3628 = p_qlident lid in
            FStar_Pprint.op_Hat_Hat FStar_Pprint.dot uu____3628 in
          FStar_Pprint.prefix (Prims.parse_int "2") (Prims.parse_int "0")
            uu____3626 uu____3627 in
        FStar_Pprint.group uu____3625
    | uu____3629 -> p_projectionLHS e
and p_projectionLHS: FStar_Parser_AST.term -> FStar_Pprint.document =
  fun e  ->
    let uu____3631 =
      let uu____3632 = unparen e in uu____3632.FStar_Parser_AST.tm in
    match uu____3631 with
    | FStar_Parser_AST.Var lid -> p_qlident lid
    | FStar_Parser_AST.Projector (constr_lid,field_lid) ->
        let uu____3636 = p_quident constr_lid in
        let uu____3637 =
          let uu____3638 =
            let uu____3639 = p_lident field_lid in
            FStar_Pprint.op_Hat_Hat FStar_Pprint.dot uu____3639 in
          FStar_Pprint.op_Hat_Hat FStar_Pprint.qmark uu____3638 in
        FStar_Pprint.op_Hat_Hat uu____3636 uu____3637
    | FStar_Parser_AST.Discrim constr_lid ->
        let uu____3641 = p_quident constr_lid in
        FStar_Pprint.op_Hat_Hat uu____3641 FStar_Pprint.qmark
    | FStar_Parser_AST.Paren e1 ->
        let uu____3643 = p_term e1 in soft_parens_with_nesting uu____3643
    | uu____3644 when is_array e ->
        let es = extract_from_list e in
        let uu____3647 =
          FStar_Pprint.op_Hat_Hat FStar_Pprint.lbracket FStar_Pprint.bar in
        let uu____3648 =
          let uu____3649 = FStar_Pprint.op_Hat_Hat FStar_Pprint.semi break1 in
          separate_map_or_flow uu____3649 p_noSeqTerm es in
        let uu____3650 =
          FStar_Pprint.op_Hat_Hat FStar_Pprint.bar FStar_Pprint.rbracket in
        FStar_Pprint.surround (Prims.parse_int "2") (Prims.parse_int "0")
          uu____3647 uu____3648 uu____3650
    | uu____3651 when is_list e ->
        let uu____3652 =
          let uu____3653 = FStar_Pprint.op_Hat_Hat FStar_Pprint.semi break1 in
          let uu____3654 = extract_from_list e in
          separate_map_or_flow uu____3653 p_noSeqTerm uu____3654 in
        FStar_Pprint.surround (Prims.parse_int "2") (Prims.parse_int "0")
          FStar_Pprint.lbracket uu____3652 FStar_Pprint.rbracket
    | uu____3656 when is_lex_list e ->
        let uu____3657 =
          FStar_Pprint.op_Hat_Hat FStar_Pprint.percent FStar_Pprint.lbracket in
        let uu____3658 =
          let uu____3659 = FStar_Pprint.op_Hat_Hat FStar_Pprint.semi break1 in
          let uu____3660 = extract_from_list e in
          separate_map_or_flow uu____3659 p_noSeqTerm uu____3660 in
        FStar_Pprint.surround (Prims.parse_int "2") (Prims.parse_int "1")
          uu____3657 uu____3658 FStar_Pprint.rbracket
    | uu____3662 when is_ref_set e ->
        let es = extract_from_ref_set e in
        let uu____3665 =
          FStar_Pprint.op_Hat_Hat FStar_Pprint.bang FStar_Pprint.lbrace in
        let uu____3666 =
          let uu____3667 = FStar_Pprint.op_Hat_Hat FStar_Pprint.comma break1 in
          separate_map_or_flow uu____3667 p_appTerm es in
        FStar_Pprint.surround (Prims.parse_int "2") (Prims.parse_int "0")
          uu____3665 uu____3666 FStar_Pprint.rbrace
    | FStar_Parser_AST.Labeled (e1,s,b) ->
        let uu____3671 = FStar_Pprint.break_ (Prims.parse_int "0") in
        let uu____3672 =
          let uu____3673 = str (Prims.strcat "(*" (Prims.strcat s "*)")) in
          let uu____3674 = p_term e1 in
          FStar_Pprint.op_Hat_Slash_Hat uu____3673 uu____3674 in
        FStar_Pprint.op_Hat_Hat uu____3671 uu____3672
    | FStar_Parser_AST.Op (op,args) when
        let uu____3679 = handleable_op op args in
        Prims.op_Negation uu____3679 ->
        let uu____3680 =
          let uu____3681 =
            let uu____3682 =
              let uu____3683 =
                let uu____3684 =
                  FStar_Util.string_of_int (FStar_List.length args) in
                Prims.strcat uu____3684
                  " arguments couldn't be handled by the pretty printer" in
              Prims.strcat " with " uu____3683 in
            Prims.strcat (FStar_Ident.text_of_id op) uu____3682 in
          Prims.strcat "Operation " uu____3681 in
        failwith uu____3680
    | FStar_Parser_AST.Uvar uu____3688 ->
        failwith "Unexpected universe variable out of universe context"
    | FStar_Parser_AST.Wild  ->
        let uu____3689 = p_term e in soft_parens_with_nesting uu____3689
    | FStar_Parser_AST.Const uu____3690 ->
        let uu____3691 = p_term e in soft_parens_with_nesting uu____3691
    | FStar_Parser_AST.Op uu____3692 ->
        let uu____3696 = p_term e in soft_parens_with_nesting uu____3696
    | FStar_Parser_AST.Tvar uu____3697 ->
        let uu____3698 = p_term e in soft_parens_with_nesting uu____3698
    | FStar_Parser_AST.Var uu____3699 ->
        let uu____3700 = p_term e in soft_parens_with_nesting uu____3700
    | FStar_Parser_AST.Name uu____3701 ->
        let uu____3702 = p_term e in soft_parens_with_nesting uu____3702
    | FStar_Parser_AST.Construct uu____3703 ->
        let uu____3709 = p_term e in soft_parens_with_nesting uu____3709
    | FStar_Parser_AST.Abs uu____3710 ->
        let uu____3714 = p_term e in soft_parens_with_nesting uu____3714
    | FStar_Parser_AST.App uu____3715 ->
        let uu____3719 = p_term e in soft_parens_with_nesting uu____3719
    | FStar_Parser_AST.Let uu____3720 ->
        let uu____3727 = p_term e in soft_parens_with_nesting uu____3727
    | FStar_Parser_AST.LetOpen uu____3728 ->
        let uu____3731 = p_term e in soft_parens_with_nesting uu____3731
    | FStar_Parser_AST.Seq uu____3732 ->
        let uu____3735 = p_term e in soft_parens_with_nesting uu____3735
    | FStar_Parser_AST.Bind uu____3736 ->
        let uu____3740 = p_term e in soft_parens_with_nesting uu____3740
    | FStar_Parser_AST.If uu____3741 ->
        let uu____3745 = p_term e in soft_parens_with_nesting uu____3745
    | FStar_Parser_AST.Match uu____3746 ->
        let uu____3754 = p_term e in soft_parens_with_nesting uu____3754
    | FStar_Parser_AST.TryWith uu____3755 ->
        let uu____3763 = p_term e in soft_parens_with_nesting uu____3763
    | FStar_Parser_AST.Ascribed uu____3764 ->
        let uu____3769 = p_term e in soft_parens_with_nesting uu____3769
    | FStar_Parser_AST.Record uu____3770 ->
        let uu____3777 = p_term e in soft_parens_with_nesting uu____3777
    | FStar_Parser_AST.Project uu____3778 ->
        let uu____3781 = p_term e in soft_parens_with_nesting uu____3781
    | FStar_Parser_AST.Product uu____3782 ->
        let uu____3786 = p_term e in soft_parens_with_nesting uu____3786
    | FStar_Parser_AST.Sum uu____3787 ->
        let uu____3791 = p_term e in soft_parens_with_nesting uu____3791
    | FStar_Parser_AST.QForall uu____3792 ->
        let uu____3799 = p_term e in soft_parens_with_nesting uu____3799
    | FStar_Parser_AST.QExists uu____3800 ->
        let uu____3807 = p_term e in soft_parens_with_nesting uu____3807
    | FStar_Parser_AST.Refine uu____3808 ->
        let uu____3811 = p_term e in soft_parens_with_nesting uu____3811
    | FStar_Parser_AST.NamedTyp uu____3812 ->
        let uu____3815 = p_term e in soft_parens_with_nesting uu____3815
    | FStar_Parser_AST.Requires uu____3816 ->
        let uu____3820 = p_term e in soft_parens_with_nesting uu____3820
    | FStar_Parser_AST.Ensures uu____3821 ->
        let uu____3825 = p_term e in soft_parens_with_nesting uu____3825
    | FStar_Parser_AST.Assign uu____3826 ->
        let uu____3829 = p_term e in soft_parens_with_nesting uu____3829
    | FStar_Parser_AST.Attributes uu____3830 ->
        let uu____3832 = p_term e in soft_parens_with_nesting uu____3832
and p_constant: FStar_Const.sconst -> FStar_Pprint.document =
  fun uu___108_3833  ->
    match uu___108_3833 with
    | FStar_Const.Const_effect  -> str "Effect"
    | FStar_Const.Const_unit  -> str "()"
    | FStar_Const.Const_bool b -> FStar_Pprint.doc_of_bool b
    | FStar_Const.Const_float x -> str (FStar_Util.string_of_float x)
    | FStar_Const.Const_char x ->
        let uu____3837 = FStar_Pprint.doc_of_char x in
        FStar_Pprint.squotes uu____3837
    | FStar_Const.Const_string (bytes,uu____3839) ->
        let uu____3842 = str (FStar_Util.string_of_bytes bytes) in
        FStar_Pprint.dquotes uu____3842
    | FStar_Const.Const_bytearray (bytes,uu____3844) ->
        let uu____3847 =
          let uu____3848 = str (FStar_Util.string_of_bytes bytes) in
          FStar_Pprint.dquotes uu____3848 in
        let uu____3849 = str "B" in
        FStar_Pprint.op_Hat_Hat uu____3847 uu____3849
    | FStar_Const.Const_int (repr,sign_width_opt) ->
        let signedness uu___106_3861 =
          match uu___106_3861 with
          | FStar_Const.Unsigned  -> str "u"
          | FStar_Const.Signed  -> FStar_Pprint.empty in
        let width uu___107_3865 =
          match uu___107_3865 with
          | FStar_Const.Int8  -> str "y"
          | FStar_Const.Int16  -> str "s"
          | FStar_Const.Int32  -> str "l"
          | FStar_Const.Int64  -> str "L" in
        let ending =
          default_or_map FStar_Pprint.empty
            (fun uu____3869  ->
               match uu____3869 with
               | (s,w) ->
                   let uu____3874 = signedness s in
                   let uu____3875 = width w in
                   FStar_Pprint.op_Hat_Hat uu____3874 uu____3875)
            sign_width_opt in
        let uu____3876 = str repr in
        FStar_Pprint.op_Hat_Hat uu____3876 ending
    | FStar_Const.Const_range r ->
        let uu____3878 = FStar_Range.string_of_range r in str uu____3878
    | FStar_Const.Const_reify  -> str "reify"
    | FStar_Const.Const_reflect lid ->
        let uu____3880 = p_quident lid in
        let uu____3881 =
          let uu____3882 =
            let uu____3883 = str "reflect" in
            FStar_Pprint.op_Hat_Hat FStar_Pprint.dot uu____3883 in
          FStar_Pprint.op_Hat_Hat FStar_Pprint.qmark uu____3882 in
        FStar_Pprint.op_Hat_Hat uu____3880 uu____3881
and p_universe: FStar_Parser_AST.term -> FStar_Pprint.document =
  fun u  ->
    let uu____3885 = str "u#" in
    let uu____3886 = p_atomicUniverse u in
    FStar_Pprint.op_Hat_Hat uu____3885 uu____3886
and p_universeFrom: FStar_Parser_AST.term -> FStar_Pprint.document =
  fun u  ->
    let uu____3888 =
      let uu____3889 = unparen u in uu____3889.FStar_Parser_AST.tm in
    match uu____3888 with
    | FStar_Parser_AST.Op
        ({ FStar_Ident.idText = "+"; FStar_Ident.idRange = uu____3890;_},u1::u2::[])
        ->
        let uu____3894 =
          let uu____3895 = p_universeFrom u1 in
          let uu____3896 =
            let uu____3897 = p_universeFrom u2 in
            FStar_Pprint.op_Hat_Slash_Hat FStar_Pprint.plus uu____3897 in
          FStar_Pprint.op_Hat_Slash_Hat uu____3895 uu____3896 in
        FStar_Pprint.group uu____3894
    | FStar_Parser_AST.App uu____3898 ->
        let uu____3902 = head_and_args u in
        (match uu____3902 with
         | (head1,args) ->
             let uu____3916 =
               let uu____3917 = unparen head1 in
               uu____3917.FStar_Parser_AST.tm in
             (match uu____3916 with
              | FStar_Parser_AST.Var maybe_max_lid when
                  FStar_Ident.lid_equals maybe_max_lid
                    FStar_Parser_Const.max_lid
                  ->
                  let uu____3919 =
                    let uu____3920 = p_qlident FStar_Parser_Const.max_lid in
                    let uu____3921 =
                      FStar_Pprint.separate_map FStar_Pprint.space
                        (fun uu____3924  ->
                           match uu____3924 with
                           | (u1,uu____3928) -> p_atomicUniverse u1) args in
                    op_Hat_Slash_Plus_Hat uu____3920 uu____3921 in
                  FStar_Pprint.group uu____3919
              | uu____3929 ->
                  let uu____3930 =
                    let uu____3931 = FStar_Parser_AST.term_to_string u in
                    FStar_Util.format1 "Invalid term in universe context %s"
                      uu____3931 in
                  failwith uu____3930))
    | uu____3932 -> p_atomicUniverse u
and p_atomicUniverse: FStar_Parser_AST.term -> FStar_Pprint.document =
  fun u  ->
    let uu____3934 =
      let uu____3935 = unparen u in uu____3935.FStar_Parser_AST.tm in
    match uu____3934 with
    | FStar_Parser_AST.Wild  -> FStar_Pprint.underscore
    | FStar_Parser_AST.Const (FStar_Const.Const_int (r,sw)) ->
        p_constant (FStar_Const.Const_int (r, sw))
    | FStar_Parser_AST.Uvar uu____3947 -> p_univar u
    | FStar_Parser_AST.Paren u1 ->
        let uu____3949 = p_universeFrom u1 in
        soft_parens_with_nesting uu____3949
    | FStar_Parser_AST.Op
        ({ FStar_Ident.idText = "+"; FStar_Ident.idRange = uu____3950;_},uu____3951::uu____3952::[])
        ->
        let uu____3954 = p_universeFrom u in
        soft_parens_with_nesting uu____3954
    | FStar_Parser_AST.App uu____3955 ->
        let uu____3959 = p_universeFrom u in
        soft_parens_with_nesting uu____3959
    | uu____3960 ->
        let uu____3961 =
          let uu____3962 = FStar_Parser_AST.term_to_string u in
          FStar_Util.format1 "Invalid term in universe context %s" uu____3962 in
        failwith uu____3961
and p_univar: FStar_Parser_AST.term -> FStar_Pprint.document =
  fun u  ->
    let uu____3964 =
      let uu____3965 = unparen u in uu____3965.FStar_Parser_AST.tm in
    match uu____3964 with
    | FStar_Parser_AST.Uvar id -> str (FStar_Ident.text_of_id id)
    | uu____3967 ->
        let uu____3968 =
          let uu____3969 = FStar_Parser_AST.term_to_string u in
          FStar_Util.format1 "Not a universe variable %s" uu____3969 in
        failwith uu____3968
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
       | FStar_Parser_AST.Module (uu____3989,decls) ->
           let uu____3993 =
             FStar_All.pipe_right decls (FStar_List.map decl_to_document) in
           FStar_All.pipe_right uu____3993
             (FStar_Pprint.separate FStar_Pprint.hardline)
       | FStar_Parser_AST.Interface (uu____3998,decls,uu____4000) ->
           let uu____4003 =
             FStar_All.pipe_right decls (FStar_List.map decl_to_document) in
           FStar_All.pipe_right uu____4003
             (FStar_Pprint.separate FStar_Pprint.hardline) in
     FStar_ST.write should_print_fs_typ_app false; res)
let comments_to_document:
  (Prims.string* FStar_Range.range) Prims.list -> FStar_Pprint.document =
  fun comments  ->
    FStar_Pprint.separate_map FStar_Pprint.hardline
      (fun uu____4022  ->
         match uu____4022 with | (comment,range) -> str comment) comments
let modul_with_comments_to_document:
  FStar_Parser_AST.modul ->
    (Prims.string* FStar_Range.range) Prims.list ->
      (FStar_Pprint.document* (Prims.string* FStar_Range.range) Prims.list)
  =
  fun m  ->
    fun comments  ->
      let decls =
        match m with
        | FStar_Parser_AST.Module (uu____4047,decls) -> decls
        | FStar_Parser_AST.Interface (uu____4051,decls,uu____4053) -> decls in
      FStar_ST.write should_print_fs_typ_app false;
      (match decls with
       | [] -> (FStar_Pprint.empty, comments)
       | d::ds ->
           let uu____4070 =
             match ds with
             | {
                 FStar_Parser_AST.d = FStar_Parser_AST.Pragma
                   (FStar_Parser_AST.LightOff );
                 FStar_Parser_AST.drange = uu____4077;
                 FStar_Parser_AST.doc = uu____4078;
                 FStar_Parser_AST.quals = uu____4079;
                 FStar_Parser_AST.attrs = uu____4080;_}::uu____4081 ->
                 let d0 = FStar_List.hd ds in
                 let uu____4085 =
                   let uu____4087 =
                     let uu____4089 = FStar_List.tl ds in d :: uu____4089 in
                   d0 :: uu____4087 in
                 (uu____4085, (d0.FStar_Parser_AST.drange))
             | uu____4092 -> ((d :: ds), (d.FStar_Parser_AST.drange)) in
           (match uu____4070 with
            | (decls1,first_range) ->
                let extract_decl_range d1 = d1.FStar_Parser_AST.drange in
                (FStar_ST.write comment_stack comments;
                 (let initial_comment =
                    let uu____4115 = FStar_Range.start_of_range first_range in
                    place_comments_until_pos (Prims.parse_int "0")
                      (Prims.parse_int "1") uu____4115 FStar_Pprint.empty in
                  let doc1 =
                    separate_map_with_comments FStar_Pprint.empty
                      FStar_Pprint.empty decl_to_document decls1
                      extract_decl_range in
                  let comments1 = FStar_ST.read comment_stack in
                  FStar_ST.write comment_stack [];
                  FStar_ST.write should_print_fs_typ_app false;
                  (let uu____4137 =
                     FStar_Pprint.op_Hat_Hat initial_comment doc1 in
                   (uu____4137, comments1))))))