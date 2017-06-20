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
         let uu____174 =
           let uu____175 =
             let uu____176 = f x in
             FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____176 in
           FStar_Pprint.op_Hat_Hat sep uu____175 in
         FStar_Pprint.op_Hat_Hat break1 uu____174) uu____169 in
  FStar_Pprint.op_Hat_Hat uu____164 uu____168
let concat_break_map f l =
  let uu____196 =
    FStar_Pprint.concat_map
      (fun x  ->
         let uu____200 = f x in FStar_Pprint.op_Hat_Hat uu____200 break1) l in
  FStar_Pprint.group uu____196
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
    let uu____222 = str "begin" in
    let uu____223 = str "end" in
    FStar_Pprint.soft_surround (Prims.parse_int "2") (Prims.parse_int "1")
      uu____222 contents uu____223
let separate_map_or_flow sep f l =
  if (FStar_List.length l) < (Prims.parse_int "10")
  then FStar_Pprint.separate_map sep f l
  else FStar_Pprint.flow_map sep f l
let soft_surround_separate_map n1 b void_ opening sep closing f xs =
  if xs = []
  then void_
  else
    (let uu____303 = FStar_Pprint.separate_map sep f xs in
     FStar_Pprint.soft_surround n1 b opening uu____303 closing)
let doc_of_fsdoc:
  (Prims.string* (Prims.string* Prims.string) Prims.list) ->
    FStar_Pprint.document
  =
  fun uu____311  ->
    match uu____311 with
    | (comment,keywords1) ->
        let uu____325 =
          let uu____326 =
            let uu____328 = str comment in
            let uu____329 =
              let uu____331 =
                let uu____333 =
                  FStar_Pprint.separate_map FStar_Pprint.comma
                    (fun uu____340  ->
                       match uu____340 with
                       | (k,v1) ->
                           let uu____345 =
                             let uu____347 = str k in
                             let uu____348 =
                               let uu____350 =
                                 let uu____352 = str v1 in [uu____352] in
                               FStar_Pprint.rarrow :: uu____350 in
                             uu____347 :: uu____348 in
                           FStar_Pprint.concat uu____345) keywords1 in
                [uu____333] in
              FStar_Pprint.space :: uu____331 in
            uu____328 :: uu____329 in
          FStar_Pprint.concat uu____326 in
        FStar_Pprint.group uu____325
let is_unit: FStar_Parser_AST.term -> Prims.bool =
  fun e  ->
    let uu____356 =
      let uu____357 = unparen e in uu____357.FStar_Parser_AST.tm in
    match uu____356 with
    | FStar_Parser_AST.Const (FStar_Const.Const_unit ) -> true
    | uu____358 -> false
let matches_var: FStar_Parser_AST.term -> FStar_Ident.ident -> Prims.bool =
  fun t  ->
    fun x  ->
      let uu____365 =
        let uu____366 = unparen t in uu____366.FStar_Parser_AST.tm in
      match uu____365 with
      | FStar_Parser_AST.Var y ->
          x.FStar_Ident.idText = (FStar_Ident.text_of_lid y)
      | uu____368 -> false
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
        let uu____385 =
          let uu____386 = unparen e in uu____386.FStar_Parser_AST.tm in
        match uu____385 with
        | FStar_Parser_AST.Construct (lid,[]) ->
            FStar_Ident.lid_equals lid nil_lid1
        | FStar_Parser_AST.Construct (lid,uu____394::(e2,uu____396)::[]) ->
            (FStar_Ident.lid_equals lid cons_lid1) && (aux e2)
        | uu____408 -> false in
      aux
let is_list: FStar_Parser_AST.term -> Prims.bool =
  is_list_structure FStar_Parser_Const.cons_lid FStar_Parser_Const.nil_lid
let is_lex_list: FStar_Parser_AST.term -> Prims.bool =
  is_list_structure FStar_Parser_Const.lexcons_lid
    FStar_Parser_Const.lextop_lid
let rec extract_from_list:
  FStar_Parser_AST.term -> FStar_Parser_AST.term Prims.list =
  fun e  ->
    let uu____417 =
      let uu____418 = unparen e in uu____418.FStar_Parser_AST.tm in
    match uu____417 with
    | FStar_Parser_AST.Construct (uu____420,[]) -> []
    | FStar_Parser_AST.Construct
        (uu____426,(e1,FStar_Parser_AST.Nothing )::(e2,FStar_Parser_AST.Nothing
                                                    )::[])
        -> let uu____438 = extract_from_list e2 in e1 :: uu____438
    | uu____440 ->
        let uu____441 =
          let uu____442 = FStar_Parser_AST.term_to_string e in
          FStar_Util.format1 "Not a list %s" uu____442 in
        failwith uu____441
let is_array: FStar_Parser_AST.term -> Prims.bool =
  fun e  ->
    let uu____447 =
      let uu____448 = unparen e in uu____448.FStar_Parser_AST.tm in
    match uu____447 with
    | FStar_Parser_AST.App
        ({ FStar_Parser_AST.tm = FStar_Parser_AST.Var lid;
           FStar_Parser_AST.range = uu____450;
           FStar_Parser_AST.level = uu____451;_},l,FStar_Parser_AST.Nothing
         )
        ->
        (FStar_Ident.lid_equals lid FStar_Parser_Const.array_mk_array_lid) &&
          (is_list l)
    | uu____453 -> false
let rec is_ref_set: FStar_Parser_AST.term -> Prims.bool =
  fun e  ->
    let uu____457 =
      let uu____458 = unparen e in uu____458.FStar_Parser_AST.tm in
    match uu____457 with
    | FStar_Parser_AST.Var maybe_empty_lid ->
        FStar_Ident.lid_equals maybe_empty_lid FStar_Parser_Const.tset_empty
    | FStar_Parser_AST.App
        ({ FStar_Parser_AST.tm = FStar_Parser_AST.Var maybe_singleton_lid;
           FStar_Parser_AST.range = uu____461;
           FStar_Parser_AST.level = uu____462;_},{
                                                   FStar_Parser_AST.tm =
                                                     FStar_Parser_AST.App
                                                     ({
                                                        FStar_Parser_AST.tm =
                                                          FStar_Parser_AST.Var
                                                          maybe_ref_lid;
                                                        FStar_Parser_AST.range
                                                          = uu____464;
                                                        FStar_Parser_AST.level
                                                          = uu____465;_},e1,FStar_Parser_AST.Nothing
                                                      );
                                                   FStar_Parser_AST.range =
                                                     uu____467;
                                                   FStar_Parser_AST.level =
                                                     uu____468;_},FStar_Parser_AST.Nothing
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
                FStar_Parser_AST.range = uu____470;
                FStar_Parser_AST.level = uu____471;_},e1,FStar_Parser_AST.Nothing
              );
           FStar_Parser_AST.range = uu____473;
           FStar_Parser_AST.level = uu____474;_},e2,FStar_Parser_AST.Nothing
         )
        ->
        ((FStar_Ident.lid_equals maybe_union_lid
            FStar_Parser_Const.tset_union)
           && (is_ref_set e1))
          && (is_ref_set e2)
    | uu____476 -> false
let rec extract_from_ref_set:
  FStar_Parser_AST.term -> FStar_Parser_AST.term Prims.list =
  fun e  ->
    let uu____481 =
      let uu____482 = unparen e in uu____482.FStar_Parser_AST.tm in
    match uu____481 with
    | FStar_Parser_AST.Var uu____484 -> []
    | FStar_Parser_AST.App
        ({ FStar_Parser_AST.tm = FStar_Parser_AST.Var uu____485;
           FStar_Parser_AST.range = uu____486;
           FStar_Parser_AST.level = uu____487;_},{
                                                   FStar_Parser_AST.tm =
                                                     FStar_Parser_AST.App
                                                     ({
                                                        FStar_Parser_AST.tm =
                                                          FStar_Parser_AST.Var
                                                          uu____488;
                                                        FStar_Parser_AST.range
                                                          = uu____489;
                                                        FStar_Parser_AST.level
                                                          = uu____490;_},e1,FStar_Parser_AST.Nothing
                                                      );
                                                   FStar_Parser_AST.range =
                                                     uu____492;
                                                   FStar_Parser_AST.level =
                                                     uu____493;_},FStar_Parser_AST.Nothing
         )
        -> [e1]
    | FStar_Parser_AST.App
        ({
           FStar_Parser_AST.tm = FStar_Parser_AST.App
             ({ FStar_Parser_AST.tm = FStar_Parser_AST.Var uu____494;
                FStar_Parser_AST.range = uu____495;
                FStar_Parser_AST.level = uu____496;_},e1,FStar_Parser_AST.Nothing
              );
           FStar_Parser_AST.range = uu____498;
           FStar_Parser_AST.level = uu____499;_},e2,FStar_Parser_AST.Nothing
         )
        ->
        let uu____501 = extract_from_ref_set e1 in
        let uu____503 = extract_from_ref_set e2 in
        FStar_List.append uu____501 uu____503
    | uu____505 ->
        let uu____506 =
          let uu____507 = FStar_Parser_AST.term_to_string e in
          FStar_Util.format1 "Not a ref set %s" uu____507 in
        failwith uu____506
let is_general_application: FStar_Parser_AST.term -> Prims.bool =
  fun e  ->
    let uu____512 = (is_array e) || (is_ref_set e) in
    Prims.op_Negation uu____512
let is_general_construction: FStar_Parser_AST.term -> Prims.bool =
  fun e  ->
    let uu____516 = (is_list e) || (is_lex_list e) in
    Prims.op_Negation uu____516
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
      let uu____547 =
        let uu____548 = unparen e1 in uu____548.FStar_Parser_AST.tm in
      match uu____547 with
      | FStar_Parser_AST.App (head1,arg,imp) -> aux head1 ((arg, imp) :: acc)
      | uu____559 -> (e1, acc) in
    aux e []
type associativity =
  | Left
  | Right
  | NonAssoc
let uu___is_Left: associativity -> Prims.bool =
  fun projectee  -> match projectee with | Left  -> true | uu____568 -> false
let uu___is_Right: associativity -> Prims.bool =
  fun projectee  ->
    match projectee with | Right  -> true | uu____572 -> false
let uu___is_NonAssoc: associativity -> Prims.bool =
  fun projectee  ->
    match projectee with | NonAssoc  -> true | uu____576 -> false
type token = (FStar_Char.char,Prims.string) FStar_Util.either
type associativity_level = (associativity* token Prims.list)
let token_to_string:
  (FStar_BaseTypes.char,Prims.string) FStar_Util.either -> Prims.string =
  fun uu___93_586  ->
    match uu___93_586 with
    | FStar_Util.Inl c -> Prims.strcat (FStar_Util.string_of_char c) ".*"
    | FStar_Util.Inr s -> s
let matches_token:
  Prims.string ->
    (FStar_Char.char,Prims.string) FStar_Util.either -> Prims.bool
  =
  fun s  ->
    fun uu___94_598  ->
      match uu___94_598 with
      | FStar_Util.Inl c ->
          let uu____602 = FStar_String.get s (Prims.parse_int "0") in
          uu____602 = c
      | FStar_Util.Inr s' -> s = s'
let matches_level s uu____620 =
  match uu____620 with
  | (assoc_levels,tokens) ->
      let uu____634 = FStar_List.tryFind (matches_token s) tokens in
      uu____634 <> None
let opinfix4 uu____652 = (Right, [FStar_Util.Inr "**"])
let opinfix3 uu____667 =
  (Left, [FStar_Util.Inl '*'; FStar_Util.Inl '/'; FStar_Util.Inl '%'])
let opinfix2 uu____686 = (Left, [FStar_Util.Inl '+'; FStar_Util.Inl '-'])
let minus_lvl uu____703 = (Left, [FStar_Util.Inr "-"])
let opinfix1 uu____718 = (Right, [FStar_Util.Inl '@'; FStar_Util.Inl '^'])
let pipe_right uu____735 = (Left, [FStar_Util.Inr "|>"])
let opinfix0d uu____750 = (Left, [FStar_Util.Inl '$'])
let opinfix0c uu____765 =
  (Left, [FStar_Util.Inl '='; FStar_Util.Inl '<'; FStar_Util.Inl '>'])
let equal uu____784 = (Left, [FStar_Util.Inr "="])
let opinfix0b uu____799 = (Left, [FStar_Util.Inl '&'])
let opinfix0a uu____814 = (Left, [FStar_Util.Inl '|'])
let colon_equals uu____829 = (NonAssoc, [FStar_Util.Inr ":="])
let amp uu____844 = (Right, [FStar_Util.Inr "&"])
let colon_colon uu____859 = (Right, [FStar_Util.Inr "::"])
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
  let levels_from_associativity l uu___95_956 =
    match uu___95_956 with
    | Left  -> (l, l, (l - (Prims.parse_int "1")))
    | Right  -> ((l - (Prims.parse_int "1")), l, l)
    | NonAssoc  -> (l, l, l) in
  FStar_List.mapi
    (fun i  ->
       fun uu____978  ->
         match uu____978 with
         | (assoc1,tokens) -> ((levels_from_associativity i assoc1), tokens))
    level_associativity_spec
let assign_levels:
  associativity_level Prims.list ->
    Prims.string -> (Prims.int* Prims.int* Prims.int)
  =
  fun token_associativity_spec  ->
    fun s  ->
      let uu____1020 = FStar_List.tryFind (matches_level s) level_table in
      match uu____1020 with
      | Some (assoc_levels,uu____1045) -> assoc_levels
      | uu____1066 -> failwith (Prims.strcat "Unrecognized operator " s)
let max: Prims.int -> Prims.int -> Prims.int =
  fun k1  -> fun k2  -> if k1 > k2 then k1 else k2
let max_level l =
  let find_level_and_max n1 level =
    let uu____1122 =
      FStar_List.tryFind
        (fun uu____1143  ->
           match uu____1143 with
           | (uu____1152,tokens) -> tokens = (snd level)) level_table in
    match uu____1122 with
    | Some ((uu____1172,l1,uu____1174),uu____1175) -> max n1 l1
    | None  ->
        let uu____1201 =
          let uu____1202 =
            let uu____1203 = FStar_List.map token_to_string (snd level) in
            FStar_String.concat "," uu____1203 in
          FStar_Util.format1 "Undefined associativity level %s" uu____1202 in
        failwith uu____1201 in
  FStar_List.fold_left find_level_and_max (Prims.parse_int "0") l
let levels: Prims.string -> (Prims.int* Prims.int* Prims.int) =
  assign_levels level_associativity_spec
let operatorInfix0ad12 uu____1228 =
  [opinfix0a ();
  opinfix0b ();
  opinfix0c ();
  opinfix0d ();
  opinfix1 ();
  opinfix2 ()]
let is_operatorInfix0ad12: FStar_Ident.ident -> Prims.bool =
  fun op  ->
    let uu____1267 =
      let uu____1274 =
        FStar_All.pipe_left matches_level (FStar_Ident.text_of_id op) in
      FStar_List.tryFind uu____1274 (operatorInfix0ad12 ()) in
    uu____1267 <> None
let is_operatorInfix34: FStar_Ident.ident -> Prims.bool =
  let opinfix34 = [opinfix3 (); opinfix4 ()] in
  fun op  ->
    let uu____1330 =
      let uu____1337 =
        FStar_All.pipe_left matches_level (FStar_Ident.text_of_id op) in
      FStar_List.tryFind uu____1337 opinfix34 in
    uu____1330 <> None
let handleable_args_length: FStar_Ident.ident -> Prims.int =
  fun op  ->
    let op_s = FStar_Ident.text_of_id op in
    let uu____1372 =
      (is_general_prefix_op op) || (FStar_List.mem op_s ["-"; "~"]) in
    if uu____1372
    then Prims.parse_int "1"
    else
      (let uu____1374 =
         ((is_operatorInfix0ad12 op) || (is_operatorInfix34 op)) ||
           (FStar_List.mem op_s
              ["<==>"; "==>"; "\\/"; "/\\"; "="; "|>"; ":="; ".()"; ".[]"]) in
       if uu____1374
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
  | uu____1392 -> false
let comment_stack: (Prims.string* FStar_Range.range) Prims.list FStar_ST.ref
  = FStar_Util.mk_ref []
let with_comment printer tm tmrange =
  let rec comments_before_pos acc print_pos lookahead_pos =
    let uu____1438 = FStar_ST.read comment_stack in
    match uu____1438 with
    | [] -> (acc, false)
    | (comment,crange)::cs ->
        let uu____1459 = FStar_Range.range_before_pos crange print_pos in
        if uu____1459
        then
          (FStar_ST.write comment_stack cs;
           (let uu____1468 =
              let uu____1469 =
                let uu____1470 = str comment in
                FStar_Pprint.op_Hat_Hat uu____1470 FStar_Pprint.hardline in
              FStar_Pprint.op_Hat_Hat acc uu____1469 in
            comments_before_pos uu____1468 print_pos lookahead_pos))
        else
          (let uu____1472 = FStar_Range.range_before_pos crange lookahead_pos in
           (acc, uu____1472)) in
  let uu____1473 =
    let uu____1476 =
      let uu____1477 = FStar_Range.start_of_range tmrange in
      FStar_Range.end_of_line uu____1477 in
    let uu____1478 = FStar_Range.end_of_range tmrange in
    comments_before_pos FStar_Pprint.empty uu____1476 uu____1478 in
  match uu____1473 with
  | (comments,has_lookahead) ->
      let printed_e = printer tm in
      let comments1 =
        if has_lookahead
        then
          let pos = FStar_Range.end_of_range tmrange in
          let uu____1484 = comments_before_pos comments pos pos in
          fst uu____1484
        else comments in
      let uu____1488 = FStar_Pprint.op_Hat_Hat comments1 printed_e in
      FStar_Pprint.group uu____1488
let rec place_comments_until_pos:
  Prims.int ->
    Prims.int ->
      FStar_Range.pos -> FStar_Pprint.document -> FStar_Pprint.document
  =
  fun k  ->
    fun lbegin  ->
      fun pos_end  ->
        fun doc1  ->
          let uu____1501 = FStar_ST.read comment_stack in
          match uu____1501 with
          | (comment,crange)::cs when
              FStar_Range.range_before_pos crange pos_end ->
              (FStar_ST.write comment_stack cs;
               (let lnum =
                  let uu____1525 =
                    let uu____1526 =
                      let uu____1527 = FStar_Range.start_of_range crange in
                      FStar_Range.line_of_pos uu____1527 in
                    uu____1526 - lbegin in
                  max k uu____1525 in
                let doc2 =
                  let uu____1529 =
                    let uu____1530 =
                      FStar_Pprint.repeat lnum FStar_Pprint.hardline in
                    let uu____1531 = str comment in
                    FStar_Pprint.op_Hat_Hat uu____1530 uu____1531 in
                  FStar_Pprint.op_Hat_Hat doc1 uu____1529 in
                let uu____1532 =
                  let uu____1533 = FStar_Range.end_of_range crange in
                  FStar_Range.line_of_pos uu____1533 in
                place_comments_until_pos (Prims.parse_int "1") uu____1532
                  pos_end doc2))
          | uu____1534 ->
              let lnum =
                let uu____1539 =
                  let uu____1540 = FStar_Range.line_of_pos pos_end in
                  uu____1540 - lbegin in
                max (Prims.parse_int "1") uu____1539 in
              let uu____1541 = FStar_Pprint.repeat lnum FStar_Pprint.hardline in
              FStar_Pprint.op_Hat_Hat doc1 uu____1541
let separate_map_with_comments prefix1 sep f xs extract_range =
  let fold_fun uu____1590 x =
    match uu____1590 with
    | (last_line,doc1) ->
        let r = extract_range x in
        let doc2 =
          let uu____1600 = FStar_Range.start_of_range r in
          place_comments_until_pos (Prims.parse_int "1") last_line uu____1600
            doc1 in
        let uu____1601 =
          let uu____1602 = FStar_Range.end_of_range r in
          FStar_Range.line_of_pos uu____1602 in
        let uu____1603 =
          let uu____1604 =
            let uu____1605 = f x in FStar_Pprint.op_Hat_Hat sep uu____1605 in
          FStar_Pprint.op_Hat_Hat doc2 uu____1604 in
        (uu____1601, uu____1603) in
  let uu____1606 =
    let uu____1610 = FStar_List.hd xs in
    let uu____1611 = FStar_List.tl xs in (uu____1610, uu____1611) in
  match uu____1606 with
  | (x,xs1) ->
      let init1 =
        let uu____1621 =
          let uu____1622 =
            let uu____1623 = extract_range x in
            FStar_Range.end_of_range uu____1623 in
          FStar_Range.line_of_pos uu____1622 in
        let uu____1624 =
          let uu____1625 = f x in FStar_Pprint.op_Hat_Hat prefix1 uu____1625 in
        (uu____1621, uu____1624) in
      let uu____1626 = FStar_List.fold_left fold_fun init1 xs1 in
      snd uu____1626
let rec p_decl: FStar_Parser_AST.decl -> FStar_Pprint.document =
  fun d  ->
    let uu____1872 =
      let uu____1873 = FStar_Pprint.optional p_fsdoc d.FStar_Parser_AST.doc in
      let uu____1874 =
        let uu____1875 = p_attributes d.FStar_Parser_AST.attrs in
        let uu____1876 =
          let uu____1877 = p_qualifiers d.FStar_Parser_AST.quals in
          let uu____1878 =
            let uu____1879 = p_rawDecl d in
            FStar_Pprint.op_Hat_Hat
              (if d.FStar_Parser_AST.quals = []
               then FStar_Pprint.empty
               else break1) uu____1879 in
          FStar_Pprint.op_Hat_Hat uu____1877 uu____1878 in
        FStar_Pprint.op_Hat_Hat uu____1875 uu____1876 in
      FStar_Pprint.op_Hat_Hat uu____1873 uu____1874 in
    FStar_Pprint.group uu____1872
and p_attributes: FStar_Parser_AST.attributes_ -> FStar_Pprint.document =
  fun attrs  ->
    let uu____1882 =
      let uu____1883 = str "@" in
      FStar_Pprint.op_Hat_Hat FStar_Pprint.lbracket uu____1883 in
    let uu____1884 =
      FStar_Pprint.op_Hat_Hat FStar_Pprint.rbracket FStar_Pprint.hardline in
    soft_surround_separate_map (Prims.parse_int "0") (Prims.parse_int "2")
      FStar_Pprint.empty uu____1882 FStar_Pprint.space uu____1884
      p_atomicTerm attrs
and p_fsdoc: FStar_Parser_AST.fsdoc -> FStar_Pprint.document =
  fun uu____1885  ->
    match uu____1885 with
    | (doc1,kwd_args) ->
        let kwd_args_doc =
          match kwd_args with
          | [] -> FStar_Pprint.empty
          | kwd_args1 ->
              let process_kwd_arg uu____1906 =
                match uu____1906 with
                | (kwd1,arg) ->
                    let uu____1911 = str "@" in
                    let uu____1912 =
                      let uu____1913 = str kwd1 in
                      let uu____1914 =
                        let uu____1915 = str arg in
                        FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____1915 in
                      FStar_Pprint.op_Hat_Hat uu____1913 uu____1914 in
                    FStar_Pprint.op_Hat_Hat uu____1911 uu____1912 in
              let uu____1916 =
                let uu____1917 =
                  FStar_Pprint.separate_map FStar_Pprint.hardline
                    process_kwd_arg kwd_args1 in
                FStar_Pprint.op_Hat_Hat uu____1917 FStar_Pprint.hardline in
              FStar_Pprint.op_Hat_Hat FStar_Pprint.hardline uu____1916 in
        let uu____1920 =
          let uu____1921 =
            let uu____1922 =
              let uu____1923 =
                let uu____1924 = str doc1 in
                let uu____1925 =
                  let uu____1926 =
                    let uu____1927 =
                      FStar_Pprint.op_Hat_Hat FStar_Pprint.rparen
                        FStar_Pprint.hardline in
                    FStar_Pprint.op_Hat_Hat FStar_Pprint.star uu____1927 in
                  FStar_Pprint.op_Hat_Hat kwd_args_doc uu____1926 in
                FStar_Pprint.op_Hat_Hat uu____1924 uu____1925 in
              FStar_Pprint.op_Hat_Hat FStar_Pprint.star uu____1923 in
            FStar_Pprint.op_Hat_Hat FStar_Pprint.star uu____1922 in
          FStar_Pprint.op_Hat_Hat FStar_Pprint.lparen uu____1921 in
        FStar_Pprint.op_Hat_Hat FStar_Pprint.hardline uu____1920
and p_rawDecl: FStar_Parser_AST.decl -> FStar_Pprint.document =
  fun d  ->
    match d.FStar_Parser_AST.d with
    | FStar_Parser_AST.Open uid ->
        let uu____1930 =
          let uu____1931 = str "open" in
          let uu____1932 = p_quident uid in
          FStar_Pprint.op_Hat_Slash_Hat uu____1931 uu____1932 in
        FStar_Pprint.group uu____1930
    | FStar_Parser_AST.Include uid ->
        let uu____1934 =
          let uu____1935 = str "include" in
          let uu____1936 = p_quident uid in
          FStar_Pprint.op_Hat_Slash_Hat uu____1935 uu____1936 in
        FStar_Pprint.group uu____1934
    | FStar_Parser_AST.ModuleAbbrev (uid1,uid2) ->
        let uu____1939 =
          let uu____1940 = str "module" in
          let uu____1941 =
            let uu____1942 =
              let uu____1943 = p_uident uid1 in
              let uu____1944 =
                FStar_Pprint.op_Hat_Hat FStar_Pprint.space
                  FStar_Pprint.equals in
              FStar_Pprint.op_Hat_Hat uu____1943 uu____1944 in
            FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____1942 in
          FStar_Pprint.op_Hat_Hat uu____1940 uu____1941 in
        let uu____1945 = p_quident uid2 in
        op_Hat_Slash_Plus_Hat uu____1939 uu____1945
    | FStar_Parser_AST.TopLevelModule uid ->
        let uu____1947 =
          let uu____1948 = str "module" in
          let uu____1949 =
            let uu____1950 = p_quident uid in
            FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____1950 in
          FStar_Pprint.op_Hat_Hat uu____1948 uu____1949 in
        FStar_Pprint.group uu____1947
    | FStar_Parser_AST.Tycon
        (true ,(FStar_Parser_AST.TyconAbbrev (uid,tpars,None ,t),None )::[])
        ->
        let effect_prefix_doc =
          let uu____1969 = str "effect" in
          let uu____1970 =
            let uu____1971 = p_uident uid in
            FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____1971 in
          FStar_Pprint.op_Hat_Hat uu____1969 uu____1970 in
        let uu____1972 =
          let uu____1973 = p_typars tpars in
          FStar_Pprint.surround (Prims.parse_int "2") (Prims.parse_int "1")
            effect_prefix_doc uu____1973 FStar_Pprint.equals in
        let uu____1974 = p_typ t in
        op_Hat_Slash_Plus_Hat uu____1972 uu____1974
    | FStar_Parser_AST.Tycon (false ,tcdefs) ->
        let uu____1984 = str "type" in
        let uu____1985 = str "and" in
        precede_break_separate_map uu____1984 uu____1985 p_fsdocTypeDeclPairs
          tcdefs
    | FStar_Parser_AST.TopLevelLet (q,lbs) ->
        let let_doc =
          let uu____1998 = str "let" in
          let uu____1999 =
            let uu____2000 = p_letqualifier q in
            FStar_Pprint.op_Hat_Hat uu____2000 FStar_Pprint.space in
          FStar_Pprint.op_Hat_Hat uu____1998 uu____1999 in
        let uu____2001 =
          let uu____2002 = str "and" in
          FStar_Pprint.op_Hat_Hat uu____2002 FStar_Pprint.space in
        separate_map_with_comments let_doc uu____2001 p_letbinding lbs
          (fun uu____2008  ->
             match uu____2008 with
             | (p,t) ->
                 FStar_Range.union_ranges p.FStar_Parser_AST.prange
                   t.FStar_Parser_AST.range)
    | FStar_Parser_AST.Val (lid,t) ->
        let uu____2015 =
          let uu____2016 = str "val" in
          let uu____2017 =
            let uu____2018 =
              let uu____2019 = p_lident lid in
              let uu____2020 =
                FStar_Pprint.op_Hat_Hat FStar_Pprint.space FStar_Pprint.colon in
              FStar_Pprint.op_Hat_Hat uu____2019 uu____2020 in
            FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____2018 in
          FStar_Pprint.op_Hat_Hat uu____2016 uu____2017 in
        let uu____2021 = p_typ t in
        op_Hat_Slash_Plus_Hat uu____2015 uu____2021
    | FStar_Parser_AST.Assume (id,t) ->
        let decl_keyword =
          let uu____2025 =
            let uu____2026 =
              FStar_Util.char_at id.FStar_Ident.idText (Prims.parse_int "0") in
            FStar_All.pipe_right uu____2026 FStar_Util.is_upper in
          if uu____2025
          then FStar_Pprint.empty
          else
            (let uu____2028 = str "val" in
             FStar_Pprint.op_Hat_Hat uu____2028 FStar_Pprint.space) in
        let uu____2029 =
          let uu____2030 =
            let uu____2031 = p_ident id in
            let uu____2032 =
              FStar_Pprint.op_Hat_Hat FStar_Pprint.space FStar_Pprint.colon in
            FStar_Pprint.op_Hat_Hat uu____2031 uu____2032 in
          FStar_Pprint.op_Hat_Hat decl_keyword uu____2030 in
        let uu____2033 = p_typ t in
        op_Hat_Slash_Plus_Hat uu____2029 uu____2033
    | FStar_Parser_AST.Exception (uid,t_opt) ->
        let uu____2038 = str "exception" in
        let uu____2039 =
          let uu____2040 =
            let uu____2041 = p_uident uid in
            let uu____2042 =
              FStar_Pprint.optional
                (fun t  ->
                   let uu____2047 = str "of" in
                   let uu____2048 = p_typ t in
                   op_Hat_Slash_Plus_Hat uu____2047 uu____2048) t_opt in
            FStar_Pprint.op_Hat_Hat uu____2041 uu____2042 in
          FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____2040 in
        FStar_Pprint.op_Hat_Hat uu____2038 uu____2039
    | FStar_Parser_AST.NewEffect ne ->
        let uu____2050 = str "new_effect" in
        let uu____2051 =
          let uu____2052 = p_newEffect ne in
          FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____2052 in
        FStar_Pprint.op_Hat_Hat uu____2050 uu____2051
    | FStar_Parser_AST.SubEffect se ->
        let uu____2054 = str "sub_effect" in
        let uu____2055 =
          let uu____2056 = p_subEffect se in
          FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____2056 in
        FStar_Pprint.op_Hat_Hat uu____2054 uu____2055
    | FStar_Parser_AST.Pragma p -> p_pragma p
    | FStar_Parser_AST.Fsdoc doc1 ->
        let uu____2059 = p_fsdoc doc1 in
        FStar_Pprint.op_Hat_Hat uu____2059 FStar_Pprint.hardline
    | FStar_Parser_AST.Main uu____2060 ->
        failwith "*Main declaration* : Is that really still in use ??"
    | FStar_Parser_AST.Tycon (true ,uu____2061) ->
        failwith
          "Effect abbreviation is expected to be defined by an abbreviation"
and p_pragma: FStar_Parser_AST.pragma -> FStar_Pprint.document =
  fun uu___96_2070  ->
    match uu___96_2070 with
    | FStar_Parser_AST.SetOptions s ->
        let uu____2072 = str "#set-options" in
        let uu____2073 =
          let uu____2074 =
            let uu____2075 = str s in FStar_Pprint.dquotes uu____2075 in
          FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____2074 in
        FStar_Pprint.op_Hat_Hat uu____2072 uu____2073
    | FStar_Parser_AST.ResetOptions s_opt ->
        let uu____2078 = str "#reset-options" in
        let uu____2079 =
          FStar_Pprint.optional
            (fun s  ->
               let uu____2083 =
                 let uu____2084 = str s in FStar_Pprint.dquotes uu____2084 in
               FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____2083) s_opt in
        FStar_Pprint.op_Hat_Hat uu____2078 uu____2079
    | FStar_Parser_AST.LightOff  ->
        (FStar_ST.write should_print_fs_typ_app true; str "#light \"off\"")
and p_typars: FStar_Parser_AST.binder Prims.list -> FStar_Pprint.document =
  fun bs  -> p_binders true bs
and p_fsdocTypeDeclPairs:
  (FStar_Parser_AST.tycon* FStar_Parser_AST.fsdoc option) ->
    FStar_Pprint.document
  =
  fun uu____2090  ->
    match uu____2090 with
    | (typedecl,fsdoc_opt) ->
        let uu____2098 = FStar_Pprint.optional p_fsdoc fsdoc_opt in
        let uu____2099 = p_typeDecl typedecl in
        FStar_Pprint.op_Hat_Hat uu____2098 uu____2099
and p_typeDecl: FStar_Parser_AST.tycon -> FStar_Pprint.document =
  fun uu___97_2100  ->
    match uu___97_2100 with
    | FStar_Parser_AST.TyconAbstract (lid,bs,typ_opt) ->
        let empty' uu____2111 = FStar_Pprint.empty in
        p_typeDeclPrefix lid bs typ_opt empty'
    | FStar_Parser_AST.TyconAbbrev (lid,bs,typ_opt,t) ->
        let f uu____2123 =
          let uu____2124 = p_typ t in prefix2 FStar_Pprint.equals uu____2124 in
        p_typeDeclPrefix lid bs typ_opt f
    | FStar_Parser_AST.TyconRecord (lid,bs,typ_opt,record_field_decls) ->
        let p_recordFieldAndComments uu____2150 =
          match uu____2150 with
          | (lid1,t,doc_opt) ->
              let uu____2160 =
                FStar_Range.extend_to_end_of_line t.FStar_Parser_AST.range in
              with_comment p_recordFieldDecl (lid1, t, doc_opt) uu____2160 in
        let p_fields uu____2169 =
          let uu____2170 =
            let uu____2171 =
              let uu____2172 =
                let uu____2173 =
                  FStar_Pprint.op_Hat_Hat FStar_Pprint.semi break1 in
                FStar_Pprint.separate_map uu____2173 p_recordFieldAndComments
                  record_field_decls in
              braces_with_nesting uu____2172 in
            FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____2171 in
          FStar_Pprint.op_Hat_Hat FStar_Pprint.equals uu____2170 in
        p_typeDeclPrefix lid bs typ_opt p_fields
    | FStar_Parser_AST.TyconVariant (lid,bs,typ_opt,ct_decls) ->
        let p_constructorBranchAndComments uu____2209 =
          match uu____2209 with
          | (uid,t_opt,doc_opt,use_of) ->
              let range =
                let uu____2225 =
                  let uu____2226 =
                    FStar_Util.map_opt t_opt
                      (fun t  -> t.FStar_Parser_AST.range) in
                  FStar_Util.dflt uid.FStar_Ident.idRange uu____2226 in
                FStar_Range.extend_to_end_of_line uu____2225 in
              let p_constructorBranch decl =
                let uu____2246 =
                  let uu____2247 =
                    let uu____2248 = p_constructorDecl decl in
                    FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____2248 in
                  FStar_Pprint.op_Hat_Hat FStar_Pprint.bar uu____2247 in
                FStar_Pprint.group uu____2246 in
              with_comment p_constructorBranch (uid, t_opt, doc_opt, use_of)
                range in
        let datacon_doc uu____2260 =
          let uu____2261 =
            FStar_Pprint.separate_map break1 p_constructorBranchAndComments
              ct_decls in
          FStar_Pprint.group uu____2261 in
        p_typeDeclPrefix lid bs typ_opt
          (fun uu____2270  ->
             let uu____2271 = datacon_doc () in
             prefix2 FStar_Pprint.equals uu____2271)
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
            let uu____2282 = p_ident lid in
            let uu____2283 =
              let uu____2284 = cont () in
              FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____2284 in
            FStar_Pprint.op_Hat_Hat uu____2282 uu____2283
          else
            (let binders_doc =
               let uu____2287 = p_typars bs in
               let uu____2288 =
                 FStar_Pprint.optional
                   (fun t  ->
                      let uu____2292 =
                        let uu____2293 =
                          let uu____2294 = p_typ t in
                          FStar_Pprint.op_Hat_Hat FStar_Pprint.space
                            uu____2294 in
                        FStar_Pprint.op_Hat_Hat FStar_Pprint.colon uu____2293 in
                      FStar_Pprint.op_Hat_Hat break1 uu____2292) typ_opt in
               FStar_Pprint.op_Hat_Hat uu____2287 uu____2288 in
             let uu____2295 = p_ident lid in
             let uu____2296 = cont () in
             FStar_Pprint.surround (Prims.parse_int "2")
               (Prims.parse_int "1") uu____2295 binders_doc uu____2296)
and p_recordFieldDecl:
  (FStar_Ident.ident* FStar_Parser_AST.term* FStar_Parser_AST.fsdoc option)
    -> FStar_Pprint.document
  =
  fun uu____2297  ->
    match uu____2297 with
    | (lid,t,doc_opt) ->
        let uu____2307 =
          let uu____2308 = FStar_Pprint.optional p_fsdoc doc_opt in
          let uu____2309 =
            let uu____2310 = p_lident lid in
            let uu____2311 =
              let uu____2312 = p_typ t in
              FStar_Pprint.op_Hat_Hat FStar_Pprint.colon uu____2312 in
            FStar_Pprint.op_Hat_Hat uu____2310 uu____2311 in
          FStar_Pprint.op_Hat_Hat uu____2308 uu____2309 in
        FStar_Pprint.group uu____2307
and p_constructorDecl:
  (FStar_Ident.ident* FStar_Parser_AST.term option* FStar_Parser_AST.fsdoc
    option* Prims.bool) -> FStar_Pprint.document
  =
  fun uu____2313  ->
    match uu____2313 with
    | (uid,t_opt,doc_opt,use_of) ->
        let sep = if use_of then str "of" else FStar_Pprint.colon in
        let uid_doc = p_uident uid in
        let uu____2331 = FStar_Pprint.optional p_fsdoc doc_opt in
        let uu____2332 =
          let uu____2333 = FStar_Pprint.break_ (Prims.parse_int "0") in
          let uu____2334 =
            default_or_map uid_doc
              (fun t  ->
                 let uu____2339 =
                   let uu____2340 =
                     FStar_Pprint.op_Hat_Hat FStar_Pprint.space sep in
                   FStar_Pprint.op_Hat_Hat uid_doc uu____2340 in
                 let uu____2341 = p_typ t in
                 op_Hat_Slash_Plus_Hat uu____2339 uu____2341) t_opt in
          FStar_Pprint.op_Hat_Hat uu____2333 uu____2334 in
        FStar_Pprint.op_Hat_Hat uu____2331 uu____2332
and p_letbinding:
  (FStar_Parser_AST.pattern* FStar_Parser_AST.term) -> FStar_Pprint.document
  =
  fun uu____2342  ->
    match uu____2342 with
    | (pat,e) ->
        let pat_doc =
          let uu____2348 =
            match pat.FStar_Parser_AST.pat with
            | FStar_Parser_AST.PatAscribed (pat1,t) ->
                let uu____2355 =
                  let uu____2356 =
                    let uu____2357 =
                      let uu____2358 =
                        let uu____2359 = p_tmArrow p_tmNoEq t in
                        FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____2359 in
                      FStar_Pprint.op_Hat_Hat FStar_Pprint.colon uu____2358 in
                    FStar_Pprint.group uu____2357 in
                  FStar_Pprint.op_Hat_Hat break1 uu____2356 in
                (pat1, uu____2355)
            | uu____2360 -> (pat, FStar_Pprint.empty) in
          match uu____2348 with
          | (pat1,ascr_doc) ->
              (match pat1.FStar_Parser_AST.pat with
               | FStar_Parser_AST.PatApp
                   ({
                      FStar_Parser_AST.pat = FStar_Parser_AST.PatVar
                        (x,uu____2364);
                      FStar_Parser_AST.prange = uu____2365;_},pats)
                   ->
                   let uu____2371 = p_lident x in
                   let uu____2372 =
                     let uu____2373 =
                       FStar_Pprint.separate_map break1 p_atomicPattern pats in
                     FStar_Pprint.op_Hat_Hat uu____2373 ascr_doc in
                   FStar_Pprint.surround (Prims.parse_int "2")
                     (Prims.parse_int "1") uu____2371 uu____2372
                     FStar_Pprint.equals
               | uu____2374 ->
                   let uu____2375 =
                     let uu____2376 = p_tuplePattern pat1 in
                     let uu____2377 =
                       FStar_Pprint.op_Hat_Slash_Hat ascr_doc
                         FStar_Pprint.equals in
                     FStar_Pprint.op_Hat_Hat uu____2376 uu____2377 in
                   FStar_Pprint.group uu____2375) in
        let uu____2378 = p_term e in prefix2 pat_doc uu____2378
and p_newEffect: FStar_Parser_AST.effect_decl -> FStar_Pprint.document =
  fun uu___98_2379  ->
    match uu___98_2379 with
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
        let uu____2397 = p_uident uid in
        let uu____2398 = p_binders true bs in
        let uu____2399 =
          let uu____2400 = p_simpleTerm t in
          prefix2 FStar_Pprint.equals uu____2400 in
        FStar_Pprint.surround (Prims.parse_int "2") (Prims.parse_int "1")
          uu____2397 uu____2398 uu____2399
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
          let uu____2407 =
            let uu____2408 =
              let uu____2409 =
                let uu____2410 = p_uident uid in
                let uu____2411 = p_binders true bs in
                let uu____2412 =
                  let uu____2413 = p_typ t in
                  prefix2 FStar_Pprint.colon uu____2413 in
                FStar_Pprint.surround (Prims.parse_int "2")
                  (Prims.parse_int "1") uu____2410 uu____2411 uu____2412 in
              FStar_Pprint.group uu____2409 in
            let uu____2414 =
              let uu____2415 = str "with" in
              let uu____2416 =
                separate_break_map FStar_Pprint.semi p_effectDecl eff_decls in
              prefix2 uu____2415 uu____2416 in
            FStar_Pprint.op_Hat_Slash_Hat uu____2408 uu____2414 in
          braces_with_nesting uu____2407
and p_effectDecl: FStar_Parser_AST.decl -> FStar_Pprint.document =
  fun d  ->
    match d.FStar_Parser_AST.d with
    | FStar_Parser_AST.Tycon
        (false ,(FStar_Parser_AST.TyconAbbrev (lid,[],None ,e),None )::[]) ->
        let uu____2433 =
          let uu____2434 = p_lident lid in
          let uu____2435 =
            FStar_Pprint.op_Hat_Hat FStar_Pprint.space FStar_Pprint.equals in
          FStar_Pprint.op_Hat_Hat uu____2434 uu____2435 in
        let uu____2436 = p_simpleTerm e in prefix2 uu____2433 uu____2436
    | uu____2437 ->
        let uu____2438 =
          let uu____2439 = FStar_Parser_AST.decl_to_string d in
          FStar_Util.format1
            "Not a declaration of an effect member... or at least I hope so : %s"
            uu____2439 in
        failwith uu____2438
and p_subEffect: FStar_Parser_AST.lift -> FStar_Pprint.document =
  fun lift  ->
    let lift_op_doc =
      let lifts =
        match lift.FStar_Parser_AST.lift_op with
        | FStar_Parser_AST.NonReifiableLift t -> [("lift_wp", t)]
        | FStar_Parser_AST.ReifiableLift (t1,t2) ->
            [("lif_wp", t1); ("lift", t2)]
        | FStar_Parser_AST.LiftForFree t -> [("lift", t)] in
      let p_lift uu____2472 =
        match uu____2472 with
        | (kwd1,t) ->
            let uu____2477 =
              let uu____2478 = str kwd1 in
              let uu____2479 =
                FStar_Pprint.op_Hat_Hat FStar_Pprint.space
                  FStar_Pprint.equals in
              FStar_Pprint.op_Hat_Hat uu____2478 uu____2479 in
            let uu____2480 = p_simpleTerm t in prefix2 uu____2477 uu____2480 in
      separate_break_map FStar_Pprint.semi p_lift lifts in
    let uu____2483 =
      let uu____2484 =
        let uu____2485 = p_quident lift.FStar_Parser_AST.msource in
        let uu____2486 =
          let uu____2487 = str "~>" in
          FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____2487 in
        FStar_Pprint.op_Hat_Hat uu____2485 uu____2486 in
      let uu____2488 = p_quident lift.FStar_Parser_AST.mdest in
      prefix2 uu____2484 uu____2488 in
    let uu____2489 =
      let uu____2490 = braces_with_nesting lift_op_doc in
      FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____2490 in
    FStar_Pprint.op_Hat_Hat uu____2483 uu____2489
and p_qualifier: FStar_Parser_AST.qualifier -> FStar_Pprint.document =
  fun uu___99_2491  ->
    match uu___99_2491 with
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
    let uu____2493 = FStar_Pprint.separate_map break1 p_qualifier qs in
    FStar_Pprint.group uu____2493
and p_letqualifier: FStar_Parser_AST.let_qualifier -> FStar_Pprint.document =
  fun uu___100_2494  ->
    match uu___100_2494 with
    | FStar_Parser_AST.Rec  ->
        let uu____2495 = str "rec" in
        FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____2495
    | FStar_Parser_AST.Mutable  ->
        let uu____2496 = str "mutable" in
        FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____2496
    | FStar_Parser_AST.NoLetQualifier  -> FStar_Pprint.empty
and p_aqual: FStar_Parser_AST.arg_qualifier -> FStar_Pprint.document =
  fun uu___101_2497  ->
    match uu___101_2497 with
    | FStar_Parser_AST.Implicit  -> str "#"
    | FStar_Parser_AST.Equality  -> str "$"
and p_disjunctivePattern: FStar_Parser_AST.pattern -> FStar_Pprint.document =
  fun p  ->
    match p.FStar_Parser_AST.pat with
    | FStar_Parser_AST.PatOr pats ->
        let uu____2501 =
          let uu____2502 =
            let uu____2503 =
              FStar_Pprint.op_Hat_Hat FStar_Pprint.bar FStar_Pprint.space in
            FStar_Pprint.op_Hat_Hat break1 uu____2503 in
          FStar_Pprint.separate_map uu____2502 p_tuplePattern pats in
        FStar_Pprint.group uu____2501
    | uu____2504 -> p_tuplePattern p
and p_tuplePattern: FStar_Parser_AST.pattern -> FStar_Pprint.document =
  fun p  ->
    match p.FStar_Parser_AST.pat with
    | FStar_Parser_AST.PatTuple (pats,false ) ->
        let uu____2509 =
          let uu____2510 = FStar_Pprint.op_Hat_Hat FStar_Pprint.comma break1 in
          FStar_Pprint.separate_map uu____2510 p_constructorPattern pats in
        FStar_Pprint.group uu____2509
    | uu____2511 -> p_constructorPattern p
and p_constructorPattern: FStar_Parser_AST.pattern -> FStar_Pprint.document =
  fun p  ->
    match p.FStar_Parser_AST.pat with
    | FStar_Parser_AST.PatApp
        ({ FStar_Parser_AST.pat = FStar_Parser_AST.PatName maybe_cons_lid;
           FStar_Parser_AST.prange = uu____2514;_},hd1::tl1::[])
        when
        FStar_Ident.lid_equals maybe_cons_lid FStar_Parser_Const.cons_lid ->
        let uu____2518 =
          FStar_Pprint.op_Hat_Hat FStar_Pprint.colon FStar_Pprint.colon in
        let uu____2519 = p_constructorPattern hd1 in
        let uu____2520 = p_constructorPattern tl1 in
        infix0 uu____2518 uu____2519 uu____2520
    | FStar_Parser_AST.PatApp
        ({ FStar_Parser_AST.pat = FStar_Parser_AST.PatName uid;
           FStar_Parser_AST.prange = uu____2522;_},pats)
        ->
        let uu____2526 = p_quident uid in
        let uu____2527 =
          FStar_Pprint.separate_map break1 p_atomicPattern pats in
        prefix2 uu____2526 uu____2527
    | uu____2528 -> p_atomicPattern p
and p_atomicPattern: FStar_Parser_AST.pattern -> FStar_Pprint.document =
  fun p  ->
    match p.FStar_Parser_AST.pat with
    | FStar_Parser_AST.PatAscribed (pat,t) ->
        let uu____2532 =
          let uu____2535 =
            let uu____2536 = unparen t in uu____2536.FStar_Parser_AST.tm in
          ((pat.FStar_Parser_AST.pat), uu____2535) in
        (match uu____2532 with
         | (FStar_Parser_AST.PatVar (lid,aqual),FStar_Parser_AST.Refine
            ({ FStar_Parser_AST.b = FStar_Parser_AST.Annotated (lid',t1);
               FStar_Parser_AST.brange = uu____2541;
               FStar_Parser_AST.blevel = uu____2542;
               FStar_Parser_AST.aqual = uu____2543;_},phi))
             when lid.FStar_Ident.idText = lid'.FStar_Ident.idText ->
             let uu____2547 =
               let uu____2548 = p_ident lid in
               p_refinement aqual uu____2548 t1 phi in
             soft_parens_with_nesting uu____2547
         | (FStar_Parser_AST.PatWild ,FStar_Parser_AST.Refine
            ({ FStar_Parser_AST.b = FStar_Parser_AST.NoName t1;
               FStar_Parser_AST.brange = uu____2550;
               FStar_Parser_AST.blevel = uu____2551;
               FStar_Parser_AST.aqual = uu____2552;_},phi))
             ->
             let uu____2554 =
               p_refinement None FStar_Pprint.underscore t1 phi in
             soft_parens_with_nesting uu____2554
         | uu____2555 ->
             let uu____2558 =
               let uu____2559 = p_tuplePattern pat in
               let uu____2560 =
                 let uu____2561 = FStar_Pprint.break_ (Prims.parse_int "0") in
                 let uu____2562 =
                   let uu____2563 = p_typ t in
                   FStar_Pprint.op_Hat_Hat FStar_Pprint.colon uu____2563 in
                 FStar_Pprint.op_Hat_Hat uu____2561 uu____2562 in
               FStar_Pprint.op_Hat_Hat uu____2559 uu____2560 in
             soft_parens_with_nesting uu____2558)
    | FStar_Parser_AST.PatList pats ->
        let uu____2566 =
          separate_break_map FStar_Pprint.semi p_tuplePattern pats in
        FStar_Pprint.surround (Prims.parse_int "2") (Prims.parse_int "0")
          FStar_Pprint.lbracket uu____2566 FStar_Pprint.rbracket
    | FStar_Parser_AST.PatRecord pats ->
        let p_recordFieldPat uu____2576 =
          match uu____2576 with
          | (lid,pat) ->
              let uu____2581 = p_qlident lid in
              let uu____2582 = p_tuplePattern pat in
              infix2 FStar_Pprint.equals uu____2581 uu____2582 in
        let uu____2583 =
          separate_break_map FStar_Pprint.semi p_recordFieldPat pats in
        soft_braces_with_nesting uu____2583
    | FStar_Parser_AST.PatTuple (pats,true ) ->
        let uu____2589 =
          FStar_Pprint.op_Hat_Hat FStar_Pprint.lparen FStar_Pprint.bar in
        let uu____2590 =
          separate_break_map FStar_Pprint.comma p_constructorPattern pats in
        let uu____2591 =
          FStar_Pprint.op_Hat_Hat FStar_Pprint.bar FStar_Pprint.rparen in
        FStar_Pprint.surround (Prims.parse_int "2") (Prims.parse_int "1")
          uu____2589 uu____2590 uu____2591
    | FStar_Parser_AST.PatTvar (tv,arg_qualifier_opt) -> p_tvar tv
    | FStar_Parser_AST.PatOp op ->
        let uu____2599 =
          let uu____2600 =
            let uu____2601 = str (FStar_Ident.text_of_id op) in
            let uu____2602 =
              FStar_Pprint.op_Hat_Hat FStar_Pprint.space FStar_Pprint.rparen in
            FStar_Pprint.op_Hat_Hat uu____2601 uu____2602 in
          FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____2600 in
        FStar_Pprint.op_Hat_Hat FStar_Pprint.lparen uu____2599
    | FStar_Parser_AST.PatWild  -> FStar_Pprint.underscore
    | FStar_Parser_AST.PatConst c -> p_constant c
    | FStar_Parser_AST.PatVar (lid,aqual) ->
        let uu____2608 = FStar_Pprint.optional p_aqual aqual in
        let uu____2609 = p_lident lid in
        FStar_Pprint.op_Hat_Hat uu____2608 uu____2609
    | FStar_Parser_AST.PatName uid -> p_quident uid
    | FStar_Parser_AST.PatOr uu____2611 -> failwith "Inner or pattern !"
    | FStar_Parser_AST.PatApp
        ({ FStar_Parser_AST.pat = FStar_Parser_AST.PatName uu____2613;
           FStar_Parser_AST.prange = uu____2614;_},uu____2615)
        ->
        let uu____2618 = p_tuplePattern p in
        soft_parens_with_nesting uu____2618
    | FStar_Parser_AST.PatTuple (uu____2619,false ) ->
        let uu____2622 = p_tuplePattern p in
        soft_parens_with_nesting uu____2622
    | uu____2623 ->
        let uu____2624 =
          let uu____2625 = FStar_Parser_AST.pat_to_string p in
          FStar_Util.format1 "Invalid pattern %s" uu____2625 in
        failwith uu____2624
and p_binder: Prims.bool -> FStar_Parser_AST.binder -> FStar_Pprint.document
  =
  fun is_atomic  ->
    fun b  ->
      match b.FStar_Parser_AST.b with
      | FStar_Parser_AST.Variable lid ->
          let uu____2629 =
            FStar_Pprint.optional p_aqual b.FStar_Parser_AST.aqual in
          let uu____2630 = p_lident lid in
          FStar_Pprint.op_Hat_Hat uu____2629 uu____2630
      | FStar_Parser_AST.TVariable lid -> p_lident lid
      | FStar_Parser_AST.Annotated (lid,t) ->
          let doc1 =
            let uu____2635 =
              let uu____2636 = unparen t in uu____2636.FStar_Parser_AST.tm in
            match uu____2635 with
            | FStar_Parser_AST.Refine
                ({ FStar_Parser_AST.b = FStar_Parser_AST.Annotated (lid',t1);
                   FStar_Parser_AST.brange = uu____2639;
                   FStar_Parser_AST.blevel = uu____2640;
                   FStar_Parser_AST.aqual = uu____2641;_},phi)
                when lid.FStar_Ident.idText = lid'.FStar_Ident.idText ->
                let uu____2643 = p_ident lid in
                p_refinement b.FStar_Parser_AST.aqual uu____2643 t1 phi
            | uu____2644 ->
                let uu____2645 =
                  FStar_Pprint.optional p_aqual b.FStar_Parser_AST.aqual in
                let uu____2646 =
                  let uu____2647 = p_lident lid in
                  let uu____2648 =
                    let uu____2649 =
                      let uu____2650 =
                        FStar_Pprint.break_ (Prims.parse_int "0") in
                      let uu____2651 = p_tmFormula t in
                      FStar_Pprint.op_Hat_Hat uu____2650 uu____2651 in
                    FStar_Pprint.op_Hat_Hat FStar_Pprint.colon uu____2649 in
                  FStar_Pprint.op_Hat_Hat uu____2647 uu____2648 in
                FStar_Pprint.op_Hat_Hat uu____2645 uu____2646 in
          if is_atomic
          then
            let uu____2652 =
              let uu____2653 =
                FStar_Pprint.op_Hat_Hat doc1 FStar_Pprint.rparen in
              FStar_Pprint.op_Hat_Hat FStar_Pprint.lparen uu____2653 in
            FStar_Pprint.group uu____2652
          else FStar_Pprint.group doc1
      | FStar_Parser_AST.TAnnotated uu____2655 ->
          failwith "Is this still used ?"
      | FStar_Parser_AST.NoName t ->
          let uu____2659 =
            let uu____2660 = unparen t in uu____2660.FStar_Parser_AST.tm in
          (match uu____2659 with
           | FStar_Parser_AST.Refine
               ({ FStar_Parser_AST.b = FStar_Parser_AST.NoName t1;
                  FStar_Parser_AST.brange = uu____2662;
                  FStar_Parser_AST.blevel = uu____2663;
                  FStar_Parser_AST.aqual = uu____2664;_},phi)
               ->
               if is_atomic
               then
                 let uu____2666 =
                   let uu____2667 =
                     let uu____2668 =
                       p_refinement b.FStar_Parser_AST.aqual
                         FStar_Pprint.underscore t1 phi in
                     FStar_Pprint.op_Hat_Hat uu____2668 FStar_Pprint.rparen in
                   FStar_Pprint.op_Hat_Hat FStar_Pprint.lparen uu____2667 in
                 FStar_Pprint.group uu____2666
               else
                 (let uu____2670 =
                    p_refinement b.FStar_Parser_AST.aqual
                      FStar_Pprint.underscore t1 phi in
                  FStar_Pprint.group uu____2670)
           | uu____2671 -> if is_atomic then p_atomicTerm t else p_appTerm t)
and p_refinement:
  FStar_Parser_AST.arg_qualifier option ->
    FStar_Pprint.document ->
      FStar_Parser_AST.term -> FStar_Parser_AST.term -> FStar_Pprint.document
  =
  fun aqual_opt  ->
    fun binder  ->
      fun t  ->
        fun phi  ->
          let uu____2678 = FStar_Pprint.optional p_aqual aqual_opt in
          let uu____2679 =
            let uu____2680 =
              let uu____2681 =
                let uu____2682 = p_appTerm t in
                let uu____2683 =
                  let uu____2684 = p_noSeqTerm phi in
                  soft_braces_with_nesting uu____2684 in
                FStar_Pprint.op_Hat_Hat uu____2682 uu____2683 in
              FStar_Pprint.op_Hat_Hat FStar_Pprint.colon uu____2681 in
            FStar_Pprint.op_Hat_Hat binder uu____2680 in
          FStar_Pprint.op_Hat_Hat uu____2678 uu____2679
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
    let uu____2697 =
      let uu____2698 = unparen e in uu____2698.FStar_Parser_AST.tm in
    match uu____2697 with
    | FStar_Parser_AST.Seq (e1,e2) ->
        let uu____2701 =
          let uu____2702 =
            let uu____2703 = p_noSeqTerm e1 in
            FStar_Pprint.op_Hat_Hat uu____2703 FStar_Pprint.semi in
          FStar_Pprint.group uu____2702 in
        let uu____2704 = p_term e2 in
        FStar_Pprint.op_Hat_Slash_Hat uu____2701 uu____2704
    | FStar_Parser_AST.Bind (x,e1,e2) ->
        let uu____2708 =
          let uu____2709 =
            let uu____2710 =
              let uu____2711 = p_lident x in
              let uu____2712 =
                FStar_Pprint.op_Hat_Hat FStar_Pprint.space
                  FStar_Pprint.long_left_arrow in
              FStar_Pprint.op_Hat_Hat uu____2711 uu____2712 in
            let uu____2713 =
              let uu____2714 = p_noSeqTerm e1 in
              let uu____2715 =
                FStar_Pprint.op_Hat_Hat FStar_Pprint.space FStar_Pprint.semi in
              FStar_Pprint.op_Hat_Hat uu____2714 uu____2715 in
            op_Hat_Slash_Plus_Hat uu____2710 uu____2713 in
          FStar_Pprint.group uu____2709 in
        let uu____2716 = p_term e2 in
        FStar_Pprint.op_Hat_Slash_Hat uu____2708 uu____2716
    | uu____2717 ->
        let uu____2718 = p_noSeqTerm e in FStar_Pprint.group uu____2718
and p_noSeqTerm: FStar_Parser_AST.term -> FStar_Pprint.document =
  fun e  -> with_comment p_noSeqTerm' e e.FStar_Parser_AST.range
and p_noSeqTerm': FStar_Parser_AST.term -> FStar_Pprint.document =
  fun e  ->
    let uu____2721 =
      let uu____2722 = unparen e in uu____2722.FStar_Parser_AST.tm in
    match uu____2721 with
    | FStar_Parser_AST.Ascribed (e1,t,None ) ->
        let uu____2726 =
          let uu____2727 = p_tmIff e1 in
          let uu____2728 =
            let uu____2729 =
              let uu____2730 = p_typ t in
              FStar_Pprint.op_Hat_Slash_Hat FStar_Pprint.colon uu____2730 in
            FStar_Pprint.op_Hat_Hat FStar_Pprint.langle uu____2729 in
          FStar_Pprint.op_Hat_Slash_Hat uu____2727 uu____2728 in
        FStar_Pprint.group uu____2726
    | FStar_Parser_AST.Ascribed (e1,t,Some tac) ->
        let uu____2735 =
          let uu____2736 = p_tmIff e1 in
          let uu____2737 =
            let uu____2738 =
              let uu____2739 =
                let uu____2740 = p_typ t in
                let uu____2741 =
                  let uu____2742 = str "by" in
                  let uu____2743 = p_typ tac in
                  FStar_Pprint.op_Hat_Slash_Hat uu____2742 uu____2743 in
                FStar_Pprint.op_Hat_Slash_Hat uu____2740 uu____2741 in
              FStar_Pprint.op_Hat_Slash_Hat FStar_Pprint.colon uu____2739 in
            FStar_Pprint.op_Hat_Hat FStar_Pprint.langle uu____2738 in
          FStar_Pprint.op_Hat_Slash_Hat uu____2736 uu____2737 in
        FStar_Pprint.group uu____2735
    | FStar_Parser_AST.Op
        ({ FStar_Ident.idText = ".()<-"; FStar_Ident.idRange = uu____2744;_},e1::e2::e3::[])
        ->
        let uu____2749 =
          let uu____2750 =
            let uu____2751 =
              let uu____2752 = p_atomicTermNotQUident e1 in
              let uu____2753 =
                let uu____2754 =
                  let uu____2755 =
                    let uu____2756 = p_term e2 in
                    soft_parens_with_nesting uu____2756 in
                  let uu____2757 =
                    FStar_Pprint.op_Hat_Hat FStar_Pprint.space
                      FStar_Pprint.larrow in
                  FStar_Pprint.op_Hat_Hat uu____2755 uu____2757 in
                FStar_Pprint.op_Hat_Hat FStar_Pprint.dot uu____2754 in
              FStar_Pprint.op_Hat_Hat uu____2752 uu____2753 in
            FStar_Pprint.group uu____2751 in
          let uu____2758 =
            let uu____2759 = p_noSeqTerm e3 in jump2 uu____2759 in
          FStar_Pprint.op_Hat_Hat uu____2750 uu____2758 in
        FStar_Pprint.group uu____2749
    | FStar_Parser_AST.Op
        ({ FStar_Ident.idText = ".[]<-"; FStar_Ident.idRange = uu____2760;_},e1::e2::e3::[])
        ->
        let uu____2765 =
          let uu____2766 =
            let uu____2767 =
              let uu____2768 = p_atomicTermNotQUident e1 in
              let uu____2769 =
                let uu____2770 =
                  let uu____2771 =
                    let uu____2772 = p_term e2 in
                    soft_brackets_with_nesting uu____2772 in
                  let uu____2773 =
                    FStar_Pprint.op_Hat_Hat FStar_Pprint.space
                      FStar_Pprint.larrow in
                  FStar_Pprint.op_Hat_Hat uu____2771 uu____2773 in
                FStar_Pprint.op_Hat_Hat FStar_Pprint.dot uu____2770 in
              FStar_Pprint.op_Hat_Hat uu____2768 uu____2769 in
            FStar_Pprint.group uu____2767 in
          let uu____2774 =
            let uu____2775 = p_noSeqTerm e3 in jump2 uu____2775 in
          FStar_Pprint.op_Hat_Hat uu____2766 uu____2774 in
        FStar_Pprint.group uu____2765
    | FStar_Parser_AST.Requires (e1,wtf) ->
        let uu____2782 =
          let uu____2783 = str "requires" in
          let uu____2784 = p_typ e1 in
          FStar_Pprint.op_Hat_Slash_Hat uu____2783 uu____2784 in
        FStar_Pprint.group uu____2782
    | FStar_Parser_AST.Ensures (e1,wtf) ->
        let uu____2791 =
          let uu____2792 = str "ensures" in
          let uu____2793 = p_typ e1 in
          FStar_Pprint.op_Hat_Slash_Hat uu____2792 uu____2793 in
        FStar_Pprint.group uu____2791
    | FStar_Parser_AST.Attributes es ->
        let uu____2796 =
          let uu____2797 = str "attributes" in
          let uu____2798 = FStar_Pprint.separate_map break1 p_atomicTerm es in
          FStar_Pprint.op_Hat_Slash_Hat uu____2797 uu____2798 in
        FStar_Pprint.group uu____2796
    | FStar_Parser_AST.If (e1,e2,e3) ->
        let uu____2802 = is_unit e3 in
        if uu____2802
        then
          let uu____2803 =
            let uu____2804 =
              let uu____2805 = str "if" in
              let uu____2806 = p_noSeqTerm e1 in
              op_Hat_Slash_Plus_Hat uu____2805 uu____2806 in
            let uu____2807 =
              let uu____2808 = str "then" in
              let uu____2809 = p_noSeqTerm e2 in
              op_Hat_Slash_Plus_Hat uu____2808 uu____2809 in
            FStar_Pprint.op_Hat_Slash_Hat uu____2804 uu____2807 in
          FStar_Pprint.group uu____2803
        else
          (let e2_doc =
             let uu____2812 =
               let uu____2813 = unparen e2 in uu____2813.FStar_Parser_AST.tm in
             match uu____2812 with
             | FStar_Parser_AST.If (uu____2814,uu____2815,e31) when
                 is_unit e31 ->
                 let uu____2817 = p_noSeqTerm e2 in
                 soft_parens_with_nesting uu____2817
             | uu____2818 -> p_noSeqTerm e2 in
           let uu____2819 =
             let uu____2820 =
               let uu____2821 = str "if" in
               let uu____2822 = p_noSeqTerm e1 in
               op_Hat_Slash_Plus_Hat uu____2821 uu____2822 in
             let uu____2823 =
               let uu____2824 =
                 let uu____2825 = str "then" in
                 op_Hat_Slash_Plus_Hat uu____2825 e2_doc in
               let uu____2826 =
                 let uu____2827 = str "else" in
                 let uu____2828 = p_noSeqTerm e3 in
                 op_Hat_Slash_Plus_Hat uu____2827 uu____2828 in
               FStar_Pprint.op_Hat_Slash_Hat uu____2824 uu____2826 in
             FStar_Pprint.op_Hat_Slash_Hat uu____2820 uu____2823 in
           FStar_Pprint.group uu____2819)
    | FStar_Parser_AST.TryWith (e1,branches) ->
        let uu____2841 =
          let uu____2842 =
            let uu____2843 = str "try" in
            let uu____2844 = p_noSeqTerm e1 in prefix2 uu____2843 uu____2844 in
          let uu____2845 =
            let uu____2846 = str "with" in
            let uu____2847 =
              FStar_Pprint.separate_map FStar_Pprint.hardline p_patternBranch
                branches in
            FStar_Pprint.op_Hat_Slash_Hat uu____2846 uu____2847 in
          FStar_Pprint.op_Hat_Slash_Hat uu____2842 uu____2845 in
        FStar_Pprint.group uu____2841
    | FStar_Parser_AST.Match (e1,branches) ->
        let uu____2864 =
          let uu____2865 =
            let uu____2866 = str "match" in
            let uu____2867 = p_noSeqTerm e1 in
            let uu____2868 = str "with" in
            FStar_Pprint.surround (Prims.parse_int "2") (Prims.parse_int "1")
              uu____2866 uu____2867 uu____2868 in
          let uu____2869 =
            FStar_Pprint.separate_map FStar_Pprint.hardline p_patternBranch
              branches in
          FStar_Pprint.op_Hat_Slash_Hat uu____2865 uu____2869 in
        FStar_Pprint.group uu____2864
    | FStar_Parser_AST.LetOpen (uid,e1) ->
        let uu____2876 =
          let uu____2877 =
            let uu____2878 = str "let open" in
            let uu____2879 = p_quident uid in
            let uu____2880 = str "in" in
            FStar_Pprint.surround (Prims.parse_int "2") (Prims.parse_int "1")
              uu____2878 uu____2879 uu____2880 in
          let uu____2881 = p_term e1 in
          FStar_Pprint.op_Hat_Slash_Hat uu____2877 uu____2881 in
        FStar_Pprint.group uu____2876
    | FStar_Parser_AST.Let (q,lbs,e1) ->
        let let_doc =
          let uu____2892 = str "let" in
          let uu____2893 = p_letqualifier q in
          FStar_Pprint.op_Hat_Hat uu____2892 uu____2893 in
        let uu____2894 =
          let uu____2895 =
            let uu____2896 =
              let uu____2897 = str "and" in
              precede_break_separate_map let_doc uu____2897 p_letbinding lbs in
            let uu____2900 = str "in" in
            FStar_Pprint.op_Hat_Slash_Hat uu____2896 uu____2900 in
          FStar_Pprint.group uu____2895 in
        let uu____2901 = p_term e1 in
        FStar_Pprint.op_Hat_Slash_Hat uu____2894 uu____2901
    | FStar_Parser_AST.Abs
        ({ FStar_Parser_AST.pat = FStar_Parser_AST.PatVar (x,typ_opt);
           FStar_Parser_AST.prange = uu____2904;_}::[],{
                                                         FStar_Parser_AST.tm
                                                           =
                                                           FStar_Parser_AST.Match
                                                           (maybe_x,branches);
                                                         FStar_Parser_AST.range
                                                           = uu____2907;
                                                         FStar_Parser_AST.level
                                                           = uu____2908;_})
        when matches_var maybe_x x ->
        let uu____2922 =
          let uu____2923 = str "function" in
          let uu____2924 =
            FStar_Pprint.separate_map FStar_Pprint.hardline p_patternBranch
              branches in
          FStar_Pprint.op_Hat_Slash_Hat uu____2923 uu____2924 in
        FStar_Pprint.group uu____2922
    | FStar_Parser_AST.Assign (id,e1) ->
        let uu____2931 =
          let uu____2932 = p_lident id in
          let uu____2933 =
            let uu____2934 = p_noSeqTerm e1 in
            FStar_Pprint.op_Hat_Slash_Hat FStar_Pprint.larrow uu____2934 in
          FStar_Pprint.op_Hat_Slash_Hat uu____2932 uu____2933 in
        FStar_Pprint.group uu____2931
    | uu____2935 -> p_typ e
and p_typ: FStar_Parser_AST.term -> FStar_Pprint.document =
  fun e  -> with_comment p_typ' e e.FStar_Parser_AST.range
and p_typ': FStar_Parser_AST.term -> FStar_Pprint.document =
  fun e  ->
    let uu____2938 =
      let uu____2939 = unparen e in uu____2939.FStar_Parser_AST.tm in
    match uu____2938 with
    | FStar_Parser_AST.QForall (bs,trigger,e1) ->
        let uu____2949 =
          let uu____2950 =
            let uu____2951 = p_quantifier e in
            FStar_Pprint.op_Hat_Hat uu____2951 FStar_Pprint.space in
          let uu____2952 = p_binders true bs in
          FStar_Pprint.soft_surround (Prims.parse_int "2")
            (Prims.parse_int "0") uu____2950 uu____2952 FStar_Pprint.dot in
        let uu____2953 =
          let uu____2954 = p_trigger trigger in
          let uu____2955 = p_noSeqTerm e1 in
          FStar_Pprint.op_Hat_Hat uu____2954 uu____2955 in
        prefix2 uu____2949 uu____2953
    | FStar_Parser_AST.QExists (bs,trigger,e1) ->
        let uu____2965 =
          let uu____2966 =
            let uu____2967 = p_quantifier e in
            FStar_Pprint.op_Hat_Hat uu____2967 FStar_Pprint.space in
          let uu____2968 = p_binders true bs in
          FStar_Pprint.soft_surround (Prims.parse_int "2")
            (Prims.parse_int "0") uu____2966 uu____2968 FStar_Pprint.dot in
        let uu____2969 =
          let uu____2970 = p_trigger trigger in
          let uu____2971 = p_noSeqTerm e1 in
          FStar_Pprint.op_Hat_Hat uu____2970 uu____2971 in
        prefix2 uu____2965 uu____2969
    | uu____2972 -> p_simpleTerm e
and p_quantifier: FStar_Parser_AST.term -> FStar_Pprint.document =
  fun e  ->
    let uu____2974 =
      let uu____2975 = unparen e in uu____2975.FStar_Parser_AST.tm in
    match uu____2974 with
    | FStar_Parser_AST.QForall uu____2976 -> str "forall"
    | FStar_Parser_AST.QExists uu____2983 -> str "exists"
    | uu____2990 ->
        failwith "Imposible : p_quantifier called on a non-quantifier term"
and p_trigger:
  FStar_Parser_AST.term Prims.list Prims.list -> FStar_Pprint.document =
  fun uu___102_2991  ->
    match uu___102_2991 with
    | [] -> FStar_Pprint.empty
    | pats ->
        let uu____2998 =
          let uu____2999 =
            let uu____3000 = str "pattern" in
            let uu____3001 =
              let uu____3002 =
                let uu____3003 = p_disjunctivePats pats in jump2 uu____3003 in
              let uu____3004 =
                FStar_Pprint.op_Hat_Hat FStar_Pprint.rbrace break1 in
              FStar_Pprint.op_Hat_Slash_Hat uu____3002 uu____3004 in
            FStar_Pprint.op_Hat_Slash_Hat uu____3000 uu____3001 in
          FStar_Pprint.op_Hat_Hat FStar_Pprint.colon uu____2999 in
        FStar_Pprint.op_Hat_Hat FStar_Pprint.lbrace uu____2998
and p_disjunctivePats:
  FStar_Parser_AST.term Prims.list Prims.list -> FStar_Pprint.document =
  fun pats  ->
    let uu____3008 = str "\\/" in
    FStar_Pprint.separate_map uu____3008 p_conjunctivePats pats
and p_conjunctivePats:
  FStar_Parser_AST.term Prims.list -> FStar_Pprint.document =
  fun pats  ->
    let uu____3012 =
      FStar_Pprint.separate_map FStar_Pprint.semi p_appTerm pats in
    FStar_Pprint.group uu____3012
and p_simpleTerm: FStar_Parser_AST.term -> FStar_Pprint.document =
  fun e  ->
    let uu____3014 =
      let uu____3015 = unparen e in uu____3015.FStar_Parser_AST.tm in
    match uu____3014 with
    | FStar_Parser_AST.Abs (pats,e1) ->
        let uu____3020 =
          let uu____3021 = str "fun" in
          let uu____3022 =
            let uu____3023 =
              FStar_Pprint.separate_map break1 p_atomicPattern pats in
            FStar_Pprint.op_Hat_Slash_Hat uu____3023 FStar_Pprint.rarrow in
          op_Hat_Slash_Plus_Hat uu____3021 uu____3022 in
        let uu____3024 = p_term e1 in
        op_Hat_Slash_Plus_Hat uu____3020 uu____3024
    | uu____3025 -> p_tmIff e
and p_maybeFocusArrow: Prims.bool -> FStar_Pprint.document =
  fun b  -> if b then str "~>" else FStar_Pprint.rarrow
and p_patternBranch:
  (FStar_Parser_AST.pattern* FStar_Parser_AST.term option*
    FStar_Parser_AST.term) -> FStar_Pprint.document
  =
  fun uu____3028  ->
    match uu____3028 with
    | (pat,when_opt,e) ->
        let maybe_paren =
          let uu____3041 =
            let uu____3042 = unparen e in uu____3042.FStar_Parser_AST.tm in
          match uu____3041 with
          | FStar_Parser_AST.Match uu____3045 -> soft_begin_end_with_nesting
          | FStar_Parser_AST.TryWith uu____3053 ->
              soft_begin_end_with_nesting
          | FStar_Parser_AST.Abs
              ({
                 FStar_Parser_AST.pat = FStar_Parser_AST.PatVar
                   (x,uu____3062);
                 FStar_Parser_AST.prange = uu____3063;_}::[],{
                                                               FStar_Parser_AST.tm
                                                                 =
                                                                 FStar_Parser_AST.Match
                                                                 (maybe_x,uu____3065);
                                                               FStar_Parser_AST.range
                                                                 = uu____3066;
                                                               FStar_Parser_AST.level
                                                                 = uu____3067;_})
              when matches_var maybe_x x -> soft_begin_end_with_nesting
          | uu____3081 -> (fun x  -> x) in
        let uu____3083 =
          let uu____3084 =
            let uu____3085 =
              let uu____3086 =
                let uu____3087 =
                  let uu____3088 = p_disjunctivePattern pat in
                  let uu____3089 =
                    let uu____3090 = p_maybeWhen when_opt in
                    FStar_Pprint.op_Hat_Hat uu____3090 FStar_Pprint.rarrow in
                  op_Hat_Slash_Plus_Hat uu____3088 uu____3089 in
                FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____3087 in
              FStar_Pprint.op_Hat_Hat FStar_Pprint.bar uu____3086 in
            FStar_Pprint.group uu____3085 in
          let uu____3091 =
            let uu____3092 = p_term e in maybe_paren uu____3092 in
          op_Hat_Slash_Plus_Hat uu____3084 uu____3091 in
        FStar_Pprint.group uu____3083
and p_maybeWhen: FStar_Parser_AST.term option -> FStar_Pprint.document =
  fun uu___103_3093  ->
    match uu___103_3093 with
    | None  -> FStar_Pprint.empty
    | Some e ->
        let uu____3096 = str "when" in
        let uu____3097 =
          let uu____3098 = p_tmFormula e in
          FStar_Pprint.op_Hat_Hat uu____3098 FStar_Pprint.space in
        op_Hat_Slash_Plus_Hat uu____3096 uu____3097
and p_tmIff: FStar_Parser_AST.term -> FStar_Pprint.document =
  fun e  ->
    let uu____3100 =
      let uu____3101 = unparen e in uu____3101.FStar_Parser_AST.tm in
    match uu____3100 with
    | FStar_Parser_AST.Op
        ({ FStar_Ident.idText = "<==>"; FStar_Ident.idRange = uu____3102;_},e1::e2::[])
        ->
        let uu____3106 = str "<==>" in
        let uu____3107 = p_tmImplies e1 in
        let uu____3108 = p_tmIff e2 in
        infix0 uu____3106 uu____3107 uu____3108
    | uu____3109 -> p_tmImplies e
and p_tmImplies: FStar_Parser_AST.term -> FStar_Pprint.document =
  fun e  ->
    let uu____3111 =
      let uu____3112 = unparen e in uu____3112.FStar_Parser_AST.tm in
    match uu____3111 with
    | FStar_Parser_AST.Op
        ({ FStar_Ident.idText = "==>"; FStar_Ident.idRange = uu____3113;_},e1::e2::[])
        ->
        let uu____3117 = str "==>" in
        let uu____3118 = p_tmArrow p_tmFormula e1 in
        let uu____3119 = p_tmImplies e2 in
        infix0 uu____3117 uu____3118 uu____3119
    | uu____3120 -> p_tmArrow p_tmFormula e
and p_tmArrow:
  (FStar_Parser_AST.term -> FStar_Pprint.document) ->
    FStar_Parser_AST.term -> FStar_Pprint.document
  =
  fun p_Tm  ->
    fun e  ->
      let uu____3125 =
        let uu____3126 = unparen e in uu____3126.FStar_Parser_AST.tm in
      match uu____3125 with
      | FStar_Parser_AST.Product (bs,tgt) ->
          let uu____3131 =
            let uu____3132 =
              FStar_Pprint.concat_map
                (fun b  ->
                   let uu____3137 = p_binder false b in
                   let uu____3138 =
                     let uu____3139 =
                       FStar_Pprint.op_Hat_Hat FStar_Pprint.rarrow break1 in
                     FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____3139 in
                   FStar_Pprint.op_Hat_Hat uu____3137 uu____3138) bs in
            let uu____3140 = p_tmArrow p_Tm tgt in
            FStar_Pprint.op_Hat_Hat uu____3132 uu____3140 in
          FStar_Pprint.group uu____3131
      | uu____3141 -> p_Tm e
and p_tmFormula: FStar_Parser_AST.term -> FStar_Pprint.document =
  fun e  ->
    let uu____3143 =
      let uu____3144 = unparen e in uu____3144.FStar_Parser_AST.tm in
    match uu____3143 with
    | FStar_Parser_AST.Op
        ({ FStar_Ident.idText = "\\/"; FStar_Ident.idRange = uu____3145;_},e1::e2::[])
        ->
        let uu____3149 = str "\\/" in
        let uu____3150 = p_tmFormula e1 in
        let uu____3151 = p_tmConjunction e2 in
        infix0 uu____3149 uu____3150 uu____3151
    | uu____3152 -> p_tmConjunction e
and p_tmConjunction: FStar_Parser_AST.term -> FStar_Pprint.document =
  fun e  ->
    let uu____3154 =
      let uu____3155 = unparen e in uu____3155.FStar_Parser_AST.tm in
    match uu____3154 with
    | FStar_Parser_AST.Op
        ({ FStar_Ident.idText = "/\\"; FStar_Ident.idRange = uu____3156;_},e1::e2::[])
        ->
        let uu____3160 = str "/\\" in
        let uu____3161 = p_tmConjunction e1 in
        let uu____3162 = p_tmTuple e2 in
        infix0 uu____3160 uu____3161 uu____3162
    | uu____3163 -> p_tmTuple e
and p_tmTuple: FStar_Parser_AST.term -> FStar_Pprint.document =
  fun e  -> with_comment p_tmTuple' e e.FStar_Parser_AST.range
and p_tmTuple': FStar_Parser_AST.term -> FStar_Pprint.document =
  fun e  ->
    let uu____3166 =
      let uu____3167 = unparen e in uu____3167.FStar_Parser_AST.tm in
    match uu____3166 with
    | FStar_Parser_AST.Construct (lid,args) when is_tuple_constructor lid ->
        let uu____3176 = FStar_Pprint.op_Hat_Hat FStar_Pprint.comma break1 in
        FStar_Pprint.separate_map uu____3176
          (fun uu____3182  ->
             match uu____3182 with | (e1,uu____3186) -> p_tmEq e1) args
    | uu____3187 -> p_tmEq e
and paren_if:
  Prims.int -> Prims.int -> FStar_Pprint.document -> FStar_Pprint.document =
  fun curr  ->
    fun mine  ->
      fun doc1  ->
        if mine <= curr
        then doc1
        else
          (let uu____3192 =
             let uu____3193 =
               FStar_Pprint.op_Hat_Hat doc1 FStar_Pprint.rparen in
             FStar_Pprint.op_Hat_Hat FStar_Pprint.lparen uu____3193 in
           FStar_Pprint.group uu____3192)
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
      let uu____3218 =
        let uu____3219 = unparen e in uu____3219.FStar_Parser_AST.tm in
      match uu____3218 with
      | FStar_Parser_AST.Op (op,e1::e2::[]) when
          ((is_operatorInfix0ad12 op) || ((FStar_Ident.text_of_id op) = "="))
            || ((FStar_Ident.text_of_id op) = "|>")
          ->
          let op1 = FStar_Ident.text_of_id op in
          let uu____3225 = levels op1 in
          (match uu____3225 with
           | (left1,mine,right1) ->
               let uu____3232 =
                 let uu____3233 = FStar_All.pipe_left str op1 in
                 let uu____3234 = p_tmEq' left1 e1 in
                 let uu____3235 = p_tmEq' right1 e2 in
                 infix0 uu____3233 uu____3234 uu____3235 in
               paren_if curr mine uu____3232)
      | FStar_Parser_AST.Op
          ({ FStar_Ident.idText = ":="; FStar_Ident.idRange = uu____3236;_},e1::e2::[])
          ->
          let uu____3240 =
            let uu____3241 = p_tmEq e1 in
            let uu____3242 =
              let uu____3243 =
                let uu____3244 =
                  let uu____3245 = p_tmEq e2 in
                  op_Hat_Slash_Plus_Hat FStar_Pprint.equals uu____3245 in
                FStar_Pprint.op_Hat_Hat FStar_Pprint.colon uu____3244 in
              FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____3243 in
            FStar_Pprint.op_Hat_Hat uu____3241 uu____3242 in
          FStar_Pprint.group uu____3240
      | FStar_Parser_AST.Op
          ({ FStar_Ident.idText = "-"; FStar_Ident.idRange = uu____3246;_},e1::[])
          ->
          let uu____3249 = levels "-" in
          (match uu____3249 with
           | (left1,mine,right1) ->
               let uu____3256 = p_tmEq' mine e1 in
               FStar_Pprint.op_Hat_Slash_Hat FStar_Pprint.minus uu____3256)
      | uu____3257 -> p_tmNoEq e
and p_tmNoEq: FStar_Parser_AST.term -> FStar_Pprint.document =
  fun e  ->
    let n1 = max_level [colon_colon (); amp (); opinfix3 (); opinfix4 ()] in
    p_tmNoEq' n1 e
and p_tmNoEq': Prims.int -> FStar_Parser_AST.term -> FStar_Pprint.document =
  fun curr  ->
    fun e  ->
      let uu____3287 =
        let uu____3288 = unparen e in uu____3288.FStar_Parser_AST.tm in
      match uu____3287 with
      | FStar_Parser_AST.Construct (lid,(e1,uu____3291)::(e2,uu____3293)::[])
          when
          (FStar_Ident.lid_equals lid FStar_Parser_Const.cons_lid) &&
            (let uu____3304 = is_list e in Prims.op_Negation uu____3304)
          ->
          let op = "::" in
          let uu____3306 = levels op in
          (match uu____3306 with
           | (left1,mine,right1) ->
               let uu____3313 =
                 let uu____3314 = str op in
                 let uu____3315 = p_tmNoEq' left1 e1 in
                 let uu____3316 = p_tmNoEq' right1 e2 in
                 infix0 uu____3314 uu____3315 uu____3316 in
               paren_if curr mine uu____3313)
      | FStar_Parser_AST.Sum (binders,res) ->
          let op = "&" in
          let uu____3322 = levels op in
          (match uu____3322 with
           | (left1,mine,right1) ->
               let p_dsumfst b =
                 let uu____3333 = p_binder false b in
                 let uu____3334 =
                   let uu____3335 =
                     let uu____3336 = str op in
                     FStar_Pprint.op_Hat_Hat uu____3336 break1 in
                   FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____3335 in
                 FStar_Pprint.op_Hat_Hat uu____3333 uu____3334 in
               let uu____3337 =
                 let uu____3338 = FStar_Pprint.concat_map p_dsumfst binders in
                 let uu____3339 = p_tmNoEq' right1 res in
                 FStar_Pprint.op_Hat_Hat uu____3338 uu____3339 in
               paren_if curr mine uu____3337)
      | FStar_Parser_AST.Op (op,e1::e2::[]) when is_operatorInfix34 op ->
          let op1 = FStar_Ident.text_of_id op in
          let uu____3345 = levels op1 in
          (match uu____3345 with
           | (left1,mine,right1) ->
               let uu____3352 =
                 let uu____3353 = str op1 in
                 let uu____3354 = p_tmNoEq' left1 e1 in
                 let uu____3355 = p_tmNoEq' right1 e2 in
                 infix0 uu____3353 uu____3354 uu____3355 in
               paren_if curr mine uu____3352)
      | FStar_Parser_AST.NamedTyp (lid,e1) ->
          let uu____3358 =
            let uu____3359 = p_lidentOrUnderscore lid in
            let uu____3360 =
              let uu____3361 = p_appTerm e1 in
              FStar_Pprint.op_Hat_Slash_Hat FStar_Pprint.colon uu____3361 in
            FStar_Pprint.op_Hat_Slash_Hat uu____3359 uu____3360 in
          FStar_Pprint.group uu____3358
      | FStar_Parser_AST.Refine (b,phi) -> p_refinedBinder b phi
      | FStar_Parser_AST.Record (with_opt,record_fields) ->
          let uu____3374 =
            let uu____3375 =
              default_or_map FStar_Pprint.empty p_with_clause with_opt in
            let uu____3376 =
              let uu____3377 =
                FStar_Pprint.op_Hat_Hat FStar_Pprint.semi break1 in
              FStar_Pprint.separate_map uu____3377 p_simpleDef record_fields in
            FStar_Pprint.op_Hat_Hat uu____3375 uu____3376 in
          braces_with_nesting uu____3374
      | FStar_Parser_AST.Op
          ({ FStar_Ident.idText = "~"; FStar_Ident.idRange = uu____3380;_},e1::[])
          ->
          let uu____3383 =
            let uu____3384 = str "~" in
            let uu____3385 = p_atomicTerm e1 in
            FStar_Pprint.op_Hat_Hat uu____3384 uu____3385 in
          FStar_Pprint.group uu____3383
      | uu____3386 -> p_appTerm e
and p_with_clause: FStar_Parser_AST.term -> FStar_Pprint.document =
  fun e  ->
    let uu____3388 = p_appTerm e in
    let uu____3389 =
      let uu____3390 =
        let uu____3391 = str "with" in
        FStar_Pprint.op_Hat_Hat uu____3391 break1 in
      FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____3390 in
    FStar_Pprint.op_Hat_Hat uu____3388 uu____3389
and p_refinedBinder:
  FStar_Parser_AST.binder -> FStar_Parser_AST.term -> FStar_Pprint.document =
  fun b  ->
    fun phi  ->
      match b.FStar_Parser_AST.b with
      | FStar_Parser_AST.Annotated (lid,t) ->
          let uu____3396 =
            let uu____3397 = p_lident lid in
            p_refinement b.FStar_Parser_AST.aqual uu____3397 t phi in
          soft_parens_with_nesting uu____3396
      | FStar_Parser_AST.TAnnotated uu____3398 ->
          failwith "Is this still used ?"
      | FStar_Parser_AST.Variable uu____3401 ->
          let uu____3402 =
            let uu____3403 = FStar_Parser_AST.binder_to_string b in
            FStar_Util.format1
              "Imposible : a refined binder ought to be annotated %s"
              uu____3403 in
          failwith uu____3402
      | FStar_Parser_AST.TVariable uu____3404 ->
          let uu____3405 =
            let uu____3406 = FStar_Parser_AST.binder_to_string b in
            FStar_Util.format1
              "Imposible : a refined binder ought to be annotated %s"
              uu____3406 in
          failwith uu____3405
      | FStar_Parser_AST.NoName uu____3407 ->
          let uu____3408 =
            let uu____3409 = FStar_Parser_AST.binder_to_string b in
            FStar_Util.format1
              "Imposible : a refined binder ought to be annotated %s"
              uu____3409 in
          failwith uu____3408
and p_simpleDef:
  (FStar_Ident.lid* FStar_Parser_AST.term) -> FStar_Pprint.document =
  fun uu____3410  ->
    match uu____3410 with
    | (lid,e) ->
        let uu____3415 =
          let uu____3416 = p_qlident lid in
          let uu____3417 =
            let uu____3418 = p_tmIff e in
            FStar_Pprint.op_Hat_Slash_Hat FStar_Pprint.equals uu____3418 in
          FStar_Pprint.op_Hat_Slash_Hat uu____3416 uu____3417 in
        FStar_Pprint.group uu____3415
and p_appTerm: FStar_Parser_AST.term -> FStar_Pprint.document =
  fun e  ->
    let uu____3420 =
      let uu____3421 = unparen e in uu____3421.FStar_Parser_AST.tm in
    match uu____3420 with
    | FStar_Parser_AST.App uu____3422 when is_general_application e ->
        let uu____3426 = head_and_args e in
        (match uu____3426 with
         | (head1,args) ->
             let uu____3440 =
               let uu____3446 = FStar_ST.read should_print_fs_typ_app in
               if uu____3446
               then
                 let uu____3454 =
                   FStar_Util.take
                     (fun uu____3468  ->
                        match uu____3468 with
                        | (uu____3471,aq) -> aq = FStar_Parser_AST.FsTypApp)
                     args in
                 match uu____3454 with
                 | (fs_typ_args,args1) ->
                     let uu____3492 =
                       let uu____3493 = p_indexingTerm head1 in
                       let uu____3494 =
                         let uu____3495 =
                           FStar_Pprint.op_Hat_Hat FStar_Pprint.comma break1 in
                         soft_surround_separate_map (Prims.parse_int "2")
                           (Prims.parse_int "0") FStar_Pprint.empty
                           FStar_Pprint.langle uu____3495 FStar_Pprint.rangle
                           p_fsTypArg fs_typ_args in
                       FStar_Pprint.op_Hat_Hat uu____3493 uu____3494 in
                     (uu____3492, args1)
               else
                 (let uu____3502 = p_indexingTerm head1 in (uu____3502, args)) in
             (match uu____3440 with
              | (head_doc,args1) ->
                  let uu____3514 =
                    let uu____3515 =
                      FStar_Pprint.op_Hat_Hat head_doc FStar_Pprint.space in
                    soft_surround_separate_map (Prims.parse_int "2")
                      (Prims.parse_int "0") head_doc uu____3515 break1
                      FStar_Pprint.empty p_argTerm args1 in
                  FStar_Pprint.group uu____3514))
    | FStar_Parser_AST.Construct (lid,args) when
        (is_general_construction e) &&
          (Prims.op_Negation (is_dtuple_constructor lid))
        ->
        (match args with
         | [] -> p_quident lid
         | arg::[] ->
             let uu____3535 =
               let uu____3536 = p_quident lid in
               let uu____3537 = p_argTerm arg in
               FStar_Pprint.op_Hat_Slash_Hat uu____3536 uu____3537 in
             FStar_Pprint.group uu____3535
         | hd1::tl1 ->
             let uu____3547 =
               let uu____3548 =
                 let uu____3549 =
                   let uu____3550 = p_quident lid in
                   let uu____3551 = p_argTerm hd1 in
                   prefix2 uu____3550 uu____3551 in
                 FStar_Pprint.group uu____3549 in
               let uu____3552 =
                 let uu____3553 =
                   FStar_Pprint.separate_map break1 p_argTerm tl1 in
                 jump2 uu____3553 in
               FStar_Pprint.op_Hat_Hat uu____3548 uu____3552 in
             FStar_Pprint.group uu____3547)
    | uu____3556 -> p_indexingTerm e
and p_argTerm:
  (FStar_Parser_AST.term* FStar_Parser_AST.imp) -> FStar_Pprint.document =
  fun arg_imp  ->
    match arg_imp with
    | ({ FStar_Parser_AST.tm = FStar_Parser_AST.Uvar uu____3560;
         FStar_Parser_AST.range = uu____3561;
         FStar_Parser_AST.level = uu____3562;_},FStar_Parser_AST.UnivApp
       ) -> p_univar (fst arg_imp)
    | (u,FStar_Parser_AST.UnivApp ) -> p_universe u
    | (e,FStar_Parser_AST.FsTypApp ) ->
        (FStar_Util.print_warning
           "Unexpected FsTypApp, output might not be formatted correctly.\n";
         (let uu____3566 = p_indexingTerm e in
          FStar_Pprint.surround (Prims.parse_int "2") (Prims.parse_int "1")
            FStar_Pprint.langle uu____3566 FStar_Pprint.rangle))
    | (e,FStar_Parser_AST.Hash ) ->
        let uu____3568 = str "#" in
        let uu____3569 = p_indexingTerm e in
        FStar_Pprint.op_Hat_Hat uu____3568 uu____3569
    | (e,FStar_Parser_AST.Nothing ) -> p_indexingTerm e
and p_fsTypArg:
  (FStar_Parser_AST.term* FStar_Parser_AST.imp) -> FStar_Pprint.document =
  fun uu____3571  ->
    match uu____3571 with | (e,uu____3575) -> p_indexingTerm e
and p_indexingTerm_aux:
  (FStar_Parser_AST.term -> FStar_Pprint.document) ->
    FStar_Parser_AST.term -> FStar_Pprint.document
  =
  fun exit1  ->
    fun e  ->
      let uu____3580 =
        let uu____3581 = unparen e in uu____3581.FStar_Parser_AST.tm in
      match uu____3580 with
      | FStar_Parser_AST.Op
          ({ FStar_Ident.idText = ".()"; FStar_Ident.idRange = uu____3582;_},e1::e2::[])
          ->
          let uu____3586 =
            let uu____3587 = p_indexingTerm_aux p_atomicTermNotQUident e1 in
            let uu____3588 =
              let uu____3589 =
                let uu____3590 = p_term e2 in
                soft_parens_with_nesting uu____3590 in
              FStar_Pprint.op_Hat_Hat FStar_Pprint.dot uu____3589 in
            FStar_Pprint.op_Hat_Hat uu____3587 uu____3588 in
          FStar_Pprint.group uu____3586
      | FStar_Parser_AST.Op
          ({ FStar_Ident.idText = ".[]"; FStar_Ident.idRange = uu____3591;_},e1::e2::[])
          ->
          let uu____3595 =
            let uu____3596 = p_indexingTerm_aux p_atomicTermNotQUident e1 in
            let uu____3597 =
              let uu____3598 =
                let uu____3599 = p_term e2 in
                soft_brackets_with_nesting uu____3599 in
              FStar_Pprint.op_Hat_Hat FStar_Pprint.dot uu____3598 in
            FStar_Pprint.op_Hat_Hat uu____3596 uu____3597 in
          FStar_Pprint.group uu____3595
      | uu____3600 -> exit1 e
and p_indexingTerm: FStar_Parser_AST.term -> FStar_Pprint.document =
  fun e  -> p_indexingTerm_aux p_atomicTerm e
and p_atomicTerm: FStar_Parser_AST.term -> FStar_Pprint.document =
  fun e  ->
    let uu____3603 =
      let uu____3604 = unparen e in uu____3604.FStar_Parser_AST.tm in
    match uu____3603 with
    | FStar_Parser_AST.LetOpen (lid,e1) ->
        let uu____3607 = p_quident lid in
        let uu____3608 =
          let uu____3609 =
            let uu____3610 = p_term e1 in soft_parens_with_nesting uu____3610 in
          FStar_Pprint.op_Hat_Hat FStar_Pprint.dot uu____3609 in
        FStar_Pprint.op_Hat_Hat uu____3607 uu____3608
    | FStar_Parser_AST.Name lid -> p_quident lid
    | FStar_Parser_AST.Op (op,e1::[]) when is_general_prefix_op op ->
        let uu____3615 = str (FStar_Ident.text_of_id op) in
        let uu____3616 = p_atomicTerm e1 in
        FStar_Pprint.op_Hat_Hat uu____3615 uu____3616
    | uu____3617 -> p_atomicTermNotQUident e
and p_atomicTermNotQUident: FStar_Parser_AST.term -> FStar_Pprint.document =
  fun e  ->
    let uu____3619 =
      let uu____3620 = unparen e in uu____3620.FStar_Parser_AST.tm in
    match uu____3619 with
    | FStar_Parser_AST.Wild  -> FStar_Pprint.underscore
    | FStar_Parser_AST.Var lid when
        FStar_Ident.lid_equals lid FStar_Parser_Const.assert_lid ->
        str "assert"
    | FStar_Parser_AST.Tvar tv -> p_tvar tv
    | FStar_Parser_AST.Const c ->
        (match c with
         | FStar_Const.Const_char x when x = '\n' -> str "0x0Az"
         | uu____3625 -> p_constant c)
    | FStar_Parser_AST.Name lid when
        FStar_Ident.lid_equals lid FStar_Parser_Const.true_lid -> str "True"
    | FStar_Parser_AST.Name lid when
        FStar_Ident.lid_equals lid FStar_Parser_Const.false_lid ->
        str "False"
    | FStar_Parser_AST.Op (op,e1::[]) when is_general_prefix_op op ->
        let uu____3631 = str (FStar_Ident.text_of_id op) in
        let uu____3632 = p_atomicTermNotQUident e1 in
        FStar_Pprint.op_Hat_Hat uu____3631 uu____3632
    | FStar_Parser_AST.Op (op,[]) ->
        let uu____3635 =
          let uu____3636 =
            let uu____3637 = str (FStar_Ident.text_of_id op) in
            let uu____3638 =
              FStar_Pprint.op_Hat_Hat FStar_Pprint.space FStar_Pprint.rparen in
            FStar_Pprint.op_Hat_Hat uu____3637 uu____3638 in
          FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____3636 in
        FStar_Pprint.op_Hat_Hat FStar_Pprint.lparen uu____3635
    | FStar_Parser_AST.Construct (lid,args) when is_dtuple_constructor lid ->
        let uu____3647 =
          FStar_Pprint.op_Hat_Hat FStar_Pprint.lparen FStar_Pprint.bar in
        let uu____3648 =
          let uu____3649 = FStar_Pprint.op_Hat_Hat FStar_Pprint.comma break1 in
          let uu____3650 = FStar_List.map FStar_Pervasives.fst args in
          FStar_Pprint.separate_map uu____3649 p_tmEq uu____3650 in
        let uu____3654 =
          FStar_Pprint.op_Hat_Hat FStar_Pprint.bar FStar_Pprint.rparen in
        FStar_Pprint.surround (Prims.parse_int "2") (Prims.parse_int "1")
          uu____3647 uu____3648 uu____3654
    | FStar_Parser_AST.Project (e1,lid) ->
        let uu____3657 =
          let uu____3658 = p_atomicTermNotQUident e1 in
          let uu____3659 =
            let uu____3660 = p_qlident lid in
            FStar_Pprint.op_Hat_Hat FStar_Pprint.dot uu____3660 in
          FStar_Pprint.prefix (Prims.parse_int "2") (Prims.parse_int "0")
            uu____3658 uu____3659 in
        FStar_Pprint.group uu____3657
    | uu____3661 -> p_projectionLHS e
and p_projectionLHS: FStar_Parser_AST.term -> FStar_Pprint.document =
  fun e  ->
    let uu____3663 =
      let uu____3664 = unparen e in uu____3664.FStar_Parser_AST.tm in
    match uu____3663 with
    | FStar_Parser_AST.Var lid -> p_qlident lid
    | FStar_Parser_AST.Projector (constr_lid,field_lid) ->
        let uu____3668 = p_quident constr_lid in
        let uu____3669 =
          let uu____3670 =
            let uu____3671 = p_lident field_lid in
            FStar_Pprint.op_Hat_Hat FStar_Pprint.dot uu____3671 in
          FStar_Pprint.op_Hat_Hat FStar_Pprint.qmark uu____3670 in
        FStar_Pprint.op_Hat_Hat uu____3668 uu____3669
    | FStar_Parser_AST.Discrim constr_lid ->
        let uu____3673 = p_quident constr_lid in
        FStar_Pprint.op_Hat_Hat uu____3673 FStar_Pprint.qmark
    | FStar_Parser_AST.Paren e1 ->
        let uu____3675 = p_term e1 in soft_parens_with_nesting uu____3675
    | uu____3676 when is_array e ->
        let es = extract_from_list e in
        let uu____3679 =
          FStar_Pprint.op_Hat_Hat FStar_Pprint.lbracket FStar_Pprint.bar in
        let uu____3680 =
          let uu____3681 = FStar_Pprint.op_Hat_Hat FStar_Pprint.semi break1 in
          separate_map_or_flow uu____3681 p_noSeqTerm es in
        let uu____3682 =
          FStar_Pprint.op_Hat_Hat FStar_Pprint.bar FStar_Pprint.rbracket in
        FStar_Pprint.surround (Prims.parse_int "2") (Prims.parse_int "0")
          uu____3679 uu____3680 uu____3682
    | uu____3683 when is_list e ->
        let uu____3684 =
          let uu____3685 = FStar_Pprint.op_Hat_Hat FStar_Pprint.semi break1 in
          let uu____3686 = extract_from_list e in
          separate_map_or_flow uu____3685 p_noSeqTerm uu____3686 in
        FStar_Pprint.surround (Prims.parse_int "2") (Prims.parse_int "0")
          FStar_Pprint.lbracket uu____3684 FStar_Pprint.rbracket
    | uu____3688 when is_lex_list e ->
        let uu____3689 =
          FStar_Pprint.op_Hat_Hat FStar_Pprint.percent FStar_Pprint.lbracket in
        let uu____3690 =
          let uu____3691 = FStar_Pprint.op_Hat_Hat FStar_Pprint.semi break1 in
          let uu____3692 = extract_from_list e in
          separate_map_or_flow uu____3691 p_noSeqTerm uu____3692 in
        FStar_Pprint.surround (Prims.parse_int "2") (Prims.parse_int "1")
          uu____3689 uu____3690 FStar_Pprint.rbracket
    | uu____3694 when is_ref_set e ->
        let es = extract_from_ref_set e in
        let uu____3697 =
          FStar_Pprint.op_Hat_Hat FStar_Pprint.bang FStar_Pprint.lbrace in
        let uu____3698 =
          let uu____3699 = FStar_Pprint.op_Hat_Hat FStar_Pprint.comma break1 in
          separate_map_or_flow uu____3699 p_appTerm es in
        FStar_Pprint.surround (Prims.parse_int "2") (Prims.parse_int "0")
          uu____3697 uu____3698 FStar_Pprint.rbrace
    | FStar_Parser_AST.Labeled (e1,s,b) ->
        let uu____3703 = FStar_Pprint.break_ (Prims.parse_int "0") in
        let uu____3704 =
          let uu____3705 = str (Prims.strcat "(*" (Prims.strcat s "*)")) in
          let uu____3706 = p_term e1 in
          FStar_Pprint.op_Hat_Slash_Hat uu____3705 uu____3706 in
        FStar_Pprint.op_Hat_Hat uu____3703 uu____3704
    | FStar_Parser_AST.Op (op,args) when
        let uu____3711 = handleable_op op args in
        Prims.op_Negation uu____3711 ->
        let uu____3712 =
          let uu____3713 =
            let uu____3714 =
              let uu____3715 =
                let uu____3716 =
                  FStar_Util.string_of_int (FStar_List.length args) in
                Prims.strcat uu____3716
                  " arguments couldn't be handled by the pretty printer" in
              Prims.strcat " with " uu____3715 in
            Prims.strcat (FStar_Ident.text_of_id op) uu____3714 in
          Prims.strcat "Operation " uu____3713 in
        failwith uu____3712
    | FStar_Parser_AST.Uvar uu____3720 ->
        failwith "Unexpected universe variable out of universe context"
    | FStar_Parser_AST.Wild  ->
        let uu____3721 = p_term e in soft_parens_with_nesting uu____3721
    | FStar_Parser_AST.Const uu____3722 ->
        let uu____3723 = p_term e in soft_parens_with_nesting uu____3723
    | FStar_Parser_AST.Op uu____3724 ->
        let uu____3728 = p_term e in soft_parens_with_nesting uu____3728
    | FStar_Parser_AST.Tvar uu____3729 ->
        let uu____3730 = p_term e in soft_parens_with_nesting uu____3730
    | FStar_Parser_AST.Var uu____3731 ->
        let uu____3732 = p_term e in soft_parens_with_nesting uu____3732
    | FStar_Parser_AST.Name uu____3733 ->
        let uu____3734 = p_term e in soft_parens_with_nesting uu____3734
    | FStar_Parser_AST.Construct uu____3735 ->
        let uu____3741 = p_term e in soft_parens_with_nesting uu____3741
    | FStar_Parser_AST.Abs uu____3742 ->
        let uu____3746 = p_term e in soft_parens_with_nesting uu____3746
    | FStar_Parser_AST.App uu____3747 ->
        let uu____3751 = p_term e in soft_parens_with_nesting uu____3751
    | FStar_Parser_AST.Let uu____3752 ->
        let uu____3759 = p_term e in soft_parens_with_nesting uu____3759
    | FStar_Parser_AST.LetOpen uu____3760 ->
        let uu____3763 = p_term e in soft_parens_with_nesting uu____3763
    | FStar_Parser_AST.Seq uu____3764 ->
        let uu____3767 = p_term e in soft_parens_with_nesting uu____3767
    | FStar_Parser_AST.Bind uu____3768 ->
        let uu____3772 = p_term e in soft_parens_with_nesting uu____3772
    | FStar_Parser_AST.If uu____3773 ->
        let uu____3777 = p_term e in soft_parens_with_nesting uu____3777
    | FStar_Parser_AST.Match uu____3778 ->
        let uu____3786 = p_term e in soft_parens_with_nesting uu____3786
    | FStar_Parser_AST.TryWith uu____3787 ->
        let uu____3795 = p_term e in soft_parens_with_nesting uu____3795
    | FStar_Parser_AST.Ascribed uu____3796 ->
        let uu____3801 = p_term e in soft_parens_with_nesting uu____3801
    | FStar_Parser_AST.Record uu____3802 ->
        let uu____3809 = p_term e in soft_parens_with_nesting uu____3809
    | FStar_Parser_AST.Project uu____3810 ->
        let uu____3813 = p_term e in soft_parens_with_nesting uu____3813
    | FStar_Parser_AST.Product uu____3814 ->
        let uu____3818 = p_term e in soft_parens_with_nesting uu____3818
    | FStar_Parser_AST.Sum uu____3819 ->
        let uu____3823 = p_term e in soft_parens_with_nesting uu____3823
    | FStar_Parser_AST.QForall uu____3824 ->
        let uu____3831 = p_term e in soft_parens_with_nesting uu____3831
    | FStar_Parser_AST.QExists uu____3832 ->
        let uu____3839 = p_term e in soft_parens_with_nesting uu____3839
    | FStar_Parser_AST.Refine uu____3840 ->
        let uu____3843 = p_term e in soft_parens_with_nesting uu____3843
    | FStar_Parser_AST.NamedTyp uu____3844 ->
        let uu____3847 = p_term e in soft_parens_with_nesting uu____3847
    | FStar_Parser_AST.Requires uu____3848 ->
        let uu____3852 = p_term e in soft_parens_with_nesting uu____3852
    | FStar_Parser_AST.Ensures uu____3853 ->
        let uu____3857 = p_term e in soft_parens_with_nesting uu____3857
    | FStar_Parser_AST.Assign uu____3858 ->
        let uu____3861 = p_term e in soft_parens_with_nesting uu____3861
    | FStar_Parser_AST.Attributes uu____3862 ->
        let uu____3864 = p_term e in soft_parens_with_nesting uu____3864
and p_constant: FStar_Const.sconst -> FStar_Pprint.document =
  fun uu___106_3865  ->
    match uu___106_3865 with
    | FStar_Const.Const_effect  -> str "Effect"
    | FStar_Const.Const_unit  -> str "()"
    | FStar_Const.Const_bool b -> FStar_Pprint.doc_of_bool b
    | FStar_Const.Const_float x -> str (FStar_Util.string_of_float x)
    | FStar_Const.Const_char x ->
        let uu____3869 = FStar_Pprint.doc_of_char x in
        FStar_Pprint.squotes uu____3869
    | FStar_Const.Const_string (bytes,uu____3871) ->
        let uu____3874 = str (FStar_Util.string_of_bytes bytes) in
        FStar_Pprint.dquotes uu____3874
    | FStar_Const.Const_bytearray (bytes,uu____3876) ->
        let uu____3879 =
          let uu____3880 = str (FStar_Util.string_of_bytes bytes) in
          FStar_Pprint.dquotes uu____3880 in
        let uu____3881 = str "B" in
        FStar_Pprint.op_Hat_Hat uu____3879 uu____3881
    | FStar_Const.Const_int (repr,sign_width_opt) ->
        let signedness uu___104_3893 =
          match uu___104_3893 with
          | FStar_Const.Unsigned  -> str "u"
          | FStar_Const.Signed  -> FStar_Pprint.empty in
        let width uu___105_3897 =
          match uu___105_3897 with
          | FStar_Const.Int8  -> str "y"
          | FStar_Const.Int16  -> str "s"
          | FStar_Const.Int32  -> str "l"
          | FStar_Const.Int64  -> str "L" in
        let ending =
          default_or_map FStar_Pprint.empty
            (fun uu____3906  ->
               match uu____3906 with
               | (s,w) ->
                   let uu____3911 = signedness s in
                   let uu____3912 = width w in
                   FStar_Pprint.op_Hat_Hat uu____3911 uu____3912)
            sign_width_opt in
        let uu____3913 = str repr in
        FStar_Pprint.op_Hat_Hat uu____3913 ending
    | FStar_Const.Const_range r ->
        let uu____3915 = FStar_Range.string_of_range r in str uu____3915
    | FStar_Const.Const_reify  -> str "reify"
    | FStar_Const.Const_reflect lid ->
        let uu____3917 = p_quident lid in
        let uu____3918 =
          let uu____3919 =
            let uu____3920 = str "reflect" in
            FStar_Pprint.op_Hat_Hat FStar_Pprint.dot uu____3920 in
          FStar_Pprint.op_Hat_Hat FStar_Pprint.qmark uu____3919 in
        FStar_Pprint.op_Hat_Hat uu____3917 uu____3918
and p_universe: FStar_Parser_AST.term -> FStar_Pprint.document =
  fun u  ->
    let uu____3922 = str "u#" in
    let uu____3923 = p_atomicUniverse u in
    FStar_Pprint.op_Hat_Hat uu____3922 uu____3923
and p_universeFrom: FStar_Parser_AST.term -> FStar_Pprint.document =
  fun u  ->
    let uu____3925 =
      let uu____3926 = unparen u in uu____3926.FStar_Parser_AST.tm in
    match uu____3925 with
    | FStar_Parser_AST.Op
        ({ FStar_Ident.idText = "+"; FStar_Ident.idRange = uu____3927;_},u1::u2::[])
        ->
        let uu____3931 =
          let uu____3932 = p_universeFrom u1 in
          let uu____3933 =
            let uu____3934 = p_universeFrom u2 in
            FStar_Pprint.op_Hat_Slash_Hat FStar_Pprint.plus uu____3934 in
          FStar_Pprint.op_Hat_Slash_Hat uu____3932 uu____3933 in
        FStar_Pprint.group uu____3931
    | FStar_Parser_AST.App uu____3935 ->
        let uu____3939 = head_and_args u in
        (match uu____3939 with
         | (head1,args) ->
             let uu____3953 =
               let uu____3954 = unparen head1 in
               uu____3954.FStar_Parser_AST.tm in
             (match uu____3953 with
              | FStar_Parser_AST.Var maybe_max_lid when
                  FStar_Ident.lid_equals maybe_max_lid
                    FStar_Parser_Const.max_lid
                  ->
                  let uu____3956 =
                    let uu____3957 = p_qlident FStar_Parser_Const.max_lid in
                    let uu____3958 =
                      FStar_Pprint.separate_map FStar_Pprint.space
                        (fun uu____3964  ->
                           match uu____3964 with
                           | (u1,uu____3968) -> p_atomicUniverse u1) args in
                    op_Hat_Slash_Plus_Hat uu____3957 uu____3958 in
                  FStar_Pprint.group uu____3956
              | uu____3969 ->
                  let uu____3970 =
                    let uu____3971 = FStar_Parser_AST.term_to_string u in
                    FStar_Util.format1 "Invalid term in universe context %s"
                      uu____3971 in
                  failwith uu____3970))
    | uu____3972 -> p_atomicUniverse u
and p_atomicUniverse: FStar_Parser_AST.term -> FStar_Pprint.document =
  fun u  ->
    let uu____3974 =
      let uu____3975 = unparen u in uu____3975.FStar_Parser_AST.tm in
    match uu____3974 with
    | FStar_Parser_AST.Wild  -> FStar_Pprint.underscore
    | FStar_Parser_AST.Const (FStar_Const.Const_int (r,sw)) ->
        p_constant (FStar_Const.Const_int (r, sw))
    | FStar_Parser_AST.Uvar uu____3987 -> p_univar u
    | FStar_Parser_AST.Paren u1 ->
        let uu____3989 = p_universeFrom u1 in
        soft_parens_with_nesting uu____3989
    | FStar_Parser_AST.Op
        ({ FStar_Ident.idText = "+"; FStar_Ident.idRange = uu____3990;_},uu____3991::uu____3992::[])
        ->
        let uu____3994 = p_universeFrom u in
        soft_parens_with_nesting uu____3994
    | FStar_Parser_AST.App uu____3995 ->
        let uu____3999 = p_universeFrom u in
        soft_parens_with_nesting uu____3999
    | uu____4000 ->
        let uu____4001 =
          let uu____4002 = FStar_Parser_AST.term_to_string u in
          FStar_Util.format1 "Invalid term in universe context %s" uu____4002 in
        failwith uu____4001
and p_univar: FStar_Parser_AST.term -> FStar_Pprint.document =
  fun u  ->
    let uu____4004 =
      let uu____4005 = unparen u in uu____4005.FStar_Parser_AST.tm in
    match uu____4004 with
    | FStar_Parser_AST.Uvar id -> str (FStar_Ident.text_of_id id)
    | uu____4007 ->
        let uu____4008 =
          let uu____4009 = FStar_Parser_AST.term_to_string u in
          FStar_Util.format1 "Not a universe variable %s" uu____4009 in
        failwith uu____4008
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
       | FStar_Parser_AST.Module (uu____4029,decls) ->
           let uu____4033 =
             FStar_All.pipe_right decls (FStar_List.map decl_to_document) in
           FStar_All.pipe_right uu____4033
             (FStar_Pprint.separate FStar_Pprint.hardline)
       | FStar_Parser_AST.Interface (uu____4038,decls,uu____4040) ->
           let uu____4043 =
             FStar_All.pipe_right decls (FStar_List.map decl_to_document) in
           FStar_All.pipe_right uu____4043
             (FStar_Pprint.separate FStar_Pprint.hardline) in
     FStar_ST.write should_print_fs_typ_app false; res)
let comments_to_document:
  (Prims.string* FStar_Range.range) Prims.list -> FStar_Pprint.document =
  fun comments  ->
    FStar_Pprint.separate_map FStar_Pprint.hardline
      (fun uu____4065  ->
         match uu____4065 with | (comment,range) -> str comment) comments
let modul_with_comments_to_document:
  FStar_Parser_AST.modul ->
    (Prims.string* FStar_Range.range) Prims.list ->
      (FStar_Pprint.document* (Prims.string* FStar_Range.range) Prims.list)
  =
  fun m  ->
    fun comments  ->
      let decls =
        match m with
        | FStar_Parser_AST.Module (uu____4090,decls) -> decls
        | FStar_Parser_AST.Interface (uu____4094,decls,uu____4096) -> decls in
      FStar_ST.write should_print_fs_typ_app false;
      (match decls with
       | [] -> (FStar_Pprint.empty, comments)
       | d::ds ->
           let uu____4113 =
             match ds with
             | {
                 FStar_Parser_AST.d = FStar_Parser_AST.Pragma
                   (FStar_Parser_AST.LightOff );
                 FStar_Parser_AST.drange = uu____4120;
                 FStar_Parser_AST.doc = uu____4121;
                 FStar_Parser_AST.quals = uu____4122;
                 FStar_Parser_AST.attrs = uu____4123;_}::uu____4124 ->
                 let d0 = FStar_List.hd ds in
                 let uu____4128 =
                   let uu____4130 =
                     let uu____4132 = FStar_List.tl ds in d :: uu____4132 in
                   d0 :: uu____4130 in
                 (uu____4128, (d0.FStar_Parser_AST.drange))
             | uu____4135 -> ((d :: ds), (d.FStar_Parser_AST.drange)) in
           (match uu____4113 with
            | (decls1,first_range) ->
                let extract_decl_range d1 = d1.FStar_Parser_AST.drange in
                (FStar_ST.write comment_stack comments;
                 (let initial_comment =
                    let uu____4158 = FStar_Range.start_of_range first_range in
                    place_comments_until_pos (Prims.parse_int "0")
                      (Prims.parse_int "1") uu____4158 FStar_Pprint.empty in
                  let doc1 =
                    separate_map_with_comments FStar_Pprint.empty
                      FStar_Pprint.empty decl_to_document decls1
                      extract_decl_range in
                  let comments1 = FStar_ST.read comment_stack in
                  FStar_ST.write comment_stack [];
                  FStar_ST.write should_print_fs_typ_app false;
                  (let uu____4180 =
                     FStar_Pprint.op_Hat_Hat initial_comment doc1 in
                   (uu____4180, comments1))))))