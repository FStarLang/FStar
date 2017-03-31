open Prims
let should_print_fs_typ_app : Prims.bool FStar_ST.ref =
  FStar_Util.mk_ref false 
let with_fs_typ_app b printer t =
  let b0 = FStar_ST.read should_print_fs_typ_app  in
  FStar_ST.write should_print_fs_typ_app b;
  (let res = printer t  in FStar_ST.write should_print_fs_typ_app b0; res) 
let should_unparen : Prims.bool FStar_ST.ref = FStar_Util.mk_ref true 
let rec unparen : FStar_Parser_AST.term -> FStar_Parser_AST.term =
  fun t  ->
    let uu____44 =
      let uu____45 = FStar_ST.read should_unparen  in
      Prims.op_Negation uu____45  in
    if uu____44
    then t
    else
      (match t.FStar_Parser_AST.tm with
       | FStar_Parser_AST.Paren t1 -> unparen t1
       | uu____50 -> t)
  
let str : Prims.string -> FStar_Pprint.document =
  fun s  -> FStar_Pprint.doc_of_string s 
let default_or_map n1 f x = match x with | None  -> n1 | Some x' -> f x' 
let prefix2 :
  FStar_Pprint.document -> FStar_Pprint.document -> FStar_Pprint.document =
  fun prefix_  ->
    fun body  ->
      FStar_Pprint.prefix (Prims.parse_int "2") (Prims.parse_int "1") prefix_
        body
  
let op_Hat_Slash_Plus_Hat :
  FStar_Pprint.document -> FStar_Pprint.document -> FStar_Pprint.document =
  fun prefix_  -> fun body  -> prefix2 prefix_ body 
let jump2 : FStar_Pprint.document -> FStar_Pprint.document =
  fun body  ->
    FStar_Pprint.jump (Prims.parse_int "2") (Prims.parse_int "1") body
  
let infix2 :
  FStar_Pprint.document ->
    FStar_Pprint.document -> FStar_Pprint.document -> FStar_Pprint.document
  = FStar_Pprint.infix (Prims.parse_int "2") (Prims.parse_int "1") 
let infix0 :
  FStar_Pprint.document ->
    FStar_Pprint.document -> FStar_Pprint.document -> FStar_Pprint.document
  = FStar_Pprint.infix (Prims.parse_int "0") (Prims.parse_int "1") 
let break1 : FStar_Pprint.document =
  FStar_Pprint.break_ (Prims.parse_int "1") 
let separate_break_map sep f l =
  let uu____132 =
    let uu____133 =
      let uu____134 = FStar_Pprint.op_Hat_Hat sep break1  in
      FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____134  in
    FStar_Pprint.separate_map uu____133 f l  in
  FStar_Pprint.group uu____132 
let precede_break_separate_map prec sep f l =
  let uu____164 =
    let uu____165 = FStar_Pprint.op_Hat_Hat prec FStar_Pprint.space  in
    let uu____166 =
      let uu____167 = FStar_List.hd l  in FStar_All.pipe_right uu____167 f
       in
    FStar_Pprint.precede uu____165 uu____166  in
  let uu____168 =
    let uu____169 = FStar_List.tl l  in
    FStar_Pprint.concat_map
      (fun x  ->
         let uu____172 =
           let uu____173 =
             let uu____174 = f x  in
             FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____174  in
           FStar_Pprint.op_Hat_Hat sep uu____173  in
         FStar_Pprint.op_Hat_Hat break1 uu____172) uu____169
     in
  FStar_Pprint.op_Hat_Hat uu____164 uu____168 
let concat_break_map f l =
  let uu____194 =
    FStar_Pprint.concat_map
      (fun x  ->
         let uu____196 = f x  in FStar_Pprint.op_Hat_Hat uu____196 break1) l
     in
  FStar_Pprint.group uu____194 
let parens_with_nesting : FStar_Pprint.document -> FStar_Pprint.document =
  fun contents  ->
    FStar_Pprint.surround (Prims.parse_int "2") (Prims.parse_int "0")
      FStar_Pprint.lparen contents FStar_Pprint.rparen
  
let soft_parens_with_nesting : FStar_Pprint.document -> FStar_Pprint.document
  =
  fun contents  ->
    FStar_Pprint.soft_surround (Prims.parse_int "2") (Prims.parse_int "0")
      FStar_Pprint.lparen contents FStar_Pprint.rparen
  
let braces_with_nesting : FStar_Pprint.document -> FStar_Pprint.document =
  fun contents  ->
    FStar_Pprint.surround (Prims.parse_int "2") (Prims.parse_int "1")
      FStar_Pprint.lbrace contents FStar_Pprint.rbrace
  
let soft_braces_with_nesting : FStar_Pprint.document -> FStar_Pprint.document
  =
  fun contents  ->
    FStar_Pprint.soft_surround (Prims.parse_int "2") (Prims.parse_int "1")
      FStar_Pprint.lbrace contents FStar_Pprint.rbrace
  
let brackets_with_nesting : FStar_Pprint.document -> FStar_Pprint.document =
  fun contents  ->
    FStar_Pprint.surround (Prims.parse_int "2") (Prims.parse_int "1")
      FStar_Pprint.lbracket contents FStar_Pprint.rbracket
  
let soft_brackets_with_nesting :
  FStar_Pprint.document -> FStar_Pprint.document =
  fun contents  ->
    FStar_Pprint.soft_surround (Prims.parse_int "2") (Prims.parse_int "1")
      FStar_Pprint.lbracket contents FStar_Pprint.rbracket
  
let soft_begin_end_with_nesting :
  FStar_Pprint.document -> FStar_Pprint.document =
  fun contents  ->
    let uu____218 = str "begin"  in
    let uu____219 = str "end"  in
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
    (let uu____299 = FStar_Pprint.separate_map sep f xs  in
     FStar_Pprint.soft_surround n1 b opening uu____299 closing)
  
let doc_of_fsdoc :
  (Prims.string * (Prims.string * Prims.string) Prims.list) ->
    FStar_Pprint.document
  =
  fun uu____307  ->
    match uu____307 with
    | (comment,keywords1) ->
        let uu____321 =
          let uu____322 =
            let uu____324 = str comment  in
            let uu____325 =
              let uu____327 =
                let uu____329 =
                  FStar_Pprint.separate_map FStar_Pprint.comma
                    (fun uu____332  ->
                       match uu____332 with
                       | (k,v1) ->
                           let uu____337 =
                             let uu____339 = str k  in
                             let uu____340 =
                               let uu____342 =
                                 let uu____344 = str v1  in [uu____344]  in
                               FStar_Pprint.rarrow :: uu____342  in
                             uu____339 :: uu____340  in
                           FStar_Pprint.concat uu____337) keywords1
                   in
                [uu____329]  in
              FStar_Pprint.space :: uu____327  in
            uu____324 :: uu____325  in
          FStar_Pprint.concat uu____322  in
        FStar_Pprint.group uu____321
  
let is_unit : FStar_Parser_AST.term -> Prims.bool =
  fun e  ->
    let uu____348 =
      let uu____349 = unparen e  in uu____349.FStar_Parser_AST.tm  in
    match uu____348 with
    | FStar_Parser_AST.Const (FStar_Const.Const_unit ) -> true
    | uu____350 -> false
  
let matches_var : FStar_Parser_AST.term -> FStar_Ident.ident -> Prims.bool =
  fun t  ->
    fun x  ->
      let uu____357 =
        let uu____358 = unparen t  in uu____358.FStar_Parser_AST.tm  in
      match uu____357 with
      | FStar_Parser_AST.Var y ->
          x.FStar_Ident.idText = (FStar_Ident.text_of_lid y)
      | uu____360 -> false
  
let is_tuple_constructor : FStar_Ident.lident -> Prims.bool =
  FStar_Syntax_Util.is_tuple_data_lid' 
let is_dtuple_constructor : FStar_Ident.lident -> Prims.bool =
  FStar_Syntax_Util.is_dtuple_data_lid' 
let is_list_structure :
  FStar_Ident.lident ->
    FStar_Ident.lident -> FStar_Parser_AST.term -> Prims.bool
  =
  fun cons_lid1  ->
    fun nil_lid1  ->
      let rec aux e =
        let uu____377 =
          let uu____378 = unparen e  in uu____378.FStar_Parser_AST.tm  in
        match uu____377 with
        | FStar_Parser_AST.Construct (lid,[]) ->
            FStar_Ident.lid_equals lid nil_lid1
        | FStar_Parser_AST.Construct (lid,uu____386::(e2,uu____388)::[]) ->
            (FStar_Ident.lid_equals lid cons_lid1) && (aux e2)
        | uu____400 -> false  in
      aux
  
let is_list : FStar_Parser_AST.term -> Prims.bool =
  is_list_structure FStar_Syntax_Const.cons_lid FStar_Syntax_Const.nil_lid 
let is_lex_list : FStar_Parser_AST.term -> Prims.bool =
  is_list_structure FStar_Syntax_Const.lexcons_lid
    FStar_Syntax_Const.lextop_lid
  
let rec extract_from_list :
  FStar_Parser_AST.term -> FStar_Parser_AST.term Prims.list =
  fun e  ->
    let uu____409 =
      let uu____410 = unparen e  in uu____410.FStar_Parser_AST.tm  in
    match uu____409 with
    | FStar_Parser_AST.Construct (uu____412,[]) -> []
    | FStar_Parser_AST.Construct
        (uu____418,(e1,FStar_Parser_AST.Nothing )::(e2,FStar_Parser_AST.Nothing
                                                    )::[])
        -> let uu____430 = extract_from_list e2  in e1 :: uu____430
    | uu____432 ->
        let uu____433 =
          let uu____434 = FStar_Parser_AST.term_to_string e  in
          FStar_Util.format1 "Not a list %s" uu____434  in
        failwith uu____433
  
let is_array : FStar_Parser_AST.term -> Prims.bool =
  fun e  ->
    let uu____439 =
      let uu____440 = unparen e  in uu____440.FStar_Parser_AST.tm  in
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
  
let rec is_ref_set : FStar_Parser_AST.term -> Prims.bool =
  fun e  ->
    let uu____449 =
      let uu____450 = unparen e  in uu____450.FStar_Parser_AST.tm  in
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
  
let rec extract_from_ref_set :
  FStar_Parser_AST.term -> FStar_Parser_AST.term Prims.list =
  fun e  ->
    let uu____473 =
      let uu____474 = unparen e  in uu____474.FStar_Parser_AST.tm  in
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
        let uu____493 = extract_from_ref_set e1  in
        let uu____495 = extract_from_ref_set e2  in
        FStar_List.append uu____493 uu____495
    | uu____497 ->
        let uu____498 =
          let uu____499 = FStar_Parser_AST.term_to_string e  in
          FStar_Util.format1 "Not a ref set %s" uu____499  in
        failwith uu____498
  
let is_general_application : FStar_Parser_AST.term -> Prims.bool =
  fun e  ->
    let uu____504 = (is_array e) || (is_ref_set e)  in
    Prims.op_Negation uu____504
  
let is_general_construction : FStar_Parser_AST.term -> Prims.bool =
  fun e  ->
    let uu____508 = (is_list e) || (is_lex_list e)  in
    Prims.op_Negation uu____508
  
let is_general_prefix_op : Prims.string -> Prims.bool = fun op  -> op <> "~" 
let head_and_args :
  FStar_Parser_AST.term ->
    (FStar_Parser_AST.term * (FStar_Parser_AST.term * FStar_Parser_AST.imp)
      Prims.list)
  =
  fun e  ->
    let rec aux e1 acc =
      let uu____538 =
        let uu____539 = unparen e1  in uu____539.FStar_Parser_AST.tm  in
      match uu____538 with
      | FStar_Parser_AST.App (head1,arg,imp) -> aux head1 ((arg, imp) :: acc)
      | uu____550 -> (e1, acc)  in
    aux e []
  
type associativity =
  | Left 
  | Right 
  | NonAssoc 
let uu___is_Left : associativity -> Prims.bool =
  fun projectee  -> match projectee with | Left  -> true | uu____559 -> false 
let uu___is_Right : associativity -> Prims.bool =
  fun projectee  ->
    match projectee with | Right  -> true | uu____563 -> false
  
let uu___is_NonAssoc : associativity -> Prims.bool =
  fun projectee  ->
    match projectee with | NonAssoc  -> true | uu____567 -> false
  
type token = (FStar_Char.char,Prims.string) FStar_Util.either
type associativity_level = (associativity * token Prims.list)
let token_to_string :
  (FStar_BaseTypes.char,Prims.string) FStar_Util.either -> Prims.string =
  fun uu___128_577  ->
    match uu___128_577 with
    | FStar_Util.Inl c -> Prims.strcat (FStar_Util.string_of_char c) ".*"
    | FStar_Util.Inr s -> s
  
let matches_token :
  Prims.string ->
    (FStar_Char.char,Prims.string) FStar_Util.either -> Prims.bool
  =
  fun s  ->
    fun uu___129_589  ->
      match uu___129_589 with
      | FStar_Util.Inl c ->
          let uu____593 = FStar_String.get s (Prims.parse_int "0")  in
          uu____593 = c
      | FStar_Util.Inr s' -> s = s'
  
let matches_level s uu____611 =
  match uu____611 with
  | (assoc_levels,tokens) ->
      let uu____625 = FStar_List.tryFind (matches_token s) tokens  in
      uu____625 <> None
  
let opinfix4 uu____643 = (Right, [FStar_Util.Inr "**"]) 
let opinfix3 uu____658 =
  (Left, [FStar_Util.Inl '*'; FStar_Util.Inl '/'; FStar_Util.Inl '%']) 
let opinfix2 uu____677 = (Left, [FStar_Util.Inl '+'; FStar_Util.Inl '-']) 
let minus_lvl uu____694 = (Left, [FStar_Util.Inr "-"]) 
let opinfix1 uu____709 = (Right, [FStar_Util.Inl '@'; FStar_Util.Inl '^']) 
let pipe_right uu____726 = (Left, [FStar_Util.Inr "|>"]) 
let opinfix0d uu____741 = (Left, [FStar_Util.Inl '$']) 
let opinfix0c uu____756 =
  (Left, [FStar_Util.Inl '='; FStar_Util.Inl '<'; FStar_Util.Inl '>']) 
let equal uu____775 = (Left, [FStar_Util.Inr "="]) 
let opinfix0b uu____790 = (Left, [FStar_Util.Inl '&']) 
let opinfix0a uu____805 = (Left, [FStar_Util.Inl '|']) 
let colon_equals uu____820 = (NonAssoc, [FStar_Util.Inr ":="]) 
let amp uu____835 = (Right, [FStar_Util.Inr "&"]) 
let colon_colon uu____850 = (Right, [FStar_Util.Inr "::"]) 
let level_associativity_spec :
  (associativity * (FStar_Char.char,Prims.string) FStar_Util.either
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
let level_table :
  ((Prims.int * Prims.int * Prims.int) * (FStar_Char.char,Prims.string)
    FStar_Util.either Prims.list) Prims.list
  =
  let levels_from_associativity l uu___130_947 =
    match uu___130_947 with
    | Left  -> (l, l, (l - (Prims.parse_int "1")))
    | Right  -> ((l - (Prims.parse_int "1")), l, l)
    | NonAssoc  -> (l, l, l)  in
  FStar_List.mapi
    (fun i  ->
       fun uu____965  ->
         match uu____965 with
         | (assoc1,tokens) -> ((levels_from_associativity i assoc1), tokens))
    level_associativity_spec
  
let assign_levels :
  associativity_level Prims.list ->
    Prims.string -> (Prims.int * Prims.int * Prims.int)
  =
  fun token_associativity_spec  ->
    fun s  ->
      let uu____1007 = FStar_List.tryFind (matches_level s) level_table  in
      match uu____1007 with
      | Some (assoc_levels,uu____1032) -> assoc_levels
      | uu____1053 -> failwith (Prims.strcat "Unrecognized operator " s)
  
let max : Prims.int -> Prims.int -> Prims.int =
  fun k1  -> fun k2  -> if k1 > k2 then k1 else k2 
let max_level l =
  let find_level_and_max n1 level =
    let uu____1109 =
      FStar_List.tryFind
        (fun uu____1127  ->
           match uu____1127 with
           | (uu____1136,tokens) -> tokens = (Prims.snd level)) level_table
       in
    match uu____1109 with
    | Some ((uu____1156,l1,uu____1158),uu____1159) -> max n1 l1
    | None  ->
        let uu____1185 =
          let uu____1186 =
            let uu____1187 = FStar_List.map token_to_string (Prims.snd level)
               in
            FStar_String.concat "," uu____1187  in
          FStar_Util.format1 "Undefined associativity level %s" uu____1186
           in
        failwith uu____1185
     in
  FStar_List.fold_left find_level_and_max (Prims.parse_int "0") l 
let levels : Prims.string -> (Prims.int * Prims.int * Prims.int) =
  assign_levels level_associativity_spec 
let operatorInfix0ad12 uu____1212 =
  [opinfix0a ();
  opinfix0b ();
  opinfix0c ();
  opinfix0d ();
  opinfix1 ();
  opinfix2 ()] 
let is_operatorInfix0ad12 : Prims.string -> Prims.bool =
  fun op  ->
    let uu____1251 =
      FStar_List.tryFind (matches_level op) (operatorInfix0ad12 ())  in
    uu____1251 <> None
  
let is_operatorInfix34 : Prims.string -> Prims.bool =
  let opinfix34 = [opinfix3 (); opinfix4 ()]  in
  fun op  ->
    let uu____1299 = FStar_List.tryFind (matches_level op) opinfix34  in
    uu____1299 <> None
  
let comment_stack :
  (Prims.string * FStar_Range.range) Prims.list FStar_ST.ref =
  FStar_Util.mk_ref [] 
let with_comment printer tm tmrange =
  let rec comments_before_pos acc print_pos lookahead_pos =
    let uu____1367 = FStar_ST.read comment_stack  in
    match uu____1367 with
    | [] -> (acc, false)
    | (comment,crange)::cs ->
        let uu____1388 = FStar_Range.range_before_pos crange print_pos  in
        if uu____1388
        then
          (FStar_ST.write comment_stack cs;
           (let uu____1397 =
              let uu____1398 =
                let uu____1399 = str comment  in
                FStar_Pprint.op_Hat_Hat uu____1399 FStar_Pprint.hardline  in
              FStar_Pprint.op_Hat_Hat acc uu____1398  in
            comments_before_pos uu____1397 print_pos lookahead_pos))
        else
          (let uu____1401 = FStar_Range.range_before_pos crange lookahead_pos
              in
           (acc, uu____1401))
     in
  let uu____1402 =
    let uu____1405 =
      let uu____1406 = FStar_Range.start_of_range tmrange  in
      FStar_Range.end_of_line uu____1406  in
    let uu____1407 = FStar_Range.end_of_range tmrange  in
    comments_before_pos FStar_Pprint.empty uu____1405 uu____1407  in
  match uu____1402 with
  | (comments,has_lookahead) ->
      let printed_e = printer tm  in
      let comments1 =
        if has_lookahead
        then
          let pos = FStar_Range.end_of_range tmrange  in
          let uu____1413 = comments_before_pos comments pos pos  in
          Prims.fst uu____1413
        else comments  in
      let uu____1417 = FStar_Pprint.op_Hat_Hat comments1 printed_e  in
      FStar_Pprint.group uu____1417
  
let rec place_comments_until_pos :
  Prims.int ->
    Prims.int ->
      FStar_Range.pos -> FStar_Pprint.document -> FStar_Pprint.document
  =
  fun k  ->
    fun lbegin  ->
      fun pos_end  ->
        fun doc1  ->
          let uu____1430 = FStar_ST.read comment_stack  in
          match uu____1430 with
          | (comment,crange)::cs when
              FStar_Range.range_before_pos crange pos_end ->
              (FStar_ST.write comment_stack cs;
               (let lnum =
                  let uu____1454 =
                    let uu____1455 =
                      let uu____1456 = FStar_Range.start_of_range crange  in
                      FStar_Range.line_of_pos uu____1456  in
                    uu____1455 - lbegin  in
                  max k uu____1454  in
                let doc2 =
                  let uu____1458 =
                    let uu____1459 =
                      FStar_Pprint.repeat lnum FStar_Pprint.hardline  in
                    let uu____1460 = str comment  in
                    FStar_Pprint.op_Hat_Hat uu____1459 uu____1460  in
                  FStar_Pprint.op_Hat_Hat doc1 uu____1458  in
                let uu____1461 =
                  let uu____1462 = FStar_Range.end_of_range crange  in
                  FStar_Range.line_of_pos uu____1462  in
                place_comments_until_pos (Prims.parse_int "1") uu____1461
                  pos_end doc2))
          | uu____1463 ->
              let lnum =
                let uu____1468 =
                  let uu____1469 = FStar_Range.line_of_pos pos_end  in
                  uu____1469 - lbegin  in
                max (Prims.parse_int "1") uu____1468  in
              let uu____1470 = FStar_Pprint.repeat lnum FStar_Pprint.hardline
                 in
              FStar_Pprint.op_Hat_Hat doc1 uu____1470
  
let separate_map_with_comments prefix1 sep f xs extract_range =
  let fold_fun uu____1519 x =
    match uu____1519 with
    | (last_line,doc1) ->
        let r = extract_range x  in
        let doc2 =
          let uu____1529 = FStar_Range.start_of_range r  in
          place_comments_until_pos (Prims.parse_int "1") last_line uu____1529
            doc1
           in
        let uu____1530 =
          let uu____1531 = FStar_Range.end_of_range r  in
          FStar_Range.line_of_pos uu____1531  in
        let uu____1532 =
          let uu____1533 =
            let uu____1534 = f x  in FStar_Pprint.op_Hat_Hat sep uu____1534
             in
          FStar_Pprint.op_Hat_Hat doc2 uu____1533  in
        (uu____1530, uu____1532)
     in
  let uu____1535 =
    let uu____1539 = FStar_List.hd xs  in
    let uu____1540 = FStar_List.tl xs  in (uu____1539, uu____1540)  in
  match uu____1535 with
  | (x,xs1) ->
      let init1 =
        let uu____1550 =
          let uu____1551 =
            let uu____1552 = extract_range x  in
            FStar_Range.end_of_range uu____1552  in
          FStar_Range.line_of_pos uu____1551  in
        let uu____1553 =
          let uu____1554 = f x  in FStar_Pprint.op_Hat_Hat prefix1 uu____1554
           in
        (uu____1550, uu____1553)  in
      let uu____1555 = FStar_List.fold_left fold_fun init1 xs1  in
      Prims.snd uu____1555
  
let rec p_decl : FStar_Parser_AST.decl -> FStar_Pprint.document =
  fun d  ->
    let uu____1809 =
      let uu____1810 = FStar_Pprint.optional p_fsdoc d.FStar_Parser_AST.doc
         in
      let uu____1811 =
        let uu____1812 = p_attributes d.FStar_Parser_AST.attrs  in
        let uu____1813 =
          let uu____1814 = p_qualifiers d.FStar_Parser_AST.quals  in
          let uu____1815 =
            let uu____1816 = p_rawDecl d  in
            FStar_Pprint.op_Hat_Hat
              (if d.FStar_Parser_AST.quals = []
               then FStar_Pprint.empty
               else break1) uu____1816
             in
          FStar_Pprint.op_Hat_Hat uu____1814 uu____1815  in
        FStar_Pprint.op_Hat_Hat uu____1812 uu____1813  in
      FStar_Pprint.op_Hat_Hat uu____1810 uu____1811  in
    FStar_Pprint.group uu____1809

and p_attributes : FStar_Parser_AST.attributes_ -> FStar_Pprint.document =
  fun attrs  ->
    let uu____1819 =
      let uu____1820 = str "@"  in
      FStar_Pprint.op_Hat_Hat FStar_Pprint.lbracket uu____1820  in
    let uu____1821 =
      FStar_Pprint.op_Hat_Hat FStar_Pprint.rbracket FStar_Pprint.hardline  in
    soft_surround_separate_map (Prims.parse_int "0") (Prims.parse_int "2")
      FStar_Pprint.empty uu____1819 FStar_Pprint.space uu____1821
      p_atomicTerm attrs

and p_fsdoc : FStar_Parser_AST.fsdoc -> FStar_Pprint.document =
  fun uu____1822  ->
    match uu____1822 with
    | (doc1,kwd_args) ->
        let kwd_args_doc =
          match kwd_args with
          | [] -> FStar_Pprint.empty
          | kwd_args1 ->
              let process_kwd_arg uu____1843 =
                match uu____1843 with
                | (kwd1,arg) ->
                    let uu____1848 = str "@"  in
                    let uu____1849 =
                      let uu____1850 = str kwd1  in
                      let uu____1851 =
                        let uu____1852 = str arg  in
                        FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____1852
                         in
                      FStar_Pprint.op_Hat_Hat uu____1850 uu____1851  in
                    FStar_Pprint.op_Hat_Hat uu____1848 uu____1849
                 in
              let uu____1853 =
                let uu____1854 =
                  FStar_Pprint.separate_map FStar_Pprint.hardline
                    process_kwd_arg kwd_args1
                   in
                FStar_Pprint.op_Hat_Hat uu____1854 FStar_Pprint.hardline  in
              FStar_Pprint.op_Hat_Hat FStar_Pprint.hardline uu____1853
           in
        let uu____1857 =
          let uu____1858 =
            let uu____1859 =
              let uu____1860 =
                let uu____1861 = str doc1  in
                let uu____1862 =
                  let uu____1863 =
                    let uu____1864 =
                      FStar_Pprint.op_Hat_Hat FStar_Pprint.rparen
                        FStar_Pprint.hardline
                       in
                    FStar_Pprint.op_Hat_Hat FStar_Pprint.star uu____1864  in
                  FStar_Pprint.op_Hat_Hat kwd_args_doc uu____1863  in
                FStar_Pprint.op_Hat_Hat uu____1861 uu____1862  in
              FStar_Pprint.op_Hat_Hat FStar_Pprint.star uu____1860  in
            FStar_Pprint.op_Hat_Hat FStar_Pprint.star uu____1859  in
          FStar_Pprint.op_Hat_Hat FStar_Pprint.lparen uu____1858  in
        FStar_Pprint.op_Hat_Hat FStar_Pprint.hardline uu____1857

and p_rawDecl : FStar_Parser_AST.decl -> FStar_Pprint.document =
  fun d  ->
    match d.FStar_Parser_AST.d with
    | FStar_Parser_AST.Open uid ->
        let uu____1867 =
          let uu____1868 = str "open"  in
          let uu____1869 = p_quident uid  in
          FStar_Pprint.op_Hat_Slash_Hat uu____1868 uu____1869  in
        FStar_Pprint.group uu____1867
    | FStar_Parser_AST.Include uid ->
        let uu____1871 =
          let uu____1872 = str "include"  in
          let uu____1873 = p_quident uid  in
          FStar_Pprint.op_Hat_Slash_Hat uu____1872 uu____1873  in
        FStar_Pprint.group uu____1871
    | FStar_Parser_AST.ModuleAbbrev (uid1,uid2) ->
        let uu____1876 =
          let uu____1877 = str "module"  in
          let uu____1878 =
            let uu____1879 =
              let uu____1880 = p_uident uid1  in
              let uu____1881 =
                FStar_Pprint.op_Hat_Hat FStar_Pprint.space
                  FStar_Pprint.equals
                 in
              FStar_Pprint.op_Hat_Hat uu____1880 uu____1881  in
            FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____1879  in
          FStar_Pprint.op_Hat_Hat uu____1877 uu____1878  in
        let uu____1882 = p_quident uid2  in
        op_Hat_Slash_Plus_Hat uu____1876 uu____1882
    | FStar_Parser_AST.TopLevelModule uid ->
        let uu____1884 =
          let uu____1885 = str "module"  in
          let uu____1886 =
            let uu____1887 = p_quident uid  in
            FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____1887  in
          FStar_Pprint.op_Hat_Hat uu____1885 uu____1886  in
        FStar_Pprint.group uu____1884
    | FStar_Parser_AST.Tycon
        (true ,(FStar_Parser_AST.TyconAbbrev (uid,tpars,None ,t),None )::[])
        ->
        let effect_prefix_doc =
          let uu____1906 = str "effect"  in
          let uu____1907 =
            let uu____1908 = p_uident uid  in
            FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____1908  in
          FStar_Pprint.op_Hat_Hat uu____1906 uu____1907  in
        let uu____1909 =
          let uu____1910 = p_typars tpars  in
          FStar_Pprint.surround (Prims.parse_int "2") (Prims.parse_int "1")
            effect_prefix_doc uu____1910 FStar_Pprint.equals
           in
        let uu____1911 = p_typ t  in
        op_Hat_Slash_Plus_Hat uu____1909 uu____1911
    | FStar_Parser_AST.Tycon (false ,tcdefs) ->
        let uu____1921 = str "type"  in
        let uu____1922 = str "and"  in
        precede_break_separate_map uu____1921 uu____1922 p_fsdocTypeDeclPairs
          tcdefs
    | FStar_Parser_AST.TopLevelLet (q,lbs) ->
        let let_doc =
          let uu____1935 = str "let"  in
          let uu____1936 =
            let uu____1937 = p_letqualifier q  in
            FStar_Pprint.op_Hat_Hat uu____1937 FStar_Pprint.space  in
          FStar_Pprint.op_Hat_Hat uu____1935 uu____1936  in
        let uu____1938 =
          let uu____1939 = str "and"  in
          FStar_Pprint.op_Hat_Hat uu____1939 FStar_Pprint.space  in
        separate_map_with_comments let_doc uu____1938 p_letbinding lbs
          (fun uu____1942  ->
             match uu____1942 with
             | (p,t) ->
                 FStar_Range.union_ranges p.FStar_Parser_AST.prange
                   t.FStar_Parser_AST.range)
    | FStar_Parser_AST.Val (lid,t) ->
        let uu____1949 =
          let uu____1950 = str "val"  in
          let uu____1951 =
            let uu____1952 =
              let uu____1953 = p_lident lid  in
              let uu____1954 =
                FStar_Pprint.op_Hat_Hat FStar_Pprint.space FStar_Pprint.colon
                 in
              FStar_Pprint.op_Hat_Hat uu____1953 uu____1954  in
            FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____1952  in
          FStar_Pprint.op_Hat_Hat uu____1950 uu____1951  in
        let uu____1955 = p_typ t  in
        op_Hat_Slash_Plus_Hat uu____1949 uu____1955
    | FStar_Parser_AST.Assume (id,t) ->
        let decl_keyword =
          let uu____1959 =
            let uu____1960 =
              FStar_Util.char_at id.FStar_Ident.idText (Prims.parse_int "0")
               in
            FStar_All.pipe_right uu____1960 FStar_Util.is_upper  in
          if uu____1959
          then FStar_Pprint.empty
          else
            (let uu____1962 = str "val"  in
             FStar_Pprint.op_Hat_Hat uu____1962 FStar_Pprint.space)
           in
        let uu____1963 =
          let uu____1964 =
            let uu____1965 = p_ident id  in
            let uu____1966 =
              FStar_Pprint.op_Hat_Hat FStar_Pprint.space FStar_Pprint.colon
               in
            FStar_Pprint.op_Hat_Hat uu____1965 uu____1966  in
          FStar_Pprint.op_Hat_Hat decl_keyword uu____1964  in
        let uu____1967 = p_typ t  in
        op_Hat_Slash_Plus_Hat uu____1963 uu____1967
    | FStar_Parser_AST.Exception (uid,t_opt) ->
        let uu____1972 = str "exception"  in
        let uu____1973 =
          let uu____1974 =
            let uu____1975 = p_uident uid  in
            let uu____1976 =
              FStar_Pprint.optional
                (fun t  ->
                   let uu____1978 = str "of"  in
                   let uu____1979 = p_typ t  in
                   op_Hat_Slash_Plus_Hat uu____1978 uu____1979) t_opt
               in
            FStar_Pprint.op_Hat_Hat uu____1975 uu____1976  in
          FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____1974  in
        FStar_Pprint.op_Hat_Hat uu____1972 uu____1973
    | FStar_Parser_AST.NewEffect ne ->
        let uu____1981 = str "new_effect"  in
        let uu____1982 =
          let uu____1983 = p_newEffect ne  in
          FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____1983  in
        FStar_Pprint.op_Hat_Hat uu____1981 uu____1982
    | FStar_Parser_AST.SubEffect se ->
        let uu____1985 = str "sub_effect"  in
        let uu____1986 = p_subEffect se  in
        op_Hat_Slash_Plus_Hat uu____1985 uu____1986
    | FStar_Parser_AST.NewEffectForFree ne ->
        let uu____1988 = str "new_effect_for_free"  in
        let uu____1989 =
          let uu____1990 = p_newEffect ne  in
          FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____1990  in
        FStar_Pprint.op_Hat_Hat uu____1988 uu____1989
    | FStar_Parser_AST.Pragma p -> p_pragma p
    | FStar_Parser_AST.Fsdoc doc1 ->
        let uu____1993 = p_fsdoc doc1  in
        FStar_Pprint.op_Hat_Hat uu____1993 FStar_Pprint.hardline
    | FStar_Parser_AST.Main uu____1994 ->
        failwith "*Main declaration* : Is that really still in use ??"
    | FStar_Parser_AST.Tycon (true ,uu____1995) ->
        failwith
          "Effect abbreviation is expected to be defined by an abbreviation"

and p_pragma : FStar_Parser_AST.pragma -> FStar_Pprint.document =
  fun uu___131_2004  ->
    match uu___131_2004 with
    | FStar_Parser_AST.SetOptions s ->
        let uu____2006 = str "#set-options"  in
        let uu____2007 =
          let uu____2008 =
            let uu____2009 = str s  in FStar_Pprint.dquotes uu____2009  in
          FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____2008  in
        FStar_Pprint.op_Hat_Hat uu____2006 uu____2007
    | FStar_Parser_AST.ResetOptions s_opt ->
        let uu____2012 = str "#reset-options"  in
        let uu____2013 =
          FStar_Pprint.optional
            (fun s  ->
               let uu____2015 =
                 let uu____2016 = str s  in FStar_Pprint.dquotes uu____2016
                  in
               FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____2015) s_opt
           in
        FStar_Pprint.op_Hat_Hat uu____2012 uu____2013
    | FStar_Parser_AST.LightOff  ->
        (FStar_ST.write should_print_fs_typ_app true; str "#light \"off\"")

and p_typars : FStar_Parser_AST.binder Prims.list -> FStar_Pprint.document =
  fun bs  -> p_binders true bs

and p_fsdocTypeDeclPairs :
  (FStar_Parser_AST.tycon * FStar_Parser_AST.fsdoc Prims.option) ->
    FStar_Pprint.document
  =
  fun uu____2022  ->
    match uu____2022 with
    | (typedecl,fsdoc_opt) ->
        let uu____2030 = FStar_Pprint.optional p_fsdoc fsdoc_opt  in
        let uu____2031 = p_typeDecl typedecl  in
        FStar_Pprint.op_Hat_Hat uu____2030 uu____2031

and p_typeDecl : FStar_Parser_AST.tycon -> FStar_Pprint.document =
  fun uu___132_2032  ->
    match uu___132_2032 with
    | FStar_Parser_AST.TyconAbstract (lid,bs,typ_opt) ->
        let empty' uu____2043 = FStar_Pprint.empty  in
        p_typeDeclPrefix lid bs typ_opt empty'
    | FStar_Parser_AST.TyconAbbrev (lid,bs,typ_opt,t) ->
        let f uu____2055 =
          let uu____2056 = p_typ t  in prefix2 FStar_Pprint.equals uu____2056
           in
        p_typeDeclPrefix lid bs typ_opt f
    | FStar_Parser_AST.TyconRecord (lid,bs,typ_opt,record_field_decls) ->
        let p_recordFieldAndComments uu____2082 =
          match uu____2082 with
          | (lid1,t,doc_opt) ->
              let uu____2092 =
                FStar_Range.extend_to_end_of_line t.FStar_Parser_AST.range
                 in
              with_comment p_recordFieldDecl (lid1, t, doc_opt) uu____2092
           in
        let p_fields uu____2101 =
          let uu____2102 =
            let uu____2103 =
              let uu____2104 =
                let uu____2105 =
                  FStar_Pprint.op_Hat_Hat FStar_Pprint.semi break1  in
                FStar_Pprint.separate_map uu____2105 p_recordFieldAndComments
                  record_field_decls
                 in
              braces_with_nesting uu____2104  in
            FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____2103  in
          FStar_Pprint.op_Hat_Hat FStar_Pprint.equals uu____2102  in
        p_typeDeclPrefix lid bs typ_opt p_fields
    | FStar_Parser_AST.TyconVariant (lid,bs,typ_opt,ct_decls) ->
        let p_constructorBranchAndComments uu____2141 =
          match uu____2141 with
          | (uid,t_opt,doc_opt,use_of) ->
              let range =
                let uu____2157 =
                  let uu____2158 =
                    FStar_Util.map_opt t_opt
                      (fun t  -> t.FStar_Parser_AST.range)
                     in
                  FStar_Util.dflt uid.FStar_Ident.idRange uu____2158  in
                FStar_Range.extend_to_end_of_line uu____2157  in
              let p_constructorBranch decl =
                let uu____2177 =
                  let uu____2178 =
                    let uu____2179 = p_constructorDecl decl  in
                    FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____2179  in
                  FStar_Pprint.op_Hat_Hat FStar_Pprint.bar uu____2178  in
                FStar_Pprint.group uu____2177  in
              with_comment p_constructorBranch (uid, t_opt, doc_opt, use_of)
                range
           in
        let datacon_doc uu____2191 =
          let uu____2192 =
            FStar_Pprint.separate_map break1 p_constructorBranchAndComments
              ct_decls
             in
          FStar_Pprint.group uu____2192  in
        p_typeDeclPrefix lid bs typ_opt
          (fun uu____2199  ->
             let uu____2200 = datacon_doc ()  in
             prefix2 FStar_Pprint.equals uu____2200)

and p_typeDeclPrefix :
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
            let uu____2211 = p_ident lid  in
            let uu____2212 =
              let uu____2213 = cont ()  in
              FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____2213  in
            FStar_Pprint.op_Hat_Hat uu____2211 uu____2212
          else
            (let binders_doc =
               let uu____2216 = p_typars bs  in
               let uu____2217 =
                 FStar_Pprint.optional
                   (fun t  ->
                      let uu____2219 =
                        let uu____2220 =
                          let uu____2221 = p_typ t  in
                          FStar_Pprint.op_Hat_Hat FStar_Pprint.space
                            uu____2221
                           in
                        FStar_Pprint.op_Hat_Hat FStar_Pprint.colon uu____2220
                         in
                      FStar_Pprint.op_Hat_Hat break1 uu____2219) typ_opt
                  in
               FStar_Pprint.op_Hat_Hat uu____2216 uu____2217  in
             let uu____2222 = p_ident lid  in
             let uu____2223 = cont ()  in
             FStar_Pprint.surround (Prims.parse_int "2")
               (Prims.parse_int "1") uu____2222 binders_doc uu____2223)

and p_recordFieldDecl :
  (FStar_Ident.ident * FStar_Parser_AST.term * FStar_Parser_AST.fsdoc
    Prims.option) -> FStar_Pprint.document
  =
  fun uu____2224  ->
    match uu____2224 with
    | (lid,t,doc_opt) ->
        let uu____2234 =
          let uu____2235 = FStar_Pprint.optional p_fsdoc doc_opt  in
          let uu____2236 =
            let uu____2237 = p_lident lid  in
            let uu____2238 =
              let uu____2239 = p_typ t  in
              FStar_Pprint.op_Hat_Hat FStar_Pprint.colon uu____2239  in
            FStar_Pprint.op_Hat_Hat uu____2237 uu____2238  in
          FStar_Pprint.op_Hat_Hat uu____2235 uu____2236  in
        FStar_Pprint.group uu____2234

and p_constructorDecl :
  (FStar_Ident.ident * FStar_Parser_AST.term Prims.option *
    FStar_Parser_AST.fsdoc Prims.option * Prims.bool) ->
    FStar_Pprint.document
  =
  fun uu____2240  ->
    match uu____2240 with
    | (uid,t_opt,doc_opt,use_of) ->
        let sep = if use_of then str "of" else FStar_Pprint.colon  in
        let uid_doc = p_uident uid  in
        let uu____2258 = FStar_Pprint.optional p_fsdoc doc_opt  in
        let uu____2259 =
          let uu____2260 = FStar_Pprint.break_ (Prims.parse_int "0")  in
          let uu____2261 =
            default_or_map uid_doc
              (fun t  ->
                 let uu____2263 =
                   let uu____2264 =
                     FStar_Pprint.op_Hat_Hat FStar_Pprint.space sep  in
                   FStar_Pprint.op_Hat_Hat uid_doc uu____2264  in
                 let uu____2265 = p_typ t  in
                 op_Hat_Slash_Plus_Hat uu____2263 uu____2265) t_opt
             in
          FStar_Pprint.op_Hat_Hat uu____2260 uu____2261  in
        FStar_Pprint.op_Hat_Hat uu____2258 uu____2259

and p_letbinding :
  (FStar_Parser_AST.pattern * FStar_Parser_AST.term) -> FStar_Pprint.document
  =
  fun uu____2266  ->
    match uu____2266 with
    | (pat,e) ->
        let pat_doc =
          let uu____2272 =
            match pat.FStar_Parser_AST.pat with
            | FStar_Parser_AST.PatAscribed (pat1,t) ->
                let uu____2279 =
                  let uu____2280 =
                    let uu____2281 =
                      let uu____2282 =
                        let uu____2283 = p_tmArrow p_tmNoEq t  in
                        FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____2283
                         in
                      FStar_Pprint.op_Hat_Hat FStar_Pprint.colon uu____2282
                       in
                    FStar_Pprint.group uu____2281  in
                  FStar_Pprint.op_Hat_Hat break1 uu____2280  in
                (pat1, uu____2279)
            | uu____2284 -> (pat, FStar_Pprint.empty)  in
          match uu____2272 with
          | (pat1,ascr_doc) ->
              (match pat1.FStar_Parser_AST.pat with
               | FStar_Parser_AST.PatApp
                   ({
                      FStar_Parser_AST.pat = FStar_Parser_AST.PatVar
                        (x,uu____2288);
                      FStar_Parser_AST.prange = uu____2289;_},pats)
                   ->
                   let uu____2295 = p_lident x  in
                   let uu____2296 =
                     let uu____2297 =
                       FStar_Pprint.separate_map break1 p_atomicPattern pats
                        in
                     FStar_Pprint.op_Hat_Hat uu____2297 ascr_doc  in
                   FStar_Pprint.surround (Prims.parse_int "2")
                     (Prims.parse_int "1") uu____2295 uu____2296
                     FStar_Pprint.equals
               | uu____2298 ->
                   let uu____2299 =
                     let uu____2300 = p_tuplePattern pat1  in
                     let uu____2301 =
                       FStar_Pprint.op_Hat_Slash_Hat ascr_doc
                         FStar_Pprint.equals
                        in
                     FStar_Pprint.op_Hat_Hat uu____2300 uu____2301  in
                   FStar_Pprint.group uu____2299)
           in
        let uu____2302 = p_term e  in prefix2 pat_doc uu____2302

and p_newEffect : FStar_Parser_AST.effect_decl -> FStar_Pprint.document =
  fun uu___133_2303  ->
    match uu___133_2303 with
    | FStar_Parser_AST.RedefineEffect (lid,bs,t) ->
        p_effectRedefinition lid bs t
    | FStar_Parser_AST.DefineEffect (lid,bs,t,eff_decls,action_decls) ->
        p_effectDefinition lid bs t eff_decls action_decls

and p_effectRedefinition :
  FStar_Ident.ident ->
    FStar_Parser_AST.binder Prims.list ->
      FStar_Parser_AST.term -> FStar_Pprint.document
  =
  fun uid  ->
    fun bs  ->
      fun t  ->
        let uu____2324 = p_uident uid  in
        let uu____2325 = p_binders true bs  in
        let uu____2326 =
          let uu____2327 = p_simpleTerm t  in
          prefix2 FStar_Pprint.equals uu____2327  in
        FStar_Pprint.surround (Prims.parse_int "2") (Prims.parse_int "1")
          uu____2324 uu____2325 uu____2326

and p_effectDefinition :
  FStar_Ident.ident ->
    FStar_Parser_AST.binder Prims.list ->
      FStar_Parser_AST.term ->
        FStar_Parser_AST.decl Prims.list ->
          FStar_Parser_AST.decl Prims.list -> FStar_Pprint.document
  =
  fun uid  ->
    fun bs  ->
      fun t  ->
        fun eff_decls  ->
          fun action_decls  ->
            let uu____2336 =
              let uu____2337 =
                let uu____2338 =
                  let uu____2339 = p_uident uid  in
                  let uu____2340 = p_binders true bs  in
                  let uu____2341 =
                    let uu____2342 = p_typ t  in
                    prefix2 FStar_Pprint.colon uu____2342  in
                  FStar_Pprint.surround (Prims.parse_int "2")
                    (Prims.parse_int "1") uu____2339 uu____2340 uu____2341
                   in
                FStar_Pprint.group uu____2338  in
              let uu____2343 =
                let uu____2344 =
                  let uu____2345 = str "with"  in
                  let uu____2346 =
                    separate_break_map FStar_Pprint.semi p_effectDecl
                      eff_decls
                     in
                  prefix2 uu____2345 uu____2346  in
                let uu____2347 = p_actionDecls action_decls  in
                FStar_Pprint.op_Hat_Hat uu____2344 uu____2347  in
              FStar_Pprint.op_Hat_Slash_Hat uu____2337 uu____2343  in
            braces_with_nesting uu____2336

and p_actionDecls : FStar_Parser_AST.decl Prims.list -> FStar_Pprint.document
  =
  fun uu___134_2348  ->
    match uu___134_2348 with
    | [] -> FStar_Pprint.empty
    | l ->
        let uu____2352 =
          let uu____2353 = str "and actions"  in
          let uu____2354 =
            separate_break_map FStar_Pprint.semi p_effectDecl l  in
          prefix2 uu____2353 uu____2354  in
        FStar_Pprint.op_Hat_Hat break1 uu____2352

and p_effectDecl : FStar_Parser_AST.decl -> FStar_Pprint.document =
  fun d  ->
    match d.FStar_Parser_AST.d with
    | FStar_Parser_AST.Tycon
        (false ,(FStar_Parser_AST.TyconAbbrev (lid,[],None ,e),None )::[]) ->
        let uu____2371 =
          let uu____2372 = p_lident lid  in
          let uu____2373 =
            FStar_Pprint.op_Hat_Hat FStar_Pprint.space FStar_Pprint.equals
             in
          FStar_Pprint.op_Hat_Hat uu____2372 uu____2373  in
        let uu____2374 = p_simpleTerm e  in prefix2 uu____2371 uu____2374
    | uu____2375 ->
        let uu____2376 =
          let uu____2377 = FStar_Parser_AST.decl_to_string d  in
          FStar_Util.format1
            "Not a declaration of an effect member... or at least I hope so : %s"
            uu____2377
           in
        failwith uu____2376

and p_subEffect : FStar_Parser_AST.lift -> FStar_Pprint.document =
  fun lift  ->
    let uu____2379 =
      let uu____2380 = p_binders true lift.FStar_Parser_AST.effect_binders
         in
      FStar_Pprint.group uu____2380  in
    let uu____2381 =
      let uu____2382 =
        let uu____2383 =
          let uu____2384 =
            let uu____2385 =
              let uu____2386 = p_appTerm lift.FStar_Parser_AST.msource  in
              let uu____2387 =
                let uu____2388 = str "~>"  in
                FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____2388  in
              FStar_Pprint.op_Hat_Hat uu____2386 uu____2387  in
            FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____2385  in
          FStar_Pprint.op_Hat_Hat FStar_Pprint.colon uu____2384  in
        let uu____2389 = p_appTerm lift.FStar_Parser_AST.mdest  in
        prefix2 uu____2383 uu____2389  in
      let uu____2390 =
        let uu____2391 =
          let uu____2392 = p_liftDefinition lift.FStar_Parser_AST.lift_op  in
          braces_with_nesting uu____2392  in
        FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____2391  in
      FStar_Pprint.op_Hat_Hat uu____2382 uu____2390  in
    FStar_Pprint.op_Hat_Slash_Hat uu____2379 uu____2381

and p_liftDefinition : FStar_Parser_AST.lift_op -> FStar_Pprint.document =
  fun lift_op  ->
    let lifts =
      match lift_op with
      | FStar_Parser_AST.NonReifiableLift t -> [("lift_wp", t)]
      | FStar_Parser_AST.ReifiableLift (t1,t2) ->
          [("lif_wp", t1); ("lift", t2)]
      | FStar_Parser_AST.LiftForFree t -> [("lift", t)]  in
    let p_lift uu____2424 =
      match uu____2424 with
      | (kwd1,t) ->
          let uu____2429 =
            let uu____2430 = str kwd1  in
            let uu____2431 =
              FStar_Pprint.op_Hat_Hat FStar_Pprint.space FStar_Pprint.equals
               in
            FStar_Pprint.op_Hat_Hat uu____2430 uu____2431  in
          let uu____2432 = p_simpleTerm t  in prefix2 uu____2429 uu____2432
       in
    separate_break_map FStar_Pprint.semi p_lift lifts

and p_qualifier : FStar_Parser_AST.qualifier -> FStar_Pprint.document =
  fun uu___135_2435  ->
    match uu___135_2435 with
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

and p_qualifiers : FStar_Parser_AST.qualifiers -> FStar_Pprint.document =
  fun qs  ->
    let uu____2437 = FStar_Pprint.separate_map break1 p_qualifier qs  in
    FStar_Pprint.group uu____2437

and p_letqualifier : FStar_Parser_AST.let_qualifier -> FStar_Pprint.document
  =
  fun uu___136_2438  ->
    match uu___136_2438 with
    | FStar_Parser_AST.Rec  ->
        let uu____2439 = str "rec"  in
        FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____2439
    | FStar_Parser_AST.Mutable  ->
        let uu____2440 = str "mutable"  in
        FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____2440
    | FStar_Parser_AST.NoLetQualifier  -> FStar_Pprint.empty

and p_aqual : FStar_Parser_AST.arg_qualifier -> FStar_Pprint.document =
  fun uu___137_2441  ->
    match uu___137_2441 with
    | FStar_Parser_AST.Implicit  -> str "#"
    | FStar_Parser_AST.Equality  -> str "$"

and p_disjunctivePattern : FStar_Parser_AST.pattern -> FStar_Pprint.document
  =
  fun p  ->
    match p.FStar_Parser_AST.pat with
    | FStar_Parser_AST.PatOr pats ->
        let uu____2445 =
          let uu____2446 =
            let uu____2447 =
              FStar_Pprint.op_Hat_Hat FStar_Pprint.bar FStar_Pprint.space  in
            FStar_Pprint.op_Hat_Hat break1 uu____2447  in
          FStar_Pprint.separate_map uu____2446 p_tuplePattern pats  in
        FStar_Pprint.group uu____2445
    | uu____2448 -> p_tuplePattern p

and p_tuplePattern : FStar_Parser_AST.pattern -> FStar_Pprint.document =
  fun p  ->
    match p.FStar_Parser_AST.pat with
    | FStar_Parser_AST.PatTuple (pats,false ) ->
        let uu____2453 =
          let uu____2454 = FStar_Pprint.op_Hat_Hat FStar_Pprint.comma break1
             in
          FStar_Pprint.separate_map uu____2454 p_constructorPattern pats  in
        FStar_Pprint.group uu____2453
    | uu____2455 -> p_constructorPattern p

and p_constructorPattern : FStar_Parser_AST.pattern -> FStar_Pprint.document
  =
  fun p  ->
    match p.FStar_Parser_AST.pat with
    | FStar_Parser_AST.PatApp
        ({ FStar_Parser_AST.pat = FStar_Parser_AST.PatName maybe_cons_lid;
           FStar_Parser_AST.prange = uu____2458;_},hd1::tl1::[])
        when
        FStar_Ident.lid_equals maybe_cons_lid FStar_Syntax_Const.cons_lid ->
        let uu____2462 =
          FStar_Pprint.op_Hat_Hat FStar_Pprint.colon FStar_Pprint.colon  in
        let uu____2463 = p_constructorPattern hd1  in
        let uu____2464 = p_constructorPattern tl1  in
        infix0 uu____2462 uu____2463 uu____2464
    | FStar_Parser_AST.PatApp
        ({ FStar_Parser_AST.pat = FStar_Parser_AST.PatName uid;
           FStar_Parser_AST.prange = uu____2466;_},pats)
        ->
        let uu____2470 = p_quident uid  in
        let uu____2471 =
          FStar_Pprint.separate_map break1 p_atomicPattern pats  in
        prefix2 uu____2470 uu____2471
    | uu____2472 -> p_atomicPattern p

and p_atomicPattern : FStar_Parser_AST.pattern -> FStar_Pprint.document =
  fun p  ->
    match p.FStar_Parser_AST.pat with
    | FStar_Parser_AST.PatAscribed (pat,t) ->
        let uu____2476 =
          let uu____2479 =
            let uu____2480 = unparen t  in uu____2480.FStar_Parser_AST.tm  in
          ((pat.FStar_Parser_AST.pat), uu____2479)  in
        (match uu____2476 with
         | (FStar_Parser_AST.PatVar (lid,aqual),FStar_Parser_AST.Refine
            ({ FStar_Parser_AST.b = FStar_Parser_AST.Annotated (lid',t1);
               FStar_Parser_AST.brange = uu____2485;
               FStar_Parser_AST.blevel = uu____2486;
               FStar_Parser_AST.aqual = uu____2487;_},phi))
             when lid.FStar_Ident.idText = lid'.FStar_Ident.idText ->
             let uu____2491 =
               let uu____2492 = p_ident lid  in
               p_refinement aqual uu____2492 t1 phi  in
             soft_parens_with_nesting uu____2491
         | (FStar_Parser_AST.PatWild ,FStar_Parser_AST.Refine
            ({ FStar_Parser_AST.b = FStar_Parser_AST.NoName t1;
               FStar_Parser_AST.brange = uu____2494;
               FStar_Parser_AST.blevel = uu____2495;
               FStar_Parser_AST.aqual = uu____2496;_},phi))
             ->
             let uu____2498 =
               p_refinement None FStar_Pprint.underscore t1 phi  in
             soft_parens_with_nesting uu____2498
         | uu____2499 ->
             let uu____2502 =
               let uu____2503 = p_tuplePattern pat  in
               let uu____2504 =
                 let uu____2505 = FStar_Pprint.break_ (Prims.parse_int "0")
                    in
                 let uu____2506 =
                   let uu____2507 = p_typ t  in
                   FStar_Pprint.op_Hat_Hat FStar_Pprint.colon uu____2507  in
                 FStar_Pprint.op_Hat_Hat uu____2505 uu____2506  in
               FStar_Pprint.op_Hat_Hat uu____2503 uu____2504  in
             soft_parens_with_nesting uu____2502)
    | FStar_Parser_AST.PatList pats ->
        let uu____2510 =
          separate_break_map FStar_Pprint.semi p_tuplePattern pats  in
        FStar_Pprint.surround (Prims.parse_int "2") (Prims.parse_int "0")
          FStar_Pprint.lbracket uu____2510 FStar_Pprint.rbracket
    | FStar_Parser_AST.PatRecord pats ->
        let p_recordFieldPat uu____2520 =
          match uu____2520 with
          | (lid,pat) ->
              let uu____2525 = p_qlident lid  in
              let uu____2526 = p_tuplePattern pat  in
              infix2 FStar_Pprint.equals uu____2525 uu____2526
           in
        let uu____2527 =
          separate_break_map FStar_Pprint.semi p_recordFieldPat pats  in
        soft_braces_with_nesting uu____2527
    | FStar_Parser_AST.PatTuple (pats,true ) ->
        let uu____2533 =
          FStar_Pprint.op_Hat_Hat FStar_Pprint.lparen FStar_Pprint.bar  in
        let uu____2534 =
          separate_break_map FStar_Pprint.comma p_constructorPattern pats  in
        let uu____2535 =
          FStar_Pprint.op_Hat_Hat FStar_Pprint.bar FStar_Pprint.rparen  in
        FStar_Pprint.surround (Prims.parse_int "2") (Prims.parse_int "1")
          uu____2533 uu____2534 uu____2535
    | FStar_Parser_AST.PatTvar (tv,arg_qualifier_opt) -> p_tvar tv
    | FStar_Parser_AST.PatOp op ->
        let uu____2542 =
          let uu____2543 =
            let uu____2544 = str op  in
            let uu____2545 =
              FStar_Pprint.op_Hat_Hat FStar_Pprint.space FStar_Pprint.rparen
               in
            FStar_Pprint.op_Hat_Hat uu____2544 uu____2545  in
          FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____2543  in
        FStar_Pprint.op_Hat_Hat FStar_Pprint.lparen uu____2542
    | FStar_Parser_AST.PatWild  -> FStar_Pprint.underscore
    | FStar_Parser_AST.PatConst c -> p_constant c
    | FStar_Parser_AST.PatVar (lid,aqual) ->
        let uu____2551 = FStar_Pprint.optional p_aqual aqual  in
        let uu____2552 = p_lident lid  in
        FStar_Pprint.op_Hat_Hat uu____2551 uu____2552
    | FStar_Parser_AST.PatName uid -> p_quident uid
    | FStar_Parser_AST.PatOr uu____2554 -> failwith "Inner or pattern !"
    | FStar_Parser_AST.PatApp
      ({ FStar_Parser_AST.pat = FStar_Parser_AST.PatName _;
         FStar_Parser_AST.prange = _;_},_)|FStar_Parser_AST.PatTuple
      (_,false ) ->
        let uu____2562 = p_tuplePattern p  in
        soft_parens_with_nesting uu____2562
    | uu____2563 ->
        let uu____2564 =
          let uu____2565 = FStar_Parser_AST.pat_to_string p  in
          FStar_Util.format1 "Invalid pattern %s" uu____2565  in
        failwith uu____2564

and p_binder : Prims.bool -> FStar_Parser_AST.binder -> FStar_Pprint.document
  =
  fun is_atomic  ->
    fun b  ->
      match b.FStar_Parser_AST.b with
      | FStar_Parser_AST.Variable lid ->
          let uu____2569 =
            FStar_Pprint.optional p_aqual b.FStar_Parser_AST.aqual  in
          let uu____2570 = p_lident lid  in
          FStar_Pprint.op_Hat_Hat uu____2569 uu____2570
      | FStar_Parser_AST.TVariable lid -> p_lident lid
      | FStar_Parser_AST.Annotated (lid,t) ->
          let doc1 =
            let uu____2575 =
              let uu____2576 = unparen t  in uu____2576.FStar_Parser_AST.tm
               in
            match uu____2575 with
            | FStar_Parser_AST.Refine
                ({ FStar_Parser_AST.b = FStar_Parser_AST.Annotated (lid',t1);
                   FStar_Parser_AST.brange = uu____2579;
                   FStar_Parser_AST.blevel = uu____2580;
                   FStar_Parser_AST.aqual = uu____2581;_},phi)
                when lid.FStar_Ident.idText = lid'.FStar_Ident.idText ->
                let uu____2583 = p_ident lid  in
                p_refinement b.FStar_Parser_AST.aqual uu____2583 t1 phi
            | uu____2584 ->
                let uu____2585 =
                  FStar_Pprint.optional p_aqual b.FStar_Parser_AST.aqual  in
                let uu____2586 =
                  let uu____2587 = p_lident lid  in
                  let uu____2588 =
                    let uu____2589 =
                      let uu____2590 =
                        FStar_Pprint.break_ (Prims.parse_int "0")  in
                      let uu____2591 = p_tmFormula t  in
                      FStar_Pprint.op_Hat_Hat uu____2590 uu____2591  in
                    FStar_Pprint.op_Hat_Hat FStar_Pprint.colon uu____2589  in
                  FStar_Pprint.op_Hat_Hat uu____2587 uu____2588  in
                FStar_Pprint.op_Hat_Hat uu____2585 uu____2586
             in
          if is_atomic
          then
            let uu____2592 =
              let uu____2593 =
                FStar_Pprint.op_Hat_Hat doc1 FStar_Pprint.rparen  in
              FStar_Pprint.op_Hat_Hat FStar_Pprint.lparen uu____2593  in
            FStar_Pprint.group uu____2592
          else FStar_Pprint.group doc1
      | FStar_Parser_AST.TAnnotated uu____2595 ->
          failwith "Is this still used ?"
      | FStar_Parser_AST.NoName t ->
          let uu____2599 =
            let uu____2600 = unparen t  in uu____2600.FStar_Parser_AST.tm  in
          (match uu____2599 with
           | FStar_Parser_AST.Refine
               ({ FStar_Parser_AST.b = FStar_Parser_AST.NoName t1;
                  FStar_Parser_AST.brange = uu____2602;
                  FStar_Parser_AST.blevel = uu____2603;
                  FStar_Parser_AST.aqual = uu____2604;_},phi)
               ->
               if is_atomic
               then
                 let uu____2606 =
                   let uu____2607 =
                     let uu____2608 =
                       p_refinement b.FStar_Parser_AST.aqual
                         FStar_Pprint.underscore t1 phi
                        in
                     FStar_Pprint.op_Hat_Hat uu____2608 FStar_Pprint.rparen
                      in
                   FStar_Pprint.op_Hat_Hat FStar_Pprint.lparen uu____2607  in
                 FStar_Pprint.group uu____2606
               else
                 (let uu____2610 =
                    p_refinement b.FStar_Parser_AST.aqual
                      FStar_Pprint.underscore t1 phi
                     in
                  FStar_Pprint.group uu____2610)
           | uu____2611 -> if is_atomic then p_atomicTerm t else p_appTerm t)

and p_refinement :
  FStar_Parser_AST.arg_qualifier Prims.option ->
    FStar_Pprint.document ->
      FStar_Parser_AST.term -> FStar_Parser_AST.term -> FStar_Pprint.document
  =
  fun aqual_opt  ->
    fun binder  ->
      fun t  ->
        fun phi  ->
          let uu____2618 = FStar_Pprint.optional p_aqual aqual_opt  in
          let uu____2619 =
            let uu____2620 =
              let uu____2621 =
                let uu____2622 = p_appTerm t  in
                let uu____2623 =
                  let uu____2624 = p_noSeqTerm phi  in
                  soft_braces_with_nesting uu____2624  in
                FStar_Pprint.op_Hat_Hat uu____2622 uu____2623  in
              FStar_Pprint.op_Hat_Hat FStar_Pprint.colon uu____2621  in
            FStar_Pprint.op_Hat_Hat binder uu____2620  in
          FStar_Pprint.op_Hat_Hat uu____2618 uu____2619

and p_binders :
  Prims.bool -> FStar_Parser_AST.binder Prims.list -> FStar_Pprint.document =
  fun is_atomic  ->
    fun bs  -> FStar_Pprint.separate_map break1 (p_binder is_atomic) bs

and p_qlident : FStar_Ident.lid -> FStar_Pprint.document =
  fun lid  -> str (FStar_Ident.text_of_lid lid)

and p_quident : FStar_Ident.lid -> FStar_Pprint.document =
  fun lid  -> str (FStar_Ident.text_of_lid lid)

and p_ident : FStar_Ident.ident -> FStar_Pprint.document =
  fun lid  -> str (FStar_Ident.text_of_id lid)

and p_lident : FStar_Ident.ident -> FStar_Pprint.document =
  fun lid  -> str (FStar_Ident.text_of_id lid)

and p_uident : FStar_Ident.ident -> FStar_Pprint.document =
  fun lid  -> str (FStar_Ident.text_of_id lid)

and p_tvar : FStar_Ident.ident -> FStar_Pprint.document =
  fun lid  -> str (FStar_Ident.text_of_id lid)

and p_lidentOrUnderscore : FStar_Ident.ident -> FStar_Pprint.document =
  fun id  ->
    if
      FStar_Util.starts_with FStar_Ident.reserved_prefix
        id.FStar_Ident.idText
    then FStar_Pprint.underscore
    else p_lident id

and p_term : FStar_Parser_AST.term -> FStar_Pprint.document =
  fun e  ->
    let uu____2637 =
      let uu____2638 = unparen e  in uu____2638.FStar_Parser_AST.tm  in
    match uu____2637 with
    | FStar_Parser_AST.Seq (e1,e2) ->
        let uu____2641 =
          let uu____2642 =
            let uu____2643 = p_noSeqTerm e1  in
            FStar_Pprint.op_Hat_Hat uu____2643 FStar_Pprint.semi  in
          FStar_Pprint.group uu____2642  in
        let uu____2644 = p_term e2  in
        FStar_Pprint.op_Hat_Slash_Hat uu____2641 uu____2644
    | uu____2645 ->
        let uu____2646 = p_noSeqTerm e  in FStar_Pprint.group uu____2646

and p_noSeqTerm : FStar_Parser_AST.term -> FStar_Pprint.document =
  fun e  -> with_comment p_noSeqTerm' e e.FStar_Parser_AST.range

and p_noSeqTerm' : FStar_Parser_AST.term -> FStar_Pprint.document =
  fun e  ->
    let uu____2649 =
      let uu____2650 = unparen e  in uu____2650.FStar_Parser_AST.tm  in
    match uu____2649 with
    | FStar_Parser_AST.Ascribed (e1,t) ->
        let uu____2653 =
          let uu____2654 = p_tmIff e1  in
          let uu____2655 =
            let uu____2656 =
              let uu____2657 = p_typ t  in
              FStar_Pprint.op_Hat_Slash_Hat FStar_Pprint.colon uu____2657  in
            FStar_Pprint.op_Hat_Hat FStar_Pprint.langle uu____2656  in
          FStar_Pprint.op_Hat_Slash_Hat uu____2654 uu____2655  in
        FStar_Pprint.group uu____2653
    | FStar_Parser_AST.Op (op,e1::e2::e3::[]) when op = ".()<-" ->
        let uu____2663 =
          let uu____2664 =
            let uu____2665 =
              let uu____2666 = p_atomicTermNotQUident e1  in
              let uu____2667 =
                let uu____2668 =
                  let uu____2669 =
                    let uu____2670 = p_term e2  in
                    soft_parens_with_nesting uu____2670  in
                  let uu____2671 =
                    FStar_Pprint.op_Hat_Hat FStar_Pprint.space
                      FStar_Pprint.larrow
                     in
                  FStar_Pprint.op_Hat_Hat uu____2669 uu____2671  in
                FStar_Pprint.op_Hat_Hat FStar_Pprint.dot uu____2668  in
              FStar_Pprint.op_Hat_Hat uu____2666 uu____2667  in
            FStar_Pprint.group uu____2665  in
          let uu____2672 =
            let uu____2673 = p_noSeqTerm e3  in jump2 uu____2673  in
          FStar_Pprint.op_Hat_Hat uu____2664 uu____2672  in
        FStar_Pprint.group uu____2663
    | FStar_Parser_AST.Op (op,e1::e2::e3::[]) when op = ".[]<-" ->
        let uu____2679 =
          let uu____2680 =
            let uu____2681 =
              let uu____2682 = p_atomicTermNotQUident e1  in
              let uu____2683 =
                let uu____2684 =
                  let uu____2685 =
                    let uu____2686 = p_term e2  in
                    soft_brackets_with_nesting uu____2686  in
                  let uu____2687 =
                    FStar_Pprint.op_Hat_Hat FStar_Pprint.space
                      FStar_Pprint.larrow
                     in
                  FStar_Pprint.op_Hat_Hat uu____2685 uu____2687  in
                FStar_Pprint.op_Hat_Hat FStar_Pprint.dot uu____2684  in
              FStar_Pprint.op_Hat_Hat uu____2682 uu____2683  in
            FStar_Pprint.group uu____2681  in
          let uu____2688 =
            let uu____2689 = p_noSeqTerm e3  in jump2 uu____2689  in
          FStar_Pprint.op_Hat_Hat uu____2680 uu____2688  in
        FStar_Pprint.group uu____2679
    | FStar_Parser_AST.Requires (e1,wtf) ->
        let uu____2695 =
          let uu____2696 = str "requires"  in
          let uu____2697 = p_typ e1  in
          FStar_Pprint.op_Hat_Slash_Hat uu____2696 uu____2697  in
        FStar_Pprint.group uu____2695
    | FStar_Parser_AST.Ensures (e1,wtf) ->
        let uu____2703 =
          let uu____2704 = str "ensures"  in
          let uu____2705 = p_typ e1  in
          FStar_Pprint.op_Hat_Slash_Hat uu____2704 uu____2705  in
        FStar_Pprint.group uu____2703
    | FStar_Parser_AST.Attributes es ->
        let uu____2708 =
          let uu____2709 = str "attributes"  in
          let uu____2710 = FStar_Pprint.separate_map break1 p_atomicTerm es
             in
          FStar_Pprint.op_Hat_Slash_Hat uu____2709 uu____2710  in
        FStar_Pprint.group uu____2708
    | FStar_Parser_AST.If (e1,e2,e3) ->
        let uu____2714 = is_unit e3  in
        if uu____2714
        then
          let uu____2715 =
            let uu____2716 =
              let uu____2717 = str "if"  in
              let uu____2718 = p_noSeqTerm e1  in
              op_Hat_Slash_Plus_Hat uu____2717 uu____2718  in
            let uu____2719 =
              let uu____2720 = str "then"  in
              let uu____2721 = p_noSeqTerm e2  in
              op_Hat_Slash_Plus_Hat uu____2720 uu____2721  in
            FStar_Pprint.op_Hat_Slash_Hat uu____2716 uu____2719  in
          FStar_Pprint.group uu____2715
        else
          (let e2_doc =
             let uu____2724 =
               let uu____2725 = unparen e2  in uu____2725.FStar_Parser_AST.tm
                in
             match uu____2724 with
             | FStar_Parser_AST.If (uu____2726,uu____2727,e31) when
                 is_unit e31 ->
                 let uu____2729 = p_noSeqTerm e2  in
                 soft_parens_with_nesting uu____2729
             | uu____2730 -> p_noSeqTerm e2  in
           let uu____2731 =
             let uu____2732 =
               let uu____2733 = str "if"  in
               let uu____2734 = p_noSeqTerm e1  in
               op_Hat_Slash_Plus_Hat uu____2733 uu____2734  in
             let uu____2735 =
               let uu____2736 =
                 let uu____2737 = str "then"  in
                 op_Hat_Slash_Plus_Hat uu____2737 e2_doc  in
               let uu____2738 =
                 let uu____2739 = str "else"  in
                 let uu____2740 = p_noSeqTerm e3  in
                 op_Hat_Slash_Plus_Hat uu____2739 uu____2740  in
               FStar_Pprint.op_Hat_Slash_Hat uu____2736 uu____2738  in
             FStar_Pprint.op_Hat_Slash_Hat uu____2732 uu____2735  in
           FStar_Pprint.group uu____2731)
    | FStar_Parser_AST.TryWith (e1,branches) ->
        let uu____2753 =
          let uu____2754 =
            let uu____2755 = str "try"  in
            let uu____2756 = p_noSeqTerm e1  in prefix2 uu____2755 uu____2756
             in
          let uu____2757 =
            let uu____2758 = str "with"  in
            let uu____2759 =
              FStar_Pprint.separate_map FStar_Pprint.hardline p_patternBranch
                branches
               in
            FStar_Pprint.op_Hat_Slash_Hat uu____2758 uu____2759  in
          FStar_Pprint.op_Hat_Slash_Hat uu____2754 uu____2757  in
        FStar_Pprint.group uu____2753
    | FStar_Parser_AST.Match (e1,branches) ->
        let uu____2776 =
          let uu____2777 =
            let uu____2778 = str "match"  in
            let uu____2779 = p_noSeqTerm e1  in
            let uu____2780 = str "with"  in
            FStar_Pprint.surround (Prims.parse_int "2") (Prims.parse_int "1")
              uu____2778 uu____2779 uu____2780
             in
          let uu____2781 =
            FStar_Pprint.separate_map FStar_Pprint.hardline p_patternBranch
              branches
             in
          FStar_Pprint.op_Hat_Slash_Hat uu____2777 uu____2781  in
        FStar_Pprint.group uu____2776
    | FStar_Parser_AST.LetOpen (uid,e1) ->
        let uu____2788 =
          let uu____2789 =
            let uu____2790 = str "let open"  in
            let uu____2791 = p_quident uid  in
            let uu____2792 = str "in"  in
            FStar_Pprint.surround (Prims.parse_int "2") (Prims.parse_int "1")
              uu____2790 uu____2791 uu____2792
             in
          let uu____2793 = p_term e1  in
          FStar_Pprint.op_Hat_Slash_Hat uu____2789 uu____2793  in
        FStar_Pprint.group uu____2788
    | FStar_Parser_AST.Let (q,lbs,e1) ->
        let let_doc =
          let uu____2804 = str "let"  in
          let uu____2805 = p_letqualifier q  in
          FStar_Pprint.op_Hat_Hat uu____2804 uu____2805  in
        let uu____2806 =
          let uu____2807 =
            let uu____2808 =
              let uu____2809 = str "and"  in
              precede_break_separate_map let_doc uu____2809 p_letbinding lbs
               in
            let uu____2812 = str "in"  in
            FStar_Pprint.op_Hat_Slash_Hat uu____2808 uu____2812  in
          FStar_Pprint.group uu____2807  in
        let uu____2813 = p_term e1  in
        FStar_Pprint.op_Hat_Slash_Hat uu____2806 uu____2813
    | FStar_Parser_AST.Abs
        ({ FStar_Parser_AST.pat = FStar_Parser_AST.PatVar (x,typ_opt);
           FStar_Parser_AST.prange = uu____2816;_}::[],{
                                                         FStar_Parser_AST.tm
                                                           =
                                                           FStar_Parser_AST.Match
                                                           (maybe_x,branches);
                                                         FStar_Parser_AST.range
                                                           = uu____2819;
                                                         FStar_Parser_AST.level
                                                           = uu____2820;_})
        when matches_var maybe_x x ->
        let uu____2834 =
          let uu____2835 = str "function"  in
          let uu____2836 =
            FStar_Pprint.separate_map FStar_Pprint.hardline p_patternBranch
              branches
             in
          FStar_Pprint.op_Hat_Slash_Hat uu____2835 uu____2836  in
        FStar_Pprint.group uu____2834
    | FStar_Parser_AST.Assign (id,e1) ->
        let uu____2843 =
          let uu____2844 = p_lident id  in
          let uu____2845 =
            let uu____2846 = p_noSeqTerm e1  in
            FStar_Pprint.op_Hat_Slash_Hat FStar_Pprint.larrow uu____2846  in
          FStar_Pprint.op_Hat_Slash_Hat uu____2844 uu____2845  in
        FStar_Pprint.group uu____2843
    | uu____2847 -> p_typ e

and p_typ : FStar_Parser_AST.term -> FStar_Pprint.document =
  fun e  -> with_comment p_typ' e e.FStar_Parser_AST.range

and p_typ' : FStar_Parser_AST.term -> FStar_Pprint.document =
  fun e  ->
    let uu____2850 =
      let uu____2851 = unparen e  in uu____2851.FStar_Parser_AST.tm  in
    match uu____2850 with
    | FStar_Parser_AST.QForall (bs,trigger,e1)|FStar_Parser_AST.QExists
      (bs,trigger,e1) ->
        let uu____2867 =
          let uu____2868 =
            let uu____2869 = p_quantifier e  in
            FStar_Pprint.op_Hat_Hat uu____2869 FStar_Pprint.space  in
          let uu____2870 = p_binders true bs  in
          FStar_Pprint.soft_surround (Prims.parse_int "2")
            (Prims.parse_int "0") uu____2868 uu____2870 FStar_Pprint.dot
           in
        let uu____2871 =
          let uu____2872 = p_trigger trigger  in
          let uu____2873 = p_noSeqTerm e1  in
          FStar_Pprint.op_Hat_Hat uu____2872 uu____2873  in
        prefix2 uu____2867 uu____2871
    | uu____2874 -> p_simpleTerm e

and p_quantifier : FStar_Parser_AST.term -> FStar_Pprint.document =
  fun e  ->
    let uu____2876 =
      let uu____2877 = unparen e  in uu____2877.FStar_Parser_AST.tm  in
    match uu____2876 with
    | FStar_Parser_AST.QForall uu____2878 -> str "forall"
    | FStar_Parser_AST.QExists uu____2885 -> str "exists"
    | uu____2892 ->
        failwith "Imposible : p_quantifier called on a non-quantifier term"

and p_trigger :
  FStar_Parser_AST.term Prims.list Prims.list -> FStar_Pprint.document =
  fun uu___138_2893  ->
    match uu___138_2893 with
    | [] -> FStar_Pprint.empty
    | pats ->
        let uu____2900 =
          let uu____2901 =
            let uu____2902 = str "pattern"  in
            let uu____2903 =
              let uu____2904 =
                let uu____2905 = p_disjunctivePats pats  in jump2 uu____2905
                 in
              let uu____2906 =
                FStar_Pprint.op_Hat_Hat FStar_Pprint.rbrace break1  in
              FStar_Pprint.op_Hat_Slash_Hat uu____2904 uu____2906  in
            FStar_Pprint.op_Hat_Slash_Hat uu____2902 uu____2903  in
          FStar_Pprint.op_Hat_Hat FStar_Pprint.colon uu____2901  in
        FStar_Pprint.op_Hat_Hat FStar_Pprint.lbrace uu____2900

and p_disjunctivePats :
  FStar_Parser_AST.term Prims.list Prims.list -> FStar_Pprint.document =
  fun pats  ->
    let uu____2910 = str "\\/"  in
    FStar_Pprint.separate_map uu____2910 p_conjunctivePats pats

and p_conjunctivePats :
  FStar_Parser_AST.term Prims.list -> FStar_Pprint.document =
  fun pats  ->
    let uu____2914 =
      FStar_Pprint.separate_map FStar_Pprint.semi p_appTerm pats  in
    FStar_Pprint.group uu____2914

and p_simpleTerm : FStar_Parser_AST.term -> FStar_Pprint.document =
  fun e  ->
    let uu____2916 =
      let uu____2917 = unparen e  in uu____2917.FStar_Parser_AST.tm  in
    match uu____2916 with
    | FStar_Parser_AST.Abs (pats,e1) ->
        let uu____2922 =
          let uu____2923 = str "fun"  in
          let uu____2924 =
            let uu____2925 =
              FStar_Pprint.separate_map break1 p_atomicPattern pats  in
            FStar_Pprint.op_Hat_Slash_Hat uu____2925 FStar_Pprint.rarrow  in
          op_Hat_Slash_Plus_Hat uu____2923 uu____2924  in
        let uu____2926 = p_term e1  in
        op_Hat_Slash_Plus_Hat uu____2922 uu____2926
    | uu____2927 -> p_tmIff e

and p_maybeFocusArrow : Prims.bool -> FStar_Pprint.document =
  fun b  -> if b then str "~>" else FStar_Pprint.rarrow

and p_patternBranch :
  (FStar_Parser_AST.pattern * FStar_Parser_AST.term Prims.option *
    FStar_Parser_AST.term) -> FStar_Pprint.document
  =
  fun uu____2930  ->
    match uu____2930 with
    | (pat,when_opt,e) ->
        let maybe_paren =
          let uu____2943 =
            let uu____2944 = unparen e  in uu____2944.FStar_Parser_AST.tm  in
          match uu____2943 with
          | FStar_Parser_AST.Match _|FStar_Parser_AST.TryWith _ ->
              soft_begin_end_with_nesting
          | FStar_Parser_AST.Abs
              ({
                 FStar_Parser_AST.pat = FStar_Parser_AST.PatVar
                   (x,uu____2950);
                 FStar_Parser_AST.prange = uu____2951;_}::[],{
                                                               FStar_Parser_AST.tm
                                                                 =
                                                                 FStar_Parser_AST.Match
                                                                 (maybe_x,uu____2953);
                                                               FStar_Parser_AST.range
                                                                 = uu____2954;
                                                               FStar_Parser_AST.level
                                                                 = uu____2955;_})
              when matches_var maybe_x x -> soft_begin_end_with_nesting
          | uu____2969 -> (fun x  -> x)  in
        let uu____2971 =
          let uu____2972 =
            let uu____2973 =
              let uu____2974 =
                let uu____2975 =
                  let uu____2976 = p_disjunctivePattern pat  in
                  let uu____2977 =
                    let uu____2978 = p_maybeWhen when_opt  in
                    FStar_Pprint.op_Hat_Hat uu____2978 FStar_Pprint.rarrow
                     in
                  op_Hat_Slash_Plus_Hat uu____2976 uu____2977  in
                FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____2975  in
              FStar_Pprint.op_Hat_Hat FStar_Pprint.bar uu____2974  in
            FStar_Pprint.group uu____2973  in
          let uu____2979 =
            let uu____2980 = p_term e  in maybe_paren uu____2980  in
          op_Hat_Slash_Plus_Hat uu____2972 uu____2979  in
        FStar_Pprint.group uu____2971

and p_maybeWhen : FStar_Parser_AST.term Prims.option -> FStar_Pprint.document
  =
  fun uu___139_2981  ->
    match uu___139_2981 with
    | None  -> FStar_Pprint.empty
    | Some e ->
        let uu____2984 = str "when"  in
        let uu____2985 =
          let uu____2986 = p_tmFormula e  in
          FStar_Pprint.op_Hat_Hat uu____2986 FStar_Pprint.space  in
        op_Hat_Slash_Plus_Hat uu____2984 uu____2985

and p_tmIff : FStar_Parser_AST.term -> FStar_Pprint.document =
  fun e  ->
    let uu____2988 =
      let uu____2989 = unparen e  in uu____2989.FStar_Parser_AST.tm  in
    match uu____2988 with
    | FStar_Parser_AST.Op ("<==>",e1::e2::[]) ->
        let uu____2993 = str "<==>"  in
        let uu____2994 = p_tmImplies e1  in
        let uu____2995 = p_tmIff e2  in
        infix0 uu____2993 uu____2994 uu____2995
    | uu____2996 -> p_tmImplies e

and p_tmImplies : FStar_Parser_AST.term -> FStar_Pprint.document =
  fun e  ->
    let uu____2998 =
      let uu____2999 = unparen e  in uu____2999.FStar_Parser_AST.tm  in
    match uu____2998 with
    | FStar_Parser_AST.Op ("==>",e1::e2::[]) ->
        let uu____3003 = str "==>"  in
        let uu____3004 = p_tmArrow p_tmFormula e1  in
        let uu____3005 = p_tmImplies e2  in
        infix0 uu____3003 uu____3004 uu____3005
    | uu____3006 -> p_tmArrow p_tmFormula e

and p_tmArrow :
  (FStar_Parser_AST.term -> FStar_Pprint.document) ->
    FStar_Parser_AST.term -> FStar_Pprint.document
  =
  fun p_Tm  ->
    fun e  ->
      let uu____3011 =
        let uu____3012 = unparen e  in uu____3012.FStar_Parser_AST.tm  in
      match uu____3011 with
      | FStar_Parser_AST.Product (bs,tgt) ->
          let uu____3017 =
            let uu____3018 =
              FStar_Pprint.concat_map
                (fun b  ->
                   let uu____3020 = p_binder false b  in
                   let uu____3021 =
                     let uu____3022 =
                       FStar_Pprint.op_Hat_Hat FStar_Pprint.rarrow break1  in
                     FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____3022
                      in
                   FStar_Pprint.op_Hat_Hat uu____3020 uu____3021) bs
               in
            let uu____3023 = p_tmArrow p_Tm tgt  in
            FStar_Pprint.op_Hat_Hat uu____3018 uu____3023  in
          FStar_Pprint.group uu____3017
      | uu____3024 -> p_Tm e

and p_tmFormula : FStar_Parser_AST.term -> FStar_Pprint.document =
  fun e  ->
    let uu____3026 =
      let uu____3027 = unparen e  in uu____3027.FStar_Parser_AST.tm  in
    match uu____3026 with
    | FStar_Parser_AST.Op ("\\/",e1::e2::[]) ->
        let uu____3031 = str "\\/"  in
        let uu____3032 = p_tmFormula e1  in
        let uu____3033 = p_tmConjunction e2  in
        infix0 uu____3031 uu____3032 uu____3033
    | uu____3034 -> p_tmConjunction e

and p_tmConjunction : FStar_Parser_AST.term -> FStar_Pprint.document =
  fun e  ->
    let uu____3036 =
      let uu____3037 = unparen e  in uu____3037.FStar_Parser_AST.tm  in
    match uu____3036 with
    | FStar_Parser_AST.Op ("/\\",e1::e2::[]) ->
        let uu____3041 = str "/\\"  in
        let uu____3042 = p_tmConjunction e1  in
        let uu____3043 = p_tmTuple e2  in
        infix0 uu____3041 uu____3042 uu____3043
    | uu____3044 -> p_tmTuple e

and p_tmTuple : FStar_Parser_AST.term -> FStar_Pprint.document =
  fun e  -> with_comment p_tmTuple' e e.FStar_Parser_AST.range

and p_tmTuple' : FStar_Parser_AST.term -> FStar_Pprint.document =
  fun e  ->
    let uu____3047 =
      let uu____3048 = unparen e  in uu____3048.FStar_Parser_AST.tm  in
    match uu____3047 with
    | FStar_Parser_AST.Construct (lid,args) when is_tuple_constructor lid ->
        let uu____3057 = FStar_Pprint.op_Hat_Hat FStar_Pprint.comma break1
           in
        FStar_Pprint.separate_map uu____3057
          (fun uu____3060  ->
             match uu____3060 with | (e1,uu____3064) -> p_tmEq e1) args
    | uu____3065 -> p_tmEq e

and paren_if :
  Prims.int -> Prims.int -> FStar_Pprint.document -> FStar_Pprint.document =
  fun curr  ->
    fun mine  ->
      fun doc1  ->
        if mine <= curr
        then doc1
        else
          (let uu____3070 =
             let uu____3071 =
               FStar_Pprint.op_Hat_Hat doc1 FStar_Pprint.rparen  in
             FStar_Pprint.op_Hat_Hat FStar_Pprint.lparen uu____3071  in
           FStar_Pprint.group uu____3070)

and p_tmEq : FStar_Parser_AST.term -> FStar_Pprint.document =
  fun e  ->
    let n1 =
      max_level
        (FStar_List.append [colon_equals (); pipe_right ()]
           (operatorInfix0ad12 ()))
       in
    p_tmEq' n1 e

and p_tmEq' : Prims.int -> FStar_Parser_AST.term -> FStar_Pprint.document =
  fun curr  ->
    fun e  ->
      let uu____3096 =
        let uu____3097 = unparen e  in uu____3097.FStar_Parser_AST.tm  in
      match uu____3096 with
      | FStar_Parser_AST.Op (op,e1::e2::[]) when
          ((is_operatorInfix0ad12 op) || (op = "=")) || (op = "|>") ->
          let uu____3102 = levels op  in
          (match uu____3102 with
           | (left1,mine,right1) ->
               let uu____3109 =
                 let uu____3110 = str op  in
                 let uu____3111 = p_tmEq' left1 e1  in
                 let uu____3112 = p_tmEq' right1 e2  in
                 infix0 uu____3110 uu____3111 uu____3112  in
               paren_if curr mine uu____3109)
      | FStar_Parser_AST.Op (":=",e1::e2::[]) ->
          let uu____3116 =
            let uu____3117 = p_tmEq e1  in
            let uu____3118 =
              let uu____3119 =
                let uu____3120 =
                  let uu____3121 = p_tmEq e2  in
                  op_Hat_Slash_Plus_Hat FStar_Pprint.equals uu____3121  in
                FStar_Pprint.op_Hat_Hat FStar_Pprint.colon uu____3120  in
              FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____3119  in
            FStar_Pprint.op_Hat_Hat uu____3117 uu____3118  in
          FStar_Pprint.group uu____3116
      | uu____3122 -> p_tmNoEq e

and p_tmNoEq : FStar_Parser_AST.term -> FStar_Pprint.document =
  fun e  ->
    let n1 = max_level [colon_colon (); amp (); opinfix3 (); opinfix4 ()]  in
    p_tmNoEq' n1 e

and p_tmNoEq' : Prims.int -> FStar_Parser_AST.term -> FStar_Pprint.document =
  fun curr  ->
    fun e  ->
      let uu____3152 =
        let uu____3153 = unparen e  in uu____3153.FStar_Parser_AST.tm  in
      match uu____3152 with
      | FStar_Parser_AST.Construct (lid,(e1,uu____3156)::(e2,uu____3158)::[])
          when
          (FStar_Ident.lid_equals lid FStar_Syntax_Const.cons_lid) &&
            (let uu____3168 = is_list e  in Prims.op_Negation uu____3168)
          ->
          let op = "::"  in
          let uu____3170 = levels op  in
          (match uu____3170 with
           | (left1,mine,right1) ->
               let uu____3177 =
                 let uu____3178 = str op  in
                 let uu____3179 = p_tmNoEq' left1 e1  in
                 let uu____3180 = p_tmNoEq' right1 e2  in
                 infix0 uu____3178 uu____3179 uu____3180  in
               paren_if curr mine uu____3177)
      | FStar_Parser_AST.Sum (binders,res) ->
          let op = "&"  in
          let uu____3186 = levels op  in
          (match uu____3186 with
           | (left1,mine,right1) ->
               let p_dsumfst b =
                 let uu____3197 = p_binder false b  in
                 let uu____3198 =
                   let uu____3199 =
                     let uu____3200 = str "&"  in
                     FStar_Pprint.op_Hat_Hat uu____3200 break1  in
                   FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____3199  in
                 FStar_Pprint.op_Hat_Hat uu____3197 uu____3198  in
               let uu____3201 =
                 let uu____3202 = FStar_Pprint.concat_map p_dsumfst binders
                    in
                 let uu____3203 = p_tmNoEq' right1 res  in
                 FStar_Pprint.op_Hat_Hat uu____3202 uu____3203  in
               paren_if curr mine uu____3201)
      | FStar_Parser_AST.Op (op,e1::e2::[]) when is_operatorInfix34 op ->
          let uu____3208 = levels op  in
          (match uu____3208 with
           | (left1,mine,right1) ->
               let uu____3215 =
                 let uu____3216 = str op  in
                 let uu____3217 = p_tmNoEq' left1 e1  in
                 let uu____3218 = p_tmNoEq' right1 e2  in
                 infix0 uu____3216 uu____3217 uu____3218  in
               paren_if curr mine uu____3215)
      | FStar_Parser_AST.Op ("-",e1::[]) ->
          let uu____3221 = levels "-"  in
          (match uu____3221 with
           | (left1,mine,right1) ->
               let uu____3228 = p_tmNoEq' mine e1  in
               FStar_Pprint.op_Hat_Slash_Hat FStar_Pprint.minus uu____3228)
      | FStar_Parser_AST.NamedTyp (lid,e1) ->
          let uu____3231 =
            let uu____3232 = p_lidentOrUnderscore lid  in
            let uu____3233 =
              let uu____3234 = p_appTerm e1  in
              FStar_Pprint.op_Hat_Slash_Hat FStar_Pprint.colon uu____3234  in
            FStar_Pprint.op_Hat_Slash_Hat uu____3232 uu____3233  in
          FStar_Pprint.group uu____3231
      | FStar_Parser_AST.Refine (b,phi) -> p_refinedBinder b phi
      | FStar_Parser_AST.Record (with_opt,record_fields) ->
          let uu____3247 =
            let uu____3248 =
              default_or_map FStar_Pprint.empty p_with_clause with_opt  in
            let uu____3249 =
              let uu____3250 =
                FStar_Pprint.op_Hat_Hat FStar_Pprint.semi break1  in
              FStar_Pprint.separate_map uu____3250 p_simpleDef record_fields
               in
            FStar_Pprint.op_Hat_Hat uu____3248 uu____3249  in
          braces_with_nesting uu____3247
      | FStar_Parser_AST.Op ("~",e1::[]) ->
          let uu____3255 =
            let uu____3256 = str "~"  in
            let uu____3257 = p_atomicTerm e1  in
            FStar_Pprint.op_Hat_Hat uu____3256 uu____3257  in
          FStar_Pprint.group uu____3255
      | uu____3258 -> p_appTerm e

and p_with_clause : FStar_Parser_AST.term -> FStar_Pprint.document =
  fun e  ->
    let uu____3260 = p_appTerm e  in
    let uu____3261 =
      let uu____3262 =
        let uu____3263 = str "with"  in
        FStar_Pprint.op_Hat_Hat uu____3263 break1  in
      FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____3262  in
    FStar_Pprint.op_Hat_Hat uu____3260 uu____3261

and p_refinedBinder :
  FStar_Parser_AST.binder -> FStar_Parser_AST.term -> FStar_Pprint.document =
  fun b  ->
    fun phi  ->
      match b.FStar_Parser_AST.b with
      | FStar_Parser_AST.Annotated (lid,t) ->
          let uu____3268 =
            let uu____3269 = p_lident lid  in
            p_refinement b.FStar_Parser_AST.aqual uu____3269 t phi  in
          soft_parens_with_nesting uu____3268
      | FStar_Parser_AST.TAnnotated uu____3270 ->
          failwith "Is this still used ?"
      | FStar_Parser_AST.Variable _
        |FStar_Parser_AST.TVariable _|FStar_Parser_AST.NoName _ ->
          let uu____3276 =
            let uu____3277 = FStar_Parser_AST.binder_to_string b  in
            FStar_Util.format1
              "Imposible : a refined binder ought to be annotated %s"
              uu____3277
             in
          failwith uu____3276

and p_simpleDef :
  (FStar_Ident.lid * FStar_Parser_AST.term) -> FStar_Pprint.document =
  fun uu____3278  ->
    match uu____3278 with
    | (lid,e) ->
        let uu____3283 =
          let uu____3284 = p_qlident lid  in
          let uu____3285 =
            let uu____3286 = p_tmIff e  in
            FStar_Pprint.op_Hat_Slash_Hat FStar_Pprint.equals uu____3286  in
          FStar_Pprint.op_Hat_Slash_Hat uu____3284 uu____3285  in
        FStar_Pprint.group uu____3283

and p_appTerm : FStar_Parser_AST.term -> FStar_Pprint.document =
  fun e  ->
    let uu____3288 =
      let uu____3289 = unparen e  in uu____3289.FStar_Parser_AST.tm  in
    match uu____3288 with
    | FStar_Parser_AST.App uu____3290 when is_general_application e ->
        let uu____3294 = head_and_args e  in
        (match uu____3294 with
         | (head1,args) ->
             let uu____3308 =
               let uu____3314 = FStar_ST.read should_print_fs_typ_app  in
               if uu____3314
               then
                 let uu____3322 =
                   FStar_Util.take
                     (fun uu____3333  ->
                        match uu____3333 with
                        | (uu____3336,aq) -> aq = FStar_Parser_AST.FsTypApp)
                     args
                    in
                 match uu____3322 with
                 | (fs_typ_args,args1) ->
                     let uu____3357 =
                       let uu____3358 = p_indexingTerm head1  in
                       let uu____3359 =
                         let uu____3360 =
                           FStar_Pprint.op_Hat_Hat FStar_Pprint.comma break1
                            in
                         soft_surround_separate_map (Prims.parse_int "2")
                           (Prims.parse_int "0") FStar_Pprint.empty
                           FStar_Pprint.langle uu____3360 FStar_Pprint.rangle
                           p_fsTypArg fs_typ_args
                          in
                       FStar_Pprint.op_Hat_Hat uu____3358 uu____3359  in
                     (uu____3357, args1)
               else
                 (let uu____3367 = p_indexingTerm head1  in
                  (uu____3367, args))
                in
             (match uu____3308 with
              | (head_doc,args1) ->
                  let uu____3379 =
                    let uu____3380 =
                      FStar_Pprint.op_Hat_Hat head_doc FStar_Pprint.space  in
                    soft_surround_separate_map (Prims.parse_int "2")
                      (Prims.parse_int "0") head_doc uu____3380 break1
                      FStar_Pprint.empty p_argTerm args1
                     in
                  FStar_Pprint.group uu____3379))
    | FStar_Parser_AST.Construct (lid,args) when
        (is_general_construction e) &&
          (Prims.op_Negation (is_dtuple_constructor lid))
        ->
        (match args with
         | [] -> p_quident lid
         | arg::[] ->
             let uu____3400 =
               let uu____3401 = p_quident lid  in
               let uu____3402 = p_argTerm arg  in
               FStar_Pprint.op_Hat_Slash_Hat uu____3401 uu____3402  in
             FStar_Pprint.group uu____3400
         | hd1::tl1 ->
             let uu____3412 =
               let uu____3413 =
                 let uu____3414 =
                   let uu____3415 = p_quident lid  in
                   let uu____3416 = p_argTerm hd1  in
                   prefix2 uu____3415 uu____3416  in
                 FStar_Pprint.group uu____3414  in
               let uu____3417 =
                 let uu____3418 =
                   FStar_Pprint.separate_map break1 p_argTerm tl1  in
                 jump2 uu____3418  in
               FStar_Pprint.op_Hat_Hat uu____3413 uu____3417  in
             FStar_Pprint.group uu____3412)
    | uu____3421 -> p_indexingTerm e

and p_argTerm :
  (FStar_Parser_AST.term * FStar_Parser_AST.imp) -> FStar_Pprint.document =
  fun arg_imp  ->
    match arg_imp with
    | ({ FStar_Parser_AST.tm = FStar_Parser_AST.Uvar uu____3425;
         FStar_Parser_AST.range = uu____3426;
         FStar_Parser_AST.level = uu____3427;_},FStar_Parser_AST.UnivApp
       ) -> p_univar (Prims.fst arg_imp)
    | (u,FStar_Parser_AST.UnivApp ) -> p_universe u
    | (e,FStar_Parser_AST.FsTypApp ) ->
        (FStar_Util.print_warning
           "Unexpected FsTypApp, output might not be formatted correctly.\n";
         (let uu____3431 = p_indexingTerm e  in
          FStar_Pprint.surround (Prims.parse_int "2") (Prims.parse_int "1")
            FStar_Pprint.langle uu____3431 FStar_Pprint.rangle))
    | (e,FStar_Parser_AST.Hash ) ->
        let uu____3433 = str "#"  in
        let uu____3434 = p_indexingTerm e  in
        FStar_Pprint.op_Hat_Hat uu____3433 uu____3434
    | (e,FStar_Parser_AST.Nothing ) -> p_indexingTerm e

and p_fsTypArg :
  (FStar_Parser_AST.term * FStar_Parser_AST.imp) -> FStar_Pprint.document =
  fun uu____3436  ->
    match uu____3436 with | (e,uu____3440) -> p_indexingTerm e

and p_indexingTerm_aux :
  (FStar_Parser_AST.term -> FStar_Pprint.document) ->
    FStar_Parser_AST.term -> FStar_Pprint.document
  =
  fun exit1  ->
    fun e  ->
      let uu____3445 =
        let uu____3446 = unparen e  in uu____3446.FStar_Parser_AST.tm  in
      match uu____3445 with
      | FStar_Parser_AST.Op (".()",e1::e2::[]) ->
          let uu____3450 =
            let uu____3451 = p_indexingTerm_aux p_atomicTermNotQUident e1  in
            let uu____3452 =
              let uu____3453 =
                let uu____3454 = p_term e2  in
                soft_parens_with_nesting uu____3454  in
              FStar_Pprint.op_Hat_Hat FStar_Pprint.dot uu____3453  in
            FStar_Pprint.op_Hat_Hat uu____3451 uu____3452  in
          FStar_Pprint.group uu____3450
      | FStar_Parser_AST.Op (".[]",e1::e2::[]) ->
          let uu____3458 =
            let uu____3459 = p_indexingTerm_aux p_atomicTermNotQUident e1  in
            let uu____3460 =
              let uu____3461 =
                let uu____3462 = p_term e2  in
                soft_brackets_with_nesting uu____3462  in
              FStar_Pprint.op_Hat_Hat FStar_Pprint.dot uu____3461  in
            FStar_Pprint.op_Hat_Hat uu____3459 uu____3460  in
          FStar_Pprint.group uu____3458
      | uu____3463 -> exit1 e

and p_indexingTerm : FStar_Parser_AST.term -> FStar_Pprint.document =
  fun e  -> p_indexingTerm_aux p_atomicTerm e

and p_atomicTerm : FStar_Parser_AST.term -> FStar_Pprint.document =
  fun e  ->
    let uu____3466 =
      let uu____3467 = unparen e  in uu____3467.FStar_Parser_AST.tm  in
    match uu____3466 with
    | FStar_Parser_AST.LetOpen (lid,e1) ->
        let uu____3470 = p_quident lid  in
        let uu____3471 =
          let uu____3472 =
            let uu____3473 = p_term e1  in
            soft_parens_with_nesting uu____3473  in
          FStar_Pprint.op_Hat_Hat FStar_Pprint.dot uu____3472  in
        FStar_Pprint.op_Hat_Hat uu____3470 uu____3471
    | FStar_Parser_AST.Name lid -> p_quident lid
    | FStar_Parser_AST.Op (op,e1::[]) when is_general_prefix_op op ->
        let uu____3478 = str op  in
        let uu____3479 = p_atomicTerm e1  in
        FStar_Pprint.op_Hat_Hat uu____3478 uu____3479
    | uu____3480 -> p_atomicTermNotQUident e

and p_atomicTermNotQUident : FStar_Parser_AST.term -> FStar_Pprint.document =
  fun e  ->
    let uu____3482 =
      let uu____3483 = unparen e  in uu____3483.FStar_Parser_AST.tm  in
    match uu____3482 with
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
        let uu____3492 = str op  in
        let uu____3493 = p_atomicTermNotQUident e1  in
        FStar_Pprint.op_Hat_Hat uu____3492 uu____3493
    | FStar_Parser_AST.Op (op,[]) ->
        let uu____3496 =
          let uu____3497 =
            let uu____3498 = str op  in
            let uu____3499 =
              FStar_Pprint.op_Hat_Hat FStar_Pprint.space FStar_Pprint.rparen
               in
            FStar_Pprint.op_Hat_Hat uu____3498 uu____3499  in
          FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____3497  in
        FStar_Pprint.op_Hat_Hat FStar_Pprint.lparen uu____3496
    | FStar_Parser_AST.Construct (lid,args) when is_dtuple_constructor lid ->
        let uu____3508 =
          FStar_Pprint.op_Hat_Hat FStar_Pprint.lparen FStar_Pprint.bar  in
        let uu____3509 =
          let uu____3510 = FStar_Pprint.op_Hat_Hat FStar_Pprint.comma break1
             in
          let uu____3511 = FStar_List.map Prims.fst args  in
          FStar_Pprint.separate_map uu____3510 p_tmEq uu____3511  in
        let uu____3515 =
          FStar_Pprint.op_Hat_Hat FStar_Pprint.bar FStar_Pprint.rparen  in
        FStar_Pprint.surround (Prims.parse_int "2") (Prims.parse_int "1")
          uu____3508 uu____3509 uu____3515
    | FStar_Parser_AST.Project (e1,lid) ->
        let uu____3518 =
          let uu____3519 = p_atomicTermNotQUident e1  in
          let uu____3520 =
            let uu____3521 = p_qlident lid  in
            FStar_Pprint.op_Hat_Hat FStar_Pprint.dot uu____3521  in
          FStar_Pprint.prefix (Prims.parse_int "2") (Prims.parse_int "0")
            uu____3519 uu____3520
           in
        FStar_Pprint.group uu____3518
    | uu____3522 -> p_projectionLHS e

and p_projectionLHS : FStar_Parser_AST.term -> FStar_Pprint.document =
  fun e  ->
    let uu____3524 =
      let uu____3525 = unparen e  in uu____3525.FStar_Parser_AST.tm  in
    match uu____3524 with
    | FStar_Parser_AST.Var lid -> p_qlident lid
    | FStar_Parser_AST.Projector (constr_lid,field_lid) ->
        let uu____3529 = p_quident constr_lid  in
        let uu____3530 =
          let uu____3531 =
            let uu____3532 = p_lident field_lid  in
            FStar_Pprint.op_Hat_Hat FStar_Pprint.dot uu____3532  in
          FStar_Pprint.op_Hat_Hat FStar_Pprint.qmark uu____3531  in
        FStar_Pprint.op_Hat_Hat uu____3529 uu____3530
    | FStar_Parser_AST.Discrim constr_lid ->
        let uu____3534 = p_quident constr_lid  in
        FStar_Pprint.op_Hat_Hat uu____3534 FStar_Pprint.qmark
    | FStar_Parser_AST.Paren e1 ->
        let uu____3536 = p_term e1  in soft_parens_with_nesting uu____3536
    | uu____3537 when is_array e ->
        let es = extract_from_list e  in
        let uu____3540 =
          FStar_Pprint.op_Hat_Hat FStar_Pprint.lbracket FStar_Pprint.bar  in
        let uu____3541 =
          let uu____3542 = FStar_Pprint.op_Hat_Hat FStar_Pprint.semi break1
             in
          separate_map_or_flow uu____3542 p_noSeqTerm es  in
        let uu____3543 =
          FStar_Pprint.op_Hat_Hat FStar_Pprint.bar FStar_Pprint.rbracket  in
        FStar_Pprint.surround (Prims.parse_int "2") (Prims.parse_int "0")
          uu____3540 uu____3541 uu____3543
    | uu____3544 when is_list e ->
        let uu____3545 =
          let uu____3546 = FStar_Pprint.op_Hat_Hat FStar_Pprint.semi break1
             in
          let uu____3547 = extract_from_list e  in
          separate_map_or_flow uu____3546 p_noSeqTerm uu____3547  in
        FStar_Pprint.surround (Prims.parse_int "2") (Prims.parse_int "0")
          FStar_Pprint.lbracket uu____3545 FStar_Pprint.rbracket
    | uu____3549 when is_lex_list e ->
        let uu____3550 =
          FStar_Pprint.op_Hat_Hat FStar_Pprint.percent FStar_Pprint.lbracket
           in
        let uu____3551 =
          let uu____3552 = FStar_Pprint.op_Hat_Hat FStar_Pprint.semi break1
             in
          let uu____3553 = extract_from_list e  in
          separate_map_or_flow uu____3552 p_noSeqTerm uu____3553  in
        FStar_Pprint.surround (Prims.parse_int "2") (Prims.parse_int "1")
          uu____3550 uu____3551 FStar_Pprint.rbracket
    | uu____3555 when is_ref_set e ->
        let es = extract_from_ref_set e  in
        let uu____3558 =
          FStar_Pprint.op_Hat_Hat FStar_Pprint.bang FStar_Pprint.lbrace  in
        let uu____3559 =
          let uu____3560 = FStar_Pprint.op_Hat_Hat FStar_Pprint.comma break1
             in
          separate_map_or_flow uu____3560 p_appTerm es  in
        FStar_Pprint.surround (Prims.parse_int "2") (Prims.parse_int "0")
          uu____3558 uu____3559 FStar_Pprint.rbrace
    | FStar_Parser_AST.Wild 
      |FStar_Parser_AST.Const _
       |FStar_Parser_AST.Op _
        |FStar_Parser_AST.Tvar _
         |FStar_Parser_AST.Uvar _
          |FStar_Parser_AST.Var _
           |FStar_Parser_AST.Name _
            |FStar_Parser_AST.Construct _
             |FStar_Parser_AST.Abs _
              |FStar_Parser_AST.App _
               |FStar_Parser_AST.Let _
                |FStar_Parser_AST.LetOpen _
                 |FStar_Parser_AST.Seq _
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
        -> let uu____3589 = p_term e  in soft_parens_with_nesting uu____3589
    | FStar_Parser_AST.Labeled uu____3590 -> failwith "Not valid in universe"

and p_constant : FStar_Const.sconst -> FStar_Pprint.document =
  fun uu___142_3594  ->
    match uu___142_3594 with
    | FStar_Const.Const_effect  -> str "Effect"
    | FStar_Const.Const_unit  -> str "()"
    | FStar_Const.Const_bool b -> FStar_Pprint.doc_of_bool b
    | FStar_Const.Const_float x -> str (FStar_Util.string_of_float x)
    | FStar_Const.Const_char x ->
        let uu____3598 = FStar_Pprint.doc_of_char x  in
        FStar_Pprint.squotes uu____3598
    | FStar_Const.Const_string (bytes,uu____3600) ->
        let uu____3603 = str (FStar_Util.string_of_bytes bytes)  in
        FStar_Pprint.dquotes uu____3603
    | FStar_Const.Const_bytearray (bytes,uu____3605) ->
        let uu____3608 =
          let uu____3609 = str (FStar_Util.string_of_bytes bytes)  in
          FStar_Pprint.dquotes uu____3609  in
        let uu____3610 = str "B"  in
        FStar_Pprint.op_Hat_Hat uu____3608 uu____3610
    | FStar_Const.Const_int (repr,sign_width_opt) ->
        let signedness uu___140_3622 =
          match uu___140_3622 with
          | FStar_Const.Unsigned  -> str "u"
          | FStar_Const.Signed  -> FStar_Pprint.empty  in
        let width uu___141_3626 =
          match uu___141_3626 with
          | FStar_Const.Int8  -> str "y"
          | FStar_Const.Int16  -> str "s"
          | FStar_Const.Int32  -> str "l"
          | FStar_Const.Int64  -> str "L"  in
        let ending =
          default_or_map FStar_Pprint.empty
            (fun uu____3630  ->
               match uu____3630 with
               | (s,w) ->
                   let uu____3635 = signedness s  in
                   let uu____3636 = width w  in
                   FStar_Pprint.op_Hat_Hat uu____3635 uu____3636)
            sign_width_opt
           in
        let uu____3637 = str repr  in
        FStar_Pprint.op_Hat_Hat uu____3637 ending
    | FStar_Const.Const_range r ->
        let uu____3639 = FStar_Range.string_of_range r  in str uu____3639
    | FStar_Const.Const_reify  -> str "reify"
    | FStar_Const.Const_reflect lid ->
        let uu____3641 = p_quident lid  in
        let uu____3642 =
          let uu____3643 =
            let uu____3644 = str "reflect"  in
            FStar_Pprint.op_Hat_Hat FStar_Pprint.dot uu____3644  in
          FStar_Pprint.op_Hat_Hat FStar_Pprint.qmark uu____3643  in
        FStar_Pprint.op_Hat_Hat uu____3641 uu____3642

and p_universe : FStar_Parser_AST.term -> FStar_Pprint.document =
  fun u  ->
    let uu____3646 = str "u#"  in
    let uu____3647 = p_atomicUniverse u  in
    FStar_Pprint.op_Hat_Hat uu____3646 uu____3647

and p_universeFrom : FStar_Parser_AST.term -> FStar_Pprint.document =
  fun u  ->
    let uu____3649 =
      let uu____3650 = unparen u  in uu____3650.FStar_Parser_AST.tm  in
    match uu____3649 with
    | FStar_Parser_AST.Op ("+",u1::u2::[]) ->
        let uu____3654 =
          let uu____3655 = p_universeFrom u1  in
          let uu____3656 =
            let uu____3657 = p_universeFrom u2  in
            FStar_Pprint.op_Hat_Slash_Hat FStar_Pprint.plus uu____3657  in
          FStar_Pprint.op_Hat_Slash_Hat uu____3655 uu____3656  in
        FStar_Pprint.group uu____3654
    | FStar_Parser_AST.App uu____3658 ->
        let uu____3662 = head_and_args u  in
        (match uu____3662 with
         | (head1,args) ->
             let uu____3676 =
               let uu____3677 = unparen head1  in
               uu____3677.FStar_Parser_AST.tm  in
             (match uu____3676 with
              | FStar_Parser_AST.Var maybe_max_lid when
                  FStar_Ident.lid_equals maybe_max_lid
                    FStar_Syntax_Const.max_lid
                  ->
                  let uu____3679 =
                    let uu____3680 = p_qlident FStar_Syntax_Const.max_lid  in
                    let uu____3681 =
                      FStar_Pprint.separate_map FStar_Pprint.space
                        (fun uu____3684  ->
                           match uu____3684 with
                           | (u1,uu____3688) -> p_atomicUniverse u1) args
                       in
                    op_Hat_Slash_Plus_Hat uu____3680 uu____3681  in
                  FStar_Pprint.group uu____3679
              | uu____3689 ->
                  let uu____3690 =
                    let uu____3691 = FStar_Parser_AST.term_to_string u  in
                    FStar_Util.format1 "Invalid term in universe context %s"
                      uu____3691
                     in
                  failwith uu____3690))
    | uu____3692 -> p_atomicUniverse u

and p_atomicUniverse : FStar_Parser_AST.term -> FStar_Pprint.document =
  fun u  ->
    let uu____3694 =
      let uu____3695 = unparen u  in uu____3695.FStar_Parser_AST.tm  in
    match uu____3694 with
    | FStar_Parser_AST.Wild  -> FStar_Pprint.underscore
    | FStar_Parser_AST.Const (FStar_Const.Const_int (r,sw)) ->
        p_constant (FStar_Const.Const_int (r, sw))
    | FStar_Parser_AST.Uvar uu____3707 -> p_univar u
    | FStar_Parser_AST.Paren u1 ->
        let uu____3709 = p_universeFrom u1  in
        soft_parens_with_nesting uu____3709
    | FStar_Parser_AST.Op ("+",_::_::[])|FStar_Parser_AST.App _ ->
        let uu____3714 = p_universeFrom u  in
        soft_parens_with_nesting uu____3714
    | uu____3715 ->
        let uu____3716 =
          let uu____3717 = FStar_Parser_AST.term_to_string u  in
          FStar_Util.format1 "Invalid term in universe context %s" uu____3717
           in
        failwith uu____3716

and p_univar : FStar_Parser_AST.term -> FStar_Pprint.document =
  fun u  ->
    let uu____3719 =
      let uu____3720 = unparen u  in uu____3720.FStar_Parser_AST.tm  in
    match uu____3719 with
    | FStar_Parser_AST.Uvar id -> str (FStar_Ident.text_of_id id)
    | uu____3722 ->
        let uu____3723 =
          let uu____3724 = FStar_Parser_AST.term_to_string u  in
          FStar_Util.format1 "Not a universe variable %s" uu____3724  in
        failwith uu____3723

let term_to_document : FStar_Parser_AST.term -> FStar_Pprint.document =
  fun e  -> p_term e 
let decl_to_document : FStar_Parser_AST.decl -> FStar_Pprint.document =
  fun e  -> p_decl e 
let modul_to_document : FStar_Parser_AST.modul -> FStar_Pprint.document =
  fun m  ->
    FStar_ST.write should_print_fs_typ_app false;
    (let res =
       match m with
       | FStar_Parser_AST.Module (_,decls)|FStar_Parser_AST.Interface
         (_,decls,_) ->
           let uu____3746 =
             FStar_All.pipe_right decls (FStar_List.map decl_to_document)  in
           FStar_All.pipe_right uu____3746
             (FStar_Pprint.separate FStar_Pprint.hardline)
        in
     FStar_ST.write should_print_fs_typ_app false; res)
  
let comments_to_document :
  (Prims.string * FStar_Range.range) Prims.list -> FStar_Pprint.document =
  fun comments  ->
    FStar_Pprint.separate_map FStar_Pprint.hardline
      (fun uu____3765  ->
         match uu____3765 with | (comment,range) -> str comment) comments
  
let modul_with_comments_to_document :
  FStar_Parser_AST.modul ->
    (Prims.string * FStar_Range.range) Prims.list ->
      (FStar_Pprint.document * (Prims.string * FStar_Range.range) Prims.list)
  =
  fun m  ->
    fun comments  ->
      let decls =
        match m with
        | FStar_Parser_AST.Module (_,decls)|FStar_Parser_AST.Interface
          (_,decls,_) -> decls
         in
      FStar_ST.write should_print_fs_typ_app false;
      (match decls with
       | [] -> (FStar_Pprint.empty, comments)
       | d::ds ->
           let uu____3812 =
             match ds with
             | {
                 FStar_Parser_AST.d = FStar_Parser_AST.Pragma
                   (FStar_Parser_AST.LightOff );
                 FStar_Parser_AST.drange = uu____3819;
                 FStar_Parser_AST.doc = uu____3820;
                 FStar_Parser_AST.quals = uu____3821;
                 FStar_Parser_AST.attrs = uu____3822;_}::uu____3823 ->
                 let d0 = FStar_List.hd ds  in
                 let uu____3827 =
                   let uu____3829 =
                     let uu____3831 = FStar_List.tl ds  in d :: uu____3831
                      in
                   d0 :: uu____3829  in
                 (uu____3827, (d0.FStar_Parser_AST.drange))
             | uu____3834 -> ((d :: ds), (d.FStar_Parser_AST.drange))  in
           (match uu____3812 with
            | (decls1,first_range) ->
                let extract_decl_range d1 = d1.FStar_Parser_AST.drange  in
                (FStar_ST.write comment_stack comments;
                 (let initial_comment =
                    let uu____3857 = FStar_Range.start_of_range first_range
                       in
                    place_comments_until_pos (Prims.parse_int "0")
                      (Prims.parse_int "1") uu____3857 FStar_Pprint.empty
                     in
                  let doc1 =
                    separate_map_with_comments FStar_Pprint.empty
                      FStar_Pprint.empty decl_to_document decls1
                      extract_decl_range
                     in
                  let comments1 = FStar_ST.read comment_stack  in
                  FStar_ST.write comment_stack [];
                  FStar_ST.write should_print_fs_typ_app false;
                  (let uu____3879 =
                     FStar_Pprint.op_Hat_Hat initial_comment doc1  in
                   (uu____3879, comments1))))))
  