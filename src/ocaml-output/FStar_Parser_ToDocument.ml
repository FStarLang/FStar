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
    let uu____1801 =
      let uu____1802 = FStar_Pprint.optional p_fsdoc d.FStar_Parser_AST.doc
         in
      let uu____1803 =
        let uu____1804 = p_attributes d.FStar_Parser_AST.attrs  in
        let uu____1805 =
          let uu____1806 = p_qualifiers d.FStar_Parser_AST.quals  in
          let uu____1807 =
            let uu____1808 = p_rawDecl d  in
            FStar_Pprint.op_Hat_Hat
              (if d.FStar_Parser_AST.quals = []
               then FStar_Pprint.empty
               else break1) uu____1808
             in
          FStar_Pprint.op_Hat_Hat uu____1806 uu____1807  in
        FStar_Pprint.op_Hat_Hat uu____1804 uu____1805  in
      FStar_Pprint.op_Hat_Hat uu____1802 uu____1803  in
    FStar_Pprint.group uu____1801

and p_attributes : FStar_Parser_AST.attributes_ -> FStar_Pprint.document =
  fun attrs  ->
    let uu____1811 =
      let uu____1812 = str "@"  in
      FStar_Pprint.op_Hat_Hat FStar_Pprint.lbracket uu____1812  in
    let uu____1813 =
      FStar_Pprint.op_Hat_Hat FStar_Pprint.rbracket FStar_Pprint.hardline  in
    soft_surround_separate_map (Prims.parse_int "0") (Prims.parse_int "2")
      FStar_Pprint.empty uu____1811 FStar_Pprint.space uu____1813
      p_atomicTerm attrs

and p_fsdoc : FStar_Parser_AST.fsdoc -> FStar_Pprint.document =
  fun uu____1814  ->
    match uu____1814 with
    | (doc1,kwd_args) ->
        let kwd_args_doc =
          match kwd_args with
          | [] -> FStar_Pprint.empty
          | kwd_args1 ->
              let process_kwd_arg uu____1835 =
                match uu____1835 with
                | (kwd1,arg) ->
                    let uu____1840 = str "@"  in
                    let uu____1841 =
                      let uu____1842 = str kwd1  in
                      let uu____1843 =
                        let uu____1844 = str arg  in
                        FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____1844
                         in
                      FStar_Pprint.op_Hat_Hat uu____1842 uu____1843  in
                    FStar_Pprint.op_Hat_Hat uu____1840 uu____1841
                 in
              let uu____1845 =
                let uu____1846 =
                  FStar_Pprint.separate_map FStar_Pprint.hardline
                    process_kwd_arg kwd_args1
                   in
                FStar_Pprint.op_Hat_Hat uu____1846 FStar_Pprint.hardline  in
              FStar_Pprint.op_Hat_Hat FStar_Pprint.hardline uu____1845
           in
        let uu____1849 =
          let uu____1850 =
            let uu____1851 =
              let uu____1852 =
                let uu____1853 = str doc1  in
                let uu____1854 =
                  let uu____1855 =
                    let uu____1856 =
                      FStar_Pprint.op_Hat_Hat FStar_Pprint.rparen
                        FStar_Pprint.hardline
                       in
                    FStar_Pprint.op_Hat_Hat FStar_Pprint.star uu____1856  in
                  FStar_Pprint.op_Hat_Hat kwd_args_doc uu____1855  in
                FStar_Pprint.op_Hat_Hat uu____1853 uu____1854  in
              FStar_Pprint.op_Hat_Hat FStar_Pprint.star uu____1852  in
            FStar_Pprint.op_Hat_Hat FStar_Pprint.star uu____1851  in
          FStar_Pprint.op_Hat_Hat FStar_Pprint.lparen uu____1850  in
        FStar_Pprint.op_Hat_Hat FStar_Pprint.hardline uu____1849

and p_rawDecl : FStar_Parser_AST.decl -> FStar_Pprint.document =
  fun d  ->
    match d.FStar_Parser_AST.d with
    | FStar_Parser_AST.Open uid ->
        let uu____1859 =
          let uu____1860 = str "open"  in
          let uu____1861 = p_quident uid  in
          FStar_Pprint.op_Hat_Slash_Hat uu____1860 uu____1861  in
        FStar_Pprint.group uu____1859
    | FStar_Parser_AST.Include uid ->
        let uu____1863 =
          let uu____1864 = str "include"  in
          let uu____1865 = p_quident uid  in
          FStar_Pprint.op_Hat_Slash_Hat uu____1864 uu____1865  in
        FStar_Pprint.group uu____1863
    | FStar_Parser_AST.ModuleAbbrev (uid1,uid2) ->
        let uu____1868 =
          let uu____1869 = str "module"  in
          let uu____1870 =
            let uu____1871 =
              let uu____1872 = p_uident uid1  in
              let uu____1873 =
                FStar_Pprint.op_Hat_Hat FStar_Pprint.space
                  FStar_Pprint.equals
                 in
              FStar_Pprint.op_Hat_Hat uu____1872 uu____1873  in
            FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____1871  in
          FStar_Pprint.op_Hat_Hat uu____1869 uu____1870  in
        let uu____1874 = p_quident uid2  in
        op_Hat_Slash_Plus_Hat uu____1868 uu____1874
    | FStar_Parser_AST.TopLevelModule uid ->
        let uu____1876 =
          let uu____1877 = str "module"  in
          let uu____1878 =
            let uu____1879 = p_quident uid  in
            FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____1879  in
          FStar_Pprint.op_Hat_Hat uu____1877 uu____1878  in
        FStar_Pprint.group uu____1876
    | FStar_Parser_AST.Tycon
        (true ,(FStar_Parser_AST.TyconAbbrev (uid,tpars,None ,t),None )::[])
        ->
        let effect_prefix_doc =
          let uu____1898 = str "effect"  in
          let uu____1899 =
            let uu____1900 = p_uident uid  in
            FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____1900  in
          FStar_Pprint.op_Hat_Hat uu____1898 uu____1899  in
        let uu____1901 =
          let uu____1902 = p_typars tpars  in
          FStar_Pprint.surround (Prims.parse_int "2") (Prims.parse_int "1")
            effect_prefix_doc uu____1902 FStar_Pprint.equals
           in
        let uu____1903 = p_typ t  in
        op_Hat_Slash_Plus_Hat uu____1901 uu____1903
    | FStar_Parser_AST.Tycon (false ,tcdefs) ->
        let uu____1913 = str "type"  in
        let uu____1914 = str "and"  in
        precede_break_separate_map uu____1913 uu____1914 p_fsdocTypeDeclPairs
          tcdefs
    | FStar_Parser_AST.TopLevelLet (q,lbs) ->
        let let_doc =
          let uu____1927 = str "let"  in
          let uu____1928 =
            let uu____1929 = p_letqualifier q  in
            FStar_Pprint.op_Hat_Hat uu____1929 FStar_Pprint.space  in
          FStar_Pprint.op_Hat_Hat uu____1927 uu____1928  in
        let uu____1930 =
          let uu____1931 = str "and"  in
          FStar_Pprint.op_Hat_Hat uu____1931 FStar_Pprint.space  in
        separate_map_with_comments let_doc uu____1930 p_letbinding lbs
          (fun uu____1934  ->
             match uu____1934 with
             | (p,t) ->
                 FStar_Range.union_ranges p.FStar_Parser_AST.prange
                   t.FStar_Parser_AST.range)
    | FStar_Parser_AST.Val (lid,t) ->
        let uu____1941 =
          let uu____1942 = str "val"  in
          let uu____1943 =
            let uu____1944 =
              let uu____1945 = p_lident lid  in
              let uu____1946 =
                FStar_Pprint.op_Hat_Hat FStar_Pprint.space FStar_Pprint.colon
                 in
              FStar_Pprint.op_Hat_Hat uu____1945 uu____1946  in
            FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____1944  in
          FStar_Pprint.op_Hat_Hat uu____1942 uu____1943  in
        let uu____1947 = p_typ t  in
        op_Hat_Slash_Plus_Hat uu____1941 uu____1947
    | FStar_Parser_AST.Assume (id,t) ->
        let decl_keyword =
          let uu____1951 =
            let uu____1952 =
              FStar_Util.char_at id.FStar_Ident.idText (Prims.parse_int "0")
               in
            FStar_All.pipe_right uu____1952 FStar_Util.is_upper  in
          if uu____1951
          then FStar_Pprint.empty
          else
            (let uu____1954 = str "val"  in
             FStar_Pprint.op_Hat_Hat uu____1954 FStar_Pprint.space)
           in
        let uu____1955 =
          let uu____1956 =
            let uu____1957 = p_ident id  in
            let uu____1958 =
              FStar_Pprint.op_Hat_Hat FStar_Pprint.space FStar_Pprint.colon
               in
            FStar_Pprint.op_Hat_Hat uu____1957 uu____1958  in
          FStar_Pprint.op_Hat_Hat decl_keyword uu____1956  in
        let uu____1959 = p_typ t  in
        op_Hat_Slash_Plus_Hat uu____1955 uu____1959
    | FStar_Parser_AST.Exception (uid,t_opt) ->
        let uu____1964 = str "exception"  in
        let uu____1965 =
          let uu____1966 =
            let uu____1967 = p_uident uid  in
            let uu____1968 =
              FStar_Pprint.optional
                (fun t  ->
                   let uu____1970 = str "of"  in
                   let uu____1971 = p_typ t  in
                   op_Hat_Slash_Plus_Hat uu____1970 uu____1971) t_opt
               in
            FStar_Pprint.op_Hat_Hat uu____1967 uu____1968  in
          FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____1966  in
        FStar_Pprint.op_Hat_Hat uu____1964 uu____1965
    | FStar_Parser_AST.NewEffect ne ->
        let uu____1973 = str "new_effect"  in
        let uu____1974 =
          let uu____1975 = p_newEffect ne  in
          FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____1975  in
        FStar_Pprint.op_Hat_Hat uu____1973 uu____1974
    | FStar_Parser_AST.SubEffect se ->
        let uu____1977 = str "sub_effect"  in
        let uu____1978 =
          let uu____1979 = p_subEffect se  in
          FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____1979  in
        FStar_Pprint.op_Hat_Hat uu____1977 uu____1978
    | FStar_Parser_AST.Pragma p -> p_pragma p
    | FStar_Parser_AST.Fsdoc doc1 ->
        let uu____1982 = p_fsdoc doc1  in
        FStar_Pprint.op_Hat_Hat uu____1982 FStar_Pprint.hardline
    | FStar_Parser_AST.Main uu____1983 ->
        failwith "*Main declaration* : Is that really still in use ??"
    | FStar_Parser_AST.Tycon (true ,uu____1984) ->
        failwith
          "Effect abbreviation is expected to be defined by an abbreviation"

and p_pragma : FStar_Parser_AST.pragma -> FStar_Pprint.document =
  fun uu___131_1993  ->
    match uu___131_1993 with
    | FStar_Parser_AST.SetOptions s ->
        let uu____1995 = str "#set-options"  in
        let uu____1996 =
          let uu____1997 =
            let uu____1998 = str s  in FStar_Pprint.dquotes uu____1998  in
          FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____1997  in
        FStar_Pprint.op_Hat_Hat uu____1995 uu____1996
    | FStar_Parser_AST.ResetOptions s_opt ->
        let uu____2001 = str "#reset-options"  in
        let uu____2002 =
          FStar_Pprint.optional
            (fun s  ->
               let uu____2004 =
                 let uu____2005 = str s  in FStar_Pprint.dquotes uu____2005
                  in
               FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____2004) s_opt
           in
        FStar_Pprint.op_Hat_Hat uu____2001 uu____2002
    | FStar_Parser_AST.LightOff  ->
        (FStar_ST.write should_print_fs_typ_app true; str "#light \"off\"")

and p_typars : FStar_Parser_AST.binder Prims.list -> FStar_Pprint.document =
  fun bs  -> p_binders true bs

and p_fsdocTypeDeclPairs :
  (FStar_Parser_AST.tycon * FStar_Parser_AST.fsdoc Prims.option) ->
    FStar_Pprint.document
  =
  fun uu____2011  ->
    match uu____2011 with
    | (typedecl,fsdoc_opt) ->
        let uu____2019 = FStar_Pprint.optional p_fsdoc fsdoc_opt  in
        let uu____2020 = p_typeDecl typedecl  in
        FStar_Pprint.op_Hat_Hat uu____2019 uu____2020

and p_typeDecl : FStar_Parser_AST.tycon -> FStar_Pprint.document =
  fun uu___132_2021  ->
    match uu___132_2021 with
    | FStar_Parser_AST.TyconAbstract (lid,bs,typ_opt) ->
        let empty' uu____2032 = FStar_Pprint.empty  in
        p_typeDeclPrefix lid bs typ_opt empty'
    | FStar_Parser_AST.TyconAbbrev (lid,bs,typ_opt,t) ->
        let f uu____2044 =
          let uu____2045 = p_typ t  in prefix2 FStar_Pprint.equals uu____2045
           in
        p_typeDeclPrefix lid bs typ_opt f
    | FStar_Parser_AST.TyconRecord (lid,bs,typ_opt,record_field_decls) ->
        let p_recordFieldAndComments uu____2071 =
          match uu____2071 with
          | (lid1,t,doc_opt) ->
              let uu____2081 =
                FStar_Range.extend_to_end_of_line t.FStar_Parser_AST.range
                 in
              with_comment p_recordFieldDecl (lid1, t, doc_opt) uu____2081
           in
        let p_fields uu____2090 =
          let uu____2091 =
            let uu____2092 =
              let uu____2093 =
                let uu____2094 =
                  FStar_Pprint.op_Hat_Hat FStar_Pprint.semi break1  in
                FStar_Pprint.separate_map uu____2094 p_recordFieldAndComments
                  record_field_decls
                 in
              braces_with_nesting uu____2093  in
            FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____2092  in
          FStar_Pprint.op_Hat_Hat FStar_Pprint.equals uu____2091  in
        p_typeDeclPrefix lid bs typ_opt p_fields
    | FStar_Parser_AST.TyconVariant (lid,bs,typ_opt,ct_decls) ->
        let p_constructorBranchAndComments uu____2130 =
          match uu____2130 with
          | (uid,t_opt,doc_opt,use_of) ->
              let range =
                let uu____2146 =
                  let uu____2147 =
                    FStar_Util.map_opt t_opt
                      (fun t  -> t.FStar_Parser_AST.range)
                     in
                  FStar_Util.dflt uid.FStar_Ident.idRange uu____2147  in
                FStar_Range.extend_to_end_of_line uu____2146  in
              let p_constructorBranch decl =
                let uu____2166 =
                  let uu____2167 =
                    let uu____2168 = p_constructorDecl decl  in
                    FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____2168  in
                  FStar_Pprint.op_Hat_Hat FStar_Pprint.bar uu____2167  in
                FStar_Pprint.group uu____2166  in
              with_comment p_constructorBranch (uid, t_opt, doc_opt, use_of)
                range
           in
        let datacon_doc uu____2180 =
          let uu____2181 =
            FStar_Pprint.separate_map break1 p_constructorBranchAndComments
              ct_decls
             in
          FStar_Pprint.group uu____2181  in
        p_typeDeclPrefix lid bs typ_opt
          (fun uu____2188  ->
             let uu____2189 = datacon_doc ()  in
             prefix2 FStar_Pprint.equals uu____2189)

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
            let uu____2200 = p_ident lid  in
            let uu____2201 =
              let uu____2202 = cont ()  in
              FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____2202  in
            FStar_Pprint.op_Hat_Hat uu____2200 uu____2201
          else
            (let binders_doc =
               let uu____2205 = p_typars bs  in
               let uu____2206 =
                 FStar_Pprint.optional
                   (fun t  ->
                      let uu____2208 =
                        let uu____2209 =
                          let uu____2210 = p_typ t  in
                          FStar_Pprint.op_Hat_Hat FStar_Pprint.space
                            uu____2210
                           in
                        FStar_Pprint.op_Hat_Hat FStar_Pprint.colon uu____2209
                         in
                      FStar_Pprint.op_Hat_Hat break1 uu____2208) typ_opt
                  in
               FStar_Pprint.op_Hat_Hat uu____2205 uu____2206  in
             let uu____2211 = p_ident lid  in
             let uu____2212 = cont ()  in
             FStar_Pprint.surround (Prims.parse_int "2")
               (Prims.parse_int "1") uu____2211 binders_doc uu____2212)

and p_recordFieldDecl :
  (FStar_Ident.ident * FStar_Parser_AST.term * FStar_Parser_AST.fsdoc
    Prims.option) -> FStar_Pprint.document
  =
  fun uu____2213  ->
    match uu____2213 with
    | (lid,t,doc_opt) ->
        let uu____2223 =
          let uu____2224 = FStar_Pprint.optional p_fsdoc doc_opt  in
          let uu____2225 =
            let uu____2226 = p_lident lid  in
            let uu____2227 =
              let uu____2228 = p_typ t  in
              FStar_Pprint.op_Hat_Hat FStar_Pprint.colon uu____2228  in
            FStar_Pprint.op_Hat_Hat uu____2226 uu____2227  in
          FStar_Pprint.op_Hat_Hat uu____2224 uu____2225  in
        FStar_Pprint.group uu____2223

and p_constructorDecl :
  (FStar_Ident.ident * FStar_Parser_AST.term Prims.option *
    FStar_Parser_AST.fsdoc Prims.option * Prims.bool) ->
    FStar_Pprint.document
  =
  fun uu____2229  ->
    match uu____2229 with
    | (uid,t_opt,doc_opt,use_of) ->
        let sep = if use_of then str "of" else FStar_Pprint.colon  in
        let uid_doc = p_uident uid  in
        let uu____2247 = FStar_Pprint.optional p_fsdoc doc_opt  in
        let uu____2248 =
          let uu____2249 = FStar_Pprint.break_ (Prims.parse_int "0")  in
          let uu____2250 =
            default_or_map uid_doc
              (fun t  ->
                 let uu____2252 =
                   let uu____2253 =
                     FStar_Pprint.op_Hat_Hat FStar_Pprint.space sep  in
                   FStar_Pprint.op_Hat_Hat uid_doc uu____2253  in
                 let uu____2254 = p_typ t  in
                 op_Hat_Slash_Plus_Hat uu____2252 uu____2254) t_opt
             in
          FStar_Pprint.op_Hat_Hat uu____2249 uu____2250  in
        FStar_Pprint.op_Hat_Hat uu____2247 uu____2248

and p_letbinding :
  (FStar_Parser_AST.pattern * FStar_Parser_AST.term) -> FStar_Pprint.document
  =
  fun uu____2255  ->
    match uu____2255 with
    | (pat,e) ->
        let pat_doc =
          let uu____2261 =
            match pat.FStar_Parser_AST.pat with
            | FStar_Parser_AST.PatAscribed (pat1,t) ->
                let uu____2268 =
                  let uu____2269 =
                    let uu____2270 =
                      let uu____2271 =
                        let uu____2272 = p_tmArrow p_tmNoEq t  in
                        FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____2272
                         in
                      FStar_Pprint.op_Hat_Hat FStar_Pprint.colon uu____2271
                       in
                    FStar_Pprint.group uu____2270  in
                  FStar_Pprint.op_Hat_Hat break1 uu____2269  in
                (pat1, uu____2268)
            | uu____2273 -> (pat, FStar_Pprint.empty)  in
          match uu____2261 with
          | (pat1,ascr_doc) ->
              (match pat1.FStar_Parser_AST.pat with
               | FStar_Parser_AST.PatApp
                   ({
                      FStar_Parser_AST.pat = FStar_Parser_AST.PatVar
                        (x,uu____2277);
                      FStar_Parser_AST.prange = uu____2278;_},pats)
                   ->
                   let uu____2284 = p_lident x  in
                   let uu____2285 =
                     let uu____2286 =
                       FStar_Pprint.separate_map break1 p_atomicPattern pats
                        in
                     FStar_Pprint.op_Hat_Hat uu____2286 ascr_doc  in
                   FStar_Pprint.surround (Prims.parse_int "2")
                     (Prims.parse_int "1") uu____2284 uu____2285
                     FStar_Pprint.equals
               | uu____2287 ->
                   let uu____2288 =
                     let uu____2289 = p_tuplePattern pat1  in
                     let uu____2290 =
                       FStar_Pprint.op_Hat_Slash_Hat ascr_doc
                         FStar_Pprint.equals
                        in
                     FStar_Pprint.op_Hat_Hat uu____2289 uu____2290  in
                   FStar_Pprint.group uu____2288)
           in
        let uu____2291 = p_term e  in prefix2 pat_doc uu____2291

and p_newEffect : FStar_Parser_AST.effect_decl -> FStar_Pprint.document =
  fun uu___133_2292  ->
    match uu___133_2292 with
    | FStar_Parser_AST.RedefineEffect (lid,bs,t) ->
        p_effectRedefinition lid bs t
    | FStar_Parser_AST.DefineEffect (lid,bs,t,eff_decls) ->
        p_effectDefinition lid bs t eff_decls

and p_effectRedefinition :
  FStar_Ident.ident ->
    FStar_Parser_AST.binder Prims.list ->
      FStar_Parser_AST.term -> FStar_Pprint.document
  =
  fun uid  ->
    fun bs  ->
      fun t  ->
        let uu____2310 = p_uident uid  in
        let uu____2311 = p_binders true bs  in
        let uu____2312 =
          let uu____2313 = p_simpleTerm t  in
          prefix2 FStar_Pprint.equals uu____2313  in
        FStar_Pprint.surround (Prims.parse_int "2") (Prims.parse_int "1")
          uu____2310 uu____2311 uu____2312

and p_effectDefinition :
  FStar_Ident.ident ->
    FStar_Parser_AST.binder Prims.list ->
      FStar_Parser_AST.term ->
        FStar_Parser_AST.decl Prims.list -> FStar_Pprint.document
  =
  fun uid  ->
    fun bs  ->
      fun t  ->
        fun eff_decls  ->
          let uu____2320 =
            let uu____2321 =
              let uu____2322 =
                let uu____2323 = p_uident uid  in
                let uu____2324 = p_binders true bs  in
                let uu____2325 =
                  let uu____2326 = p_typ t  in
                  prefix2 FStar_Pprint.colon uu____2326  in
                FStar_Pprint.surround (Prims.parse_int "2")
                  (Prims.parse_int "1") uu____2323 uu____2324 uu____2325
                 in
              FStar_Pprint.group uu____2322  in
            let uu____2327 =
              let uu____2328 = str "with"  in
              let uu____2329 =
                separate_break_map FStar_Pprint.semi p_effectDecl eff_decls
                 in
              prefix2 uu____2328 uu____2329  in
            FStar_Pprint.op_Hat_Slash_Hat uu____2321 uu____2327  in
          braces_with_nesting uu____2320

and p_effectDecl : FStar_Parser_AST.decl -> FStar_Pprint.document =
  fun d  ->
    match d.FStar_Parser_AST.d with
    | FStar_Parser_AST.Tycon
        (false ,(FStar_Parser_AST.TyconAbbrev (lid,[],None ,e),None )::[]) ->
        let uu____2346 =
          let uu____2347 = p_lident lid  in
          let uu____2348 =
            FStar_Pprint.op_Hat_Hat FStar_Pprint.space FStar_Pprint.equals
             in
          FStar_Pprint.op_Hat_Hat uu____2347 uu____2348  in
        let uu____2349 = p_simpleTerm e  in prefix2 uu____2346 uu____2349
    | uu____2350 ->
        let uu____2351 =
          let uu____2352 = FStar_Parser_AST.decl_to_string d  in
          FStar_Util.format1
            "Not a declaration of an effect member... or at least I hope so : %s"
            uu____2352
           in
        failwith uu____2351

and p_subEffect : FStar_Parser_AST.lift -> FStar_Pprint.document =
  fun lift  ->
    let lift_op_doc =
      let lifts =
        match lift.FStar_Parser_AST.lift_op with
        | FStar_Parser_AST.NonReifiableLift t -> [("lift_wp", t)]
        | FStar_Parser_AST.ReifiableLift (t1,t2) ->
            [("lif_wp", t1); ("lift", t2)]
        | FStar_Parser_AST.LiftForFree t -> [("lift", t)]  in
      let p_lift uu____2385 =
        match uu____2385 with
        | (kwd1,t) ->
            let uu____2390 =
              let uu____2391 = str kwd1  in
              let uu____2392 =
                FStar_Pprint.op_Hat_Hat FStar_Pprint.space
                  FStar_Pprint.equals
                 in
              FStar_Pprint.op_Hat_Hat uu____2391 uu____2392  in
            let uu____2393 = p_simpleTerm t  in prefix2 uu____2390 uu____2393
         in
      separate_break_map FStar_Pprint.semi p_lift lifts  in
    let uu____2396 =
      let uu____2397 =
        let uu____2398 = p_quident lift.FStar_Parser_AST.msource  in
        let uu____2399 =
          let uu____2400 = str "~>"  in
          FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____2400  in
        FStar_Pprint.op_Hat_Hat uu____2398 uu____2399  in
      let uu____2401 = p_quident lift.FStar_Parser_AST.mdest  in
      prefix2 uu____2397 uu____2401  in
    let uu____2402 =
      let uu____2403 = braces_with_nesting lift_op_doc  in
      FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____2403  in
    FStar_Pprint.op_Hat_Hat uu____2396 uu____2402

and p_qualifier : FStar_Parser_AST.qualifier -> FStar_Pprint.document =
  fun uu___134_2404  ->
    match uu___134_2404 with
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
    let uu____2406 = FStar_Pprint.separate_map break1 p_qualifier qs  in
    FStar_Pprint.group uu____2406

and p_letqualifier : FStar_Parser_AST.let_qualifier -> FStar_Pprint.document
  =
  fun uu___135_2407  ->
    match uu___135_2407 with
    | FStar_Parser_AST.Rec  ->
        let uu____2408 = str "rec"  in
        FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____2408
    | FStar_Parser_AST.Mutable  ->
        let uu____2409 = str "mutable"  in
        FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____2409
    | FStar_Parser_AST.NoLetQualifier  -> FStar_Pprint.empty

and p_aqual : FStar_Parser_AST.arg_qualifier -> FStar_Pprint.document =
  fun uu___136_2410  ->
    match uu___136_2410 with
    | FStar_Parser_AST.Implicit  -> str "#"
    | FStar_Parser_AST.Equality  -> str "$"

and p_disjunctivePattern : FStar_Parser_AST.pattern -> FStar_Pprint.document
  =
  fun p  ->
    match p.FStar_Parser_AST.pat with
    | FStar_Parser_AST.PatOr pats ->
        let uu____2414 =
          let uu____2415 =
            let uu____2416 =
              FStar_Pprint.op_Hat_Hat FStar_Pprint.bar FStar_Pprint.space  in
            FStar_Pprint.op_Hat_Hat break1 uu____2416  in
          FStar_Pprint.separate_map uu____2415 p_tuplePattern pats  in
        FStar_Pprint.group uu____2414
    | uu____2417 -> p_tuplePattern p

and p_tuplePattern : FStar_Parser_AST.pattern -> FStar_Pprint.document =
  fun p  ->
    match p.FStar_Parser_AST.pat with
    | FStar_Parser_AST.PatTuple (pats,false ) ->
        let uu____2422 =
          let uu____2423 = FStar_Pprint.op_Hat_Hat FStar_Pprint.comma break1
             in
          FStar_Pprint.separate_map uu____2423 p_constructorPattern pats  in
        FStar_Pprint.group uu____2422
    | uu____2424 -> p_constructorPattern p

and p_constructorPattern : FStar_Parser_AST.pattern -> FStar_Pprint.document
  =
  fun p  ->
    match p.FStar_Parser_AST.pat with
    | FStar_Parser_AST.PatApp
        ({ FStar_Parser_AST.pat = FStar_Parser_AST.PatName maybe_cons_lid;
           FStar_Parser_AST.prange = uu____2427;_},hd1::tl1::[])
        when
        FStar_Ident.lid_equals maybe_cons_lid FStar_Syntax_Const.cons_lid ->
        let uu____2431 =
          FStar_Pprint.op_Hat_Hat FStar_Pprint.colon FStar_Pprint.colon  in
        let uu____2432 = p_constructorPattern hd1  in
        let uu____2433 = p_constructorPattern tl1  in
        infix0 uu____2431 uu____2432 uu____2433
    | FStar_Parser_AST.PatApp
        ({ FStar_Parser_AST.pat = FStar_Parser_AST.PatName uid;
           FStar_Parser_AST.prange = uu____2435;_},pats)
        ->
        let uu____2439 = p_quident uid  in
        let uu____2440 =
          FStar_Pprint.separate_map break1 p_atomicPattern pats  in
        prefix2 uu____2439 uu____2440
    | uu____2441 -> p_atomicPattern p

and p_atomicPattern : FStar_Parser_AST.pattern -> FStar_Pprint.document =
  fun p  ->
    match p.FStar_Parser_AST.pat with
    | FStar_Parser_AST.PatAscribed (pat,t) ->
        let uu____2445 =
          let uu____2448 =
            let uu____2449 = unparen t  in uu____2449.FStar_Parser_AST.tm  in
          ((pat.FStar_Parser_AST.pat), uu____2448)  in
        (match uu____2445 with
         | (FStar_Parser_AST.PatVar (lid,aqual),FStar_Parser_AST.Refine
            ({ FStar_Parser_AST.b = FStar_Parser_AST.Annotated (lid',t1);
               FStar_Parser_AST.brange = uu____2454;
               FStar_Parser_AST.blevel = uu____2455;
               FStar_Parser_AST.aqual = uu____2456;_},phi))
             when lid.FStar_Ident.idText = lid'.FStar_Ident.idText ->
             let uu____2460 =
               let uu____2461 = p_ident lid  in
               p_refinement aqual uu____2461 t1 phi  in
             soft_parens_with_nesting uu____2460
         | (FStar_Parser_AST.PatWild ,FStar_Parser_AST.Refine
            ({ FStar_Parser_AST.b = FStar_Parser_AST.NoName t1;
               FStar_Parser_AST.brange = uu____2463;
               FStar_Parser_AST.blevel = uu____2464;
               FStar_Parser_AST.aqual = uu____2465;_},phi))
             ->
             let uu____2467 =
               p_refinement None FStar_Pprint.underscore t1 phi  in
             soft_parens_with_nesting uu____2467
         | uu____2468 ->
             let uu____2471 =
               let uu____2472 = p_tuplePattern pat  in
               let uu____2473 =
                 let uu____2474 = FStar_Pprint.break_ (Prims.parse_int "0")
                    in
                 let uu____2475 =
                   let uu____2476 = p_typ t  in
                   FStar_Pprint.op_Hat_Hat FStar_Pprint.colon uu____2476  in
                 FStar_Pprint.op_Hat_Hat uu____2474 uu____2475  in
               FStar_Pprint.op_Hat_Hat uu____2472 uu____2473  in
             soft_parens_with_nesting uu____2471)
    | FStar_Parser_AST.PatList pats ->
        let uu____2479 =
          separate_break_map FStar_Pprint.semi p_tuplePattern pats  in
        FStar_Pprint.surround (Prims.parse_int "2") (Prims.parse_int "0")
          FStar_Pprint.lbracket uu____2479 FStar_Pprint.rbracket
    | FStar_Parser_AST.PatRecord pats ->
        let p_recordFieldPat uu____2489 =
          match uu____2489 with
          | (lid,pat) ->
              let uu____2494 = p_qlident lid  in
              let uu____2495 = p_tuplePattern pat  in
              infix2 FStar_Pprint.equals uu____2494 uu____2495
           in
        let uu____2496 =
          separate_break_map FStar_Pprint.semi p_recordFieldPat pats  in
        soft_braces_with_nesting uu____2496
    | FStar_Parser_AST.PatTuple (pats,true ) ->
        let uu____2502 =
          FStar_Pprint.op_Hat_Hat FStar_Pprint.lparen FStar_Pprint.bar  in
        let uu____2503 =
          separate_break_map FStar_Pprint.comma p_constructorPattern pats  in
        let uu____2504 =
          FStar_Pprint.op_Hat_Hat FStar_Pprint.bar FStar_Pprint.rparen  in
        FStar_Pprint.surround (Prims.parse_int "2") (Prims.parse_int "1")
          uu____2502 uu____2503 uu____2504
    | FStar_Parser_AST.PatTvar (tv,arg_qualifier_opt) -> p_tvar tv
    | FStar_Parser_AST.PatOp op ->
        let uu____2511 =
          let uu____2512 =
            let uu____2513 = str op  in
            let uu____2514 =
              FStar_Pprint.op_Hat_Hat FStar_Pprint.space FStar_Pprint.rparen
               in
            FStar_Pprint.op_Hat_Hat uu____2513 uu____2514  in
          FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____2512  in
        FStar_Pprint.op_Hat_Hat FStar_Pprint.lparen uu____2511
    | FStar_Parser_AST.PatWild  -> FStar_Pprint.underscore
    | FStar_Parser_AST.PatConst c -> p_constant c
    | FStar_Parser_AST.PatVar (lid,aqual) ->
        let uu____2520 = FStar_Pprint.optional p_aqual aqual  in
        let uu____2521 = p_lident lid  in
        FStar_Pprint.op_Hat_Hat uu____2520 uu____2521
    | FStar_Parser_AST.PatName uid -> p_quident uid
    | FStar_Parser_AST.PatOr uu____2523 -> failwith "Inner or pattern !"
    | FStar_Parser_AST.PatApp
      ({ FStar_Parser_AST.pat = FStar_Parser_AST.PatName _;
         FStar_Parser_AST.prange = _;_},_)|FStar_Parser_AST.PatTuple
      (_,false ) ->
        let uu____2531 = p_tuplePattern p  in
        soft_parens_with_nesting uu____2531
    | uu____2532 ->
        let uu____2533 =
          let uu____2534 = FStar_Parser_AST.pat_to_string p  in
          FStar_Util.format1 "Invalid pattern %s" uu____2534  in
        failwith uu____2533

and p_binder : Prims.bool -> FStar_Parser_AST.binder -> FStar_Pprint.document
  =
  fun is_atomic  ->
    fun b  ->
      match b.FStar_Parser_AST.b with
      | FStar_Parser_AST.Variable lid ->
          let uu____2538 =
            FStar_Pprint.optional p_aqual b.FStar_Parser_AST.aqual  in
          let uu____2539 = p_lident lid  in
          FStar_Pprint.op_Hat_Hat uu____2538 uu____2539
      | FStar_Parser_AST.TVariable lid -> p_lident lid
      | FStar_Parser_AST.Annotated (lid,t) ->
          let doc1 =
            let uu____2544 =
              let uu____2545 = unparen t  in uu____2545.FStar_Parser_AST.tm
               in
            match uu____2544 with
            | FStar_Parser_AST.Refine
                ({ FStar_Parser_AST.b = FStar_Parser_AST.Annotated (lid',t1);
                   FStar_Parser_AST.brange = uu____2548;
                   FStar_Parser_AST.blevel = uu____2549;
                   FStar_Parser_AST.aqual = uu____2550;_},phi)
                when lid.FStar_Ident.idText = lid'.FStar_Ident.idText ->
                let uu____2552 = p_ident lid  in
                p_refinement b.FStar_Parser_AST.aqual uu____2552 t1 phi
            | uu____2553 ->
                let uu____2554 =
                  FStar_Pprint.optional p_aqual b.FStar_Parser_AST.aqual  in
                let uu____2555 =
                  let uu____2556 = p_lident lid  in
                  let uu____2557 =
                    let uu____2558 =
                      let uu____2559 =
                        FStar_Pprint.break_ (Prims.parse_int "0")  in
                      let uu____2560 = p_tmFormula t  in
                      FStar_Pprint.op_Hat_Hat uu____2559 uu____2560  in
                    FStar_Pprint.op_Hat_Hat FStar_Pprint.colon uu____2558  in
                  FStar_Pprint.op_Hat_Hat uu____2556 uu____2557  in
                FStar_Pprint.op_Hat_Hat uu____2554 uu____2555
             in
          if is_atomic
          then
            let uu____2561 =
              let uu____2562 =
                FStar_Pprint.op_Hat_Hat doc1 FStar_Pprint.rparen  in
              FStar_Pprint.op_Hat_Hat FStar_Pprint.lparen uu____2562  in
            FStar_Pprint.group uu____2561
          else FStar_Pprint.group doc1
      | FStar_Parser_AST.TAnnotated uu____2564 ->
          failwith "Is this still used ?"
      | FStar_Parser_AST.NoName t ->
          let uu____2568 =
            let uu____2569 = unparen t  in uu____2569.FStar_Parser_AST.tm  in
          (match uu____2568 with
           | FStar_Parser_AST.Refine
               ({ FStar_Parser_AST.b = FStar_Parser_AST.NoName t1;
                  FStar_Parser_AST.brange = uu____2571;
                  FStar_Parser_AST.blevel = uu____2572;
                  FStar_Parser_AST.aqual = uu____2573;_},phi)
               ->
               if is_atomic
               then
                 let uu____2575 =
                   let uu____2576 =
                     let uu____2577 =
                       p_refinement b.FStar_Parser_AST.aqual
                         FStar_Pprint.underscore t1 phi
                        in
                     FStar_Pprint.op_Hat_Hat uu____2577 FStar_Pprint.rparen
                      in
                   FStar_Pprint.op_Hat_Hat FStar_Pprint.lparen uu____2576  in
                 FStar_Pprint.group uu____2575
               else
                 (let uu____2579 =
                    p_refinement b.FStar_Parser_AST.aqual
                      FStar_Pprint.underscore t1 phi
                     in
                  FStar_Pprint.group uu____2579)
           | uu____2580 -> if is_atomic then p_atomicTerm t else p_appTerm t)

and p_refinement :
  FStar_Parser_AST.arg_qualifier Prims.option ->
    FStar_Pprint.document ->
      FStar_Parser_AST.term -> FStar_Parser_AST.term -> FStar_Pprint.document
  =
  fun aqual_opt  ->
    fun binder  ->
      fun t  ->
        fun phi  ->
          let uu____2587 = FStar_Pprint.optional p_aqual aqual_opt  in
          let uu____2588 =
            let uu____2589 =
              let uu____2590 =
                let uu____2591 = p_appTerm t  in
                let uu____2592 =
                  let uu____2593 = p_noSeqTerm phi  in
                  soft_braces_with_nesting uu____2593  in
                FStar_Pprint.op_Hat_Hat uu____2591 uu____2592  in
              FStar_Pprint.op_Hat_Hat FStar_Pprint.colon uu____2590  in
            FStar_Pprint.op_Hat_Hat binder uu____2589  in
          FStar_Pprint.op_Hat_Hat uu____2587 uu____2588

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
    let uu____2606 =
      let uu____2607 = unparen e  in uu____2607.FStar_Parser_AST.tm  in
    match uu____2606 with
    | FStar_Parser_AST.Seq (e1,e2) ->
        let uu____2610 =
          let uu____2611 =
            let uu____2612 = p_noSeqTerm e1  in
            FStar_Pprint.op_Hat_Hat uu____2612 FStar_Pprint.semi  in
          FStar_Pprint.group uu____2611  in
        let uu____2613 = p_term e2  in
        FStar_Pprint.op_Hat_Slash_Hat uu____2610 uu____2613
    | uu____2614 ->
        let uu____2615 = p_noSeqTerm e  in FStar_Pprint.group uu____2615

and p_noSeqTerm : FStar_Parser_AST.term -> FStar_Pprint.document =
  fun e  -> with_comment p_noSeqTerm' e e.FStar_Parser_AST.range

and p_noSeqTerm' : FStar_Parser_AST.term -> FStar_Pprint.document =
  fun e  ->
    let uu____2618 =
      let uu____2619 = unparen e  in uu____2619.FStar_Parser_AST.tm  in
    match uu____2618 with
    | FStar_Parser_AST.Ascribed (e1,t) ->
        let uu____2622 =
          let uu____2623 = p_tmIff e1  in
          let uu____2624 =
            let uu____2625 =
              let uu____2626 = p_typ t  in
              FStar_Pprint.op_Hat_Slash_Hat FStar_Pprint.colon uu____2626  in
            FStar_Pprint.op_Hat_Hat FStar_Pprint.langle uu____2625  in
          FStar_Pprint.op_Hat_Slash_Hat uu____2623 uu____2624  in
        FStar_Pprint.group uu____2622
    | FStar_Parser_AST.Op (op,e1::e2::e3::[]) when op = ".()<-" ->
        let uu____2632 =
          let uu____2633 =
            let uu____2634 =
              let uu____2635 = p_atomicTermNotQUident e1  in
              let uu____2636 =
                let uu____2637 =
                  let uu____2638 =
                    let uu____2639 = p_term e2  in
                    soft_parens_with_nesting uu____2639  in
                  let uu____2640 =
                    FStar_Pprint.op_Hat_Hat FStar_Pprint.space
                      FStar_Pprint.larrow
                     in
                  FStar_Pprint.op_Hat_Hat uu____2638 uu____2640  in
                FStar_Pprint.op_Hat_Hat FStar_Pprint.dot uu____2637  in
              FStar_Pprint.op_Hat_Hat uu____2635 uu____2636  in
            FStar_Pprint.group uu____2634  in
          let uu____2641 =
            let uu____2642 = p_noSeqTerm e3  in jump2 uu____2642  in
          FStar_Pprint.op_Hat_Hat uu____2633 uu____2641  in
        FStar_Pprint.group uu____2632
    | FStar_Parser_AST.Op (op,e1::e2::e3::[]) when op = ".[]<-" ->
        let uu____2648 =
          let uu____2649 =
            let uu____2650 =
              let uu____2651 = p_atomicTermNotQUident e1  in
              let uu____2652 =
                let uu____2653 =
                  let uu____2654 =
                    let uu____2655 = p_term e2  in
                    soft_brackets_with_nesting uu____2655  in
                  let uu____2656 =
                    FStar_Pprint.op_Hat_Hat FStar_Pprint.space
                      FStar_Pprint.larrow
                     in
                  FStar_Pprint.op_Hat_Hat uu____2654 uu____2656  in
                FStar_Pprint.op_Hat_Hat FStar_Pprint.dot uu____2653  in
              FStar_Pprint.op_Hat_Hat uu____2651 uu____2652  in
            FStar_Pprint.group uu____2650  in
          let uu____2657 =
            let uu____2658 = p_noSeqTerm e3  in jump2 uu____2658  in
          FStar_Pprint.op_Hat_Hat uu____2649 uu____2657  in
        FStar_Pprint.group uu____2648
    | FStar_Parser_AST.Requires (e1,wtf) ->
        let uu____2664 =
          let uu____2665 = str "requires"  in
          let uu____2666 = p_typ e1  in
          FStar_Pprint.op_Hat_Slash_Hat uu____2665 uu____2666  in
        FStar_Pprint.group uu____2664
    | FStar_Parser_AST.Ensures (e1,wtf) ->
        let uu____2672 =
          let uu____2673 = str "ensures"  in
          let uu____2674 = p_typ e1  in
          FStar_Pprint.op_Hat_Slash_Hat uu____2673 uu____2674  in
        FStar_Pprint.group uu____2672
    | FStar_Parser_AST.Attributes es ->
        let uu____2677 =
          let uu____2678 = str "attributes"  in
          let uu____2679 = FStar_Pprint.separate_map break1 p_atomicTerm es
             in
          FStar_Pprint.op_Hat_Slash_Hat uu____2678 uu____2679  in
        FStar_Pprint.group uu____2677
    | FStar_Parser_AST.If (e1,e2,e3) ->
        let uu____2683 = is_unit e3  in
        if uu____2683
        then
          let uu____2684 =
            let uu____2685 =
              let uu____2686 = str "if"  in
              let uu____2687 = p_noSeqTerm e1  in
              op_Hat_Slash_Plus_Hat uu____2686 uu____2687  in
            let uu____2688 =
              let uu____2689 = str "then"  in
              let uu____2690 = p_noSeqTerm e2  in
              op_Hat_Slash_Plus_Hat uu____2689 uu____2690  in
            FStar_Pprint.op_Hat_Slash_Hat uu____2685 uu____2688  in
          FStar_Pprint.group uu____2684
        else
          (let e2_doc =
             let uu____2693 =
               let uu____2694 = unparen e2  in uu____2694.FStar_Parser_AST.tm
                in
             match uu____2693 with
             | FStar_Parser_AST.If (uu____2695,uu____2696,e31) when
                 is_unit e31 ->
                 let uu____2698 = p_noSeqTerm e2  in
                 soft_parens_with_nesting uu____2698
             | uu____2699 -> p_noSeqTerm e2  in
           let uu____2700 =
             let uu____2701 =
               let uu____2702 = str "if"  in
               let uu____2703 = p_noSeqTerm e1  in
               op_Hat_Slash_Plus_Hat uu____2702 uu____2703  in
             let uu____2704 =
               let uu____2705 =
                 let uu____2706 = str "then"  in
                 op_Hat_Slash_Plus_Hat uu____2706 e2_doc  in
               let uu____2707 =
                 let uu____2708 = str "else"  in
                 let uu____2709 = p_noSeqTerm e3  in
                 op_Hat_Slash_Plus_Hat uu____2708 uu____2709  in
               FStar_Pprint.op_Hat_Slash_Hat uu____2705 uu____2707  in
             FStar_Pprint.op_Hat_Slash_Hat uu____2701 uu____2704  in
           FStar_Pprint.group uu____2700)
    | FStar_Parser_AST.TryWith (e1,branches) ->
        let uu____2722 =
          let uu____2723 =
            let uu____2724 = str "try"  in
            let uu____2725 = p_noSeqTerm e1  in prefix2 uu____2724 uu____2725
             in
          let uu____2726 =
            let uu____2727 = str "with"  in
            let uu____2728 =
              FStar_Pprint.separate_map FStar_Pprint.hardline p_patternBranch
                branches
               in
            FStar_Pprint.op_Hat_Slash_Hat uu____2727 uu____2728  in
          FStar_Pprint.op_Hat_Slash_Hat uu____2723 uu____2726  in
        FStar_Pprint.group uu____2722
    | FStar_Parser_AST.Match (e1,branches) ->
        let uu____2745 =
          let uu____2746 =
            let uu____2747 = str "match"  in
            let uu____2748 = p_noSeqTerm e1  in
            let uu____2749 = str "with"  in
            FStar_Pprint.surround (Prims.parse_int "2") (Prims.parse_int "1")
              uu____2747 uu____2748 uu____2749
             in
          let uu____2750 =
            FStar_Pprint.separate_map FStar_Pprint.hardline p_patternBranch
              branches
             in
          FStar_Pprint.op_Hat_Slash_Hat uu____2746 uu____2750  in
        FStar_Pprint.group uu____2745
    | FStar_Parser_AST.LetOpen (uid,e1) ->
        let uu____2757 =
          let uu____2758 =
            let uu____2759 = str "let open"  in
            let uu____2760 = p_quident uid  in
            let uu____2761 = str "in"  in
            FStar_Pprint.surround (Prims.parse_int "2") (Prims.parse_int "1")
              uu____2759 uu____2760 uu____2761
             in
          let uu____2762 = p_term e1  in
          FStar_Pprint.op_Hat_Slash_Hat uu____2758 uu____2762  in
        FStar_Pprint.group uu____2757
    | FStar_Parser_AST.Let (q,lbs,e1) ->
        let let_doc =
          let uu____2773 = str "let"  in
          let uu____2774 = p_letqualifier q  in
          FStar_Pprint.op_Hat_Hat uu____2773 uu____2774  in
        let uu____2775 =
          let uu____2776 =
            let uu____2777 =
              let uu____2778 = str "and"  in
              precede_break_separate_map let_doc uu____2778 p_letbinding lbs
               in
            let uu____2781 = str "in"  in
            FStar_Pprint.op_Hat_Slash_Hat uu____2777 uu____2781  in
          FStar_Pprint.group uu____2776  in
        let uu____2782 = p_term e1  in
        FStar_Pprint.op_Hat_Slash_Hat uu____2775 uu____2782
    | FStar_Parser_AST.Abs
        ({ FStar_Parser_AST.pat = FStar_Parser_AST.PatVar (x,typ_opt);
           FStar_Parser_AST.prange = uu____2785;_}::[],{
                                                         FStar_Parser_AST.tm
                                                           =
                                                           FStar_Parser_AST.Match
                                                           (maybe_x,branches);
                                                         FStar_Parser_AST.range
                                                           = uu____2788;
                                                         FStar_Parser_AST.level
                                                           = uu____2789;_})
        when matches_var maybe_x x ->
        let uu____2803 =
          let uu____2804 = str "function"  in
          let uu____2805 =
            FStar_Pprint.separate_map FStar_Pprint.hardline p_patternBranch
              branches
             in
          FStar_Pprint.op_Hat_Slash_Hat uu____2804 uu____2805  in
        FStar_Pprint.group uu____2803
    | FStar_Parser_AST.Assign (id,e1) ->
        let uu____2812 =
          let uu____2813 = p_lident id  in
          let uu____2814 =
            let uu____2815 = p_noSeqTerm e1  in
            FStar_Pprint.op_Hat_Slash_Hat FStar_Pprint.larrow uu____2815  in
          FStar_Pprint.op_Hat_Slash_Hat uu____2813 uu____2814  in
        FStar_Pprint.group uu____2812
    | uu____2816 -> p_typ e

and p_typ : FStar_Parser_AST.term -> FStar_Pprint.document =
  fun e  -> with_comment p_typ' e e.FStar_Parser_AST.range

and p_typ' : FStar_Parser_AST.term -> FStar_Pprint.document =
  fun e  ->
    let uu____2819 =
      let uu____2820 = unparen e  in uu____2820.FStar_Parser_AST.tm  in
    match uu____2819 with
    | FStar_Parser_AST.QForall (bs,trigger,e1)|FStar_Parser_AST.QExists
      (bs,trigger,e1) ->
        let uu____2836 =
          let uu____2837 =
            let uu____2838 = p_quantifier e  in
            FStar_Pprint.op_Hat_Hat uu____2838 FStar_Pprint.space  in
          let uu____2839 = p_binders true bs  in
          FStar_Pprint.soft_surround (Prims.parse_int "2")
            (Prims.parse_int "0") uu____2837 uu____2839 FStar_Pprint.dot
           in
        let uu____2840 =
          let uu____2841 = p_trigger trigger  in
          let uu____2842 = p_noSeqTerm e1  in
          FStar_Pprint.op_Hat_Hat uu____2841 uu____2842  in
        prefix2 uu____2836 uu____2840
    | uu____2843 -> p_simpleTerm e

and p_quantifier : FStar_Parser_AST.term -> FStar_Pprint.document =
  fun e  ->
    let uu____2845 =
      let uu____2846 = unparen e  in uu____2846.FStar_Parser_AST.tm  in
    match uu____2845 with
    | FStar_Parser_AST.QForall uu____2847 -> str "forall"
    | FStar_Parser_AST.QExists uu____2854 -> str "exists"
    | uu____2861 ->
        failwith "Imposible : p_quantifier called on a non-quantifier term"

and p_trigger :
  FStar_Parser_AST.term Prims.list Prims.list -> FStar_Pprint.document =
  fun uu___137_2862  ->
    match uu___137_2862 with
    | [] -> FStar_Pprint.empty
    | pats ->
        let uu____2869 =
          let uu____2870 =
            let uu____2871 = str "pattern"  in
            let uu____2872 =
              let uu____2873 =
                let uu____2874 = p_disjunctivePats pats  in jump2 uu____2874
                 in
              let uu____2875 =
                FStar_Pprint.op_Hat_Hat FStar_Pprint.rbrace break1  in
              FStar_Pprint.op_Hat_Slash_Hat uu____2873 uu____2875  in
            FStar_Pprint.op_Hat_Slash_Hat uu____2871 uu____2872  in
          FStar_Pprint.op_Hat_Hat FStar_Pprint.colon uu____2870  in
        FStar_Pprint.op_Hat_Hat FStar_Pprint.lbrace uu____2869

and p_disjunctivePats :
  FStar_Parser_AST.term Prims.list Prims.list -> FStar_Pprint.document =
  fun pats  ->
    let uu____2879 = str "\\/"  in
    FStar_Pprint.separate_map uu____2879 p_conjunctivePats pats

and p_conjunctivePats :
  FStar_Parser_AST.term Prims.list -> FStar_Pprint.document =
  fun pats  ->
    let uu____2883 =
      FStar_Pprint.separate_map FStar_Pprint.semi p_appTerm pats  in
    FStar_Pprint.group uu____2883

and p_simpleTerm : FStar_Parser_AST.term -> FStar_Pprint.document =
  fun e  ->
    let uu____2885 =
      let uu____2886 = unparen e  in uu____2886.FStar_Parser_AST.tm  in
    match uu____2885 with
    | FStar_Parser_AST.Abs (pats,e1) ->
        let uu____2891 =
          let uu____2892 = str "fun"  in
          let uu____2893 =
            let uu____2894 =
              FStar_Pprint.separate_map break1 p_atomicPattern pats  in
            FStar_Pprint.op_Hat_Slash_Hat uu____2894 FStar_Pprint.rarrow  in
          op_Hat_Slash_Plus_Hat uu____2892 uu____2893  in
        let uu____2895 = p_term e1  in
        op_Hat_Slash_Plus_Hat uu____2891 uu____2895
    | uu____2896 -> p_tmIff e

and p_maybeFocusArrow : Prims.bool -> FStar_Pprint.document =
  fun b  -> if b then str "~>" else FStar_Pprint.rarrow

and p_patternBranch :
  (FStar_Parser_AST.pattern * FStar_Parser_AST.term Prims.option *
    FStar_Parser_AST.term) -> FStar_Pprint.document
  =
  fun uu____2899  ->
    match uu____2899 with
    | (pat,when_opt,e) ->
        let maybe_paren =
          let uu____2912 =
            let uu____2913 = unparen e  in uu____2913.FStar_Parser_AST.tm  in
          match uu____2912 with
          | FStar_Parser_AST.Match _|FStar_Parser_AST.TryWith _ ->
              soft_begin_end_with_nesting
          | FStar_Parser_AST.Abs
              ({
                 FStar_Parser_AST.pat = FStar_Parser_AST.PatVar
                   (x,uu____2919);
                 FStar_Parser_AST.prange = uu____2920;_}::[],{
                                                               FStar_Parser_AST.tm
                                                                 =
                                                                 FStar_Parser_AST.Match
                                                                 (maybe_x,uu____2922);
                                                               FStar_Parser_AST.range
                                                                 = uu____2923;
                                                               FStar_Parser_AST.level
                                                                 = uu____2924;_})
              when matches_var maybe_x x -> soft_begin_end_with_nesting
          | uu____2938 -> (fun x  -> x)  in
        let uu____2940 =
          let uu____2941 =
            let uu____2942 =
              let uu____2943 =
                let uu____2944 =
                  let uu____2945 = p_disjunctivePattern pat  in
                  let uu____2946 =
                    let uu____2947 = p_maybeWhen when_opt  in
                    FStar_Pprint.op_Hat_Hat uu____2947 FStar_Pprint.rarrow
                     in
                  op_Hat_Slash_Plus_Hat uu____2945 uu____2946  in
                FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____2944  in
              FStar_Pprint.op_Hat_Hat FStar_Pprint.bar uu____2943  in
            FStar_Pprint.group uu____2942  in
          let uu____2948 =
            let uu____2949 = p_term e  in maybe_paren uu____2949  in
          op_Hat_Slash_Plus_Hat uu____2941 uu____2948  in
        FStar_Pprint.group uu____2940

and p_maybeWhen : FStar_Parser_AST.term Prims.option -> FStar_Pprint.document
  =
  fun uu___138_2950  ->
    match uu___138_2950 with
    | None  -> FStar_Pprint.empty
    | Some e ->
        let uu____2953 = str "when"  in
        let uu____2954 =
          let uu____2955 = p_tmFormula e  in
          FStar_Pprint.op_Hat_Hat uu____2955 FStar_Pprint.space  in
        op_Hat_Slash_Plus_Hat uu____2953 uu____2954

and p_tmIff : FStar_Parser_AST.term -> FStar_Pprint.document =
  fun e  ->
    let uu____2957 =
      let uu____2958 = unparen e  in uu____2958.FStar_Parser_AST.tm  in
    match uu____2957 with
    | FStar_Parser_AST.Op ("<==>",e1::e2::[]) ->
        let uu____2962 = str "<==>"  in
        let uu____2963 = p_tmImplies e1  in
        let uu____2964 = p_tmIff e2  in
        infix0 uu____2962 uu____2963 uu____2964
    | uu____2965 -> p_tmImplies e

and p_tmImplies : FStar_Parser_AST.term -> FStar_Pprint.document =
  fun e  ->
    let uu____2967 =
      let uu____2968 = unparen e  in uu____2968.FStar_Parser_AST.tm  in
    match uu____2967 with
    | FStar_Parser_AST.Op ("==>",e1::e2::[]) ->
        let uu____2972 = str "==>"  in
        let uu____2973 = p_tmArrow p_tmFormula e1  in
        let uu____2974 = p_tmImplies e2  in
        infix0 uu____2972 uu____2973 uu____2974
    | uu____2975 -> p_tmArrow p_tmFormula e

and p_tmArrow :
  (FStar_Parser_AST.term -> FStar_Pprint.document) ->
    FStar_Parser_AST.term -> FStar_Pprint.document
  =
  fun p_Tm  ->
    fun e  ->
      let uu____2980 =
        let uu____2981 = unparen e  in uu____2981.FStar_Parser_AST.tm  in
      match uu____2980 with
      | FStar_Parser_AST.Product (bs,tgt) ->
          let uu____2986 =
            let uu____2987 =
              FStar_Pprint.concat_map
                (fun b  ->
                   let uu____2989 = p_binder false b  in
                   let uu____2990 =
                     let uu____2991 =
                       FStar_Pprint.op_Hat_Hat FStar_Pprint.rarrow break1  in
                     FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____2991
                      in
                   FStar_Pprint.op_Hat_Hat uu____2989 uu____2990) bs
               in
            let uu____2992 = p_tmArrow p_Tm tgt  in
            FStar_Pprint.op_Hat_Hat uu____2987 uu____2992  in
          FStar_Pprint.group uu____2986
      | uu____2993 -> p_Tm e

and p_tmFormula : FStar_Parser_AST.term -> FStar_Pprint.document =
  fun e  ->
    let uu____2995 =
      let uu____2996 = unparen e  in uu____2996.FStar_Parser_AST.tm  in
    match uu____2995 with
    | FStar_Parser_AST.Op ("\\/",e1::e2::[]) ->
        let uu____3000 = str "\\/"  in
        let uu____3001 = p_tmFormula e1  in
        let uu____3002 = p_tmConjunction e2  in
        infix0 uu____3000 uu____3001 uu____3002
    | uu____3003 -> p_tmConjunction e

and p_tmConjunction : FStar_Parser_AST.term -> FStar_Pprint.document =
  fun e  ->
    let uu____3005 =
      let uu____3006 = unparen e  in uu____3006.FStar_Parser_AST.tm  in
    match uu____3005 with
    | FStar_Parser_AST.Op ("/\\",e1::e2::[]) ->
        let uu____3010 = str "/\\"  in
        let uu____3011 = p_tmConjunction e1  in
        let uu____3012 = p_tmTuple e2  in
        infix0 uu____3010 uu____3011 uu____3012
    | uu____3013 -> p_tmTuple e

and p_tmTuple : FStar_Parser_AST.term -> FStar_Pprint.document =
  fun e  -> with_comment p_tmTuple' e e.FStar_Parser_AST.range

and p_tmTuple' : FStar_Parser_AST.term -> FStar_Pprint.document =
  fun e  ->
    let uu____3016 =
      let uu____3017 = unparen e  in uu____3017.FStar_Parser_AST.tm  in
    match uu____3016 with
    | FStar_Parser_AST.Construct (lid,args) when is_tuple_constructor lid ->
        let uu____3026 = FStar_Pprint.op_Hat_Hat FStar_Pprint.comma break1
           in
        FStar_Pprint.separate_map uu____3026
          (fun uu____3029  ->
             match uu____3029 with | (e1,uu____3033) -> p_tmEq e1) args
    | uu____3034 -> p_tmEq e

and paren_if :
  Prims.int -> Prims.int -> FStar_Pprint.document -> FStar_Pprint.document =
  fun curr  ->
    fun mine  ->
      fun doc1  ->
        if mine <= curr
        then doc1
        else
          (let uu____3039 =
             let uu____3040 =
               FStar_Pprint.op_Hat_Hat doc1 FStar_Pprint.rparen  in
             FStar_Pprint.op_Hat_Hat FStar_Pprint.lparen uu____3040  in
           FStar_Pprint.group uu____3039)

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
      let uu____3065 =
        let uu____3066 = unparen e  in uu____3066.FStar_Parser_AST.tm  in
      match uu____3065 with
      | FStar_Parser_AST.Op (op,e1::e2::[]) when
          ((is_operatorInfix0ad12 op) || (op = "=")) || (op = "|>") ->
          let uu____3071 = levels op  in
          (match uu____3071 with
           | (left1,mine,right1) ->
               let uu____3078 =
                 let uu____3079 = str op  in
                 let uu____3080 = p_tmEq' left1 e1  in
                 let uu____3081 = p_tmEq' right1 e2  in
                 infix0 uu____3079 uu____3080 uu____3081  in
               paren_if curr mine uu____3078)
      | FStar_Parser_AST.Op (":=",e1::e2::[]) ->
          let uu____3085 =
            let uu____3086 = p_tmEq e1  in
            let uu____3087 =
              let uu____3088 =
                let uu____3089 =
                  let uu____3090 = p_tmEq e2  in
                  op_Hat_Slash_Plus_Hat FStar_Pprint.equals uu____3090  in
                FStar_Pprint.op_Hat_Hat FStar_Pprint.colon uu____3089  in
              FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____3088  in
            FStar_Pprint.op_Hat_Hat uu____3086 uu____3087  in
          FStar_Pprint.group uu____3085
      | uu____3091 -> p_tmNoEq e

and p_tmNoEq : FStar_Parser_AST.term -> FStar_Pprint.document =
  fun e  ->
    let n1 = max_level [colon_colon (); amp (); opinfix3 (); opinfix4 ()]  in
    p_tmNoEq' n1 e

and p_tmNoEq' : Prims.int -> FStar_Parser_AST.term -> FStar_Pprint.document =
  fun curr  ->
    fun e  ->
      let uu____3121 =
        let uu____3122 = unparen e  in uu____3122.FStar_Parser_AST.tm  in
      match uu____3121 with
      | FStar_Parser_AST.Construct (lid,(e1,uu____3125)::(e2,uu____3127)::[])
          when
          (FStar_Ident.lid_equals lid FStar_Syntax_Const.cons_lid) &&
            (let uu____3137 = is_list e  in Prims.op_Negation uu____3137)
          ->
          let op = "::"  in
          let uu____3139 = levels op  in
          (match uu____3139 with
           | (left1,mine,right1) ->
               let uu____3146 =
                 let uu____3147 = str op  in
                 let uu____3148 = p_tmNoEq' left1 e1  in
                 let uu____3149 = p_tmNoEq' right1 e2  in
                 infix0 uu____3147 uu____3148 uu____3149  in
               paren_if curr mine uu____3146)
      | FStar_Parser_AST.Sum (binders,res) ->
          let op = "&"  in
          let uu____3155 = levels op  in
          (match uu____3155 with
           | (left1,mine,right1) ->
               let p_dsumfst b =
                 let uu____3166 = p_binder false b  in
                 let uu____3167 =
                   let uu____3168 =
                     let uu____3169 = str "&"  in
                     FStar_Pprint.op_Hat_Hat uu____3169 break1  in
                   FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____3168  in
                 FStar_Pprint.op_Hat_Hat uu____3166 uu____3167  in
               let uu____3170 =
                 let uu____3171 = FStar_Pprint.concat_map p_dsumfst binders
                    in
                 let uu____3172 = p_tmNoEq' right1 res  in
                 FStar_Pprint.op_Hat_Hat uu____3171 uu____3172  in
               paren_if curr mine uu____3170)
      | FStar_Parser_AST.Op (op,e1::e2::[]) when is_operatorInfix34 op ->
          let uu____3177 = levels op  in
          (match uu____3177 with
           | (left1,mine,right1) ->
               let uu____3184 =
                 let uu____3185 = str op  in
                 let uu____3186 = p_tmNoEq' left1 e1  in
                 let uu____3187 = p_tmNoEq' right1 e2  in
                 infix0 uu____3185 uu____3186 uu____3187  in
               paren_if curr mine uu____3184)
      | FStar_Parser_AST.Op ("-",e1::[]) ->
          let uu____3190 = levels "-"  in
          (match uu____3190 with
           | (left1,mine,right1) ->
               let uu____3197 = p_tmNoEq' mine e1  in
               FStar_Pprint.op_Hat_Slash_Hat FStar_Pprint.minus uu____3197)
      | FStar_Parser_AST.NamedTyp (lid,e1) ->
          let uu____3200 =
            let uu____3201 = p_lidentOrUnderscore lid  in
            let uu____3202 =
              let uu____3203 = p_appTerm e1  in
              FStar_Pprint.op_Hat_Slash_Hat FStar_Pprint.colon uu____3203  in
            FStar_Pprint.op_Hat_Slash_Hat uu____3201 uu____3202  in
          FStar_Pprint.group uu____3200
      | FStar_Parser_AST.Refine (b,phi) -> p_refinedBinder b phi
      | FStar_Parser_AST.Record (with_opt,record_fields) ->
          let uu____3216 =
            let uu____3217 =
              default_or_map FStar_Pprint.empty p_with_clause with_opt  in
            let uu____3218 =
              let uu____3219 =
                FStar_Pprint.op_Hat_Hat FStar_Pprint.semi break1  in
              FStar_Pprint.separate_map uu____3219 p_simpleDef record_fields
               in
            FStar_Pprint.op_Hat_Hat uu____3217 uu____3218  in
          braces_with_nesting uu____3216
      | FStar_Parser_AST.Op ("~",e1::[]) ->
          let uu____3224 =
            let uu____3225 = str "~"  in
            let uu____3226 = p_atomicTerm e1  in
            FStar_Pprint.op_Hat_Hat uu____3225 uu____3226  in
          FStar_Pprint.group uu____3224
      | uu____3227 -> p_appTerm e

and p_with_clause : FStar_Parser_AST.term -> FStar_Pprint.document =
  fun e  ->
    let uu____3229 = p_appTerm e  in
    let uu____3230 =
      let uu____3231 =
        let uu____3232 = str "with"  in
        FStar_Pprint.op_Hat_Hat uu____3232 break1  in
      FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____3231  in
    FStar_Pprint.op_Hat_Hat uu____3229 uu____3230

and p_refinedBinder :
  FStar_Parser_AST.binder -> FStar_Parser_AST.term -> FStar_Pprint.document =
  fun b  ->
    fun phi  ->
      match b.FStar_Parser_AST.b with
      | FStar_Parser_AST.Annotated (lid,t) ->
          let uu____3237 =
            let uu____3238 = p_lident lid  in
            p_refinement b.FStar_Parser_AST.aqual uu____3238 t phi  in
          soft_parens_with_nesting uu____3237
      | FStar_Parser_AST.TAnnotated uu____3239 ->
          failwith "Is this still used ?"
      | FStar_Parser_AST.Variable _
        |FStar_Parser_AST.TVariable _|FStar_Parser_AST.NoName _ ->
          let uu____3245 =
            let uu____3246 = FStar_Parser_AST.binder_to_string b  in
            FStar_Util.format1
              "Imposible : a refined binder ought to be annotated %s"
              uu____3246
             in
          failwith uu____3245

and p_simpleDef :
  (FStar_Ident.lid * FStar_Parser_AST.term) -> FStar_Pprint.document =
  fun uu____3247  ->
    match uu____3247 with
    | (lid,e) ->
        let uu____3252 =
          let uu____3253 = p_qlident lid  in
          let uu____3254 =
            let uu____3255 = p_tmIff e  in
            FStar_Pprint.op_Hat_Slash_Hat FStar_Pprint.equals uu____3255  in
          FStar_Pprint.op_Hat_Slash_Hat uu____3253 uu____3254  in
        FStar_Pprint.group uu____3252

and p_appTerm : FStar_Parser_AST.term -> FStar_Pprint.document =
  fun e  ->
    let uu____3257 =
      let uu____3258 = unparen e  in uu____3258.FStar_Parser_AST.tm  in
    match uu____3257 with
    | FStar_Parser_AST.App uu____3259 when is_general_application e ->
        let uu____3263 = head_and_args e  in
        (match uu____3263 with
         | (head1,args) ->
             let uu____3277 =
               let uu____3283 = FStar_ST.read should_print_fs_typ_app  in
               if uu____3283
               then
                 let uu____3291 =
                   FStar_Util.take
                     (fun uu____3302  ->
                        match uu____3302 with
                        | (uu____3305,aq) -> aq = FStar_Parser_AST.FsTypApp)
                     args
                    in
                 match uu____3291 with
                 | (fs_typ_args,args1) ->
                     let uu____3326 =
                       let uu____3327 = p_indexingTerm head1  in
                       let uu____3328 =
                         let uu____3329 =
                           FStar_Pprint.op_Hat_Hat FStar_Pprint.comma break1
                            in
                         soft_surround_separate_map (Prims.parse_int "2")
                           (Prims.parse_int "0") FStar_Pprint.empty
                           FStar_Pprint.langle uu____3329 FStar_Pprint.rangle
                           p_fsTypArg fs_typ_args
                          in
                       FStar_Pprint.op_Hat_Hat uu____3327 uu____3328  in
                     (uu____3326, args1)
               else
                 (let uu____3336 = p_indexingTerm head1  in
                  (uu____3336, args))
                in
             (match uu____3277 with
              | (head_doc,args1) ->
                  let uu____3348 =
                    let uu____3349 =
                      FStar_Pprint.op_Hat_Hat head_doc FStar_Pprint.space  in
                    soft_surround_separate_map (Prims.parse_int "2")
                      (Prims.parse_int "0") head_doc uu____3349 break1
                      FStar_Pprint.empty p_argTerm args1
                     in
                  FStar_Pprint.group uu____3348))
    | FStar_Parser_AST.Construct (lid,args) when
        (is_general_construction e) &&
          (Prims.op_Negation (is_dtuple_constructor lid))
        ->
        (match args with
         | [] -> p_quident lid
         | arg::[] ->
             let uu____3369 =
               let uu____3370 = p_quident lid  in
               let uu____3371 = p_argTerm arg  in
               FStar_Pprint.op_Hat_Slash_Hat uu____3370 uu____3371  in
             FStar_Pprint.group uu____3369
         | hd1::tl1 ->
             let uu____3381 =
               let uu____3382 =
                 let uu____3383 =
                   let uu____3384 = p_quident lid  in
                   let uu____3385 = p_argTerm hd1  in
                   prefix2 uu____3384 uu____3385  in
                 FStar_Pprint.group uu____3383  in
               let uu____3386 =
                 let uu____3387 =
                   FStar_Pprint.separate_map break1 p_argTerm tl1  in
                 jump2 uu____3387  in
               FStar_Pprint.op_Hat_Hat uu____3382 uu____3386  in
             FStar_Pprint.group uu____3381)
    | uu____3390 -> p_indexingTerm e

and p_argTerm :
  (FStar_Parser_AST.term * FStar_Parser_AST.imp) -> FStar_Pprint.document =
  fun arg_imp  ->
    match arg_imp with
    | ({ FStar_Parser_AST.tm = FStar_Parser_AST.Uvar uu____3394;
         FStar_Parser_AST.range = uu____3395;
         FStar_Parser_AST.level = uu____3396;_},FStar_Parser_AST.UnivApp
       ) -> p_univar (Prims.fst arg_imp)
    | (u,FStar_Parser_AST.UnivApp ) -> p_universe u
    | (e,FStar_Parser_AST.FsTypApp ) ->
        (FStar_Util.print_warning
           "Unexpected FsTypApp, output might not be formatted correctly.\n";
         (let uu____3400 = p_indexingTerm e  in
          FStar_Pprint.surround (Prims.parse_int "2") (Prims.parse_int "1")
            FStar_Pprint.langle uu____3400 FStar_Pprint.rangle))
    | (e,FStar_Parser_AST.Hash ) ->
        let uu____3402 = str "#"  in
        let uu____3403 = p_indexingTerm e  in
        FStar_Pprint.op_Hat_Hat uu____3402 uu____3403
    | (e,FStar_Parser_AST.Nothing ) -> p_indexingTerm e

and p_fsTypArg :
  (FStar_Parser_AST.term * FStar_Parser_AST.imp) -> FStar_Pprint.document =
  fun uu____3405  ->
    match uu____3405 with | (e,uu____3409) -> p_indexingTerm e

and p_indexingTerm_aux :
  (FStar_Parser_AST.term -> FStar_Pprint.document) ->
    FStar_Parser_AST.term -> FStar_Pprint.document
  =
  fun exit1  ->
    fun e  ->
      let uu____3414 =
        let uu____3415 = unparen e  in uu____3415.FStar_Parser_AST.tm  in
      match uu____3414 with
      | FStar_Parser_AST.Op (".()",e1::e2::[]) ->
          let uu____3419 =
            let uu____3420 = p_indexingTerm_aux p_atomicTermNotQUident e1  in
            let uu____3421 =
              let uu____3422 =
                let uu____3423 = p_term e2  in
                soft_parens_with_nesting uu____3423  in
              FStar_Pprint.op_Hat_Hat FStar_Pprint.dot uu____3422  in
            FStar_Pprint.op_Hat_Hat uu____3420 uu____3421  in
          FStar_Pprint.group uu____3419
      | FStar_Parser_AST.Op (".[]",e1::e2::[]) ->
          let uu____3427 =
            let uu____3428 = p_indexingTerm_aux p_atomicTermNotQUident e1  in
            let uu____3429 =
              let uu____3430 =
                let uu____3431 = p_term e2  in
                soft_brackets_with_nesting uu____3431  in
              FStar_Pprint.op_Hat_Hat FStar_Pprint.dot uu____3430  in
            FStar_Pprint.op_Hat_Hat uu____3428 uu____3429  in
          FStar_Pprint.group uu____3427
      | uu____3432 -> exit1 e

and p_indexingTerm : FStar_Parser_AST.term -> FStar_Pprint.document =
  fun e  -> p_indexingTerm_aux p_atomicTerm e

and p_atomicTerm : FStar_Parser_AST.term -> FStar_Pprint.document =
  fun e  ->
    let uu____3435 =
      let uu____3436 = unparen e  in uu____3436.FStar_Parser_AST.tm  in
    match uu____3435 with
    | FStar_Parser_AST.LetOpen (lid,e1) ->
        let uu____3439 = p_quident lid  in
        let uu____3440 =
          let uu____3441 =
            let uu____3442 = p_term e1  in
            soft_parens_with_nesting uu____3442  in
          FStar_Pprint.op_Hat_Hat FStar_Pprint.dot uu____3441  in
        FStar_Pprint.op_Hat_Hat uu____3439 uu____3440
    | FStar_Parser_AST.Name lid -> p_quident lid
    | FStar_Parser_AST.Op (op,e1::[]) when is_general_prefix_op op ->
        let uu____3447 = str op  in
        let uu____3448 = p_atomicTerm e1  in
        FStar_Pprint.op_Hat_Hat uu____3447 uu____3448
    | uu____3449 -> p_atomicTermNotQUident e

and p_atomicTermNotQUident : FStar_Parser_AST.term -> FStar_Pprint.document =
  fun e  ->
    let uu____3451 =
      let uu____3452 = unparen e  in uu____3452.FStar_Parser_AST.tm  in
    match uu____3451 with
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
        let uu____3461 = str op  in
        let uu____3462 = p_atomicTermNotQUident e1  in
        FStar_Pprint.op_Hat_Hat uu____3461 uu____3462
    | FStar_Parser_AST.Op (op,[]) ->
        let uu____3465 =
          let uu____3466 =
            let uu____3467 = str op  in
            let uu____3468 =
              FStar_Pprint.op_Hat_Hat FStar_Pprint.space FStar_Pprint.rparen
               in
            FStar_Pprint.op_Hat_Hat uu____3467 uu____3468  in
          FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____3466  in
        FStar_Pprint.op_Hat_Hat FStar_Pprint.lparen uu____3465
    | FStar_Parser_AST.Construct (lid,args) when is_dtuple_constructor lid ->
        let uu____3477 =
          FStar_Pprint.op_Hat_Hat FStar_Pprint.lparen FStar_Pprint.bar  in
        let uu____3478 =
          let uu____3479 = FStar_Pprint.op_Hat_Hat FStar_Pprint.comma break1
             in
          let uu____3480 = FStar_List.map Prims.fst args  in
          FStar_Pprint.separate_map uu____3479 p_tmEq uu____3480  in
        let uu____3484 =
          FStar_Pprint.op_Hat_Hat FStar_Pprint.bar FStar_Pprint.rparen  in
        FStar_Pprint.surround (Prims.parse_int "2") (Prims.parse_int "1")
          uu____3477 uu____3478 uu____3484
    | FStar_Parser_AST.Project (e1,lid) ->
        let uu____3487 =
          let uu____3488 = p_atomicTermNotQUident e1  in
          let uu____3489 =
            let uu____3490 = p_qlident lid  in
            FStar_Pprint.op_Hat_Hat FStar_Pprint.dot uu____3490  in
          FStar_Pprint.prefix (Prims.parse_int "2") (Prims.parse_int "0")
            uu____3488 uu____3489
           in
        FStar_Pprint.group uu____3487
    | uu____3491 -> p_projectionLHS e

and p_projectionLHS : FStar_Parser_AST.term -> FStar_Pprint.document =
  fun e  ->
    let uu____3493 =
      let uu____3494 = unparen e  in uu____3494.FStar_Parser_AST.tm  in
    match uu____3493 with
    | FStar_Parser_AST.Var lid -> p_qlident lid
    | FStar_Parser_AST.Projector (constr_lid,field_lid) ->
        let uu____3498 = p_quident constr_lid  in
        let uu____3499 =
          let uu____3500 =
            let uu____3501 = p_lident field_lid  in
            FStar_Pprint.op_Hat_Hat FStar_Pprint.dot uu____3501  in
          FStar_Pprint.op_Hat_Hat FStar_Pprint.qmark uu____3500  in
        FStar_Pprint.op_Hat_Hat uu____3498 uu____3499
    | FStar_Parser_AST.Discrim constr_lid ->
        let uu____3503 = p_quident constr_lid  in
        FStar_Pprint.op_Hat_Hat uu____3503 FStar_Pprint.qmark
    | FStar_Parser_AST.Paren e1 ->
        let uu____3505 = p_term e1  in soft_parens_with_nesting uu____3505
    | uu____3506 when is_array e ->
        let es = extract_from_list e  in
        let uu____3509 =
          FStar_Pprint.op_Hat_Hat FStar_Pprint.lbracket FStar_Pprint.bar  in
        let uu____3510 =
          let uu____3511 = FStar_Pprint.op_Hat_Hat FStar_Pprint.semi break1
             in
          separate_map_or_flow uu____3511 p_noSeqTerm es  in
        let uu____3512 =
          FStar_Pprint.op_Hat_Hat FStar_Pprint.bar FStar_Pprint.rbracket  in
        FStar_Pprint.surround (Prims.parse_int "2") (Prims.parse_int "0")
          uu____3509 uu____3510 uu____3512
    | uu____3513 when is_list e ->
        let uu____3514 =
          let uu____3515 = FStar_Pprint.op_Hat_Hat FStar_Pprint.semi break1
             in
          let uu____3516 = extract_from_list e  in
          separate_map_or_flow uu____3515 p_noSeqTerm uu____3516  in
        FStar_Pprint.surround (Prims.parse_int "2") (Prims.parse_int "0")
          FStar_Pprint.lbracket uu____3514 FStar_Pprint.rbracket
    | uu____3518 when is_lex_list e ->
        let uu____3519 =
          FStar_Pprint.op_Hat_Hat FStar_Pprint.percent FStar_Pprint.lbracket
           in
        let uu____3520 =
          let uu____3521 = FStar_Pprint.op_Hat_Hat FStar_Pprint.semi break1
             in
          let uu____3522 = extract_from_list e  in
          separate_map_or_flow uu____3521 p_noSeqTerm uu____3522  in
        FStar_Pprint.surround (Prims.parse_int "2") (Prims.parse_int "1")
          uu____3519 uu____3520 FStar_Pprint.rbracket
    | uu____3524 when is_ref_set e ->
        let es = extract_from_ref_set e  in
        let uu____3527 =
          FStar_Pprint.op_Hat_Hat FStar_Pprint.bang FStar_Pprint.lbrace  in
        let uu____3528 =
          let uu____3529 = FStar_Pprint.op_Hat_Hat FStar_Pprint.comma break1
             in
          separate_map_or_flow uu____3529 p_appTerm es  in
        FStar_Pprint.surround (Prims.parse_int "2") (Prims.parse_int "0")
          uu____3527 uu____3528 FStar_Pprint.rbrace
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
        -> let uu____3558 = p_term e  in soft_parens_with_nesting uu____3558
    | FStar_Parser_AST.Labeled uu____3559 -> failwith "Not valid in universe"

and p_constant : FStar_Const.sconst -> FStar_Pprint.document =
  fun uu___141_3563  ->
    match uu___141_3563 with
    | FStar_Const.Const_effect  -> str "Effect"
    | FStar_Const.Const_unit  -> str "()"
    | FStar_Const.Const_bool b -> FStar_Pprint.doc_of_bool b
    | FStar_Const.Const_float x -> str (FStar_Util.string_of_float x)
    | FStar_Const.Const_char x ->
        let uu____3567 = FStar_Pprint.doc_of_char x  in
        FStar_Pprint.squotes uu____3567
    | FStar_Const.Const_string (bytes,uu____3569) ->
        let uu____3572 = str (FStar_Util.string_of_bytes bytes)  in
        FStar_Pprint.dquotes uu____3572
    | FStar_Const.Const_bytearray (bytes,uu____3574) ->
        let uu____3577 =
          let uu____3578 = str (FStar_Util.string_of_bytes bytes)  in
          FStar_Pprint.dquotes uu____3578  in
        let uu____3579 = str "B"  in
        FStar_Pprint.op_Hat_Hat uu____3577 uu____3579
    | FStar_Const.Const_int (repr,sign_width_opt) ->
        let signedness uu___139_3591 =
          match uu___139_3591 with
          | FStar_Const.Unsigned  -> str "u"
          | FStar_Const.Signed  -> FStar_Pprint.empty  in
        let width uu___140_3595 =
          match uu___140_3595 with
          | FStar_Const.Int8  -> str "y"
          | FStar_Const.Int16  -> str "s"
          | FStar_Const.Int32  -> str "l"
          | FStar_Const.Int64  -> str "L"  in
        let ending =
          default_or_map FStar_Pprint.empty
            (fun uu____3599  ->
               match uu____3599 with
               | (s,w) ->
                   let uu____3604 = signedness s  in
                   let uu____3605 = width w  in
                   FStar_Pprint.op_Hat_Hat uu____3604 uu____3605)
            sign_width_opt
           in
        let uu____3606 = str repr  in
        FStar_Pprint.op_Hat_Hat uu____3606 ending
    | FStar_Const.Const_range r ->
        let uu____3608 = FStar_Range.string_of_range r  in str uu____3608
    | FStar_Const.Const_reify  -> str "reify"
    | FStar_Const.Const_reflect lid ->
        let uu____3610 = p_quident lid  in
        let uu____3611 =
          let uu____3612 =
            let uu____3613 = str "reflect"  in
            FStar_Pprint.op_Hat_Hat FStar_Pprint.dot uu____3613  in
          FStar_Pprint.op_Hat_Hat FStar_Pprint.qmark uu____3612  in
        FStar_Pprint.op_Hat_Hat uu____3610 uu____3611

and p_universe : FStar_Parser_AST.term -> FStar_Pprint.document =
  fun u  ->
    let uu____3615 = str "u#"  in
    let uu____3616 = p_atomicUniverse u  in
    FStar_Pprint.op_Hat_Hat uu____3615 uu____3616

and p_universeFrom : FStar_Parser_AST.term -> FStar_Pprint.document =
  fun u  ->
    let uu____3618 =
      let uu____3619 = unparen u  in uu____3619.FStar_Parser_AST.tm  in
    match uu____3618 with
    | FStar_Parser_AST.Op ("+",u1::u2::[]) ->
        let uu____3623 =
          let uu____3624 = p_universeFrom u1  in
          let uu____3625 =
            let uu____3626 = p_universeFrom u2  in
            FStar_Pprint.op_Hat_Slash_Hat FStar_Pprint.plus uu____3626  in
          FStar_Pprint.op_Hat_Slash_Hat uu____3624 uu____3625  in
        FStar_Pprint.group uu____3623
    | FStar_Parser_AST.App uu____3627 ->
        let uu____3631 = head_and_args u  in
        (match uu____3631 with
         | (head1,args) ->
             let uu____3645 =
               let uu____3646 = unparen head1  in
               uu____3646.FStar_Parser_AST.tm  in
             (match uu____3645 with
              | FStar_Parser_AST.Var maybe_max_lid when
                  FStar_Ident.lid_equals maybe_max_lid
                    FStar_Syntax_Const.max_lid
                  ->
                  let uu____3648 =
                    let uu____3649 = p_qlident FStar_Syntax_Const.max_lid  in
                    let uu____3650 =
                      FStar_Pprint.separate_map FStar_Pprint.space
                        (fun uu____3653  ->
                           match uu____3653 with
                           | (u1,uu____3657) -> p_atomicUniverse u1) args
                       in
                    op_Hat_Slash_Plus_Hat uu____3649 uu____3650  in
                  FStar_Pprint.group uu____3648
              | uu____3658 ->
                  let uu____3659 =
                    let uu____3660 = FStar_Parser_AST.term_to_string u  in
                    FStar_Util.format1 "Invalid term in universe context %s"
                      uu____3660
                     in
                  failwith uu____3659))
    | uu____3661 -> p_atomicUniverse u

and p_atomicUniverse : FStar_Parser_AST.term -> FStar_Pprint.document =
  fun u  ->
    let uu____3663 =
      let uu____3664 = unparen u  in uu____3664.FStar_Parser_AST.tm  in
    match uu____3663 with
    | FStar_Parser_AST.Wild  -> FStar_Pprint.underscore
    | FStar_Parser_AST.Const (FStar_Const.Const_int (r,sw)) ->
        p_constant (FStar_Const.Const_int (r, sw))
    | FStar_Parser_AST.Uvar uu____3676 -> p_univar u
    | FStar_Parser_AST.Paren u1 ->
        let uu____3678 = p_universeFrom u1  in
        soft_parens_with_nesting uu____3678
    | FStar_Parser_AST.Op ("+",_::_::[])|FStar_Parser_AST.App _ ->
        let uu____3683 = p_universeFrom u  in
        soft_parens_with_nesting uu____3683
    | uu____3684 ->
        let uu____3685 =
          let uu____3686 = FStar_Parser_AST.term_to_string u  in
          FStar_Util.format1 "Invalid term in universe context %s" uu____3686
           in
        failwith uu____3685

and p_univar : FStar_Parser_AST.term -> FStar_Pprint.document =
  fun u  ->
    let uu____3688 =
      let uu____3689 = unparen u  in uu____3689.FStar_Parser_AST.tm  in
    match uu____3688 with
    | FStar_Parser_AST.Uvar id -> str (FStar_Ident.text_of_id id)
    | uu____3691 ->
        let uu____3692 =
          let uu____3693 = FStar_Parser_AST.term_to_string u  in
          FStar_Util.format1 "Not a universe variable %s" uu____3693  in
        failwith uu____3692

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
           let uu____3715 =
             FStar_All.pipe_right decls (FStar_List.map decl_to_document)  in
           FStar_All.pipe_right uu____3715
             (FStar_Pprint.separate FStar_Pprint.hardline)
        in
     FStar_ST.write should_print_fs_typ_app false; res)
  
let comments_to_document :
  (Prims.string * FStar_Range.range) Prims.list -> FStar_Pprint.document =
  fun comments  ->
    FStar_Pprint.separate_map FStar_Pprint.hardline
      (fun uu____3734  ->
         match uu____3734 with | (comment,range) -> str comment) comments
  
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
           let uu____3781 =
             match ds with
             | {
                 FStar_Parser_AST.d = FStar_Parser_AST.Pragma
                   (FStar_Parser_AST.LightOff );
                 FStar_Parser_AST.drange = uu____3788;
                 FStar_Parser_AST.doc = uu____3789;
                 FStar_Parser_AST.quals = uu____3790;
                 FStar_Parser_AST.attrs = uu____3791;_}::uu____3792 ->
                 let d0 = FStar_List.hd ds  in
                 let uu____3796 =
                   let uu____3798 =
                     let uu____3800 = FStar_List.tl ds  in d :: uu____3800
                      in
                   d0 :: uu____3798  in
                 (uu____3796, (d0.FStar_Parser_AST.drange))
             | uu____3803 -> ((d :: ds), (d.FStar_Parser_AST.drange))  in
           (match uu____3781 with
            | (decls1,first_range) ->
                let extract_decl_range d1 = d1.FStar_Parser_AST.drange  in
                (FStar_ST.write comment_stack comments;
                 (let initial_comment =
                    let uu____3826 = FStar_Range.start_of_range first_range
                       in
                    place_comments_until_pos (Prims.parse_int "0")
                      (Prims.parse_int "1") uu____3826 FStar_Pprint.empty
                     in
                  let doc1 =
                    separate_map_with_comments FStar_Pprint.empty
                      FStar_Pprint.empty decl_to_document decls1
                      extract_decl_range
                     in
                  let comments1 = FStar_ST.read comment_stack  in
                  FStar_ST.write comment_stack [];
                  FStar_ST.write should_print_fs_typ_app false;
                  (let uu____3848 =
                     FStar_Pprint.op_Hat_Hat initial_comment doc1  in
                   (uu____3848, comments1))))))
  