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
    let uu____1807 =
      let uu____1808 = FStar_Pprint.optional p_fsdoc d.FStar_Parser_AST.doc
         in
      let uu____1809 =
        let uu____1810 = p_attributes d.FStar_Parser_AST.attrs  in
        let uu____1811 =
          let uu____1812 = p_qualifiers d.FStar_Parser_AST.quals  in
          let uu____1813 =
            let uu____1814 = p_rawDecl d  in
            FStar_Pprint.op_Hat_Hat
              (if d.FStar_Parser_AST.quals = []
               then FStar_Pprint.empty
               else break1) uu____1814
             in
          FStar_Pprint.op_Hat_Hat uu____1812 uu____1813  in
        FStar_Pprint.op_Hat_Hat uu____1810 uu____1811  in
      FStar_Pprint.op_Hat_Hat uu____1808 uu____1809  in
    FStar_Pprint.group uu____1807

and p_attributes : FStar_Parser_AST.attributes_ -> FStar_Pprint.document =
  fun attrs  ->
    let uu____1817 =
      let uu____1818 = str "@"  in
      FStar_Pprint.op_Hat_Hat FStar_Pprint.lbracket uu____1818  in
    let uu____1819 =
      FStar_Pprint.op_Hat_Hat FStar_Pprint.rbracket FStar_Pprint.hardline  in
    soft_surround_separate_map (Prims.parse_int "0") (Prims.parse_int "2")
      FStar_Pprint.empty uu____1817 FStar_Pprint.space uu____1819
      p_atomicTerm attrs

and p_fsdoc : FStar_Parser_AST.fsdoc -> FStar_Pprint.document =
  fun uu____1820  ->
    match uu____1820 with
    | (doc1,kwd_args) ->
        let kwd_args_doc =
          match kwd_args with
          | [] -> FStar_Pprint.empty
          | kwd_args1 ->
              let process_kwd_arg uu____1841 =
                match uu____1841 with
                | (kwd1,arg) ->
                    let uu____1846 = str "@"  in
                    let uu____1847 =
                      let uu____1848 = str kwd1  in
                      let uu____1849 =
                        let uu____1850 = str arg  in
                        FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____1850
                         in
                      FStar_Pprint.op_Hat_Hat uu____1848 uu____1849  in
                    FStar_Pprint.op_Hat_Hat uu____1846 uu____1847
                 in
              let uu____1851 =
                let uu____1852 =
                  FStar_Pprint.separate_map FStar_Pprint.hardline
                    process_kwd_arg kwd_args1
                   in
                FStar_Pprint.op_Hat_Hat uu____1852 FStar_Pprint.hardline  in
              FStar_Pprint.op_Hat_Hat FStar_Pprint.hardline uu____1851
           in
        let uu____1855 =
          let uu____1856 =
            let uu____1857 =
              let uu____1858 =
                let uu____1859 = str doc1  in
                let uu____1860 =
                  let uu____1861 =
                    let uu____1862 =
                      FStar_Pprint.op_Hat_Hat FStar_Pprint.rparen
                        FStar_Pprint.hardline
                       in
                    FStar_Pprint.op_Hat_Hat FStar_Pprint.star uu____1862  in
                  FStar_Pprint.op_Hat_Hat kwd_args_doc uu____1861  in
                FStar_Pprint.op_Hat_Hat uu____1859 uu____1860  in
              FStar_Pprint.op_Hat_Hat FStar_Pprint.star uu____1858  in
            FStar_Pprint.op_Hat_Hat FStar_Pprint.star uu____1857  in
          FStar_Pprint.op_Hat_Hat FStar_Pprint.lparen uu____1856  in
        FStar_Pprint.op_Hat_Hat FStar_Pprint.hardline uu____1855

and p_rawDecl : FStar_Parser_AST.decl -> FStar_Pprint.document =
  fun d  ->
    match d.FStar_Parser_AST.d with
    | FStar_Parser_AST.Open uid ->
        let uu____1865 =
          let uu____1866 = str "open"  in
          let uu____1867 = p_quident uid  in
          FStar_Pprint.op_Hat_Slash_Hat uu____1866 uu____1867  in
        FStar_Pprint.group uu____1865
    | FStar_Parser_AST.Include uid ->
        let uu____1869 =
          let uu____1870 = str "include"  in
          let uu____1871 = p_quident uid  in
          FStar_Pprint.op_Hat_Slash_Hat uu____1870 uu____1871  in
        FStar_Pprint.group uu____1869
    | FStar_Parser_AST.ModuleAbbrev (uid1,uid2) ->
        let uu____1874 =
          let uu____1875 = str "module"  in
          let uu____1876 =
            let uu____1877 =
              let uu____1878 = p_uident uid1  in
              let uu____1879 =
                FStar_Pprint.op_Hat_Hat FStar_Pprint.space
                  FStar_Pprint.equals
                 in
              FStar_Pprint.op_Hat_Hat uu____1878 uu____1879  in
            FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____1877  in
          FStar_Pprint.op_Hat_Hat uu____1875 uu____1876  in
        let uu____1880 = p_quident uid2  in
        op_Hat_Slash_Plus_Hat uu____1874 uu____1880
    | FStar_Parser_AST.TopLevelModule uid ->
        let uu____1882 =
          let uu____1883 = str "module"  in
          let uu____1884 =
            let uu____1885 = p_quident uid  in
            FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____1885  in
          FStar_Pprint.op_Hat_Hat uu____1883 uu____1884  in
        FStar_Pprint.group uu____1882
    | FStar_Parser_AST.Tycon
        (true ,(FStar_Parser_AST.TyconAbbrev (uid,tpars,None ,t),None )::[])
        ->
        let effect_prefix_doc =
          let uu____1904 = str "effect"  in
          let uu____1905 =
            let uu____1906 = p_uident uid  in
            FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____1906  in
          FStar_Pprint.op_Hat_Hat uu____1904 uu____1905  in
        let uu____1907 =
          let uu____1908 = p_typars tpars  in
          FStar_Pprint.surround (Prims.parse_int "2") (Prims.parse_int "1")
            effect_prefix_doc uu____1908 FStar_Pprint.equals
           in
        let uu____1909 = p_typ t  in
        op_Hat_Slash_Plus_Hat uu____1907 uu____1909
    | FStar_Parser_AST.Tycon (false ,tcdefs) ->
        let uu____1919 = str "type"  in
        let uu____1920 = str "and"  in
        precede_break_separate_map uu____1919 uu____1920 p_fsdocTypeDeclPairs
          tcdefs
    | FStar_Parser_AST.TopLevelLet (q,lbs) ->
        let let_doc =
          let uu____1933 = str "let"  in
          let uu____1934 =
            let uu____1935 = p_letqualifier q  in
            FStar_Pprint.op_Hat_Hat uu____1935 FStar_Pprint.space  in
          FStar_Pprint.op_Hat_Hat uu____1933 uu____1934  in
        let uu____1936 =
          let uu____1937 = str "and"  in
          FStar_Pprint.op_Hat_Hat uu____1937 FStar_Pprint.space  in
        separate_map_with_comments let_doc uu____1936 p_letbinding lbs
          (fun uu____1940  ->
             match uu____1940 with
             | (p,t) ->
                 FStar_Range.union_ranges p.FStar_Parser_AST.prange
                   t.FStar_Parser_AST.range)
    | FStar_Parser_AST.Val (lid,t) ->
        let uu____1947 =
          let uu____1948 = str "val"  in
          let uu____1949 =
            let uu____1950 =
              let uu____1951 = p_lident lid  in
              let uu____1952 =
                FStar_Pprint.op_Hat_Hat FStar_Pprint.space FStar_Pprint.colon
                 in
              FStar_Pprint.op_Hat_Hat uu____1951 uu____1952  in
            FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____1950  in
          FStar_Pprint.op_Hat_Hat uu____1948 uu____1949  in
        let uu____1953 = p_typ t  in
        op_Hat_Slash_Plus_Hat uu____1947 uu____1953
    | FStar_Parser_AST.Assume (id,t) ->
        let decl_keyword =
          let uu____1957 =
            let uu____1958 =
              FStar_Util.char_at id.FStar_Ident.idText (Prims.parse_int "0")
               in
            FStar_All.pipe_right uu____1958 FStar_Util.is_upper  in
          if uu____1957
          then FStar_Pprint.empty
          else
            (let uu____1960 = str "val"  in
             FStar_Pprint.op_Hat_Hat uu____1960 FStar_Pprint.space)
           in
        let uu____1961 =
          let uu____1962 =
            let uu____1963 = p_ident id  in
            let uu____1964 =
              FStar_Pprint.op_Hat_Hat FStar_Pprint.space FStar_Pprint.colon
               in
            FStar_Pprint.op_Hat_Hat uu____1963 uu____1964  in
          FStar_Pprint.op_Hat_Hat decl_keyword uu____1962  in
        let uu____1965 = p_typ t  in
        op_Hat_Slash_Plus_Hat uu____1961 uu____1965
    | FStar_Parser_AST.Exception (uid,t_opt) ->
        let uu____1970 = str "exception"  in
        let uu____1971 =
          let uu____1972 =
            let uu____1973 = p_uident uid  in
            let uu____1974 =
              FStar_Pprint.optional
                (fun t  ->
                   let uu____1976 = str "of"  in
                   let uu____1977 = p_typ t  in
                   op_Hat_Slash_Plus_Hat uu____1976 uu____1977) t_opt
               in
            FStar_Pprint.op_Hat_Hat uu____1973 uu____1974  in
          FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____1972  in
        FStar_Pprint.op_Hat_Hat uu____1970 uu____1971
    | FStar_Parser_AST.NewEffect ne ->
        let uu____1979 = str "new_effect"  in
        let uu____1980 =
          let uu____1981 = p_newEffect ne  in
          FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____1981  in
        FStar_Pprint.op_Hat_Hat uu____1979 uu____1980
    | FStar_Parser_AST.SubEffect se ->
        let uu____1983 = str "sub_effect"  in
        let uu____1984 =
          let uu____1985 = p_subEffect se  in
          FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____1985  in
        FStar_Pprint.op_Hat_Hat uu____1983 uu____1984
    | FStar_Parser_AST.NewEffectForFree ne ->
        let uu____1987 = str "new_effect_for_free"  in
        let uu____1988 =
          let uu____1989 = p_newEffect ne  in
          FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____1989  in
        FStar_Pprint.op_Hat_Hat uu____1987 uu____1988
    | FStar_Parser_AST.Pragma p -> p_pragma p
    | FStar_Parser_AST.Fsdoc doc1 ->
        let uu____1992 = p_fsdoc doc1  in
        FStar_Pprint.op_Hat_Hat uu____1992 FStar_Pprint.hardline
    | FStar_Parser_AST.Main uu____1993 ->
        failwith "*Main declaration* : Is that really still in use ??"
    | FStar_Parser_AST.Tycon (true ,uu____1994) ->
        failwith
          "Effect abbreviation is expected to be defined by an abbreviation"

and p_pragma : FStar_Parser_AST.pragma -> FStar_Pprint.document =
  fun uu___131_2003  ->
    match uu___131_2003 with
    | FStar_Parser_AST.SetOptions s ->
        let uu____2005 = str "#set-options"  in
        let uu____2006 =
          let uu____2007 =
            let uu____2008 = str s  in FStar_Pprint.dquotes uu____2008  in
          FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____2007  in
        FStar_Pprint.op_Hat_Hat uu____2005 uu____2006
    | FStar_Parser_AST.ResetOptions s_opt ->
        let uu____2011 = str "#reset-options"  in
        let uu____2012 =
          FStar_Pprint.optional
            (fun s  ->
               let uu____2014 =
                 let uu____2015 = str s  in FStar_Pprint.dquotes uu____2015
                  in
               FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____2014) s_opt
           in
        FStar_Pprint.op_Hat_Hat uu____2011 uu____2012
    | FStar_Parser_AST.LightOff  ->
        (FStar_ST.write should_print_fs_typ_app true; str "#light \"off\"")

and p_typars : FStar_Parser_AST.binder Prims.list -> FStar_Pprint.document =
  fun bs  -> p_binders true bs

and p_fsdocTypeDeclPairs :
  (FStar_Parser_AST.tycon * FStar_Parser_AST.fsdoc Prims.option) ->
    FStar_Pprint.document
  =
  fun uu____2021  ->
    match uu____2021 with
    | (typedecl,fsdoc_opt) ->
        let uu____2029 = FStar_Pprint.optional p_fsdoc fsdoc_opt  in
        let uu____2030 = p_typeDecl typedecl  in
        FStar_Pprint.op_Hat_Hat uu____2029 uu____2030

and p_typeDecl : FStar_Parser_AST.tycon -> FStar_Pprint.document =
  fun uu___132_2031  ->
    match uu___132_2031 with
    | FStar_Parser_AST.TyconAbstract (lid,bs,typ_opt) ->
        let empty' uu____2042 = FStar_Pprint.empty  in
        p_typeDeclPrefix lid bs typ_opt empty'
    | FStar_Parser_AST.TyconAbbrev (lid,bs,typ_opt,t) ->
        let f uu____2054 =
          let uu____2055 = p_typ t  in prefix2 FStar_Pprint.equals uu____2055
           in
        p_typeDeclPrefix lid bs typ_opt f
    | FStar_Parser_AST.TyconRecord (lid,bs,typ_opt,record_field_decls) ->
        let p_recordFieldAndComments uu____2081 =
          match uu____2081 with
          | (lid1,t,doc_opt) ->
              let uu____2091 =
                FStar_Range.extend_to_end_of_line t.FStar_Parser_AST.range
                 in
              with_comment p_recordFieldDecl (lid1, t, doc_opt) uu____2091
           in
        let p_fields uu____2100 =
          let uu____2101 =
            let uu____2102 =
              let uu____2103 =
                let uu____2104 =
                  FStar_Pprint.op_Hat_Hat FStar_Pprint.semi break1  in
                FStar_Pprint.separate_map uu____2104 p_recordFieldAndComments
                  record_field_decls
                 in
              braces_with_nesting uu____2103  in
            FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____2102  in
          FStar_Pprint.op_Hat_Hat FStar_Pprint.equals uu____2101  in
        p_typeDeclPrefix lid bs typ_opt p_fields
    | FStar_Parser_AST.TyconVariant (lid,bs,typ_opt,ct_decls) ->
        let p_constructorBranchAndComments uu____2140 =
          match uu____2140 with
          | (uid,t_opt,doc_opt,use_of) ->
              let range =
                let uu____2156 =
                  let uu____2157 =
                    FStar_Util.map_opt t_opt
                      (fun t  -> t.FStar_Parser_AST.range)
                     in
                  FStar_Util.dflt uid.FStar_Ident.idRange uu____2157  in
                FStar_Range.extend_to_end_of_line uu____2156  in
              let p_constructorBranch decl =
                let uu____2176 =
                  let uu____2177 =
                    let uu____2178 = p_constructorDecl decl  in
                    FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____2178  in
                  FStar_Pprint.op_Hat_Hat FStar_Pprint.bar uu____2177  in
                FStar_Pprint.group uu____2176  in
              with_comment p_constructorBranch (uid, t_opt, doc_opt, use_of)
                range
           in
        let datacon_doc uu____2190 =
          let uu____2191 =
            FStar_Pprint.separate_map break1 p_constructorBranchAndComments
              ct_decls
             in
          FStar_Pprint.group uu____2191  in
        p_typeDeclPrefix lid bs typ_opt
          (fun uu____2198  ->
             let uu____2199 = datacon_doc ()  in
             prefix2 FStar_Pprint.equals uu____2199)

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
            let uu____2210 = p_ident lid  in
            let uu____2211 =
              let uu____2212 = cont ()  in
              FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____2212  in
            FStar_Pprint.op_Hat_Hat uu____2210 uu____2211
          else
            (let binders_doc =
               let uu____2215 = p_typars bs  in
               let uu____2216 =
                 FStar_Pprint.optional
                   (fun t  ->
                      let uu____2218 =
                        let uu____2219 =
                          let uu____2220 = p_typ t  in
                          FStar_Pprint.op_Hat_Hat FStar_Pprint.space
                            uu____2220
                           in
                        FStar_Pprint.op_Hat_Hat FStar_Pprint.colon uu____2219
                         in
                      FStar_Pprint.op_Hat_Hat break1 uu____2218) typ_opt
                  in
               FStar_Pprint.op_Hat_Hat uu____2215 uu____2216  in
             let uu____2221 = p_ident lid  in
             let uu____2222 = cont ()  in
             FStar_Pprint.surround (Prims.parse_int "2")
               (Prims.parse_int "1") uu____2221 binders_doc uu____2222)

and p_recordFieldDecl :
  (FStar_Ident.ident * FStar_Parser_AST.term * FStar_Parser_AST.fsdoc
    Prims.option) -> FStar_Pprint.document
  =
  fun uu____2223  ->
    match uu____2223 with
    | (lid,t,doc_opt) ->
        let uu____2233 =
          let uu____2234 = FStar_Pprint.optional p_fsdoc doc_opt  in
          let uu____2235 =
            let uu____2236 = p_lident lid  in
            let uu____2237 =
              let uu____2238 = p_typ t  in
              FStar_Pprint.op_Hat_Hat FStar_Pprint.colon uu____2238  in
            FStar_Pprint.op_Hat_Hat uu____2236 uu____2237  in
          FStar_Pprint.op_Hat_Hat uu____2234 uu____2235  in
        FStar_Pprint.group uu____2233

and p_constructorDecl :
  (FStar_Ident.ident * FStar_Parser_AST.term Prims.option *
    FStar_Parser_AST.fsdoc Prims.option * Prims.bool) ->
    FStar_Pprint.document
  =
  fun uu____2239  ->
    match uu____2239 with
    | (uid,t_opt,doc_opt,use_of) ->
        let sep = if use_of then str "of" else FStar_Pprint.colon  in
        let uid_doc = p_uident uid  in
        let uu____2257 = FStar_Pprint.optional p_fsdoc doc_opt  in
        let uu____2258 =
          let uu____2259 = FStar_Pprint.break_ (Prims.parse_int "0")  in
          let uu____2260 =
            default_or_map uid_doc
              (fun t  ->
                 let uu____2262 =
                   let uu____2263 =
                     FStar_Pprint.op_Hat_Hat FStar_Pprint.space sep  in
                   FStar_Pprint.op_Hat_Hat uid_doc uu____2263  in
                 let uu____2264 = p_typ t  in
                 op_Hat_Slash_Plus_Hat uu____2262 uu____2264) t_opt
             in
          FStar_Pprint.op_Hat_Hat uu____2259 uu____2260  in
        FStar_Pprint.op_Hat_Hat uu____2257 uu____2258

and p_letbinding :
  (FStar_Parser_AST.pattern * FStar_Parser_AST.term) -> FStar_Pprint.document
  =
  fun uu____2265  ->
    match uu____2265 with
    | (pat,e) ->
        let pat_doc =
          let uu____2271 =
            match pat.FStar_Parser_AST.pat with
            | FStar_Parser_AST.PatAscribed (pat1,t) ->
                let uu____2278 =
                  let uu____2279 =
                    let uu____2280 =
                      let uu____2281 =
                        let uu____2282 = p_tmArrow p_tmNoEq t  in
                        FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____2282
                         in
                      FStar_Pprint.op_Hat_Hat FStar_Pprint.colon uu____2281
                       in
                    FStar_Pprint.group uu____2280  in
                  FStar_Pprint.op_Hat_Hat break1 uu____2279  in
                (pat1, uu____2278)
            | uu____2283 -> (pat, FStar_Pprint.empty)  in
          match uu____2271 with
          | (pat1,ascr_doc) ->
              (match pat1.FStar_Parser_AST.pat with
               | FStar_Parser_AST.PatApp
                   ({
                      FStar_Parser_AST.pat = FStar_Parser_AST.PatVar
                        (x,uu____2287);
                      FStar_Parser_AST.prange = uu____2288;_},pats)
                   ->
                   let uu____2294 = p_lident x  in
                   let uu____2295 =
                     let uu____2296 =
                       FStar_Pprint.separate_map break1 p_atomicPattern pats
                        in
                     FStar_Pprint.op_Hat_Hat uu____2296 ascr_doc  in
                   FStar_Pprint.surround (Prims.parse_int "2")
                     (Prims.parse_int "1") uu____2294 uu____2295
                     FStar_Pprint.equals
               | uu____2297 ->
                   let uu____2298 =
                     let uu____2299 = p_tuplePattern pat1  in
                     let uu____2300 =
                       FStar_Pprint.op_Hat_Slash_Hat ascr_doc
                         FStar_Pprint.equals
                        in
                     FStar_Pprint.op_Hat_Hat uu____2299 uu____2300  in
                   FStar_Pprint.group uu____2298)
           in
        let uu____2301 = p_term e  in prefix2 pat_doc uu____2301

and p_newEffect : FStar_Parser_AST.effect_decl -> FStar_Pprint.document =
  fun uu___133_2302  ->
    match uu___133_2302 with
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
        let uu____2323 = p_uident uid  in
        let uu____2324 = p_binders true bs  in
        let uu____2325 =
          let uu____2326 = p_simpleTerm t  in
          prefix2 FStar_Pprint.equals uu____2326  in
        FStar_Pprint.surround (Prims.parse_int "2") (Prims.parse_int "1")
          uu____2323 uu____2324 uu____2325

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
            let uu____2335 =
              let uu____2336 =
                let uu____2337 =
                  let uu____2338 = p_uident uid  in
                  let uu____2339 = p_binders true bs  in
                  let uu____2340 =
                    let uu____2341 = p_typ t  in
                    prefix2 FStar_Pprint.colon uu____2341  in
                  FStar_Pprint.surround (Prims.parse_int "2")
                    (Prims.parse_int "1") uu____2338 uu____2339 uu____2340
                   in
                FStar_Pprint.group uu____2337  in
              let uu____2342 =
                let uu____2343 =
                  let uu____2344 = str "with"  in
                  let uu____2345 =
                    separate_break_map FStar_Pprint.semi p_effectDecl
                      eff_decls
                     in
                  prefix2 uu____2344 uu____2345  in
                let uu____2346 = p_actionDecls action_decls  in
                FStar_Pprint.op_Hat_Hat uu____2343 uu____2346  in
              FStar_Pprint.op_Hat_Slash_Hat uu____2336 uu____2342  in
            braces_with_nesting uu____2335

and p_actionDecls : FStar_Parser_AST.decl Prims.list -> FStar_Pprint.document
  =
  fun uu___134_2347  ->
    match uu___134_2347 with
    | [] -> FStar_Pprint.empty
    | l ->
        let uu____2351 =
          let uu____2352 = str "and actions"  in
          let uu____2353 =
            separate_break_map FStar_Pprint.semi p_effectDecl l  in
          prefix2 uu____2352 uu____2353  in
        FStar_Pprint.op_Hat_Hat break1 uu____2351

and p_effectDecl : FStar_Parser_AST.decl -> FStar_Pprint.document =
  fun d  ->
    match d.FStar_Parser_AST.d with
    | FStar_Parser_AST.Tycon
        (false ,(FStar_Parser_AST.TyconAbbrev (lid,[],None ,e),None )::[]) ->
        let uu____2370 =
          let uu____2371 = p_lident lid  in
          let uu____2372 =
            FStar_Pprint.op_Hat_Hat FStar_Pprint.space FStar_Pprint.equals
             in
          FStar_Pprint.op_Hat_Hat uu____2371 uu____2372  in
        let uu____2373 = p_simpleTerm e  in prefix2 uu____2370 uu____2373
    | uu____2374 ->
        let uu____2375 =
          let uu____2376 = FStar_Parser_AST.decl_to_string d  in
          FStar_Util.format1
            "Not a declaration of an effect member... or at least I hope so : %s"
            uu____2376
           in
        failwith uu____2375

and p_subEffect : FStar_Parser_AST.lift -> FStar_Pprint.document =
  fun lift  ->
    let lift_op_doc =
      let lifts =
        match lift.FStar_Parser_AST.lift_op with
        | FStar_Parser_AST.NonReifiableLift t -> [("lift_wp", t)]
        | FStar_Parser_AST.ReifiableLift (t1,t2) ->
            [("lif_wp", t1); ("lift", t2)]
        | FStar_Parser_AST.LiftForFree t -> [("lift", t)]  in
      let p_lift uu____2409 =
        match uu____2409 with
        | (kwd1,t) ->
            let uu____2414 =
              let uu____2415 = str kwd1  in
              let uu____2416 =
                FStar_Pprint.op_Hat_Hat FStar_Pprint.space
                  FStar_Pprint.equals
                 in
              FStar_Pprint.op_Hat_Hat uu____2415 uu____2416  in
            let uu____2417 = p_simpleTerm t  in prefix2 uu____2414 uu____2417
         in
      separate_break_map FStar_Pprint.semi p_lift lifts  in
    let uu____2420 =
      let uu____2421 =
        let uu____2422 = p_quident lift.FStar_Parser_AST.msource  in
        let uu____2423 =
          let uu____2424 = str "~>"  in
          FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____2424  in
        FStar_Pprint.op_Hat_Hat uu____2422 uu____2423  in
      let uu____2425 = p_quident lift.FStar_Parser_AST.mdest  in
      prefix2 uu____2421 uu____2425  in
    let uu____2426 =
      let uu____2427 = braces_with_nesting lift_op_doc  in
      FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____2427  in
    FStar_Pprint.op_Hat_Hat uu____2420 uu____2426

and p_qualifier : FStar_Parser_AST.qualifier -> FStar_Pprint.document =
  fun uu___135_2428  ->
    match uu___135_2428 with
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
    let uu____2430 = FStar_Pprint.separate_map break1 p_qualifier qs  in
    FStar_Pprint.group uu____2430

and p_letqualifier : FStar_Parser_AST.let_qualifier -> FStar_Pprint.document
  =
  fun uu___136_2431  ->
    match uu___136_2431 with
    | FStar_Parser_AST.Rec  ->
        let uu____2432 = str "rec"  in
        FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____2432
    | FStar_Parser_AST.Mutable  ->
        let uu____2433 = str "mutable"  in
        FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____2433
    | FStar_Parser_AST.NoLetQualifier  -> FStar_Pprint.empty

and p_aqual : FStar_Parser_AST.arg_qualifier -> FStar_Pprint.document =
  fun uu___137_2434  ->
    match uu___137_2434 with
    | FStar_Parser_AST.Implicit  -> str "#"
    | FStar_Parser_AST.Equality  -> str "$"

and p_disjunctivePattern : FStar_Parser_AST.pattern -> FStar_Pprint.document
  =
  fun p  ->
    match p.FStar_Parser_AST.pat with
    | FStar_Parser_AST.PatOr pats ->
        let uu____2438 =
          let uu____2439 =
            let uu____2440 =
              FStar_Pprint.op_Hat_Hat FStar_Pprint.bar FStar_Pprint.space  in
            FStar_Pprint.op_Hat_Hat break1 uu____2440  in
          FStar_Pprint.separate_map uu____2439 p_tuplePattern pats  in
        FStar_Pprint.group uu____2438
    | uu____2441 -> p_tuplePattern p

and p_tuplePattern : FStar_Parser_AST.pattern -> FStar_Pprint.document =
  fun p  ->
    match p.FStar_Parser_AST.pat with
    | FStar_Parser_AST.PatTuple (pats,false ) ->
        let uu____2446 =
          let uu____2447 = FStar_Pprint.op_Hat_Hat FStar_Pprint.comma break1
             in
          FStar_Pprint.separate_map uu____2447 p_constructorPattern pats  in
        FStar_Pprint.group uu____2446
    | uu____2448 -> p_constructorPattern p

and p_constructorPattern : FStar_Parser_AST.pattern -> FStar_Pprint.document
  =
  fun p  ->
    match p.FStar_Parser_AST.pat with
    | FStar_Parser_AST.PatApp
        ({ FStar_Parser_AST.pat = FStar_Parser_AST.PatName maybe_cons_lid;
           FStar_Parser_AST.prange = uu____2451;_},hd1::tl1::[])
        when
        FStar_Ident.lid_equals maybe_cons_lid FStar_Syntax_Const.cons_lid ->
        let uu____2455 =
          FStar_Pprint.op_Hat_Hat FStar_Pprint.colon FStar_Pprint.colon  in
        let uu____2456 = p_constructorPattern hd1  in
        let uu____2457 = p_constructorPattern tl1  in
        infix0 uu____2455 uu____2456 uu____2457
    | FStar_Parser_AST.PatApp
        ({ FStar_Parser_AST.pat = FStar_Parser_AST.PatName uid;
           FStar_Parser_AST.prange = uu____2459;_},pats)
        ->
        let uu____2463 = p_quident uid  in
        let uu____2464 =
          FStar_Pprint.separate_map break1 p_atomicPattern pats  in
        prefix2 uu____2463 uu____2464
    | uu____2465 -> p_atomicPattern p

and p_atomicPattern : FStar_Parser_AST.pattern -> FStar_Pprint.document =
  fun p  ->
    match p.FStar_Parser_AST.pat with
    | FStar_Parser_AST.PatAscribed (pat,t) ->
        let uu____2469 =
          let uu____2472 =
            let uu____2473 = unparen t  in uu____2473.FStar_Parser_AST.tm  in
          ((pat.FStar_Parser_AST.pat), uu____2472)  in
        (match uu____2469 with
         | (FStar_Parser_AST.PatVar (lid,aqual),FStar_Parser_AST.Refine
            ({ FStar_Parser_AST.b = FStar_Parser_AST.Annotated (lid',t1);
               FStar_Parser_AST.brange = uu____2478;
               FStar_Parser_AST.blevel = uu____2479;
               FStar_Parser_AST.aqual = uu____2480;_},phi))
             when lid.FStar_Ident.idText = lid'.FStar_Ident.idText ->
             let uu____2484 =
               let uu____2485 = p_ident lid  in
               p_refinement aqual uu____2485 t1 phi  in
             soft_parens_with_nesting uu____2484
         | (FStar_Parser_AST.PatWild ,FStar_Parser_AST.Refine
            ({ FStar_Parser_AST.b = FStar_Parser_AST.NoName t1;
               FStar_Parser_AST.brange = uu____2487;
               FStar_Parser_AST.blevel = uu____2488;
               FStar_Parser_AST.aqual = uu____2489;_},phi))
             ->
             let uu____2491 =
               p_refinement None FStar_Pprint.underscore t1 phi  in
             soft_parens_with_nesting uu____2491
         | uu____2492 ->
             let uu____2495 =
               let uu____2496 = p_tuplePattern pat  in
               let uu____2497 =
                 let uu____2498 = FStar_Pprint.break_ (Prims.parse_int "0")
                    in
                 let uu____2499 =
                   let uu____2500 = p_typ t  in
                   FStar_Pprint.op_Hat_Hat FStar_Pprint.colon uu____2500  in
                 FStar_Pprint.op_Hat_Hat uu____2498 uu____2499  in
               FStar_Pprint.op_Hat_Hat uu____2496 uu____2497  in
             soft_parens_with_nesting uu____2495)
    | FStar_Parser_AST.PatList pats ->
        let uu____2503 =
          separate_break_map FStar_Pprint.semi p_tuplePattern pats  in
        FStar_Pprint.surround (Prims.parse_int "2") (Prims.parse_int "0")
          FStar_Pprint.lbracket uu____2503 FStar_Pprint.rbracket
    | FStar_Parser_AST.PatRecord pats ->
        let p_recordFieldPat uu____2513 =
          match uu____2513 with
          | (lid,pat) ->
              let uu____2518 = p_qlident lid  in
              let uu____2519 = p_tuplePattern pat  in
              infix2 FStar_Pprint.equals uu____2518 uu____2519
           in
        let uu____2520 =
          separate_break_map FStar_Pprint.semi p_recordFieldPat pats  in
        soft_braces_with_nesting uu____2520
    | FStar_Parser_AST.PatTuple (pats,true ) ->
        let uu____2526 =
          FStar_Pprint.op_Hat_Hat FStar_Pprint.lparen FStar_Pprint.bar  in
        let uu____2527 =
          separate_break_map FStar_Pprint.comma p_constructorPattern pats  in
        let uu____2528 =
          FStar_Pprint.op_Hat_Hat FStar_Pprint.bar FStar_Pprint.rparen  in
        FStar_Pprint.surround (Prims.parse_int "2") (Prims.parse_int "1")
          uu____2526 uu____2527 uu____2528
    | FStar_Parser_AST.PatTvar (tv,arg_qualifier_opt) -> p_tvar tv
    | FStar_Parser_AST.PatOp op ->
        let uu____2535 =
          let uu____2536 =
            let uu____2537 = str op  in
            let uu____2538 =
              FStar_Pprint.op_Hat_Hat FStar_Pprint.space FStar_Pprint.rparen
               in
            FStar_Pprint.op_Hat_Hat uu____2537 uu____2538  in
          FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____2536  in
        FStar_Pprint.op_Hat_Hat FStar_Pprint.lparen uu____2535
    | FStar_Parser_AST.PatWild  -> FStar_Pprint.underscore
    | FStar_Parser_AST.PatConst c -> p_constant c
    | FStar_Parser_AST.PatVar (lid,aqual) ->
        let uu____2544 = FStar_Pprint.optional p_aqual aqual  in
        let uu____2545 = p_lident lid  in
        FStar_Pprint.op_Hat_Hat uu____2544 uu____2545
    | FStar_Parser_AST.PatName uid -> p_quident uid
    | FStar_Parser_AST.PatOr uu____2547 -> failwith "Inner or pattern !"
    | FStar_Parser_AST.PatApp
      ({ FStar_Parser_AST.pat = FStar_Parser_AST.PatName _;
         FStar_Parser_AST.prange = _;_},_)|FStar_Parser_AST.PatTuple
      (_,false ) ->
        let uu____2555 = p_tuplePattern p  in
        soft_parens_with_nesting uu____2555
    | uu____2556 ->
        let uu____2557 =
          let uu____2558 = FStar_Parser_AST.pat_to_string p  in
          FStar_Util.format1 "Invalid pattern %s" uu____2558  in
        failwith uu____2557

and p_binder : Prims.bool -> FStar_Parser_AST.binder -> FStar_Pprint.document
  =
  fun is_atomic  ->
    fun b  ->
      match b.FStar_Parser_AST.b with
      | FStar_Parser_AST.Variable lid ->
          let uu____2562 =
            FStar_Pprint.optional p_aqual b.FStar_Parser_AST.aqual  in
          let uu____2563 = p_lident lid  in
          FStar_Pprint.op_Hat_Hat uu____2562 uu____2563
      | FStar_Parser_AST.TVariable lid -> p_lident lid
      | FStar_Parser_AST.Annotated (lid,t) ->
          let doc1 =
            let uu____2568 =
              let uu____2569 = unparen t  in uu____2569.FStar_Parser_AST.tm
               in
            match uu____2568 with
            | FStar_Parser_AST.Refine
                ({ FStar_Parser_AST.b = FStar_Parser_AST.Annotated (lid',t1);
                   FStar_Parser_AST.brange = uu____2572;
                   FStar_Parser_AST.blevel = uu____2573;
                   FStar_Parser_AST.aqual = uu____2574;_},phi)
                when lid.FStar_Ident.idText = lid'.FStar_Ident.idText ->
                let uu____2576 = p_ident lid  in
                p_refinement b.FStar_Parser_AST.aqual uu____2576 t1 phi
            | uu____2577 ->
                let uu____2578 =
                  FStar_Pprint.optional p_aqual b.FStar_Parser_AST.aqual  in
                let uu____2579 =
                  let uu____2580 = p_lident lid  in
                  let uu____2581 =
                    let uu____2582 =
                      let uu____2583 =
                        FStar_Pprint.break_ (Prims.parse_int "0")  in
                      let uu____2584 = p_tmFormula t  in
                      FStar_Pprint.op_Hat_Hat uu____2583 uu____2584  in
                    FStar_Pprint.op_Hat_Hat FStar_Pprint.colon uu____2582  in
                  FStar_Pprint.op_Hat_Hat uu____2580 uu____2581  in
                FStar_Pprint.op_Hat_Hat uu____2578 uu____2579
             in
          if is_atomic
          then
            let uu____2585 =
              let uu____2586 =
                FStar_Pprint.op_Hat_Hat doc1 FStar_Pprint.rparen  in
              FStar_Pprint.op_Hat_Hat FStar_Pprint.lparen uu____2586  in
            FStar_Pprint.group uu____2585
          else FStar_Pprint.group doc1
      | FStar_Parser_AST.TAnnotated uu____2588 ->
          failwith "Is this still used ?"
      | FStar_Parser_AST.NoName t ->
          let uu____2592 =
            let uu____2593 = unparen t  in uu____2593.FStar_Parser_AST.tm  in
          (match uu____2592 with
           | FStar_Parser_AST.Refine
               ({ FStar_Parser_AST.b = FStar_Parser_AST.NoName t1;
                  FStar_Parser_AST.brange = uu____2595;
                  FStar_Parser_AST.blevel = uu____2596;
                  FStar_Parser_AST.aqual = uu____2597;_},phi)
               ->
               if is_atomic
               then
                 let uu____2599 =
                   let uu____2600 =
                     let uu____2601 =
                       p_refinement b.FStar_Parser_AST.aqual
                         FStar_Pprint.underscore t1 phi
                        in
                     FStar_Pprint.op_Hat_Hat uu____2601 FStar_Pprint.rparen
                      in
                   FStar_Pprint.op_Hat_Hat FStar_Pprint.lparen uu____2600  in
                 FStar_Pprint.group uu____2599
               else
                 (let uu____2603 =
                    p_refinement b.FStar_Parser_AST.aqual
                      FStar_Pprint.underscore t1 phi
                     in
                  FStar_Pprint.group uu____2603)
           | uu____2604 -> if is_atomic then p_atomicTerm t else p_appTerm t)

and p_refinement :
  FStar_Parser_AST.arg_qualifier Prims.option ->
    FStar_Pprint.document ->
      FStar_Parser_AST.term -> FStar_Parser_AST.term -> FStar_Pprint.document
  =
  fun aqual_opt  ->
    fun binder  ->
      fun t  ->
        fun phi  ->
          let uu____2611 = FStar_Pprint.optional p_aqual aqual_opt  in
          let uu____2612 =
            let uu____2613 =
              let uu____2614 =
                let uu____2615 = p_appTerm t  in
                let uu____2616 =
                  let uu____2617 = p_noSeqTerm phi  in
                  soft_braces_with_nesting uu____2617  in
                FStar_Pprint.op_Hat_Hat uu____2615 uu____2616  in
              FStar_Pprint.op_Hat_Hat FStar_Pprint.colon uu____2614  in
            FStar_Pprint.op_Hat_Hat binder uu____2613  in
          FStar_Pprint.op_Hat_Hat uu____2611 uu____2612

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
    let uu____2630 =
      let uu____2631 = unparen e  in uu____2631.FStar_Parser_AST.tm  in
    match uu____2630 with
    | FStar_Parser_AST.Seq (e1,e2) ->
        let uu____2634 =
          let uu____2635 =
            let uu____2636 = p_noSeqTerm e1  in
            FStar_Pprint.op_Hat_Hat uu____2636 FStar_Pprint.semi  in
          FStar_Pprint.group uu____2635  in
        let uu____2637 = p_term e2  in
        FStar_Pprint.op_Hat_Slash_Hat uu____2634 uu____2637
    | uu____2638 ->
        let uu____2639 = p_noSeqTerm e  in FStar_Pprint.group uu____2639

and p_noSeqTerm : FStar_Parser_AST.term -> FStar_Pprint.document =
  fun e  -> with_comment p_noSeqTerm' e e.FStar_Parser_AST.range

and p_noSeqTerm' : FStar_Parser_AST.term -> FStar_Pprint.document =
  fun e  ->
    let uu____2642 =
      let uu____2643 = unparen e  in uu____2643.FStar_Parser_AST.tm  in
    match uu____2642 with
    | FStar_Parser_AST.Ascribed (e1,t) ->
        let uu____2646 =
          let uu____2647 = p_tmIff e1  in
          let uu____2648 =
            let uu____2649 =
              let uu____2650 = p_typ t  in
              FStar_Pprint.op_Hat_Slash_Hat FStar_Pprint.colon uu____2650  in
            FStar_Pprint.op_Hat_Hat FStar_Pprint.langle uu____2649  in
          FStar_Pprint.op_Hat_Slash_Hat uu____2647 uu____2648  in
        FStar_Pprint.group uu____2646
    | FStar_Parser_AST.Op (op,e1::e2::e3::[]) when op = ".()<-" ->
        let uu____2656 =
          let uu____2657 =
            let uu____2658 =
              let uu____2659 = p_atomicTermNotQUident e1  in
              let uu____2660 =
                let uu____2661 =
                  let uu____2662 =
                    let uu____2663 = p_term e2  in
                    soft_parens_with_nesting uu____2663  in
                  let uu____2664 =
                    FStar_Pprint.op_Hat_Hat FStar_Pprint.space
                      FStar_Pprint.larrow
                     in
                  FStar_Pprint.op_Hat_Hat uu____2662 uu____2664  in
                FStar_Pprint.op_Hat_Hat FStar_Pprint.dot uu____2661  in
              FStar_Pprint.op_Hat_Hat uu____2659 uu____2660  in
            FStar_Pprint.group uu____2658  in
          let uu____2665 =
            let uu____2666 = p_noSeqTerm e3  in jump2 uu____2666  in
          FStar_Pprint.op_Hat_Hat uu____2657 uu____2665  in
        FStar_Pprint.group uu____2656
    | FStar_Parser_AST.Op (op,e1::e2::e3::[]) when op = ".[]<-" ->
        let uu____2672 =
          let uu____2673 =
            let uu____2674 =
              let uu____2675 = p_atomicTermNotQUident e1  in
              let uu____2676 =
                let uu____2677 =
                  let uu____2678 =
                    let uu____2679 = p_term e2  in
                    soft_brackets_with_nesting uu____2679  in
                  let uu____2680 =
                    FStar_Pprint.op_Hat_Hat FStar_Pprint.space
                      FStar_Pprint.larrow
                     in
                  FStar_Pprint.op_Hat_Hat uu____2678 uu____2680  in
                FStar_Pprint.op_Hat_Hat FStar_Pprint.dot uu____2677  in
              FStar_Pprint.op_Hat_Hat uu____2675 uu____2676  in
            FStar_Pprint.group uu____2674  in
          let uu____2681 =
            let uu____2682 = p_noSeqTerm e3  in jump2 uu____2682  in
          FStar_Pprint.op_Hat_Hat uu____2673 uu____2681  in
        FStar_Pprint.group uu____2672
    | FStar_Parser_AST.Requires (e1,wtf) ->
        let uu____2688 =
          let uu____2689 = str "requires"  in
          let uu____2690 = p_typ e1  in
          FStar_Pprint.op_Hat_Slash_Hat uu____2689 uu____2690  in
        FStar_Pprint.group uu____2688
    | FStar_Parser_AST.Ensures (e1,wtf) ->
        let uu____2696 =
          let uu____2697 = str "ensures"  in
          let uu____2698 = p_typ e1  in
          FStar_Pprint.op_Hat_Slash_Hat uu____2697 uu____2698  in
        FStar_Pprint.group uu____2696
    | FStar_Parser_AST.Attributes es ->
        let uu____2701 =
          let uu____2702 = str "attributes"  in
          let uu____2703 = FStar_Pprint.separate_map break1 p_atomicTerm es
             in
          FStar_Pprint.op_Hat_Slash_Hat uu____2702 uu____2703  in
        FStar_Pprint.group uu____2701
    | FStar_Parser_AST.If (e1,e2,e3) ->
        let uu____2707 = is_unit e3  in
        if uu____2707
        then
          let uu____2708 =
            let uu____2709 =
              let uu____2710 = str "if"  in
              let uu____2711 = p_noSeqTerm e1  in
              op_Hat_Slash_Plus_Hat uu____2710 uu____2711  in
            let uu____2712 =
              let uu____2713 = str "then"  in
              let uu____2714 = p_noSeqTerm e2  in
              op_Hat_Slash_Plus_Hat uu____2713 uu____2714  in
            FStar_Pprint.op_Hat_Slash_Hat uu____2709 uu____2712  in
          FStar_Pprint.group uu____2708
        else
          (let e2_doc =
             let uu____2717 =
               let uu____2718 = unparen e2  in uu____2718.FStar_Parser_AST.tm
                in
             match uu____2717 with
             | FStar_Parser_AST.If (uu____2719,uu____2720,e31) when
                 is_unit e31 ->
                 let uu____2722 = p_noSeqTerm e2  in
                 soft_parens_with_nesting uu____2722
             | uu____2723 -> p_noSeqTerm e2  in
           let uu____2724 =
             let uu____2725 =
               let uu____2726 = str "if"  in
               let uu____2727 = p_noSeqTerm e1  in
               op_Hat_Slash_Plus_Hat uu____2726 uu____2727  in
             let uu____2728 =
               let uu____2729 =
                 let uu____2730 = str "then"  in
                 op_Hat_Slash_Plus_Hat uu____2730 e2_doc  in
               let uu____2731 =
                 let uu____2732 = str "else"  in
                 let uu____2733 = p_noSeqTerm e3  in
                 op_Hat_Slash_Plus_Hat uu____2732 uu____2733  in
               FStar_Pprint.op_Hat_Slash_Hat uu____2729 uu____2731  in
             FStar_Pprint.op_Hat_Slash_Hat uu____2725 uu____2728  in
           FStar_Pprint.group uu____2724)
    | FStar_Parser_AST.TryWith (e1,branches) ->
        let uu____2746 =
          let uu____2747 =
            let uu____2748 = str "try"  in
            let uu____2749 = p_noSeqTerm e1  in prefix2 uu____2748 uu____2749
             in
          let uu____2750 =
            let uu____2751 = str "with"  in
            let uu____2752 =
              FStar_Pprint.separate_map FStar_Pprint.hardline p_patternBranch
                branches
               in
            FStar_Pprint.op_Hat_Slash_Hat uu____2751 uu____2752  in
          FStar_Pprint.op_Hat_Slash_Hat uu____2747 uu____2750  in
        FStar_Pprint.group uu____2746
    | FStar_Parser_AST.Match (e1,branches) ->
        let uu____2769 =
          let uu____2770 =
            let uu____2771 = str "match"  in
            let uu____2772 = p_noSeqTerm e1  in
            let uu____2773 = str "with"  in
            FStar_Pprint.surround (Prims.parse_int "2") (Prims.parse_int "1")
              uu____2771 uu____2772 uu____2773
             in
          let uu____2774 =
            FStar_Pprint.separate_map FStar_Pprint.hardline p_patternBranch
              branches
             in
          FStar_Pprint.op_Hat_Slash_Hat uu____2770 uu____2774  in
        FStar_Pprint.group uu____2769
    | FStar_Parser_AST.LetOpen (uid,e1) ->
        let uu____2781 =
          let uu____2782 =
            let uu____2783 = str "let open"  in
            let uu____2784 = p_quident uid  in
            let uu____2785 = str "in"  in
            FStar_Pprint.surround (Prims.parse_int "2") (Prims.parse_int "1")
              uu____2783 uu____2784 uu____2785
             in
          let uu____2786 = p_term e1  in
          FStar_Pprint.op_Hat_Slash_Hat uu____2782 uu____2786  in
        FStar_Pprint.group uu____2781
    | FStar_Parser_AST.Let (q,lbs,e1) ->
        let let_doc =
          let uu____2797 = str "let"  in
          let uu____2798 = p_letqualifier q  in
          FStar_Pprint.op_Hat_Hat uu____2797 uu____2798  in
        let uu____2799 =
          let uu____2800 =
            let uu____2801 =
              let uu____2802 = str "and"  in
              precede_break_separate_map let_doc uu____2802 p_letbinding lbs
               in
            let uu____2805 = str "in"  in
            FStar_Pprint.op_Hat_Slash_Hat uu____2801 uu____2805  in
          FStar_Pprint.group uu____2800  in
        let uu____2806 = p_term e1  in
        FStar_Pprint.op_Hat_Slash_Hat uu____2799 uu____2806
    | FStar_Parser_AST.Abs
        ({ FStar_Parser_AST.pat = FStar_Parser_AST.PatVar (x,typ_opt);
           FStar_Parser_AST.prange = uu____2809;_}::[],{
                                                         FStar_Parser_AST.tm
                                                           =
                                                           FStar_Parser_AST.Match
                                                           (maybe_x,branches);
                                                         FStar_Parser_AST.range
                                                           = uu____2812;
                                                         FStar_Parser_AST.level
                                                           = uu____2813;_})
        when matches_var maybe_x x ->
        let uu____2827 =
          let uu____2828 = str "function"  in
          let uu____2829 =
            FStar_Pprint.separate_map FStar_Pprint.hardline p_patternBranch
              branches
             in
          FStar_Pprint.op_Hat_Slash_Hat uu____2828 uu____2829  in
        FStar_Pprint.group uu____2827
    | FStar_Parser_AST.Assign (id,e1) ->
        let uu____2836 =
          let uu____2837 = p_lident id  in
          let uu____2838 =
            let uu____2839 = p_noSeqTerm e1  in
            FStar_Pprint.op_Hat_Slash_Hat FStar_Pprint.larrow uu____2839  in
          FStar_Pprint.op_Hat_Slash_Hat uu____2837 uu____2838  in
        FStar_Pprint.group uu____2836
    | uu____2840 -> p_typ e

and p_typ : FStar_Parser_AST.term -> FStar_Pprint.document =
  fun e  -> with_comment p_typ' e e.FStar_Parser_AST.range

and p_typ' : FStar_Parser_AST.term -> FStar_Pprint.document =
  fun e  ->
    let uu____2843 =
      let uu____2844 = unparen e  in uu____2844.FStar_Parser_AST.tm  in
    match uu____2843 with
    | FStar_Parser_AST.QForall (bs,trigger,e1)|FStar_Parser_AST.QExists
      (bs,trigger,e1) ->
        let uu____2860 =
          let uu____2861 =
            let uu____2862 = p_quantifier e  in
            FStar_Pprint.op_Hat_Hat uu____2862 FStar_Pprint.space  in
          let uu____2863 = p_binders true bs  in
          FStar_Pprint.soft_surround (Prims.parse_int "2")
            (Prims.parse_int "0") uu____2861 uu____2863 FStar_Pprint.dot
           in
        let uu____2864 =
          let uu____2865 = p_trigger trigger  in
          let uu____2866 = p_noSeqTerm e1  in
          FStar_Pprint.op_Hat_Hat uu____2865 uu____2866  in
        prefix2 uu____2860 uu____2864
    | uu____2867 -> p_simpleTerm e

and p_quantifier : FStar_Parser_AST.term -> FStar_Pprint.document =
  fun e  ->
    let uu____2869 =
      let uu____2870 = unparen e  in uu____2870.FStar_Parser_AST.tm  in
    match uu____2869 with
    | FStar_Parser_AST.QForall uu____2871 -> str "forall"
    | FStar_Parser_AST.QExists uu____2878 -> str "exists"
    | uu____2885 ->
        failwith "Imposible : p_quantifier called on a non-quantifier term"

and p_trigger :
  FStar_Parser_AST.term Prims.list Prims.list -> FStar_Pprint.document =
  fun uu___138_2886  ->
    match uu___138_2886 with
    | [] -> FStar_Pprint.empty
    | pats ->
        let uu____2893 =
          let uu____2894 =
            let uu____2895 = str "pattern"  in
            let uu____2896 =
              let uu____2897 =
                let uu____2898 = p_disjunctivePats pats  in jump2 uu____2898
                 in
              let uu____2899 =
                FStar_Pprint.op_Hat_Hat FStar_Pprint.rbrace break1  in
              FStar_Pprint.op_Hat_Slash_Hat uu____2897 uu____2899  in
            FStar_Pprint.op_Hat_Slash_Hat uu____2895 uu____2896  in
          FStar_Pprint.op_Hat_Hat FStar_Pprint.colon uu____2894  in
        FStar_Pprint.op_Hat_Hat FStar_Pprint.lbrace uu____2893

and p_disjunctivePats :
  FStar_Parser_AST.term Prims.list Prims.list -> FStar_Pprint.document =
  fun pats  ->
    let uu____2903 = str "\\/"  in
    FStar_Pprint.separate_map uu____2903 p_conjunctivePats pats

and p_conjunctivePats :
  FStar_Parser_AST.term Prims.list -> FStar_Pprint.document =
  fun pats  ->
    let uu____2907 =
      FStar_Pprint.separate_map FStar_Pprint.semi p_appTerm pats  in
    FStar_Pprint.group uu____2907

and p_simpleTerm : FStar_Parser_AST.term -> FStar_Pprint.document =
  fun e  ->
    let uu____2909 =
      let uu____2910 = unparen e  in uu____2910.FStar_Parser_AST.tm  in
    match uu____2909 with
    | FStar_Parser_AST.Abs (pats,e1) ->
        let uu____2915 =
          let uu____2916 = str "fun"  in
          let uu____2917 =
            let uu____2918 =
              FStar_Pprint.separate_map break1 p_atomicPattern pats  in
            FStar_Pprint.op_Hat_Slash_Hat uu____2918 FStar_Pprint.rarrow  in
          op_Hat_Slash_Plus_Hat uu____2916 uu____2917  in
        let uu____2919 = p_term e1  in
        op_Hat_Slash_Plus_Hat uu____2915 uu____2919
    | uu____2920 -> p_tmIff e

and p_maybeFocusArrow : Prims.bool -> FStar_Pprint.document =
  fun b  -> if b then str "~>" else FStar_Pprint.rarrow

and p_patternBranch :
  (FStar_Parser_AST.pattern * FStar_Parser_AST.term Prims.option *
    FStar_Parser_AST.term) -> FStar_Pprint.document
  =
  fun uu____2923  ->
    match uu____2923 with
    | (pat,when_opt,e) ->
        let maybe_paren =
          let uu____2936 =
            let uu____2937 = unparen e  in uu____2937.FStar_Parser_AST.tm  in
          match uu____2936 with
          | FStar_Parser_AST.Match _|FStar_Parser_AST.TryWith _ ->
              soft_begin_end_with_nesting
          | FStar_Parser_AST.Abs
              ({
                 FStar_Parser_AST.pat = FStar_Parser_AST.PatVar
                   (x,uu____2943);
                 FStar_Parser_AST.prange = uu____2944;_}::[],{
                                                               FStar_Parser_AST.tm
                                                                 =
                                                                 FStar_Parser_AST.Match
                                                                 (maybe_x,uu____2946);
                                                               FStar_Parser_AST.range
                                                                 = uu____2947;
                                                               FStar_Parser_AST.level
                                                                 = uu____2948;_})
              when matches_var maybe_x x -> soft_begin_end_with_nesting
          | uu____2962 -> (fun x  -> x)  in
        let uu____2964 =
          let uu____2965 =
            let uu____2966 =
              let uu____2967 =
                let uu____2968 =
                  let uu____2969 = p_disjunctivePattern pat  in
                  let uu____2970 =
                    let uu____2971 = p_maybeWhen when_opt  in
                    FStar_Pprint.op_Hat_Hat uu____2971 FStar_Pprint.rarrow
                     in
                  op_Hat_Slash_Plus_Hat uu____2969 uu____2970  in
                FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____2968  in
              FStar_Pprint.op_Hat_Hat FStar_Pprint.bar uu____2967  in
            FStar_Pprint.group uu____2966  in
          let uu____2972 =
            let uu____2973 = p_term e  in maybe_paren uu____2973  in
          op_Hat_Slash_Plus_Hat uu____2965 uu____2972  in
        FStar_Pprint.group uu____2964

and p_maybeWhen : FStar_Parser_AST.term Prims.option -> FStar_Pprint.document
  =
  fun uu___139_2974  ->
    match uu___139_2974 with
    | None  -> FStar_Pprint.empty
    | Some e ->
        let uu____2977 = str "when"  in
        let uu____2978 =
          let uu____2979 = p_tmFormula e  in
          FStar_Pprint.op_Hat_Hat uu____2979 FStar_Pprint.space  in
        op_Hat_Slash_Plus_Hat uu____2977 uu____2978

and p_tmIff : FStar_Parser_AST.term -> FStar_Pprint.document =
  fun e  ->
    let uu____2981 =
      let uu____2982 = unparen e  in uu____2982.FStar_Parser_AST.tm  in
    match uu____2981 with
    | FStar_Parser_AST.Op ("<==>",e1::e2::[]) ->
        let uu____2986 = str "<==>"  in
        let uu____2987 = p_tmImplies e1  in
        let uu____2988 = p_tmIff e2  in
        infix0 uu____2986 uu____2987 uu____2988
    | uu____2989 -> p_tmImplies e

and p_tmImplies : FStar_Parser_AST.term -> FStar_Pprint.document =
  fun e  ->
    let uu____2991 =
      let uu____2992 = unparen e  in uu____2992.FStar_Parser_AST.tm  in
    match uu____2991 with
    | FStar_Parser_AST.Op ("==>",e1::e2::[]) ->
        let uu____2996 = str "==>"  in
        let uu____2997 = p_tmArrow p_tmFormula e1  in
        let uu____2998 = p_tmImplies e2  in
        infix0 uu____2996 uu____2997 uu____2998
    | uu____2999 -> p_tmArrow p_tmFormula e

and p_tmArrow :
  (FStar_Parser_AST.term -> FStar_Pprint.document) ->
    FStar_Parser_AST.term -> FStar_Pprint.document
  =
  fun p_Tm  ->
    fun e  ->
      let uu____3004 =
        let uu____3005 = unparen e  in uu____3005.FStar_Parser_AST.tm  in
      match uu____3004 with
      | FStar_Parser_AST.Product (bs,tgt) ->
          let uu____3010 =
            let uu____3011 =
              FStar_Pprint.concat_map
                (fun b  ->
                   let uu____3013 = p_binder false b  in
                   let uu____3014 =
                     let uu____3015 =
                       FStar_Pprint.op_Hat_Hat FStar_Pprint.rarrow break1  in
                     FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____3015
                      in
                   FStar_Pprint.op_Hat_Hat uu____3013 uu____3014) bs
               in
            let uu____3016 = p_tmArrow p_Tm tgt  in
            FStar_Pprint.op_Hat_Hat uu____3011 uu____3016  in
          FStar_Pprint.group uu____3010
      | uu____3017 -> p_Tm e

and p_tmFormula : FStar_Parser_AST.term -> FStar_Pprint.document =
  fun e  ->
    let uu____3019 =
      let uu____3020 = unparen e  in uu____3020.FStar_Parser_AST.tm  in
    match uu____3019 with
    | FStar_Parser_AST.Op ("\\/",e1::e2::[]) ->
        let uu____3024 = str "\\/"  in
        let uu____3025 = p_tmFormula e1  in
        let uu____3026 = p_tmConjunction e2  in
        infix0 uu____3024 uu____3025 uu____3026
    | uu____3027 -> p_tmConjunction e

and p_tmConjunction : FStar_Parser_AST.term -> FStar_Pprint.document =
  fun e  ->
    let uu____3029 =
      let uu____3030 = unparen e  in uu____3030.FStar_Parser_AST.tm  in
    match uu____3029 with
    | FStar_Parser_AST.Op ("/\\",e1::e2::[]) ->
        let uu____3034 = str "/\\"  in
        let uu____3035 = p_tmConjunction e1  in
        let uu____3036 = p_tmTuple e2  in
        infix0 uu____3034 uu____3035 uu____3036
    | uu____3037 -> p_tmTuple e

and p_tmTuple : FStar_Parser_AST.term -> FStar_Pprint.document =
  fun e  -> with_comment p_tmTuple' e e.FStar_Parser_AST.range

and p_tmTuple' : FStar_Parser_AST.term -> FStar_Pprint.document =
  fun e  ->
    let uu____3040 =
      let uu____3041 = unparen e  in uu____3041.FStar_Parser_AST.tm  in
    match uu____3040 with
    | FStar_Parser_AST.Construct (lid,args) when is_tuple_constructor lid ->
        let uu____3050 = FStar_Pprint.op_Hat_Hat FStar_Pprint.comma break1
           in
        FStar_Pprint.separate_map uu____3050
          (fun uu____3053  ->
             match uu____3053 with | (e1,uu____3057) -> p_tmEq e1) args
    | uu____3058 -> p_tmEq e

and paren_if :
  Prims.int -> Prims.int -> FStar_Pprint.document -> FStar_Pprint.document =
  fun curr  ->
    fun mine  ->
      fun doc1  ->
        if mine <= curr
        then doc1
        else
          (let uu____3063 =
             let uu____3064 =
               FStar_Pprint.op_Hat_Hat doc1 FStar_Pprint.rparen  in
             FStar_Pprint.op_Hat_Hat FStar_Pprint.lparen uu____3064  in
           FStar_Pprint.group uu____3063)

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
      let uu____3089 =
        let uu____3090 = unparen e  in uu____3090.FStar_Parser_AST.tm  in
      match uu____3089 with
      | FStar_Parser_AST.Op (op,e1::e2::[]) when
          ((is_operatorInfix0ad12 op) || (op = "=")) || (op = "|>") ->
          let uu____3095 = levels op  in
          (match uu____3095 with
           | (left1,mine,right1) ->
               let uu____3102 =
                 let uu____3103 = str op  in
                 let uu____3104 = p_tmEq' left1 e1  in
                 let uu____3105 = p_tmEq' right1 e2  in
                 infix0 uu____3103 uu____3104 uu____3105  in
               paren_if curr mine uu____3102)
      | FStar_Parser_AST.Op (":=",e1::e2::[]) ->
          let uu____3109 =
            let uu____3110 = p_tmEq e1  in
            let uu____3111 =
              let uu____3112 =
                let uu____3113 =
                  let uu____3114 = p_tmEq e2  in
                  op_Hat_Slash_Plus_Hat FStar_Pprint.equals uu____3114  in
                FStar_Pprint.op_Hat_Hat FStar_Pprint.colon uu____3113  in
              FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____3112  in
            FStar_Pprint.op_Hat_Hat uu____3110 uu____3111  in
          FStar_Pprint.group uu____3109
      | uu____3115 -> p_tmNoEq e

and p_tmNoEq : FStar_Parser_AST.term -> FStar_Pprint.document =
  fun e  ->
    let n1 = max_level [colon_colon (); amp (); opinfix3 (); opinfix4 ()]  in
    p_tmNoEq' n1 e

and p_tmNoEq' : Prims.int -> FStar_Parser_AST.term -> FStar_Pprint.document =
  fun curr  ->
    fun e  ->
      let uu____3145 =
        let uu____3146 = unparen e  in uu____3146.FStar_Parser_AST.tm  in
      match uu____3145 with
      | FStar_Parser_AST.Construct (lid,(e1,uu____3149)::(e2,uu____3151)::[])
          when
          (FStar_Ident.lid_equals lid FStar_Syntax_Const.cons_lid) &&
            (let uu____3161 = is_list e  in Prims.op_Negation uu____3161)
          ->
          let op = "::"  in
          let uu____3163 = levels op  in
          (match uu____3163 with
           | (left1,mine,right1) ->
               let uu____3170 =
                 let uu____3171 = str op  in
                 let uu____3172 = p_tmNoEq' left1 e1  in
                 let uu____3173 = p_tmNoEq' right1 e2  in
                 infix0 uu____3171 uu____3172 uu____3173  in
               paren_if curr mine uu____3170)
      | FStar_Parser_AST.Sum (binders,res) ->
          let op = "&"  in
          let uu____3179 = levels op  in
          (match uu____3179 with
           | (left1,mine,right1) ->
               let p_dsumfst b =
                 let uu____3190 = p_binder false b  in
                 let uu____3191 =
                   let uu____3192 =
                     let uu____3193 = str "&"  in
                     FStar_Pprint.op_Hat_Hat uu____3193 break1  in
                   FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____3192  in
                 FStar_Pprint.op_Hat_Hat uu____3190 uu____3191  in
               let uu____3194 =
                 let uu____3195 = FStar_Pprint.concat_map p_dsumfst binders
                    in
                 let uu____3196 = p_tmNoEq' right1 res  in
                 FStar_Pprint.op_Hat_Hat uu____3195 uu____3196  in
               paren_if curr mine uu____3194)
      | FStar_Parser_AST.Op (op,e1::e2::[]) when is_operatorInfix34 op ->
          let uu____3201 = levels op  in
          (match uu____3201 with
           | (left1,mine,right1) ->
               let uu____3208 =
                 let uu____3209 = str op  in
                 let uu____3210 = p_tmNoEq' left1 e1  in
                 let uu____3211 = p_tmNoEq' right1 e2  in
                 infix0 uu____3209 uu____3210 uu____3211  in
               paren_if curr mine uu____3208)
      | FStar_Parser_AST.Op ("-",e1::[]) ->
          let uu____3214 = levels "-"  in
          (match uu____3214 with
           | (left1,mine,right1) ->
               let uu____3221 = p_tmNoEq' mine e1  in
               FStar_Pprint.op_Hat_Slash_Hat FStar_Pprint.minus uu____3221)
      | FStar_Parser_AST.NamedTyp (lid,e1) ->
          let uu____3224 =
            let uu____3225 = p_lidentOrUnderscore lid  in
            let uu____3226 =
              let uu____3227 = p_appTerm e1  in
              FStar_Pprint.op_Hat_Slash_Hat FStar_Pprint.colon uu____3227  in
            FStar_Pprint.op_Hat_Slash_Hat uu____3225 uu____3226  in
          FStar_Pprint.group uu____3224
      | FStar_Parser_AST.Refine (b,phi) -> p_refinedBinder b phi
      | FStar_Parser_AST.Record (with_opt,record_fields) ->
          let uu____3240 =
            let uu____3241 =
              default_or_map FStar_Pprint.empty p_with_clause with_opt  in
            let uu____3242 =
              let uu____3243 =
                FStar_Pprint.op_Hat_Hat FStar_Pprint.semi break1  in
              FStar_Pprint.separate_map uu____3243 p_simpleDef record_fields
               in
            FStar_Pprint.op_Hat_Hat uu____3241 uu____3242  in
          braces_with_nesting uu____3240
      | FStar_Parser_AST.Op ("~",e1::[]) ->
          let uu____3248 =
            let uu____3249 = str "~"  in
            let uu____3250 = p_atomicTerm e1  in
            FStar_Pprint.op_Hat_Hat uu____3249 uu____3250  in
          FStar_Pprint.group uu____3248
      | uu____3251 -> p_appTerm e

and p_with_clause : FStar_Parser_AST.term -> FStar_Pprint.document =
  fun e  ->
    let uu____3253 = p_appTerm e  in
    let uu____3254 =
      let uu____3255 =
        let uu____3256 = str "with"  in
        FStar_Pprint.op_Hat_Hat uu____3256 break1  in
      FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____3255  in
    FStar_Pprint.op_Hat_Hat uu____3253 uu____3254

and p_refinedBinder :
  FStar_Parser_AST.binder -> FStar_Parser_AST.term -> FStar_Pprint.document =
  fun b  ->
    fun phi  ->
      match b.FStar_Parser_AST.b with
      | FStar_Parser_AST.Annotated (lid,t) ->
          let uu____3261 =
            let uu____3262 = p_lident lid  in
            p_refinement b.FStar_Parser_AST.aqual uu____3262 t phi  in
          soft_parens_with_nesting uu____3261
      | FStar_Parser_AST.TAnnotated uu____3263 ->
          failwith "Is this still used ?"
      | FStar_Parser_AST.Variable _
        |FStar_Parser_AST.TVariable _|FStar_Parser_AST.NoName _ ->
          let uu____3269 =
            let uu____3270 = FStar_Parser_AST.binder_to_string b  in
            FStar_Util.format1
              "Imposible : a refined binder ought to be annotated %s"
              uu____3270
             in
          failwith uu____3269

and p_simpleDef :
  (FStar_Ident.lid * FStar_Parser_AST.term) -> FStar_Pprint.document =
  fun uu____3271  ->
    match uu____3271 with
    | (lid,e) ->
        let uu____3276 =
          let uu____3277 = p_qlident lid  in
          let uu____3278 =
            let uu____3279 = p_tmIff e  in
            FStar_Pprint.op_Hat_Slash_Hat FStar_Pprint.equals uu____3279  in
          FStar_Pprint.op_Hat_Slash_Hat uu____3277 uu____3278  in
        FStar_Pprint.group uu____3276

and p_appTerm : FStar_Parser_AST.term -> FStar_Pprint.document =
  fun e  ->
    let uu____3281 =
      let uu____3282 = unparen e  in uu____3282.FStar_Parser_AST.tm  in
    match uu____3281 with
    | FStar_Parser_AST.App uu____3283 when is_general_application e ->
        let uu____3287 = head_and_args e  in
        (match uu____3287 with
         | (head1,args) ->
             let uu____3301 =
               let uu____3307 = FStar_ST.read should_print_fs_typ_app  in
               if uu____3307
               then
                 let uu____3315 =
                   FStar_Util.take
                     (fun uu____3326  ->
                        match uu____3326 with
                        | (uu____3329,aq) -> aq = FStar_Parser_AST.FsTypApp)
                     args
                    in
                 match uu____3315 with
                 | (fs_typ_args,args1) ->
                     let uu____3350 =
                       let uu____3351 = p_indexingTerm head1  in
                       let uu____3352 =
                         let uu____3353 =
                           FStar_Pprint.op_Hat_Hat FStar_Pprint.comma break1
                            in
                         soft_surround_separate_map (Prims.parse_int "2")
                           (Prims.parse_int "0") FStar_Pprint.empty
                           FStar_Pprint.langle uu____3353 FStar_Pprint.rangle
                           p_fsTypArg fs_typ_args
                          in
                       FStar_Pprint.op_Hat_Hat uu____3351 uu____3352  in
                     (uu____3350, args1)
               else
                 (let uu____3360 = p_indexingTerm head1  in
                  (uu____3360, args))
                in
             (match uu____3301 with
              | (head_doc,args1) ->
                  let uu____3372 =
                    let uu____3373 =
                      FStar_Pprint.op_Hat_Hat head_doc FStar_Pprint.space  in
                    soft_surround_separate_map (Prims.parse_int "2")
                      (Prims.parse_int "0") head_doc uu____3373 break1
                      FStar_Pprint.empty p_argTerm args1
                     in
                  FStar_Pprint.group uu____3372))
    | FStar_Parser_AST.Construct (lid,args) when
        (is_general_construction e) &&
          (Prims.op_Negation (is_dtuple_constructor lid))
        ->
        (match args with
         | [] -> p_quident lid
         | arg::[] ->
             let uu____3393 =
               let uu____3394 = p_quident lid  in
               let uu____3395 = p_argTerm arg  in
               FStar_Pprint.op_Hat_Slash_Hat uu____3394 uu____3395  in
             FStar_Pprint.group uu____3393
         | hd1::tl1 ->
             let uu____3405 =
               let uu____3406 =
                 let uu____3407 =
                   let uu____3408 = p_quident lid  in
                   let uu____3409 = p_argTerm hd1  in
                   prefix2 uu____3408 uu____3409  in
                 FStar_Pprint.group uu____3407  in
               let uu____3410 =
                 let uu____3411 =
                   FStar_Pprint.separate_map break1 p_argTerm tl1  in
                 jump2 uu____3411  in
               FStar_Pprint.op_Hat_Hat uu____3406 uu____3410  in
             FStar_Pprint.group uu____3405)
    | uu____3414 -> p_indexingTerm e

and p_argTerm :
  (FStar_Parser_AST.term * FStar_Parser_AST.imp) -> FStar_Pprint.document =
  fun arg_imp  ->
    match arg_imp with
    | ({ FStar_Parser_AST.tm = FStar_Parser_AST.Uvar uu____3418;
         FStar_Parser_AST.range = uu____3419;
         FStar_Parser_AST.level = uu____3420;_},FStar_Parser_AST.UnivApp
       ) -> p_univar (Prims.fst arg_imp)
    | (u,FStar_Parser_AST.UnivApp ) -> p_universe u
    | (e,FStar_Parser_AST.FsTypApp ) ->
        (FStar_Util.print_warning
           "Unexpected FsTypApp, output might not be formatted correctly.\n";
         (let uu____3424 = p_indexingTerm e  in
          FStar_Pprint.surround (Prims.parse_int "2") (Prims.parse_int "1")
            FStar_Pprint.langle uu____3424 FStar_Pprint.rangle))
    | (e,FStar_Parser_AST.Hash ) ->
        let uu____3426 = str "#"  in
        let uu____3427 = p_indexingTerm e  in
        FStar_Pprint.op_Hat_Hat uu____3426 uu____3427
    | (e,FStar_Parser_AST.Nothing ) -> p_indexingTerm e

and p_fsTypArg :
  (FStar_Parser_AST.term * FStar_Parser_AST.imp) -> FStar_Pprint.document =
  fun uu____3429  ->
    match uu____3429 with | (e,uu____3433) -> p_indexingTerm e

and p_indexingTerm_aux :
  (FStar_Parser_AST.term -> FStar_Pprint.document) ->
    FStar_Parser_AST.term -> FStar_Pprint.document
  =
  fun exit1  ->
    fun e  ->
      let uu____3438 =
        let uu____3439 = unparen e  in uu____3439.FStar_Parser_AST.tm  in
      match uu____3438 with
      | FStar_Parser_AST.Op (".()",e1::e2::[]) ->
          let uu____3443 =
            let uu____3444 = p_indexingTerm_aux p_atomicTermNotQUident e1  in
            let uu____3445 =
              let uu____3446 =
                let uu____3447 = p_term e2  in
                soft_parens_with_nesting uu____3447  in
              FStar_Pprint.op_Hat_Hat FStar_Pprint.dot uu____3446  in
            FStar_Pprint.op_Hat_Hat uu____3444 uu____3445  in
          FStar_Pprint.group uu____3443
      | FStar_Parser_AST.Op (".[]",e1::e2::[]) ->
          let uu____3451 =
            let uu____3452 = p_indexingTerm_aux p_atomicTermNotQUident e1  in
            let uu____3453 =
              let uu____3454 =
                let uu____3455 = p_term e2  in
                soft_brackets_with_nesting uu____3455  in
              FStar_Pprint.op_Hat_Hat FStar_Pprint.dot uu____3454  in
            FStar_Pprint.op_Hat_Hat uu____3452 uu____3453  in
          FStar_Pprint.group uu____3451
      | uu____3456 -> exit1 e

and p_indexingTerm : FStar_Parser_AST.term -> FStar_Pprint.document =
  fun e  -> p_indexingTerm_aux p_atomicTerm e

and p_atomicTerm : FStar_Parser_AST.term -> FStar_Pprint.document =
  fun e  ->
    let uu____3459 =
      let uu____3460 = unparen e  in uu____3460.FStar_Parser_AST.tm  in
    match uu____3459 with
    | FStar_Parser_AST.LetOpen (lid,e1) ->
        let uu____3463 = p_quident lid  in
        let uu____3464 =
          let uu____3465 =
            let uu____3466 = p_term e1  in
            soft_parens_with_nesting uu____3466  in
          FStar_Pprint.op_Hat_Hat FStar_Pprint.dot uu____3465  in
        FStar_Pprint.op_Hat_Hat uu____3463 uu____3464
    | FStar_Parser_AST.Name lid -> p_quident lid
    | FStar_Parser_AST.Op (op,e1::[]) when is_general_prefix_op op ->
        let uu____3471 = str op  in
        let uu____3472 = p_atomicTerm e1  in
        FStar_Pprint.op_Hat_Hat uu____3471 uu____3472
    | uu____3473 -> p_atomicTermNotQUident e

and p_atomicTermNotQUident : FStar_Parser_AST.term -> FStar_Pprint.document =
  fun e  ->
    let uu____3475 =
      let uu____3476 = unparen e  in uu____3476.FStar_Parser_AST.tm  in
    match uu____3475 with
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
        let uu____3485 = str op  in
        let uu____3486 = p_atomicTermNotQUident e1  in
        FStar_Pprint.op_Hat_Hat uu____3485 uu____3486
    | FStar_Parser_AST.Op (op,[]) ->
        let uu____3489 =
          let uu____3490 =
            let uu____3491 = str op  in
            let uu____3492 =
              FStar_Pprint.op_Hat_Hat FStar_Pprint.space FStar_Pprint.rparen
               in
            FStar_Pprint.op_Hat_Hat uu____3491 uu____3492  in
          FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____3490  in
        FStar_Pprint.op_Hat_Hat FStar_Pprint.lparen uu____3489
    | FStar_Parser_AST.Construct (lid,args) when is_dtuple_constructor lid ->
        let uu____3501 =
          FStar_Pprint.op_Hat_Hat FStar_Pprint.lparen FStar_Pprint.bar  in
        let uu____3502 =
          let uu____3503 = FStar_Pprint.op_Hat_Hat FStar_Pprint.comma break1
             in
          let uu____3504 = FStar_List.map Prims.fst args  in
          FStar_Pprint.separate_map uu____3503 p_tmEq uu____3504  in
        let uu____3508 =
          FStar_Pprint.op_Hat_Hat FStar_Pprint.bar FStar_Pprint.rparen  in
        FStar_Pprint.surround (Prims.parse_int "2") (Prims.parse_int "1")
          uu____3501 uu____3502 uu____3508
    | FStar_Parser_AST.Project (e1,lid) ->
        let uu____3511 =
          let uu____3512 = p_atomicTermNotQUident e1  in
          let uu____3513 =
            let uu____3514 = p_qlident lid  in
            FStar_Pprint.op_Hat_Hat FStar_Pprint.dot uu____3514  in
          FStar_Pprint.prefix (Prims.parse_int "2") (Prims.parse_int "0")
            uu____3512 uu____3513
           in
        FStar_Pprint.group uu____3511
    | uu____3515 -> p_projectionLHS e

and p_projectionLHS : FStar_Parser_AST.term -> FStar_Pprint.document =
  fun e  ->
    let uu____3517 =
      let uu____3518 = unparen e  in uu____3518.FStar_Parser_AST.tm  in
    match uu____3517 with
    | FStar_Parser_AST.Var lid -> p_qlident lid
    | FStar_Parser_AST.Projector (constr_lid,field_lid) ->
        let uu____3522 = p_quident constr_lid  in
        let uu____3523 =
          let uu____3524 =
            let uu____3525 = p_lident field_lid  in
            FStar_Pprint.op_Hat_Hat FStar_Pprint.dot uu____3525  in
          FStar_Pprint.op_Hat_Hat FStar_Pprint.qmark uu____3524  in
        FStar_Pprint.op_Hat_Hat uu____3522 uu____3523
    | FStar_Parser_AST.Discrim constr_lid ->
        let uu____3527 = p_quident constr_lid  in
        FStar_Pprint.op_Hat_Hat uu____3527 FStar_Pprint.qmark
    | FStar_Parser_AST.Paren e1 ->
        let uu____3529 = p_term e1  in soft_parens_with_nesting uu____3529
    | uu____3530 when is_array e ->
        let es = extract_from_list e  in
        let uu____3533 =
          FStar_Pprint.op_Hat_Hat FStar_Pprint.lbracket FStar_Pprint.bar  in
        let uu____3534 =
          let uu____3535 = FStar_Pprint.op_Hat_Hat FStar_Pprint.semi break1
             in
          separate_map_or_flow uu____3535 p_noSeqTerm es  in
        let uu____3536 =
          FStar_Pprint.op_Hat_Hat FStar_Pprint.bar FStar_Pprint.rbracket  in
        FStar_Pprint.surround (Prims.parse_int "2") (Prims.parse_int "0")
          uu____3533 uu____3534 uu____3536
    | uu____3537 when is_list e ->
        let uu____3538 =
          let uu____3539 = FStar_Pprint.op_Hat_Hat FStar_Pprint.semi break1
             in
          let uu____3540 = extract_from_list e  in
          separate_map_or_flow uu____3539 p_noSeqTerm uu____3540  in
        FStar_Pprint.surround (Prims.parse_int "2") (Prims.parse_int "0")
          FStar_Pprint.lbracket uu____3538 FStar_Pprint.rbracket
    | uu____3542 when is_lex_list e ->
        let uu____3543 =
          FStar_Pprint.op_Hat_Hat FStar_Pprint.percent FStar_Pprint.lbracket
           in
        let uu____3544 =
          let uu____3545 = FStar_Pprint.op_Hat_Hat FStar_Pprint.semi break1
             in
          let uu____3546 = extract_from_list e  in
          separate_map_or_flow uu____3545 p_noSeqTerm uu____3546  in
        FStar_Pprint.surround (Prims.parse_int "2") (Prims.parse_int "1")
          uu____3543 uu____3544 FStar_Pprint.rbracket
    | uu____3548 when is_ref_set e ->
        let es = extract_from_ref_set e  in
        let uu____3551 =
          FStar_Pprint.op_Hat_Hat FStar_Pprint.bang FStar_Pprint.lbrace  in
        let uu____3552 =
          let uu____3553 = FStar_Pprint.op_Hat_Hat FStar_Pprint.comma break1
             in
          separate_map_or_flow uu____3553 p_appTerm es  in
        FStar_Pprint.surround (Prims.parse_int "2") (Prims.parse_int "0")
          uu____3551 uu____3552 FStar_Pprint.rbrace
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
        -> let uu____3582 = p_term e  in soft_parens_with_nesting uu____3582
    | FStar_Parser_AST.Labeled uu____3583 -> failwith "Not valid in universe"

and p_constant : FStar_Const.sconst -> FStar_Pprint.document =
  fun uu___142_3587  ->
    match uu___142_3587 with
    | FStar_Const.Const_effect  -> str "Effect"
    | FStar_Const.Const_unit  -> str "()"
    | FStar_Const.Const_bool b -> FStar_Pprint.doc_of_bool b
    | FStar_Const.Const_float x -> str (FStar_Util.string_of_float x)
    | FStar_Const.Const_char x ->
        let uu____3591 = FStar_Pprint.doc_of_char x  in
        FStar_Pprint.squotes uu____3591
    | FStar_Const.Const_string (bytes,uu____3593) ->
        let uu____3596 = str (FStar_Util.string_of_bytes bytes)  in
        FStar_Pprint.dquotes uu____3596
    | FStar_Const.Const_bytearray (bytes,uu____3598) ->
        let uu____3601 =
          let uu____3602 = str (FStar_Util.string_of_bytes bytes)  in
          FStar_Pprint.dquotes uu____3602  in
        let uu____3603 = str "B"  in
        FStar_Pprint.op_Hat_Hat uu____3601 uu____3603
    | FStar_Const.Const_int (repr,sign_width_opt) ->
        let signedness uu___140_3615 =
          match uu___140_3615 with
          | FStar_Const.Unsigned  -> str "u"
          | FStar_Const.Signed  -> FStar_Pprint.empty  in
        let width uu___141_3619 =
          match uu___141_3619 with
          | FStar_Const.Int8  -> str "y"
          | FStar_Const.Int16  -> str "s"
          | FStar_Const.Int32  -> str "l"
          | FStar_Const.Int64  -> str "L"  in
        let ending =
          default_or_map FStar_Pprint.empty
            (fun uu____3623  ->
               match uu____3623 with
               | (s,w) ->
                   let uu____3628 = signedness s  in
                   let uu____3629 = width w  in
                   FStar_Pprint.op_Hat_Hat uu____3628 uu____3629)
            sign_width_opt
           in
        let uu____3630 = str repr  in
        FStar_Pprint.op_Hat_Hat uu____3630 ending
    | FStar_Const.Const_range r ->
        let uu____3632 = FStar_Range.string_of_range r  in str uu____3632
    | FStar_Const.Const_reify  -> str "reify"
    | FStar_Const.Const_reflect lid ->
        let uu____3634 = p_quident lid  in
        let uu____3635 =
          let uu____3636 =
            let uu____3637 = str "reflect"  in
            FStar_Pprint.op_Hat_Hat FStar_Pprint.dot uu____3637  in
          FStar_Pprint.op_Hat_Hat FStar_Pprint.qmark uu____3636  in
        FStar_Pprint.op_Hat_Hat uu____3634 uu____3635

and p_universe : FStar_Parser_AST.term -> FStar_Pprint.document =
  fun u  ->
    let uu____3639 = str "u#"  in
    let uu____3640 = p_atomicUniverse u  in
    FStar_Pprint.op_Hat_Hat uu____3639 uu____3640

and p_universeFrom : FStar_Parser_AST.term -> FStar_Pprint.document =
  fun u  ->
    let uu____3642 =
      let uu____3643 = unparen u  in uu____3643.FStar_Parser_AST.tm  in
    match uu____3642 with
    | FStar_Parser_AST.Op ("+",u1::u2::[]) ->
        let uu____3647 =
          let uu____3648 = p_universeFrom u1  in
          let uu____3649 =
            let uu____3650 = p_universeFrom u2  in
            FStar_Pprint.op_Hat_Slash_Hat FStar_Pprint.plus uu____3650  in
          FStar_Pprint.op_Hat_Slash_Hat uu____3648 uu____3649  in
        FStar_Pprint.group uu____3647
    | FStar_Parser_AST.App uu____3651 ->
        let uu____3655 = head_and_args u  in
        (match uu____3655 with
         | (head1,args) ->
             let uu____3669 =
               let uu____3670 = unparen head1  in
               uu____3670.FStar_Parser_AST.tm  in
             (match uu____3669 with
              | FStar_Parser_AST.Var maybe_max_lid when
                  FStar_Ident.lid_equals maybe_max_lid
                    FStar_Syntax_Const.max_lid
                  ->
                  let uu____3672 =
                    let uu____3673 = p_qlident FStar_Syntax_Const.max_lid  in
                    let uu____3674 =
                      FStar_Pprint.separate_map FStar_Pprint.space
                        (fun uu____3677  ->
                           match uu____3677 with
                           | (u1,uu____3681) -> p_atomicUniverse u1) args
                       in
                    op_Hat_Slash_Plus_Hat uu____3673 uu____3674  in
                  FStar_Pprint.group uu____3672
              | uu____3682 ->
                  let uu____3683 =
                    let uu____3684 = FStar_Parser_AST.term_to_string u  in
                    FStar_Util.format1 "Invalid term in universe context %s"
                      uu____3684
                     in
                  failwith uu____3683))
    | uu____3685 -> p_atomicUniverse u

and p_atomicUniverse : FStar_Parser_AST.term -> FStar_Pprint.document =
  fun u  ->
    let uu____3687 =
      let uu____3688 = unparen u  in uu____3688.FStar_Parser_AST.tm  in
    match uu____3687 with
    | FStar_Parser_AST.Wild  -> FStar_Pprint.underscore
    | FStar_Parser_AST.Const (FStar_Const.Const_int (r,sw)) ->
        p_constant (FStar_Const.Const_int (r, sw))
    | FStar_Parser_AST.Uvar uu____3700 -> p_univar u
    | FStar_Parser_AST.Paren u1 ->
        let uu____3702 = p_universeFrom u1  in
        soft_parens_with_nesting uu____3702
    | FStar_Parser_AST.Op ("+",_::_::[])|FStar_Parser_AST.App _ ->
        let uu____3707 = p_universeFrom u  in
        soft_parens_with_nesting uu____3707
    | uu____3708 ->
        let uu____3709 =
          let uu____3710 = FStar_Parser_AST.term_to_string u  in
          FStar_Util.format1 "Invalid term in universe context %s" uu____3710
           in
        failwith uu____3709

and p_univar : FStar_Parser_AST.term -> FStar_Pprint.document =
  fun u  ->
    let uu____3712 =
      let uu____3713 = unparen u  in uu____3713.FStar_Parser_AST.tm  in
    match uu____3712 with
    | FStar_Parser_AST.Uvar id -> str (FStar_Ident.text_of_id id)
    | uu____3715 ->
        let uu____3716 =
          let uu____3717 = FStar_Parser_AST.term_to_string u  in
          FStar_Util.format1 "Not a universe variable %s" uu____3717  in
        failwith uu____3716

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
           let uu____3739 =
             FStar_All.pipe_right decls (FStar_List.map decl_to_document)  in
           FStar_All.pipe_right uu____3739
             (FStar_Pprint.separate FStar_Pprint.hardline)
        in
     FStar_ST.write should_print_fs_typ_app false; res)
  
let comments_to_document :
  (Prims.string * FStar_Range.range) Prims.list -> FStar_Pprint.document =
  fun comments  ->
    FStar_Pprint.separate_map FStar_Pprint.hardline
      (fun uu____3758  ->
         match uu____3758 with | (comment,range) -> str comment) comments
  
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
           let uu____3805 =
             match ds with
             | {
                 FStar_Parser_AST.d = FStar_Parser_AST.Pragma
                   (FStar_Parser_AST.LightOff );
                 FStar_Parser_AST.drange = uu____3812;
                 FStar_Parser_AST.doc = uu____3813;
                 FStar_Parser_AST.quals = uu____3814;
                 FStar_Parser_AST.attrs = uu____3815;_}::uu____3816 ->
                 let d0 = FStar_List.hd ds  in
                 let uu____3820 =
                   let uu____3822 =
                     let uu____3824 = FStar_List.tl ds  in d :: uu____3824
                      in
                   d0 :: uu____3822  in
                 (uu____3820, (d0.FStar_Parser_AST.drange))
             | uu____3827 -> ((d :: ds), (d.FStar_Parser_AST.drange))  in
           (match uu____3805 with
            | (decls1,first_range) ->
                let extract_decl_range d1 = d1.FStar_Parser_AST.drange  in
                (FStar_ST.write comment_stack comments;
                 (let initial_comment =
                    let uu____3850 = FStar_Range.start_of_range first_range
                       in
                    place_comments_until_pos (Prims.parse_int "0")
                      (Prims.parse_int "1") uu____3850 FStar_Pprint.empty
                     in
                  let doc1 =
                    separate_map_with_comments FStar_Pprint.empty
                      FStar_Pprint.empty decl_to_document decls1
                      extract_decl_range
                     in
                  let comments1 = FStar_ST.read comment_stack  in
                  FStar_ST.write comment_stack [];
                  FStar_ST.write should_print_fs_typ_app false;
                  (let uu____3872 =
                     FStar_Pprint.op_Hat_Hat initial_comment doc1  in
                   (uu____3872, comments1))))))
  