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
  fun uu___126_577  ->
    match uu___126_577 with
    | FStar_Util.Inl c -> Prims.strcat (FStar_Util.string_of_char c) ".*"
    | FStar_Util.Inr s -> s
  
let matches_token :
  Prims.string ->
    (FStar_Char.char,Prims.string) FStar_Util.either -> Prims.bool
  =
  fun s  ->
    fun uu___127_589  ->
      match uu___127_589 with
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
  let levels_from_associativity l uu___128_947 =
    match uu___128_947 with
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
  
let handleable_op op args =
  match FStar_List.length args with
  | _0_28 when _0_28 = (Prims.parse_int "0") -> true
  | _0_29 when _0_29 = (Prims.parse_int "1") ->
      (is_general_prefix_op op) || (FStar_List.mem op ["-"; "~"])
  | _0_30 when _0_30 = (Prims.parse_int "2") ->
      ((is_operatorInfix0ad12 op) || (is_operatorInfix34 op)) ||
        (FStar_List.mem op
           ["<==>"; "==>"; "\\/"; "/\\"; "="; "|>"; ":="; ".()"; ".[]"])
  | _0_31 when _0_31 = (Prims.parse_int "3") ->
      FStar_List.mem op [".()<-"; ".[]<-"]
  | uu____1337 -> false 
let comment_stack :
  (Prims.string * FStar_Range.range) Prims.list FStar_ST.ref =
  FStar_Util.mk_ref [] 
let with_comment printer tm tmrange =
  let rec comments_before_pos acc print_pos lookahead_pos =
    let uu____1383 = FStar_ST.read comment_stack  in
    match uu____1383 with
    | [] -> (acc, false)
    | (comment,crange)::cs ->
        let uu____1404 = FStar_Range.range_before_pos crange print_pos  in
        if uu____1404
        then
          (FStar_ST.write comment_stack cs;
           (let uu____1413 =
              let uu____1414 =
                let uu____1415 = str comment  in
                FStar_Pprint.op_Hat_Hat uu____1415 FStar_Pprint.hardline  in
              FStar_Pprint.op_Hat_Hat acc uu____1414  in
            comments_before_pos uu____1413 print_pos lookahead_pos))
        else
          (let uu____1417 = FStar_Range.range_before_pos crange lookahead_pos
              in
           (acc, uu____1417))
     in
  let uu____1418 =
    let uu____1421 =
      let uu____1422 = FStar_Range.start_of_range tmrange  in
      FStar_Range.end_of_line uu____1422  in
    let uu____1423 = FStar_Range.end_of_range tmrange  in
    comments_before_pos FStar_Pprint.empty uu____1421 uu____1423  in
  match uu____1418 with
  | (comments,has_lookahead) ->
      let printed_e = printer tm  in
      let comments1 =
        if has_lookahead
        then
          let pos = FStar_Range.end_of_range tmrange  in
          let uu____1429 = comments_before_pos comments pos pos  in
          Prims.fst uu____1429
        else comments  in
      let uu____1433 = FStar_Pprint.op_Hat_Hat comments1 printed_e  in
      FStar_Pprint.group uu____1433
  
let rec place_comments_until_pos :
  Prims.int ->
    Prims.int ->
      FStar_Range.pos -> FStar_Pprint.document -> FStar_Pprint.document
  =
  fun k  ->
    fun lbegin  ->
      fun pos_end  ->
        fun doc1  ->
          let uu____1446 = FStar_ST.read comment_stack  in
          match uu____1446 with
          | (comment,crange)::cs when
              FStar_Range.range_before_pos crange pos_end ->
              (FStar_ST.write comment_stack cs;
               (let lnum =
                  let uu____1470 =
                    let uu____1471 =
                      let uu____1472 = FStar_Range.start_of_range crange  in
                      FStar_Range.line_of_pos uu____1472  in
                    uu____1471 - lbegin  in
                  max k uu____1470  in
                let doc2 =
                  let uu____1474 =
                    let uu____1475 =
                      FStar_Pprint.repeat lnum FStar_Pprint.hardline  in
                    let uu____1476 = str comment  in
                    FStar_Pprint.op_Hat_Hat uu____1475 uu____1476  in
                  FStar_Pprint.op_Hat_Hat doc1 uu____1474  in
                let uu____1477 =
                  let uu____1478 = FStar_Range.end_of_range crange  in
                  FStar_Range.line_of_pos uu____1478  in
                place_comments_until_pos (Prims.parse_int "1") uu____1477
                  pos_end doc2))
          | uu____1479 ->
              let lnum =
                let uu____1484 =
                  let uu____1485 = FStar_Range.line_of_pos pos_end  in
                  uu____1485 - lbegin  in
                max (Prims.parse_int "1") uu____1484  in
              let uu____1486 = FStar_Pprint.repeat lnum FStar_Pprint.hardline
                 in
              FStar_Pprint.op_Hat_Hat doc1 uu____1486
  
let separate_map_with_comments prefix1 sep f xs extract_range =
  let fold_fun uu____1535 x =
    match uu____1535 with
    | (last_line,doc1) ->
        let r = extract_range x  in
        let doc2 =
          let uu____1545 = FStar_Range.start_of_range r  in
          place_comments_until_pos (Prims.parse_int "1") last_line uu____1545
            doc1
           in
        let uu____1546 =
          let uu____1547 = FStar_Range.end_of_range r  in
          FStar_Range.line_of_pos uu____1547  in
        let uu____1548 =
          let uu____1549 =
            let uu____1550 = f x  in FStar_Pprint.op_Hat_Hat sep uu____1550
             in
          FStar_Pprint.op_Hat_Hat doc2 uu____1549  in
        (uu____1546, uu____1548)
     in
  let uu____1551 =
    let uu____1555 = FStar_List.hd xs  in
    let uu____1556 = FStar_List.tl xs  in (uu____1555, uu____1556)  in
  match uu____1551 with
  | (x,xs1) ->
      let init1 =
        let uu____1566 =
          let uu____1567 =
            let uu____1568 = extract_range x  in
            FStar_Range.end_of_range uu____1568  in
          FStar_Range.line_of_pos uu____1567  in
        let uu____1569 =
          let uu____1570 = f x  in FStar_Pprint.op_Hat_Hat prefix1 uu____1570
           in
        (uu____1566, uu____1569)  in
      let uu____1571 = FStar_List.fold_left fold_fun init1 xs1  in
      Prims.snd uu____1571
  
let rec p_decl : FStar_Parser_AST.decl -> FStar_Pprint.document =
  fun d  ->
    let uu____1817 =
      let uu____1818 = FStar_Pprint.optional p_fsdoc d.FStar_Parser_AST.doc
         in
      let uu____1819 =
        let uu____1820 = p_attributes d.FStar_Parser_AST.attrs  in
        let uu____1821 =
          let uu____1822 = p_qualifiers d.FStar_Parser_AST.quals  in
          let uu____1823 =
            let uu____1824 = p_rawDecl d  in
            FStar_Pprint.op_Hat_Hat
              (if d.FStar_Parser_AST.quals = []
               then FStar_Pprint.empty
               else break1) uu____1824
             in
          FStar_Pprint.op_Hat_Hat uu____1822 uu____1823  in
        FStar_Pprint.op_Hat_Hat uu____1820 uu____1821  in
      FStar_Pprint.op_Hat_Hat uu____1818 uu____1819  in
    FStar_Pprint.group uu____1817

and p_attributes : FStar_Parser_AST.attributes_ -> FStar_Pprint.document =
  fun attrs  ->
    let uu____1827 =
      let uu____1828 = str "@"  in
      FStar_Pprint.op_Hat_Hat FStar_Pprint.lbracket uu____1828  in
    let uu____1829 =
      FStar_Pprint.op_Hat_Hat FStar_Pprint.rbracket FStar_Pprint.hardline  in
    soft_surround_separate_map (Prims.parse_int "0") (Prims.parse_int "2")
      FStar_Pprint.empty uu____1827 FStar_Pprint.space uu____1829
      p_atomicTerm attrs

and p_fsdoc : FStar_Parser_AST.fsdoc -> FStar_Pprint.document =
  fun uu____1830  ->
    match uu____1830 with
    | (doc1,kwd_args) ->
        let kwd_args_doc =
          match kwd_args with
          | [] -> FStar_Pprint.empty
          | kwd_args1 ->
              let process_kwd_arg uu____1851 =
                match uu____1851 with
                | (kwd1,arg) ->
                    let uu____1856 = str "@"  in
                    let uu____1857 =
                      let uu____1858 = str kwd1  in
                      let uu____1859 =
                        let uu____1860 = str arg  in
                        FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____1860
                         in
                      FStar_Pprint.op_Hat_Hat uu____1858 uu____1859  in
                    FStar_Pprint.op_Hat_Hat uu____1856 uu____1857
                 in
              let uu____1861 =
                let uu____1862 =
                  FStar_Pprint.separate_map FStar_Pprint.hardline
                    process_kwd_arg kwd_args1
                   in
                FStar_Pprint.op_Hat_Hat uu____1862 FStar_Pprint.hardline  in
              FStar_Pprint.op_Hat_Hat FStar_Pprint.hardline uu____1861
           in
        let uu____1865 =
          let uu____1866 =
            let uu____1867 =
              let uu____1868 =
                let uu____1869 = str doc1  in
                let uu____1870 =
                  let uu____1871 =
                    let uu____1872 =
                      FStar_Pprint.op_Hat_Hat FStar_Pprint.rparen
                        FStar_Pprint.hardline
                       in
                    FStar_Pprint.op_Hat_Hat FStar_Pprint.star uu____1872  in
                  FStar_Pprint.op_Hat_Hat kwd_args_doc uu____1871  in
                FStar_Pprint.op_Hat_Hat uu____1869 uu____1870  in
              FStar_Pprint.op_Hat_Hat FStar_Pprint.star uu____1868  in
            FStar_Pprint.op_Hat_Hat FStar_Pprint.star uu____1867  in
          FStar_Pprint.op_Hat_Hat FStar_Pprint.lparen uu____1866  in
        FStar_Pprint.op_Hat_Hat FStar_Pprint.hardline uu____1865

and p_rawDecl : FStar_Parser_AST.decl -> FStar_Pprint.document =
  fun d  ->
    match d.FStar_Parser_AST.d with
    | FStar_Parser_AST.Open uid ->
        let uu____1875 =
          let uu____1876 = str "open"  in
          let uu____1877 = p_quident uid  in
          FStar_Pprint.op_Hat_Slash_Hat uu____1876 uu____1877  in
        FStar_Pprint.group uu____1875
    | FStar_Parser_AST.Include uid ->
        let uu____1879 =
          let uu____1880 = str "include"  in
          let uu____1881 = p_quident uid  in
          FStar_Pprint.op_Hat_Slash_Hat uu____1880 uu____1881  in
        FStar_Pprint.group uu____1879
    | FStar_Parser_AST.ModuleAbbrev (uid1,uid2) ->
        let uu____1884 =
          let uu____1885 = str "module"  in
          let uu____1886 =
            let uu____1887 =
              let uu____1888 = p_uident uid1  in
              let uu____1889 =
                FStar_Pprint.op_Hat_Hat FStar_Pprint.space
                  FStar_Pprint.equals
                 in
              FStar_Pprint.op_Hat_Hat uu____1888 uu____1889  in
            FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____1887  in
          FStar_Pprint.op_Hat_Hat uu____1885 uu____1886  in
        let uu____1890 = p_quident uid2  in
        op_Hat_Slash_Plus_Hat uu____1884 uu____1890
    | FStar_Parser_AST.TopLevelModule uid ->
        let uu____1892 =
          let uu____1893 = str "module"  in
          let uu____1894 =
            let uu____1895 = p_quident uid  in
            FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____1895  in
          FStar_Pprint.op_Hat_Hat uu____1893 uu____1894  in
        FStar_Pprint.group uu____1892
    | FStar_Parser_AST.Tycon
        (true ,(FStar_Parser_AST.TyconAbbrev (uid,tpars,None ,t),None )::[])
        ->
        let effect_prefix_doc =
          let uu____1914 = str "effect"  in
          let uu____1915 =
            let uu____1916 = p_uident uid  in
            FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____1916  in
          FStar_Pprint.op_Hat_Hat uu____1914 uu____1915  in
        let uu____1917 =
          let uu____1918 = p_typars tpars  in
          FStar_Pprint.surround (Prims.parse_int "2") (Prims.parse_int "1")
            effect_prefix_doc uu____1918 FStar_Pprint.equals
           in
        let uu____1919 = p_typ t  in
        op_Hat_Slash_Plus_Hat uu____1917 uu____1919
    | FStar_Parser_AST.Tycon (false ,tcdefs) ->
        let uu____1929 = str "type"  in
        let uu____1930 = str "and"  in
        precede_break_separate_map uu____1929 uu____1930 p_fsdocTypeDeclPairs
          tcdefs
    | FStar_Parser_AST.TopLevelLet (q,lbs) ->
        let let_doc =
          let uu____1943 = str "let"  in
          let uu____1944 =
            let uu____1945 = p_letqualifier q  in
            FStar_Pprint.op_Hat_Hat uu____1945 FStar_Pprint.space  in
          FStar_Pprint.op_Hat_Hat uu____1943 uu____1944  in
        let uu____1946 =
          let uu____1947 = str "and"  in
          FStar_Pprint.op_Hat_Hat uu____1947 FStar_Pprint.space  in
        separate_map_with_comments let_doc uu____1946 p_letbinding lbs
          (fun uu____1950  ->
             match uu____1950 with
             | (p,t) ->
                 FStar_Range.union_ranges p.FStar_Parser_AST.prange
                   t.FStar_Parser_AST.range)
    | FStar_Parser_AST.Val (lid,t) ->
        let uu____1957 =
          let uu____1958 = str "val"  in
          let uu____1959 =
            let uu____1960 =
              let uu____1961 = p_lident lid  in
              let uu____1962 =
                FStar_Pprint.op_Hat_Hat FStar_Pprint.space FStar_Pprint.colon
                 in
              FStar_Pprint.op_Hat_Hat uu____1961 uu____1962  in
            FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____1960  in
          FStar_Pprint.op_Hat_Hat uu____1958 uu____1959  in
        let uu____1963 = p_typ t  in
        op_Hat_Slash_Plus_Hat uu____1957 uu____1963
    | FStar_Parser_AST.Assume (id,t) ->
        let decl_keyword =
          let uu____1967 =
            let uu____1968 =
              FStar_Util.char_at id.FStar_Ident.idText (Prims.parse_int "0")
               in
            FStar_All.pipe_right uu____1968 FStar_Util.is_upper  in
          if uu____1967
          then FStar_Pprint.empty
          else
            (let uu____1970 = str "val"  in
             FStar_Pprint.op_Hat_Hat uu____1970 FStar_Pprint.space)
           in
        let uu____1971 =
          let uu____1972 =
            let uu____1973 = p_ident id  in
            let uu____1974 =
              FStar_Pprint.op_Hat_Hat FStar_Pprint.space FStar_Pprint.colon
               in
            FStar_Pprint.op_Hat_Hat uu____1973 uu____1974  in
          FStar_Pprint.op_Hat_Hat decl_keyword uu____1972  in
        let uu____1975 = p_typ t  in
        op_Hat_Slash_Plus_Hat uu____1971 uu____1975
    | FStar_Parser_AST.Exception (uid,t_opt) ->
        let uu____1980 = str "exception"  in
        let uu____1981 =
          let uu____1982 =
            let uu____1983 = p_uident uid  in
            let uu____1984 =
              FStar_Pprint.optional
                (fun t  ->
                   let uu____1986 = str "of"  in
                   let uu____1987 = p_typ t  in
                   op_Hat_Slash_Plus_Hat uu____1986 uu____1987) t_opt
               in
            FStar_Pprint.op_Hat_Hat uu____1983 uu____1984  in
          FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____1982  in
        FStar_Pprint.op_Hat_Hat uu____1980 uu____1981
    | FStar_Parser_AST.NewEffect ne ->
        let uu____1989 = str "new_effect"  in
        let uu____1990 =
          let uu____1991 = p_newEffect ne  in
          FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____1991  in
        FStar_Pprint.op_Hat_Hat uu____1989 uu____1990
    | FStar_Parser_AST.SubEffect se ->
        let uu____1993 = str "sub_effect"  in
        let uu____1994 =
          let uu____1995 = p_subEffect se  in
          FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____1995  in
        FStar_Pprint.op_Hat_Hat uu____1993 uu____1994
    | FStar_Parser_AST.Pragma p -> p_pragma p
    | FStar_Parser_AST.Fsdoc doc1 ->
        let uu____1998 = p_fsdoc doc1  in
        FStar_Pprint.op_Hat_Hat uu____1998 FStar_Pprint.hardline
    | FStar_Parser_AST.Main uu____1999 ->
        failwith "*Main declaration* : Is that really still in use ??"
    | FStar_Parser_AST.Tycon (true ,uu____2000) ->
        failwith
          "Effect abbreviation is expected to be defined by an abbreviation"

and p_pragma : FStar_Parser_AST.pragma -> FStar_Pprint.document =
  fun uu___129_2009  ->
    match uu___129_2009 with
    | FStar_Parser_AST.SetOptions s ->
        let uu____2011 = str "#set-options"  in
        let uu____2012 =
          let uu____2013 =
            let uu____2014 = str s  in FStar_Pprint.dquotes uu____2014  in
          FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____2013  in
        FStar_Pprint.op_Hat_Hat uu____2011 uu____2012
    | FStar_Parser_AST.ResetOptions s_opt ->
        let uu____2017 = str "#reset-options"  in
        let uu____2018 =
          FStar_Pprint.optional
            (fun s  ->
               let uu____2020 =
                 let uu____2021 = str s  in FStar_Pprint.dquotes uu____2021
                  in
               FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____2020) s_opt
           in
        FStar_Pprint.op_Hat_Hat uu____2017 uu____2018
    | FStar_Parser_AST.LightOff  ->
        (FStar_ST.write should_print_fs_typ_app true; str "#light \"off\"")

and p_typars : FStar_Parser_AST.binder Prims.list -> FStar_Pprint.document =
  fun bs  -> p_binders true bs

and p_fsdocTypeDeclPairs :
  (FStar_Parser_AST.tycon * FStar_Parser_AST.fsdoc Prims.option) ->
    FStar_Pprint.document
  =
  fun uu____2027  ->
    match uu____2027 with
    | (typedecl,fsdoc_opt) ->
        let uu____2035 = FStar_Pprint.optional p_fsdoc fsdoc_opt  in
        let uu____2036 = p_typeDecl typedecl  in
        FStar_Pprint.op_Hat_Hat uu____2035 uu____2036

and p_typeDecl : FStar_Parser_AST.tycon -> FStar_Pprint.document =
  fun uu___130_2037  ->
    match uu___130_2037 with
    | FStar_Parser_AST.TyconAbstract (lid,bs,typ_opt) ->
        let empty' uu____2048 = FStar_Pprint.empty  in
        p_typeDeclPrefix lid bs typ_opt empty'
    | FStar_Parser_AST.TyconAbbrev (lid,bs,typ_opt,t) ->
        let f uu____2060 =
          let uu____2061 = p_typ t  in prefix2 FStar_Pprint.equals uu____2061
           in
        p_typeDeclPrefix lid bs typ_opt f
    | FStar_Parser_AST.TyconRecord (lid,bs,typ_opt,record_field_decls) ->
        let p_recordFieldAndComments uu____2087 =
          match uu____2087 with
          | (lid1,t,doc_opt) ->
              let uu____2097 =
                FStar_Range.extend_to_end_of_line t.FStar_Parser_AST.range
                 in
              with_comment p_recordFieldDecl (lid1, t, doc_opt) uu____2097
           in
        let p_fields uu____2106 =
          let uu____2107 =
            let uu____2108 =
              let uu____2109 =
                let uu____2110 =
                  FStar_Pprint.op_Hat_Hat FStar_Pprint.semi break1  in
                FStar_Pprint.separate_map uu____2110 p_recordFieldAndComments
                  record_field_decls
                 in
              braces_with_nesting uu____2109  in
            FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____2108  in
          FStar_Pprint.op_Hat_Hat FStar_Pprint.equals uu____2107  in
        p_typeDeclPrefix lid bs typ_opt p_fields
    | FStar_Parser_AST.TyconVariant (lid,bs,typ_opt,ct_decls) ->
        let p_constructorBranchAndComments uu____2146 =
          match uu____2146 with
          | (uid,t_opt,doc_opt,use_of) ->
              let range =
                let uu____2162 =
                  let uu____2163 =
                    FStar_Util.map_opt t_opt
                      (fun t  -> t.FStar_Parser_AST.range)
                     in
                  FStar_Util.dflt uid.FStar_Ident.idRange uu____2163  in
                FStar_Range.extend_to_end_of_line uu____2162  in
              let p_constructorBranch decl =
                let uu____2182 =
                  let uu____2183 =
                    let uu____2184 = p_constructorDecl decl  in
                    FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____2184  in
                  FStar_Pprint.op_Hat_Hat FStar_Pprint.bar uu____2183  in
                FStar_Pprint.group uu____2182  in
              with_comment p_constructorBranch (uid, t_opt, doc_opt, use_of)
                range
           in
        let datacon_doc uu____2196 =
          let uu____2197 =
            FStar_Pprint.separate_map break1 p_constructorBranchAndComments
              ct_decls
             in
          FStar_Pprint.group uu____2197  in
        p_typeDeclPrefix lid bs typ_opt
          (fun uu____2204  ->
             let uu____2205 = datacon_doc ()  in
             prefix2 FStar_Pprint.equals uu____2205)

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
            let uu____2216 = p_ident lid  in
            let uu____2217 =
              let uu____2218 = cont ()  in
              FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____2218  in
            FStar_Pprint.op_Hat_Hat uu____2216 uu____2217
          else
            (let binders_doc =
               let uu____2221 = p_typars bs  in
               let uu____2222 =
                 FStar_Pprint.optional
                   (fun t  ->
                      let uu____2224 =
                        let uu____2225 =
                          let uu____2226 = p_typ t  in
                          FStar_Pprint.op_Hat_Hat FStar_Pprint.space
                            uu____2226
                           in
                        FStar_Pprint.op_Hat_Hat FStar_Pprint.colon uu____2225
                         in
                      FStar_Pprint.op_Hat_Hat break1 uu____2224) typ_opt
                  in
               FStar_Pprint.op_Hat_Hat uu____2221 uu____2222  in
             let uu____2227 = p_ident lid  in
             let uu____2228 = cont ()  in
             FStar_Pprint.surround (Prims.parse_int "2")
               (Prims.parse_int "1") uu____2227 binders_doc uu____2228)

and p_recordFieldDecl :
  (FStar_Ident.ident * FStar_Parser_AST.term * FStar_Parser_AST.fsdoc
    Prims.option) -> FStar_Pprint.document
  =
  fun uu____2229  ->
    match uu____2229 with
    | (lid,t,doc_opt) ->
        let uu____2239 =
          let uu____2240 = FStar_Pprint.optional p_fsdoc doc_opt  in
          let uu____2241 =
            let uu____2242 = p_lident lid  in
            let uu____2243 =
              let uu____2244 = p_typ t  in
              FStar_Pprint.op_Hat_Hat FStar_Pprint.colon uu____2244  in
            FStar_Pprint.op_Hat_Hat uu____2242 uu____2243  in
          FStar_Pprint.op_Hat_Hat uu____2240 uu____2241  in
        FStar_Pprint.group uu____2239

and p_constructorDecl :
  (FStar_Ident.ident * FStar_Parser_AST.term Prims.option *
    FStar_Parser_AST.fsdoc Prims.option * Prims.bool) ->
    FStar_Pprint.document
  =
  fun uu____2245  ->
    match uu____2245 with
    | (uid,t_opt,doc_opt,use_of) ->
        let sep = if use_of then str "of" else FStar_Pprint.colon  in
        let uid_doc = p_uident uid  in
        let uu____2263 = FStar_Pprint.optional p_fsdoc doc_opt  in
        let uu____2264 =
          let uu____2265 = FStar_Pprint.break_ (Prims.parse_int "0")  in
          let uu____2266 =
            default_or_map uid_doc
              (fun t  ->
                 let uu____2268 =
                   let uu____2269 =
                     FStar_Pprint.op_Hat_Hat FStar_Pprint.space sep  in
                   FStar_Pprint.op_Hat_Hat uid_doc uu____2269  in
                 let uu____2270 = p_typ t  in
                 op_Hat_Slash_Plus_Hat uu____2268 uu____2270) t_opt
             in
          FStar_Pprint.op_Hat_Hat uu____2265 uu____2266  in
        FStar_Pprint.op_Hat_Hat uu____2263 uu____2264

and p_letbinding :
  (FStar_Parser_AST.pattern * FStar_Parser_AST.term) -> FStar_Pprint.document
  =
  fun uu____2271  ->
    match uu____2271 with
    | (pat,e) ->
        let pat_doc =
          let uu____2277 =
            match pat.FStar_Parser_AST.pat with
            | FStar_Parser_AST.PatAscribed (pat1,t) ->
                let uu____2284 =
                  let uu____2285 =
                    let uu____2286 =
                      let uu____2287 =
                        let uu____2288 = p_tmArrow p_tmNoEq t  in
                        FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____2288
                         in
                      FStar_Pprint.op_Hat_Hat FStar_Pprint.colon uu____2287
                       in
                    FStar_Pprint.group uu____2286  in
                  FStar_Pprint.op_Hat_Hat break1 uu____2285  in
                (pat1, uu____2284)
            | uu____2289 -> (pat, FStar_Pprint.empty)  in
          match uu____2277 with
          | (pat1,ascr_doc) ->
              (match pat1.FStar_Parser_AST.pat with
               | FStar_Parser_AST.PatApp
                   ({
                      FStar_Parser_AST.pat = FStar_Parser_AST.PatVar
                        (x,uu____2293);
                      FStar_Parser_AST.prange = uu____2294;_},pats)
                   ->
                   let uu____2300 = p_lident x  in
                   let uu____2301 =
                     let uu____2302 =
                       FStar_Pprint.separate_map break1 p_atomicPattern pats
                        in
                     FStar_Pprint.op_Hat_Hat uu____2302 ascr_doc  in
                   FStar_Pprint.surround (Prims.parse_int "2")
                     (Prims.parse_int "1") uu____2300 uu____2301
                     FStar_Pprint.equals
               | uu____2303 ->
                   let uu____2304 =
                     let uu____2305 = p_tuplePattern pat1  in
                     let uu____2306 =
                       FStar_Pprint.op_Hat_Slash_Hat ascr_doc
                         FStar_Pprint.equals
                        in
                     FStar_Pprint.op_Hat_Hat uu____2305 uu____2306  in
                   FStar_Pprint.group uu____2304)
           in
        let uu____2307 = p_term e  in prefix2 pat_doc uu____2307

and p_newEffect : FStar_Parser_AST.effect_decl -> FStar_Pprint.document =
  fun uu___131_2308  ->
    match uu___131_2308 with
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
        let uu____2326 = p_uident uid  in
        let uu____2327 = p_binders true bs  in
        let uu____2328 =
          let uu____2329 = p_simpleTerm t  in
          prefix2 FStar_Pprint.equals uu____2329  in
        FStar_Pprint.surround (Prims.parse_int "2") (Prims.parse_int "1")
          uu____2326 uu____2327 uu____2328

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
              let uu____2344 = str "with"  in
              let uu____2345 =
                separate_break_map FStar_Pprint.semi p_effectDecl eff_decls
                 in
              prefix2 uu____2344 uu____2345  in
            FStar_Pprint.op_Hat_Slash_Hat uu____2337 uu____2343  in
          braces_with_nesting uu____2336

and p_effectDecl : FStar_Parser_AST.decl -> FStar_Pprint.document =
  fun d  ->
    match d.FStar_Parser_AST.d with
    | FStar_Parser_AST.Tycon
        (false ,(FStar_Parser_AST.TyconAbbrev (lid,[],None ,e),None )::[]) ->
        let uu____2362 =
          let uu____2363 = p_lident lid  in
          let uu____2364 =
            FStar_Pprint.op_Hat_Hat FStar_Pprint.space FStar_Pprint.equals
             in
          FStar_Pprint.op_Hat_Hat uu____2363 uu____2364  in
        let uu____2365 = p_simpleTerm e  in prefix2 uu____2362 uu____2365
    | uu____2366 ->
        let uu____2367 =
          let uu____2368 = FStar_Parser_AST.decl_to_string d  in
          FStar_Util.format1
            "Not a declaration of an effect member... or at least I hope so : %s"
            uu____2368
           in
        failwith uu____2367

and p_subEffect : FStar_Parser_AST.lift -> FStar_Pprint.document =
  fun lift  ->
    let lift_op_doc =
      let lifts =
        match lift.FStar_Parser_AST.lift_op with
        | FStar_Parser_AST.NonReifiableLift t -> [("lift_wp", t)]
        | FStar_Parser_AST.ReifiableLift (t1,t2) ->
            [("lif_wp", t1); ("lift", t2)]
        | FStar_Parser_AST.LiftForFree t -> [("lift", t)]  in
      let p_lift uu____2401 =
        match uu____2401 with
        | (kwd1,t) ->
            let uu____2406 =
              let uu____2407 = str kwd1  in
              let uu____2408 =
                FStar_Pprint.op_Hat_Hat FStar_Pprint.space
                  FStar_Pprint.equals
                 in
              FStar_Pprint.op_Hat_Hat uu____2407 uu____2408  in
            let uu____2409 = p_simpleTerm t  in prefix2 uu____2406 uu____2409
         in
      separate_break_map FStar_Pprint.semi p_lift lifts  in
    let uu____2412 =
      let uu____2413 =
        let uu____2414 = p_quident lift.FStar_Parser_AST.msource  in
        let uu____2415 =
          let uu____2416 = str "~>"  in
          FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____2416  in
        FStar_Pprint.op_Hat_Hat uu____2414 uu____2415  in
      let uu____2417 = p_quident lift.FStar_Parser_AST.mdest  in
      prefix2 uu____2413 uu____2417  in
    let uu____2418 =
      let uu____2419 = braces_with_nesting lift_op_doc  in
      FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____2419  in
    FStar_Pprint.op_Hat_Hat uu____2412 uu____2418

and p_qualifier : FStar_Parser_AST.qualifier -> FStar_Pprint.document =
  fun uu___132_2420  ->
    match uu___132_2420 with
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
    let uu____2422 = FStar_Pprint.separate_map break1 p_qualifier qs  in
    FStar_Pprint.group uu____2422

and p_letqualifier : FStar_Parser_AST.let_qualifier -> FStar_Pprint.document
  =
  fun uu___133_2423  ->
    match uu___133_2423 with
    | FStar_Parser_AST.Rec  ->
        let uu____2424 = str "rec"  in
        FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____2424
    | FStar_Parser_AST.Mutable  ->
        let uu____2425 = str "mutable"  in
        FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____2425
    | FStar_Parser_AST.NoLetQualifier  -> FStar_Pprint.empty

and p_aqual : FStar_Parser_AST.arg_qualifier -> FStar_Pprint.document =
  fun uu___134_2426  ->
    match uu___134_2426 with
    | FStar_Parser_AST.Implicit  -> str "#"
    | FStar_Parser_AST.Equality  -> str "$"

and p_disjunctivePattern : FStar_Parser_AST.pattern -> FStar_Pprint.document
  =
  fun p  ->
    match p.FStar_Parser_AST.pat with
    | FStar_Parser_AST.PatOr pats ->
        let uu____2430 =
          let uu____2431 =
            let uu____2432 =
              FStar_Pprint.op_Hat_Hat FStar_Pprint.bar FStar_Pprint.space  in
            FStar_Pprint.op_Hat_Hat break1 uu____2432  in
          FStar_Pprint.separate_map uu____2431 p_tuplePattern pats  in
        FStar_Pprint.group uu____2430
    | uu____2433 -> p_tuplePattern p

and p_tuplePattern : FStar_Parser_AST.pattern -> FStar_Pprint.document =
  fun p  ->
    match p.FStar_Parser_AST.pat with
    | FStar_Parser_AST.PatTuple (pats,false ) ->
        let uu____2438 =
          let uu____2439 = FStar_Pprint.op_Hat_Hat FStar_Pprint.comma break1
             in
          FStar_Pprint.separate_map uu____2439 p_constructorPattern pats  in
        FStar_Pprint.group uu____2438
    | uu____2440 -> p_constructorPattern p

and p_constructorPattern : FStar_Parser_AST.pattern -> FStar_Pprint.document
  =
  fun p  ->
    match p.FStar_Parser_AST.pat with
    | FStar_Parser_AST.PatApp
        ({ FStar_Parser_AST.pat = FStar_Parser_AST.PatName maybe_cons_lid;
           FStar_Parser_AST.prange = uu____2443;_},hd1::tl1::[])
        when
        FStar_Ident.lid_equals maybe_cons_lid FStar_Syntax_Const.cons_lid ->
        let uu____2447 =
          FStar_Pprint.op_Hat_Hat FStar_Pprint.colon FStar_Pprint.colon  in
        let uu____2448 = p_constructorPattern hd1  in
        let uu____2449 = p_constructorPattern tl1  in
        infix0 uu____2447 uu____2448 uu____2449
    | FStar_Parser_AST.PatApp
        ({ FStar_Parser_AST.pat = FStar_Parser_AST.PatName uid;
           FStar_Parser_AST.prange = uu____2451;_},pats)
        ->
        let uu____2455 = p_quident uid  in
        let uu____2456 =
          FStar_Pprint.separate_map break1 p_atomicPattern pats  in
        prefix2 uu____2455 uu____2456
    | uu____2457 -> p_atomicPattern p

and p_atomicPattern : FStar_Parser_AST.pattern -> FStar_Pprint.document =
  fun p  ->
    match p.FStar_Parser_AST.pat with
    | FStar_Parser_AST.PatAscribed (pat,t) ->
        let uu____2461 =
          let uu____2464 =
            let uu____2465 = unparen t  in uu____2465.FStar_Parser_AST.tm  in
          ((pat.FStar_Parser_AST.pat), uu____2464)  in
        (match uu____2461 with
         | (FStar_Parser_AST.PatVar (lid,aqual),FStar_Parser_AST.Refine
            ({ FStar_Parser_AST.b = FStar_Parser_AST.Annotated (lid',t1);
               FStar_Parser_AST.brange = uu____2470;
               FStar_Parser_AST.blevel = uu____2471;
               FStar_Parser_AST.aqual = uu____2472;_},phi))
             when lid.FStar_Ident.idText = lid'.FStar_Ident.idText ->
             let uu____2476 =
               let uu____2477 = p_ident lid  in
               p_refinement aqual uu____2477 t1 phi  in
             soft_parens_with_nesting uu____2476
         | (FStar_Parser_AST.PatWild ,FStar_Parser_AST.Refine
            ({ FStar_Parser_AST.b = FStar_Parser_AST.NoName t1;
               FStar_Parser_AST.brange = uu____2479;
               FStar_Parser_AST.blevel = uu____2480;
               FStar_Parser_AST.aqual = uu____2481;_},phi))
             ->
             let uu____2483 =
               p_refinement None FStar_Pprint.underscore t1 phi  in
             soft_parens_with_nesting uu____2483
         | uu____2484 ->
             let uu____2487 =
               let uu____2488 = p_tuplePattern pat  in
               let uu____2489 =
                 let uu____2490 = FStar_Pprint.break_ (Prims.parse_int "0")
                    in
                 let uu____2491 =
                   let uu____2492 = p_typ t  in
                   FStar_Pprint.op_Hat_Hat FStar_Pprint.colon uu____2492  in
                 FStar_Pprint.op_Hat_Hat uu____2490 uu____2491  in
               FStar_Pprint.op_Hat_Hat uu____2488 uu____2489  in
             soft_parens_with_nesting uu____2487)
    | FStar_Parser_AST.PatList pats ->
        let uu____2495 =
          separate_break_map FStar_Pprint.semi p_tuplePattern pats  in
        FStar_Pprint.surround (Prims.parse_int "2") (Prims.parse_int "0")
          FStar_Pprint.lbracket uu____2495 FStar_Pprint.rbracket
    | FStar_Parser_AST.PatRecord pats ->
        let p_recordFieldPat uu____2505 =
          match uu____2505 with
          | (lid,pat) ->
              let uu____2510 = p_qlident lid  in
              let uu____2511 = p_tuplePattern pat  in
              infix2 FStar_Pprint.equals uu____2510 uu____2511
           in
        let uu____2512 =
          separate_break_map FStar_Pprint.semi p_recordFieldPat pats  in
        soft_braces_with_nesting uu____2512
    | FStar_Parser_AST.PatTuple (pats,true ) ->
        let uu____2518 =
          FStar_Pprint.op_Hat_Hat FStar_Pprint.lparen FStar_Pprint.bar  in
        let uu____2519 =
          separate_break_map FStar_Pprint.comma p_constructorPattern pats  in
        let uu____2520 =
          FStar_Pprint.op_Hat_Hat FStar_Pprint.bar FStar_Pprint.rparen  in
        FStar_Pprint.surround (Prims.parse_int "2") (Prims.parse_int "1")
          uu____2518 uu____2519 uu____2520
    | FStar_Parser_AST.PatTvar (tv,arg_qualifier_opt) -> p_tvar tv
    | FStar_Parser_AST.PatOp op ->
        let uu____2527 =
          let uu____2528 =
            let uu____2529 = str op  in
            let uu____2530 =
              FStar_Pprint.op_Hat_Hat FStar_Pprint.space FStar_Pprint.rparen
               in
            FStar_Pprint.op_Hat_Hat uu____2529 uu____2530  in
          FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____2528  in
        FStar_Pprint.op_Hat_Hat FStar_Pprint.lparen uu____2527
    | FStar_Parser_AST.PatWild  -> FStar_Pprint.underscore
    | FStar_Parser_AST.PatConst c -> p_constant c
    | FStar_Parser_AST.PatVar (lid,aqual) ->
        let uu____2536 = FStar_Pprint.optional p_aqual aqual  in
        let uu____2537 = p_lident lid  in
        FStar_Pprint.op_Hat_Hat uu____2536 uu____2537
    | FStar_Parser_AST.PatName uid -> p_quident uid
    | FStar_Parser_AST.PatOr uu____2539 -> failwith "Inner or pattern !"
    | FStar_Parser_AST.PatApp
      ({ FStar_Parser_AST.pat = FStar_Parser_AST.PatName _;
         FStar_Parser_AST.prange = _;_},_)|FStar_Parser_AST.PatTuple
      (_,false ) ->
        let uu____2547 = p_tuplePattern p  in
        soft_parens_with_nesting uu____2547
    | uu____2548 ->
        let uu____2549 =
          let uu____2550 = FStar_Parser_AST.pat_to_string p  in
          FStar_Util.format1 "Invalid pattern %s" uu____2550  in
        failwith uu____2549

and p_binder : Prims.bool -> FStar_Parser_AST.binder -> FStar_Pprint.document
  =
  fun is_atomic  ->
    fun b  ->
      match b.FStar_Parser_AST.b with
      | FStar_Parser_AST.Variable lid ->
          let uu____2554 =
            FStar_Pprint.optional p_aqual b.FStar_Parser_AST.aqual  in
          let uu____2555 = p_lident lid  in
          FStar_Pprint.op_Hat_Hat uu____2554 uu____2555
      | FStar_Parser_AST.TVariable lid -> p_lident lid
      | FStar_Parser_AST.Annotated (lid,t) ->
          let doc1 =
            let uu____2560 =
              let uu____2561 = unparen t  in uu____2561.FStar_Parser_AST.tm
               in
            match uu____2560 with
            | FStar_Parser_AST.Refine
                ({ FStar_Parser_AST.b = FStar_Parser_AST.Annotated (lid',t1);
                   FStar_Parser_AST.brange = uu____2564;
                   FStar_Parser_AST.blevel = uu____2565;
                   FStar_Parser_AST.aqual = uu____2566;_},phi)
                when lid.FStar_Ident.idText = lid'.FStar_Ident.idText ->
                let uu____2568 = p_ident lid  in
                p_refinement b.FStar_Parser_AST.aqual uu____2568 t1 phi
            | uu____2569 ->
                let uu____2570 =
                  FStar_Pprint.optional p_aqual b.FStar_Parser_AST.aqual  in
                let uu____2571 =
                  let uu____2572 = p_lident lid  in
                  let uu____2573 =
                    let uu____2574 =
                      let uu____2575 =
                        FStar_Pprint.break_ (Prims.parse_int "0")  in
                      let uu____2576 = p_tmFormula t  in
                      FStar_Pprint.op_Hat_Hat uu____2575 uu____2576  in
                    FStar_Pprint.op_Hat_Hat FStar_Pprint.colon uu____2574  in
                  FStar_Pprint.op_Hat_Hat uu____2572 uu____2573  in
                FStar_Pprint.op_Hat_Hat uu____2570 uu____2571
             in
          if is_atomic
          then
            let uu____2577 =
              let uu____2578 =
                FStar_Pprint.op_Hat_Hat doc1 FStar_Pprint.rparen  in
              FStar_Pprint.op_Hat_Hat FStar_Pprint.lparen uu____2578  in
            FStar_Pprint.group uu____2577
          else FStar_Pprint.group doc1
      | FStar_Parser_AST.TAnnotated uu____2580 ->
          failwith "Is this still used ?"
      | FStar_Parser_AST.NoName t ->
          let uu____2584 =
            let uu____2585 = unparen t  in uu____2585.FStar_Parser_AST.tm  in
          (match uu____2584 with
           | FStar_Parser_AST.Refine
               ({ FStar_Parser_AST.b = FStar_Parser_AST.NoName t1;
                  FStar_Parser_AST.brange = uu____2587;
                  FStar_Parser_AST.blevel = uu____2588;
                  FStar_Parser_AST.aqual = uu____2589;_},phi)
               ->
               if is_atomic
               then
                 let uu____2591 =
                   let uu____2592 =
                     let uu____2593 =
                       p_refinement b.FStar_Parser_AST.aqual
                         FStar_Pprint.underscore t1 phi
                        in
                     FStar_Pprint.op_Hat_Hat uu____2593 FStar_Pprint.rparen
                      in
                   FStar_Pprint.op_Hat_Hat FStar_Pprint.lparen uu____2592  in
                 FStar_Pprint.group uu____2591
               else
                 (let uu____2595 =
                    p_refinement b.FStar_Parser_AST.aqual
                      FStar_Pprint.underscore t1 phi
                     in
                  FStar_Pprint.group uu____2595)
           | uu____2596 -> if is_atomic then p_atomicTerm t else p_appTerm t)

and p_refinement :
  FStar_Parser_AST.arg_qualifier Prims.option ->
    FStar_Pprint.document ->
      FStar_Parser_AST.term -> FStar_Parser_AST.term -> FStar_Pprint.document
  =
  fun aqual_opt  ->
    fun binder  ->
      fun t  ->
        fun phi  ->
          let uu____2603 = FStar_Pprint.optional p_aqual aqual_opt  in
          let uu____2604 =
            let uu____2605 =
              let uu____2606 =
                let uu____2607 = p_appTerm t  in
                let uu____2608 =
                  let uu____2609 = p_noSeqTerm phi  in
                  soft_braces_with_nesting uu____2609  in
                FStar_Pprint.op_Hat_Hat uu____2607 uu____2608  in
              FStar_Pprint.op_Hat_Hat FStar_Pprint.colon uu____2606  in
            FStar_Pprint.op_Hat_Hat binder uu____2605  in
          FStar_Pprint.op_Hat_Hat uu____2603 uu____2604

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
    let uu____2622 =
      let uu____2623 = unparen e  in uu____2623.FStar_Parser_AST.tm  in
    match uu____2622 with
    | FStar_Parser_AST.Seq (e1,e2) ->
        let uu____2626 =
          let uu____2627 =
            let uu____2628 = p_noSeqTerm e1  in
            FStar_Pprint.op_Hat_Hat uu____2628 FStar_Pprint.semi  in
          FStar_Pprint.group uu____2627  in
        let uu____2629 = p_term e2  in
        FStar_Pprint.op_Hat_Slash_Hat uu____2626 uu____2629
    | uu____2630 ->
        let uu____2631 = p_noSeqTerm e  in FStar_Pprint.group uu____2631

and p_noSeqTerm : FStar_Parser_AST.term -> FStar_Pprint.document =
  fun e  -> with_comment p_noSeqTerm' e e.FStar_Parser_AST.range

and p_noSeqTerm' : FStar_Parser_AST.term -> FStar_Pprint.document =
  fun e  ->
    let uu____2634 =
      let uu____2635 = unparen e  in uu____2635.FStar_Parser_AST.tm  in
    match uu____2634 with
    | FStar_Parser_AST.Ascribed (e1,t,None ) ->
        let uu____2639 =
          let uu____2640 = p_tmIff e1  in
          let uu____2641 =
            let uu____2642 =
              let uu____2643 = p_typ t  in
              FStar_Pprint.op_Hat_Slash_Hat FStar_Pprint.colon uu____2643  in
            FStar_Pprint.op_Hat_Hat FStar_Pprint.langle uu____2642  in
          FStar_Pprint.op_Hat_Slash_Hat uu____2640 uu____2641  in
        FStar_Pprint.group uu____2639
    | FStar_Parser_AST.Ascribed (e1,t,Some tac) ->
        let uu____2648 =
          let uu____2649 = p_tmIff e1  in
          let uu____2650 =
            let uu____2651 =
              let uu____2652 =
                let uu____2653 = p_typ t  in
                let uu____2654 =
                  let uu____2655 = str "by"  in
                  let uu____2656 = p_typ tac  in
                  FStar_Pprint.op_Hat_Slash_Hat uu____2655 uu____2656  in
                FStar_Pprint.op_Hat_Slash_Hat uu____2653 uu____2654  in
              FStar_Pprint.op_Hat_Slash_Hat FStar_Pprint.colon uu____2652  in
            FStar_Pprint.op_Hat_Hat FStar_Pprint.langle uu____2651  in
          FStar_Pprint.op_Hat_Slash_Hat uu____2649 uu____2650  in
        FStar_Pprint.group uu____2648
    | FStar_Parser_AST.Op (op,e1::e2::e3::[]) when op = ".()<-" ->
        let uu____2662 =
          let uu____2663 =
            let uu____2664 =
              let uu____2665 = p_atomicTermNotQUident e1  in
              let uu____2666 =
                let uu____2667 =
                  let uu____2668 =
                    let uu____2669 = p_term e2  in
                    soft_parens_with_nesting uu____2669  in
                  let uu____2670 =
                    FStar_Pprint.op_Hat_Hat FStar_Pprint.space
                      FStar_Pprint.larrow
                     in
                  FStar_Pprint.op_Hat_Hat uu____2668 uu____2670  in
                FStar_Pprint.op_Hat_Hat FStar_Pprint.dot uu____2667  in
              FStar_Pprint.op_Hat_Hat uu____2665 uu____2666  in
            FStar_Pprint.group uu____2664  in
          let uu____2671 =
            let uu____2672 = p_noSeqTerm e3  in jump2 uu____2672  in
          FStar_Pprint.op_Hat_Hat uu____2663 uu____2671  in
        FStar_Pprint.group uu____2662
    | FStar_Parser_AST.Op (op,e1::e2::e3::[]) when op = ".[]<-" ->
        let uu____2678 =
          let uu____2679 =
            let uu____2680 =
              let uu____2681 = p_atomicTermNotQUident e1  in
              let uu____2682 =
                let uu____2683 =
                  let uu____2684 =
                    let uu____2685 = p_term e2  in
                    soft_brackets_with_nesting uu____2685  in
                  let uu____2686 =
                    FStar_Pprint.op_Hat_Hat FStar_Pprint.space
                      FStar_Pprint.larrow
                     in
                  FStar_Pprint.op_Hat_Hat uu____2684 uu____2686  in
                FStar_Pprint.op_Hat_Hat FStar_Pprint.dot uu____2683  in
              FStar_Pprint.op_Hat_Hat uu____2681 uu____2682  in
            FStar_Pprint.group uu____2680  in
          let uu____2687 =
            let uu____2688 = p_noSeqTerm e3  in jump2 uu____2688  in
          FStar_Pprint.op_Hat_Hat uu____2679 uu____2687  in
        FStar_Pprint.group uu____2678
    | FStar_Parser_AST.Requires (e1,wtf) ->
        let uu____2694 =
          let uu____2695 = str "requires"  in
          let uu____2696 = p_typ e1  in
          FStar_Pprint.op_Hat_Slash_Hat uu____2695 uu____2696  in
        FStar_Pprint.group uu____2694
    | FStar_Parser_AST.Ensures (e1,wtf) ->
        let uu____2702 =
          let uu____2703 = str "ensures"  in
          let uu____2704 = p_typ e1  in
          FStar_Pprint.op_Hat_Slash_Hat uu____2703 uu____2704  in
        FStar_Pprint.group uu____2702
    | FStar_Parser_AST.Attributes es ->
        let uu____2707 =
          let uu____2708 = str "attributes"  in
          let uu____2709 = FStar_Pprint.separate_map break1 p_atomicTerm es
             in
          FStar_Pprint.op_Hat_Slash_Hat uu____2708 uu____2709  in
        FStar_Pprint.group uu____2707
    | FStar_Parser_AST.If (e1,e2,e3) ->
        let uu____2713 = is_unit e3  in
        if uu____2713
        then
          let uu____2714 =
            let uu____2715 =
              let uu____2716 = str "if"  in
              let uu____2717 = p_noSeqTerm e1  in
              op_Hat_Slash_Plus_Hat uu____2716 uu____2717  in
            let uu____2718 =
              let uu____2719 = str "then"  in
              let uu____2720 = p_noSeqTerm e2  in
              op_Hat_Slash_Plus_Hat uu____2719 uu____2720  in
            FStar_Pprint.op_Hat_Slash_Hat uu____2715 uu____2718  in
          FStar_Pprint.group uu____2714
        else
          (let e2_doc =
             let uu____2723 =
               let uu____2724 = unparen e2  in uu____2724.FStar_Parser_AST.tm
                in
             match uu____2723 with
             | FStar_Parser_AST.If (uu____2725,uu____2726,e31) when
                 is_unit e31 ->
                 let uu____2728 = p_noSeqTerm e2  in
                 soft_parens_with_nesting uu____2728
             | uu____2729 -> p_noSeqTerm e2  in
           let uu____2730 =
             let uu____2731 =
               let uu____2732 = str "if"  in
               let uu____2733 = p_noSeqTerm e1  in
               op_Hat_Slash_Plus_Hat uu____2732 uu____2733  in
             let uu____2734 =
               let uu____2735 =
                 let uu____2736 = str "then"  in
                 op_Hat_Slash_Plus_Hat uu____2736 e2_doc  in
               let uu____2737 =
                 let uu____2738 = str "else"  in
                 let uu____2739 = p_noSeqTerm e3  in
                 op_Hat_Slash_Plus_Hat uu____2738 uu____2739  in
               FStar_Pprint.op_Hat_Slash_Hat uu____2735 uu____2737  in
             FStar_Pprint.op_Hat_Slash_Hat uu____2731 uu____2734  in
           FStar_Pprint.group uu____2730)
    | FStar_Parser_AST.TryWith (e1,branches) ->
        let uu____2752 =
          let uu____2753 =
            let uu____2754 = str "try"  in
            let uu____2755 = p_noSeqTerm e1  in prefix2 uu____2754 uu____2755
             in
          let uu____2756 =
            let uu____2757 = str "with"  in
            let uu____2758 =
              FStar_Pprint.separate_map FStar_Pprint.hardline p_patternBranch
                branches
               in
            FStar_Pprint.op_Hat_Slash_Hat uu____2757 uu____2758  in
          FStar_Pprint.op_Hat_Slash_Hat uu____2753 uu____2756  in
        FStar_Pprint.group uu____2752
    | FStar_Parser_AST.Match (e1,branches) ->
        let uu____2775 =
          let uu____2776 =
            let uu____2777 = str "match"  in
            let uu____2778 = p_noSeqTerm e1  in
            let uu____2779 = str "with"  in
            FStar_Pprint.surround (Prims.parse_int "2") (Prims.parse_int "1")
              uu____2777 uu____2778 uu____2779
             in
          let uu____2780 =
            FStar_Pprint.separate_map FStar_Pprint.hardline p_patternBranch
              branches
             in
          FStar_Pprint.op_Hat_Slash_Hat uu____2776 uu____2780  in
        FStar_Pprint.group uu____2775
    | FStar_Parser_AST.LetOpen (uid,e1) ->
        let uu____2787 =
          let uu____2788 =
            let uu____2789 = str "let open"  in
            let uu____2790 = p_quident uid  in
            let uu____2791 = str "in"  in
            FStar_Pprint.surround (Prims.parse_int "2") (Prims.parse_int "1")
              uu____2789 uu____2790 uu____2791
             in
          let uu____2792 = p_term e1  in
          FStar_Pprint.op_Hat_Slash_Hat uu____2788 uu____2792  in
        FStar_Pprint.group uu____2787
    | FStar_Parser_AST.Let (q,lbs,e1) ->
        let let_doc =
          let uu____2803 = str "let"  in
          let uu____2804 = p_letqualifier q  in
          FStar_Pprint.op_Hat_Hat uu____2803 uu____2804  in
        let uu____2805 =
          let uu____2806 =
            let uu____2807 =
              let uu____2808 = str "and"  in
              precede_break_separate_map let_doc uu____2808 p_letbinding lbs
               in
            let uu____2811 = str "in"  in
            FStar_Pprint.op_Hat_Slash_Hat uu____2807 uu____2811  in
          FStar_Pprint.group uu____2806  in
        let uu____2812 = p_term e1  in
        FStar_Pprint.op_Hat_Slash_Hat uu____2805 uu____2812
    | FStar_Parser_AST.Abs
        ({ FStar_Parser_AST.pat = FStar_Parser_AST.PatVar (x,typ_opt);
           FStar_Parser_AST.prange = uu____2815;_}::[],{
                                                         FStar_Parser_AST.tm
                                                           =
                                                           FStar_Parser_AST.Match
                                                           (maybe_x,branches);
                                                         FStar_Parser_AST.range
                                                           = uu____2818;
                                                         FStar_Parser_AST.level
                                                           = uu____2819;_})
        when matches_var maybe_x x ->
        let uu____2833 =
          let uu____2834 = str "function"  in
          let uu____2835 =
            FStar_Pprint.separate_map FStar_Pprint.hardline p_patternBranch
              branches
             in
          FStar_Pprint.op_Hat_Slash_Hat uu____2834 uu____2835  in
        FStar_Pprint.group uu____2833
    | FStar_Parser_AST.Assign (id,e1) ->
        let uu____2842 =
          let uu____2843 = p_lident id  in
          let uu____2844 =
            let uu____2845 = p_noSeqTerm e1  in
            FStar_Pprint.op_Hat_Slash_Hat FStar_Pprint.larrow uu____2845  in
          FStar_Pprint.op_Hat_Slash_Hat uu____2843 uu____2844  in
        FStar_Pprint.group uu____2842
    | uu____2846 -> p_typ e

and p_typ : FStar_Parser_AST.term -> FStar_Pprint.document =
  fun e  -> with_comment p_typ' e e.FStar_Parser_AST.range

and p_typ' : FStar_Parser_AST.term -> FStar_Pprint.document =
  fun e  ->
    let uu____2849 =
      let uu____2850 = unparen e  in uu____2850.FStar_Parser_AST.tm  in
    match uu____2849 with
    | FStar_Parser_AST.QForall (bs,trigger,e1)|FStar_Parser_AST.QExists
      (bs,trigger,e1) ->
        let uu____2866 =
          let uu____2867 =
            let uu____2868 = p_quantifier e  in
            FStar_Pprint.op_Hat_Hat uu____2868 FStar_Pprint.space  in
          let uu____2869 = p_binders true bs  in
          FStar_Pprint.soft_surround (Prims.parse_int "2")
            (Prims.parse_int "0") uu____2867 uu____2869 FStar_Pprint.dot
           in
        let uu____2870 =
          let uu____2871 = p_trigger trigger  in
          let uu____2872 = p_noSeqTerm e1  in
          FStar_Pprint.op_Hat_Hat uu____2871 uu____2872  in
        prefix2 uu____2866 uu____2870
    | uu____2873 -> p_simpleTerm e

and p_quantifier : FStar_Parser_AST.term -> FStar_Pprint.document =
  fun e  ->
    let uu____2875 =
      let uu____2876 = unparen e  in uu____2876.FStar_Parser_AST.tm  in
    match uu____2875 with
    | FStar_Parser_AST.QForall uu____2877 -> str "forall"
    | FStar_Parser_AST.QExists uu____2884 -> str "exists"
    | uu____2891 ->
        failwith "Imposible : p_quantifier called on a non-quantifier term"

and p_trigger :
  FStar_Parser_AST.term Prims.list Prims.list -> FStar_Pprint.document =
  fun uu___135_2892  ->
    match uu___135_2892 with
    | [] -> FStar_Pprint.empty
    | pats ->
        let uu____2899 =
          let uu____2900 =
            let uu____2901 = str "pattern"  in
            let uu____2902 =
              let uu____2903 =
                let uu____2904 = p_disjunctivePats pats  in jump2 uu____2904
                 in
              let uu____2905 =
                FStar_Pprint.op_Hat_Hat FStar_Pprint.rbrace break1  in
              FStar_Pprint.op_Hat_Slash_Hat uu____2903 uu____2905  in
            FStar_Pprint.op_Hat_Slash_Hat uu____2901 uu____2902  in
          FStar_Pprint.op_Hat_Hat FStar_Pprint.colon uu____2900  in
        FStar_Pprint.op_Hat_Hat FStar_Pprint.lbrace uu____2899

and p_disjunctivePats :
  FStar_Parser_AST.term Prims.list Prims.list -> FStar_Pprint.document =
  fun pats  ->
    let uu____2909 = str "\\/"  in
    FStar_Pprint.separate_map uu____2909 p_conjunctivePats pats

and p_conjunctivePats :
  FStar_Parser_AST.term Prims.list -> FStar_Pprint.document =
  fun pats  ->
    let uu____2913 =
      FStar_Pprint.separate_map FStar_Pprint.semi p_appTerm pats  in
    FStar_Pprint.group uu____2913

and p_simpleTerm : FStar_Parser_AST.term -> FStar_Pprint.document =
  fun e  ->
    let uu____2915 =
      let uu____2916 = unparen e  in uu____2916.FStar_Parser_AST.tm  in
    match uu____2915 with
    | FStar_Parser_AST.Abs (pats,e1) ->
        let uu____2921 =
          let uu____2922 = str "fun"  in
          let uu____2923 =
            let uu____2924 =
              FStar_Pprint.separate_map break1 p_atomicPattern pats  in
            FStar_Pprint.op_Hat_Slash_Hat uu____2924 FStar_Pprint.rarrow  in
          op_Hat_Slash_Plus_Hat uu____2922 uu____2923  in
        let uu____2925 = p_term e1  in
        op_Hat_Slash_Plus_Hat uu____2921 uu____2925
    | uu____2926 -> p_tmIff e

and p_maybeFocusArrow : Prims.bool -> FStar_Pprint.document =
  fun b  -> if b then str "~>" else FStar_Pprint.rarrow

and p_patternBranch :
  (FStar_Parser_AST.pattern * FStar_Parser_AST.term Prims.option *
    FStar_Parser_AST.term) -> FStar_Pprint.document
  =
  fun uu____2929  ->
    match uu____2929 with
    | (pat,when_opt,e) ->
        let maybe_paren =
          let uu____2942 =
            let uu____2943 = unparen e  in uu____2943.FStar_Parser_AST.tm  in
          match uu____2942 with
          | FStar_Parser_AST.Match _|FStar_Parser_AST.TryWith _ ->
              soft_begin_end_with_nesting
          | FStar_Parser_AST.Abs
              ({
                 FStar_Parser_AST.pat = FStar_Parser_AST.PatVar
                   (x,uu____2949);
                 FStar_Parser_AST.prange = uu____2950;_}::[],{
                                                               FStar_Parser_AST.tm
                                                                 =
                                                                 FStar_Parser_AST.Match
                                                                 (maybe_x,uu____2952);
                                                               FStar_Parser_AST.range
                                                                 = uu____2953;
                                                               FStar_Parser_AST.level
                                                                 = uu____2954;_})
              when matches_var maybe_x x -> soft_begin_end_with_nesting
          | uu____2968 -> (fun x  -> x)  in
        let uu____2970 =
          let uu____2971 =
            let uu____2972 =
              let uu____2973 =
                let uu____2974 =
                  let uu____2975 = p_disjunctivePattern pat  in
                  let uu____2976 =
                    let uu____2977 = p_maybeWhen when_opt  in
                    FStar_Pprint.op_Hat_Hat uu____2977 FStar_Pprint.rarrow
                     in
                  op_Hat_Slash_Plus_Hat uu____2975 uu____2976  in
                FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____2974  in
              FStar_Pprint.op_Hat_Hat FStar_Pprint.bar uu____2973  in
            FStar_Pprint.group uu____2972  in
          let uu____2978 =
            let uu____2979 = p_term e  in maybe_paren uu____2979  in
          op_Hat_Slash_Plus_Hat uu____2971 uu____2978  in
        FStar_Pprint.group uu____2970

and p_maybeWhen : FStar_Parser_AST.term Prims.option -> FStar_Pprint.document
  =
  fun uu___136_2980  ->
    match uu___136_2980 with
    | None  -> FStar_Pprint.empty
    | Some e ->
        let uu____2983 = str "when"  in
        let uu____2984 =
          let uu____2985 = p_tmFormula e  in
          FStar_Pprint.op_Hat_Hat uu____2985 FStar_Pprint.space  in
        op_Hat_Slash_Plus_Hat uu____2983 uu____2984

and p_tmIff : FStar_Parser_AST.term -> FStar_Pprint.document =
  fun e  ->
    let uu____2987 =
      let uu____2988 = unparen e  in uu____2988.FStar_Parser_AST.tm  in
    match uu____2987 with
    | FStar_Parser_AST.Op ("<==>",e1::e2::[]) ->
        let uu____2992 = str "<==>"  in
        let uu____2993 = p_tmImplies e1  in
        let uu____2994 = p_tmIff e2  in
        infix0 uu____2992 uu____2993 uu____2994
    | uu____2995 -> p_tmImplies e

and p_tmImplies : FStar_Parser_AST.term -> FStar_Pprint.document =
  fun e  ->
    let uu____2997 =
      let uu____2998 = unparen e  in uu____2998.FStar_Parser_AST.tm  in
    match uu____2997 with
    | FStar_Parser_AST.Op ("==>",e1::e2::[]) ->
        let uu____3002 = str "==>"  in
        let uu____3003 = p_tmArrow p_tmFormula e1  in
        let uu____3004 = p_tmImplies e2  in
        infix0 uu____3002 uu____3003 uu____3004
    | uu____3005 -> p_tmArrow p_tmFormula e

and p_tmArrow :
  (FStar_Parser_AST.term -> FStar_Pprint.document) ->
    FStar_Parser_AST.term -> FStar_Pprint.document
  =
  fun p_Tm  ->
    fun e  ->
      let uu____3010 =
        let uu____3011 = unparen e  in uu____3011.FStar_Parser_AST.tm  in
      match uu____3010 with
      | FStar_Parser_AST.Product (bs,tgt) ->
          let uu____3016 =
            let uu____3017 =
              FStar_Pprint.concat_map
                (fun b  ->
                   let uu____3019 = p_binder false b  in
                   let uu____3020 =
                     let uu____3021 =
                       FStar_Pprint.op_Hat_Hat FStar_Pprint.rarrow break1  in
                     FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____3021
                      in
                   FStar_Pprint.op_Hat_Hat uu____3019 uu____3020) bs
               in
            let uu____3022 = p_tmArrow p_Tm tgt  in
            FStar_Pprint.op_Hat_Hat uu____3017 uu____3022  in
          FStar_Pprint.group uu____3016
      | uu____3023 -> p_Tm e

and p_tmFormula : FStar_Parser_AST.term -> FStar_Pprint.document =
  fun e  ->
    let uu____3025 =
      let uu____3026 = unparen e  in uu____3026.FStar_Parser_AST.tm  in
    match uu____3025 with
    | FStar_Parser_AST.Op ("\\/",e1::e2::[]) ->
        let uu____3030 = str "\\/"  in
        let uu____3031 = p_tmFormula e1  in
        let uu____3032 = p_tmConjunction e2  in
        infix0 uu____3030 uu____3031 uu____3032
    | uu____3033 -> p_tmConjunction e

and p_tmConjunction : FStar_Parser_AST.term -> FStar_Pprint.document =
  fun e  ->
    let uu____3035 =
      let uu____3036 = unparen e  in uu____3036.FStar_Parser_AST.tm  in
    match uu____3035 with
    | FStar_Parser_AST.Op ("/\\",e1::e2::[]) ->
        let uu____3040 = str "/\\"  in
        let uu____3041 = p_tmConjunction e1  in
        let uu____3042 = p_tmTuple e2  in
        infix0 uu____3040 uu____3041 uu____3042
    | uu____3043 -> p_tmTuple e

and p_tmTuple : FStar_Parser_AST.term -> FStar_Pprint.document =
  fun e  -> with_comment p_tmTuple' e e.FStar_Parser_AST.range

and p_tmTuple' : FStar_Parser_AST.term -> FStar_Pprint.document =
  fun e  ->
    let uu____3046 =
      let uu____3047 = unparen e  in uu____3047.FStar_Parser_AST.tm  in
    match uu____3046 with
    | FStar_Parser_AST.Construct (lid,args) when is_tuple_constructor lid ->
        let uu____3056 = FStar_Pprint.op_Hat_Hat FStar_Pprint.comma break1
           in
        FStar_Pprint.separate_map uu____3056
          (fun uu____3059  ->
             match uu____3059 with | (e1,uu____3063) -> p_tmEq e1) args
    | uu____3064 -> p_tmEq e

and paren_if :
  Prims.int -> Prims.int -> FStar_Pprint.document -> FStar_Pprint.document =
  fun curr  ->
    fun mine  ->
      fun doc1  ->
        if mine <= curr
        then doc1
        else
          (let uu____3069 =
             let uu____3070 =
               FStar_Pprint.op_Hat_Hat doc1 FStar_Pprint.rparen  in
             FStar_Pprint.op_Hat_Hat FStar_Pprint.lparen uu____3070  in
           FStar_Pprint.group uu____3069)

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
      let uu____3095 =
        let uu____3096 = unparen e  in uu____3096.FStar_Parser_AST.tm  in
      match uu____3095 with
      | FStar_Parser_AST.Op (op,e1::e2::[]) when
          ((is_operatorInfix0ad12 op) || (op = "=")) || (op = "|>") ->
          let uu____3101 = levels op  in
          (match uu____3101 with
           | (left1,mine,right1) ->
               let uu____3108 =
                 let uu____3109 = str op  in
                 let uu____3110 = p_tmEq' left1 e1  in
                 let uu____3111 = p_tmEq' right1 e2  in
                 infix0 uu____3109 uu____3110 uu____3111  in
               paren_if curr mine uu____3108)
      | FStar_Parser_AST.Op (":=",e1::e2::[]) ->
          let uu____3115 =
            let uu____3116 = p_tmEq e1  in
            let uu____3117 =
              let uu____3118 =
                let uu____3119 =
                  let uu____3120 = p_tmEq e2  in
                  op_Hat_Slash_Plus_Hat FStar_Pprint.equals uu____3120  in
                FStar_Pprint.op_Hat_Hat FStar_Pprint.colon uu____3119  in
              FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____3118  in
            FStar_Pprint.op_Hat_Hat uu____3116 uu____3117  in
          FStar_Pprint.group uu____3115
      | uu____3121 -> p_tmNoEq e

and p_tmNoEq : FStar_Parser_AST.term -> FStar_Pprint.document =
  fun e  ->
    let n1 = max_level [colon_colon (); amp (); opinfix3 (); opinfix4 ()]  in
    p_tmNoEq' n1 e

and p_tmNoEq' : Prims.int -> FStar_Parser_AST.term -> FStar_Pprint.document =
  fun curr  ->
    fun e  ->
      let uu____3151 =
        let uu____3152 = unparen e  in uu____3152.FStar_Parser_AST.tm  in
      match uu____3151 with
      | FStar_Parser_AST.Construct (lid,(e1,uu____3155)::(e2,uu____3157)::[])
          when
          (FStar_Ident.lid_equals lid FStar_Syntax_Const.cons_lid) &&
            (let uu____3167 = is_list e  in Prims.op_Negation uu____3167)
          ->
          let op = "::"  in
          let uu____3169 = levels op  in
          (match uu____3169 with
           | (left1,mine,right1) ->
               let uu____3176 =
                 let uu____3177 = str op  in
                 let uu____3178 = p_tmNoEq' left1 e1  in
                 let uu____3179 = p_tmNoEq' right1 e2  in
                 infix0 uu____3177 uu____3178 uu____3179  in
               paren_if curr mine uu____3176)
      | FStar_Parser_AST.Sum (binders,res) ->
          let op = "&"  in
          let uu____3185 = levels op  in
          (match uu____3185 with
           | (left1,mine,right1) ->
               let p_dsumfst b =
                 let uu____3196 = p_binder false b  in
                 let uu____3197 =
                   let uu____3198 =
                     let uu____3199 = str "&"  in
                     FStar_Pprint.op_Hat_Hat uu____3199 break1  in
                   FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____3198  in
                 FStar_Pprint.op_Hat_Hat uu____3196 uu____3197  in
               let uu____3200 =
                 let uu____3201 = FStar_Pprint.concat_map p_dsumfst binders
                    in
                 let uu____3202 = p_tmNoEq' right1 res  in
                 FStar_Pprint.op_Hat_Hat uu____3201 uu____3202  in
               paren_if curr mine uu____3200)
      | FStar_Parser_AST.Op (op,e1::e2::[]) when is_operatorInfix34 op ->
          let uu____3207 = levels op  in
          (match uu____3207 with
           | (left1,mine,right1) ->
               let uu____3214 =
                 let uu____3215 = str op  in
                 let uu____3216 = p_tmNoEq' left1 e1  in
                 let uu____3217 = p_tmNoEq' right1 e2  in
                 infix0 uu____3215 uu____3216 uu____3217  in
               paren_if curr mine uu____3214)
      | FStar_Parser_AST.Op ("-",e1::[]) ->
          let uu____3220 = levels "-"  in
          (match uu____3220 with
           | (left1,mine,right1) ->
               let uu____3227 = p_tmNoEq' mine e1  in
               FStar_Pprint.op_Hat_Slash_Hat FStar_Pprint.minus uu____3227)
      | FStar_Parser_AST.NamedTyp (lid,e1) ->
          let uu____3230 =
            let uu____3231 = p_lidentOrUnderscore lid  in
            let uu____3232 =
              let uu____3233 = p_appTerm e1  in
              FStar_Pprint.op_Hat_Slash_Hat FStar_Pprint.colon uu____3233  in
            FStar_Pprint.op_Hat_Slash_Hat uu____3231 uu____3232  in
          FStar_Pprint.group uu____3230
      | FStar_Parser_AST.Refine (b,phi) -> p_refinedBinder b phi
      | FStar_Parser_AST.Record (with_opt,record_fields) ->
          let uu____3246 =
            let uu____3247 =
              default_or_map FStar_Pprint.empty p_with_clause with_opt  in
            let uu____3248 =
              let uu____3249 =
                FStar_Pprint.op_Hat_Hat FStar_Pprint.semi break1  in
              FStar_Pprint.separate_map uu____3249 p_simpleDef record_fields
               in
            FStar_Pprint.op_Hat_Hat uu____3247 uu____3248  in
          braces_with_nesting uu____3246
      | FStar_Parser_AST.Op ("~",e1::[]) ->
          let uu____3254 =
            let uu____3255 = str "~"  in
            let uu____3256 = p_atomicTerm e1  in
            FStar_Pprint.op_Hat_Hat uu____3255 uu____3256  in
          FStar_Pprint.group uu____3254
      | uu____3257 -> p_appTerm e

and p_with_clause : FStar_Parser_AST.term -> FStar_Pprint.document =
  fun e  ->
    let uu____3259 = p_appTerm e  in
    let uu____3260 =
      let uu____3261 =
        let uu____3262 = str "with"  in
        FStar_Pprint.op_Hat_Hat uu____3262 break1  in
      FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____3261  in
    FStar_Pprint.op_Hat_Hat uu____3259 uu____3260

and p_refinedBinder :
  FStar_Parser_AST.binder -> FStar_Parser_AST.term -> FStar_Pprint.document =
  fun b  ->
    fun phi  ->
      match b.FStar_Parser_AST.b with
      | FStar_Parser_AST.Annotated (lid,t) ->
          let uu____3267 =
            let uu____3268 = p_lident lid  in
            p_refinement b.FStar_Parser_AST.aqual uu____3268 t phi  in
          soft_parens_with_nesting uu____3267
      | FStar_Parser_AST.TAnnotated uu____3269 ->
          failwith "Is this still used ?"
      | FStar_Parser_AST.Variable _
        |FStar_Parser_AST.TVariable _|FStar_Parser_AST.NoName _ ->
          let uu____3275 =
            let uu____3276 = FStar_Parser_AST.binder_to_string b  in
            FStar_Util.format1
              "Imposible : a refined binder ought to be annotated %s"
              uu____3276
             in
          failwith uu____3275

and p_simpleDef :
  (FStar_Ident.lid * FStar_Parser_AST.term) -> FStar_Pprint.document =
  fun uu____3277  ->
    match uu____3277 with
    | (lid,e) ->
        let uu____3282 =
          let uu____3283 = p_qlident lid  in
          let uu____3284 =
            let uu____3285 = p_tmIff e  in
            FStar_Pprint.op_Hat_Slash_Hat FStar_Pprint.equals uu____3285  in
          FStar_Pprint.op_Hat_Slash_Hat uu____3283 uu____3284  in
        FStar_Pprint.group uu____3282

and p_appTerm : FStar_Parser_AST.term -> FStar_Pprint.document =
  fun e  ->
    let uu____3287 =
      let uu____3288 = unparen e  in uu____3288.FStar_Parser_AST.tm  in
    match uu____3287 with
    | FStar_Parser_AST.App uu____3289 when is_general_application e ->
        let uu____3293 = head_and_args e  in
        (match uu____3293 with
         | (head1,args) ->
             let uu____3307 =
               let uu____3313 = FStar_ST.read should_print_fs_typ_app  in
               if uu____3313
               then
                 let uu____3321 =
                   FStar_Util.take
                     (fun uu____3332  ->
                        match uu____3332 with
                        | (uu____3335,aq) -> aq = FStar_Parser_AST.FsTypApp)
                     args
                    in
                 match uu____3321 with
                 | (fs_typ_args,args1) ->
                     let uu____3356 =
                       let uu____3357 = p_indexingTerm head1  in
                       let uu____3358 =
                         let uu____3359 =
                           FStar_Pprint.op_Hat_Hat FStar_Pprint.comma break1
                            in
                         soft_surround_separate_map (Prims.parse_int "2")
                           (Prims.parse_int "0") FStar_Pprint.empty
                           FStar_Pprint.langle uu____3359 FStar_Pprint.rangle
                           p_fsTypArg fs_typ_args
                          in
                       FStar_Pprint.op_Hat_Hat uu____3357 uu____3358  in
                     (uu____3356, args1)
               else
                 (let uu____3366 = p_indexingTerm head1  in
                  (uu____3366, args))
                in
             (match uu____3307 with
              | (head_doc,args1) ->
                  let uu____3378 =
                    let uu____3379 =
                      FStar_Pprint.op_Hat_Hat head_doc FStar_Pprint.space  in
                    soft_surround_separate_map (Prims.parse_int "2")
                      (Prims.parse_int "0") head_doc uu____3379 break1
                      FStar_Pprint.empty p_argTerm args1
                     in
                  FStar_Pprint.group uu____3378))
    | FStar_Parser_AST.Construct (lid,args) when
        (is_general_construction e) &&
          (Prims.op_Negation (is_dtuple_constructor lid))
        ->
        (match args with
         | [] -> p_quident lid
         | arg::[] ->
             let uu____3399 =
               let uu____3400 = p_quident lid  in
               let uu____3401 = p_argTerm arg  in
               FStar_Pprint.op_Hat_Slash_Hat uu____3400 uu____3401  in
             FStar_Pprint.group uu____3399
         | hd1::tl1 ->
             let uu____3411 =
               let uu____3412 =
                 let uu____3413 =
                   let uu____3414 = p_quident lid  in
                   let uu____3415 = p_argTerm hd1  in
                   prefix2 uu____3414 uu____3415  in
                 FStar_Pprint.group uu____3413  in
               let uu____3416 =
                 let uu____3417 =
                   FStar_Pprint.separate_map break1 p_argTerm tl1  in
                 jump2 uu____3417  in
               FStar_Pprint.op_Hat_Hat uu____3412 uu____3416  in
             FStar_Pprint.group uu____3411)
    | uu____3420 -> p_indexingTerm e

and p_argTerm :
  (FStar_Parser_AST.term * FStar_Parser_AST.imp) -> FStar_Pprint.document =
  fun arg_imp  ->
    match arg_imp with
    | ({ FStar_Parser_AST.tm = FStar_Parser_AST.Uvar uu____3424;
         FStar_Parser_AST.range = uu____3425;
         FStar_Parser_AST.level = uu____3426;_},FStar_Parser_AST.UnivApp
       ) -> p_univar (Prims.fst arg_imp)
    | (u,FStar_Parser_AST.UnivApp ) -> p_universe u
    | (e,FStar_Parser_AST.FsTypApp ) ->
        (FStar_Util.print_warning
           "Unexpected FsTypApp, output might not be formatted correctly.\n";
         (let uu____3430 = p_indexingTerm e  in
          FStar_Pprint.surround (Prims.parse_int "2") (Prims.parse_int "1")
            FStar_Pprint.langle uu____3430 FStar_Pprint.rangle))
    | (e,FStar_Parser_AST.Hash ) ->
        let uu____3432 = str "#"  in
        let uu____3433 = p_indexingTerm e  in
        FStar_Pprint.op_Hat_Hat uu____3432 uu____3433
    | (e,FStar_Parser_AST.Nothing ) -> p_indexingTerm e

and p_fsTypArg :
  (FStar_Parser_AST.term * FStar_Parser_AST.imp) -> FStar_Pprint.document =
  fun uu____3435  ->
    match uu____3435 with | (e,uu____3439) -> p_indexingTerm e

and p_indexingTerm_aux :
  (FStar_Parser_AST.term -> FStar_Pprint.document) ->
    FStar_Parser_AST.term -> FStar_Pprint.document
  =
  fun exit1  ->
    fun e  ->
      let uu____3444 =
        let uu____3445 = unparen e  in uu____3445.FStar_Parser_AST.tm  in
      match uu____3444 with
      | FStar_Parser_AST.Op (".()",e1::e2::[]) ->
          let uu____3449 =
            let uu____3450 = p_indexingTerm_aux p_atomicTermNotQUident e1  in
            let uu____3451 =
              let uu____3452 =
                let uu____3453 = p_term e2  in
                soft_parens_with_nesting uu____3453  in
              FStar_Pprint.op_Hat_Hat FStar_Pprint.dot uu____3452  in
            FStar_Pprint.op_Hat_Hat uu____3450 uu____3451  in
          FStar_Pprint.group uu____3449
      | FStar_Parser_AST.Op (".[]",e1::e2::[]) ->
          let uu____3457 =
            let uu____3458 = p_indexingTerm_aux p_atomicTermNotQUident e1  in
            let uu____3459 =
              let uu____3460 =
                let uu____3461 = p_term e2  in
                soft_brackets_with_nesting uu____3461  in
              FStar_Pprint.op_Hat_Hat FStar_Pprint.dot uu____3460  in
            FStar_Pprint.op_Hat_Hat uu____3458 uu____3459  in
          FStar_Pprint.group uu____3457
      | uu____3462 -> exit1 e

and p_indexingTerm : FStar_Parser_AST.term -> FStar_Pprint.document =
  fun e  -> p_indexingTerm_aux p_atomicTerm e

and p_atomicTerm : FStar_Parser_AST.term -> FStar_Pprint.document =
  fun e  ->
    let uu____3465 =
      let uu____3466 = unparen e  in uu____3466.FStar_Parser_AST.tm  in
    match uu____3465 with
    | FStar_Parser_AST.LetOpen (lid,e1) ->
        let uu____3469 = p_quident lid  in
        let uu____3470 =
          let uu____3471 =
            let uu____3472 = p_term e1  in
            soft_parens_with_nesting uu____3472  in
          FStar_Pprint.op_Hat_Hat FStar_Pprint.dot uu____3471  in
        FStar_Pprint.op_Hat_Hat uu____3469 uu____3470
    | FStar_Parser_AST.Name lid -> p_quident lid
    | FStar_Parser_AST.Op (op,e1::[]) when is_general_prefix_op op ->
        let uu____3477 = str op  in
        let uu____3478 = p_atomicTerm e1  in
        FStar_Pprint.op_Hat_Hat uu____3477 uu____3478
    | uu____3479 -> p_atomicTermNotQUident e

and p_atomicTermNotQUident : FStar_Parser_AST.term -> FStar_Pprint.document =
  fun e  ->
    let uu____3481 =
      let uu____3482 = unparen e  in uu____3482.FStar_Parser_AST.tm  in
    match uu____3481 with
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
        let uu____3491 = str op  in
        let uu____3492 = p_atomicTermNotQUident e1  in
        FStar_Pprint.op_Hat_Hat uu____3491 uu____3492
    | FStar_Parser_AST.Op (op,[]) ->
        let uu____3495 =
          let uu____3496 =
            let uu____3497 = str op  in
            let uu____3498 =
              FStar_Pprint.op_Hat_Hat FStar_Pprint.space FStar_Pprint.rparen
               in
            FStar_Pprint.op_Hat_Hat uu____3497 uu____3498  in
          FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____3496  in
        FStar_Pprint.op_Hat_Hat FStar_Pprint.lparen uu____3495
    | FStar_Parser_AST.Construct (lid,args) when is_dtuple_constructor lid ->
        let uu____3507 =
          FStar_Pprint.op_Hat_Hat FStar_Pprint.lparen FStar_Pprint.bar  in
        let uu____3508 =
          let uu____3509 = FStar_Pprint.op_Hat_Hat FStar_Pprint.comma break1
             in
          let uu____3510 = FStar_List.map Prims.fst args  in
          FStar_Pprint.separate_map uu____3509 p_tmEq uu____3510  in
        let uu____3514 =
          FStar_Pprint.op_Hat_Hat FStar_Pprint.bar FStar_Pprint.rparen  in
        FStar_Pprint.surround (Prims.parse_int "2") (Prims.parse_int "1")
          uu____3507 uu____3508 uu____3514
    | FStar_Parser_AST.Project (e1,lid) ->
        let uu____3517 =
          let uu____3518 = p_atomicTermNotQUident e1  in
          let uu____3519 =
            let uu____3520 = p_qlident lid  in
            FStar_Pprint.op_Hat_Hat FStar_Pprint.dot uu____3520  in
          FStar_Pprint.prefix (Prims.parse_int "2") (Prims.parse_int "0")
            uu____3518 uu____3519
           in
        FStar_Pprint.group uu____3517
    | uu____3521 -> p_projectionLHS e

and p_projectionLHS : FStar_Parser_AST.term -> FStar_Pprint.document =
  fun e  ->
    let uu____3523 =
      let uu____3524 = unparen e  in uu____3524.FStar_Parser_AST.tm  in
    match uu____3523 with
    | FStar_Parser_AST.Var lid -> p_qlident lid
    | FStar_Parser_AST.Projector (constr_lid,field_lid) ->
        let uu____3528 = p_quident constr_lid  in
        let uu____3529 =
          let uu____3530 =
            let uu____3531 = p_lident field_lid  in
            FStar_Pprint.op_Hat_Hat FStar_Pprint.dot uu____3531  in
          FStar_Pprint.op_Hat_Hat FStar_Pprint.qmark uu____3530  in
        FStar_Pprint.op_Hat_Hat uu____3528 uu____3529
    | FStar_Parser_AST.Discrim constr_lid ->
        let uu____3533 = p_quident constr_lid  in
        FStar_Pprint.op_Hat_Hat uu____3533 FStar_Pprint.qmark
    | FStar_Parser_AST.Paren e1 ->
        let uu____3535 = p_term e1  in soft_parens_with_nesting uu____3535
    | uu____3536 when is_array e ->
        let es = extract_from_list e  in
        let uu____3539 =
          FStar_Pprint.op_Hat_Hat FStar_Pprint.lbracket FStar_Pprint.bar  in
        let uu____3540 =
          let uu____3541 = FStar_Pprint.op_Hat_Hat FStar_Pprint.semi break1
             in
          separate_map_or_flow uu____3541 p_noSeqTerm es  in
        let uu____3542 =
          FStar_Pprint.op_Hat_Hat FStar_Pprint.bar FStar_Pprint.rbracket  in
        FStar_Pprint.surround (Prims.parse_int "2") (Prims.parse_int "0")
          uu____3539 uu____3540 uu____3542
    | uu____3543 when is_list e ->
        let uu____3544 =
          let uu____3545 = FStar_Pprint.op_Hat_Hat FStar_Pprint.semi break1
             in
          let uu____3546 = extract_from_list e  in
          separate_map_or_flow uu____3545 p_noSeqTerm uu____3546  in
        FStar_Pprint.surround (Prims.parse_int "2") (Prims.parse_int "0")
          FStar_Pprint.lbracket uu____3544 FStar_Pprint.rbracket
    | uu____3548 when is_lex_list e ->
        let uu____3549 =
          FStar_Pprint.op_Hat_Hat FStar_Pprint.percent FStar_Pprint.lbracket
           in
        let uu____3550 =
          let uu____3551 = FStar_Pprint.op_Hat_Hat FStar_Pprint.semi break1
             in
          let uu____3552 = extract_from_list e  in
          separate_map_or_flow uu____3551 p_noSeqTerm uu____3552  in
        FStar_Pprint.surround (Prims.parse_int "2") (Prims.parse_int "1")
          uu____3549 uu____3550 FStar_Pprint.rbracket
    | uu____3554 when is_ref_set e ->
        let es = extract_from_ref_set e  in
        let uu____3557 =
          FStar_Pprint.op_Hat_Hat FStar_Pprint.bang FStar_Pprint.lbrace  in
        let uu____3558 =
          let uu____3559 = FStar_Pprint.op_Hat_Hat FStar_Pprint.comma break1
             in
          separate_map_or_flow uu____3559 p_appTerm es  in
        FStar_Pprint.surround (Prims.parse_int "2") (Prims.parse_int "0")
          uu____3557 uu____3558 FStar_Pprint.rbrace
    | FStar_Parser_AST.Op (op,args) when
        let uu____3564 = handleable_op op args  in
        Prims.op_Negation uu____3564 ->
        let uu____3565 =
          let uu____3566 =
            let uu____3567 =
              let uu____3568 =
                let uu____3569 =
                  FStar_Util.string_of_int (FStar_List.length args)  in
                Prims.strcat uu____3569
                  " arguments couldn't be handled by the pretty printer"
                 in
              Prims.strcat " with " uu____3568  in
            Prims.strcat op uu____3567  in
          Prims.strcat "Operation " uu____3566  in
        failwith uu____3565
    | FStar_Parser_AST.Uvar uu____3573 ->
        failwith "Unexpected universe variable out of universe context"
    | FStar_Parser_AST.Labeled uu____3574 -> failwith "Not valid in universe"
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
        -> let uu____3605 = p_term e  in soft_parens_with_nesting uu____3605

and p_constant : FStar_Const.sconst -> FStar_Pprint.document =
  fun uu___139_3606  ->
    match uu___139_3606 with
    | FStar_Const.Const_effect  -> str "Effect"
    | FStar_Const.Const_unit  -> str "()"
    | FStar_Const.Const_bool b -> FStar_Pprint.doc_of_bool b
    | FStar_Const.Const_float x -> str (FStar_Util.string_of_float x)
    | FStar_Const.Const_char x ->
        let uu____3610 = FStar_Pprint.doc_of_char x  in
        FStar_Pprint.squotes uu____3610
    | FStar_Const.Const_string (bytes,uu____3612) ->
        let uu____3615 = str (FStar_Util.string_of_bytes bytes)  in
        FStar_Pprint.dquotes uu____3615
    | FStar_Const.Const_bytearray (bytes,uu____3617) ->
        let uu____3620 =
          let uu____3621 = str (FStar_Util.string_of_bytes bytes)  in
          FStar_Pprint.dquotes uu____3621  in
        let uu____3622 = str "B"  in
        FStar_Pprint.op_Hat_Hat uu____3620 uu____3622
    | FStar_Const.Const_int (repr,sign_width_opt) ->
        let signedness uu___137_3634 =
          match uu___137_3634 with
          | FStar_Const.Unsigned  -> str "u"
          | FStar_Const.Signed  -> FStar_Pprint.empty  in
        let width uu___138_3638 =
          match uu___138_3638 with
          | FStar_Const.Int8  -> str "y"
          | FStar_Const.Int16  -> str "s"
          | FStar_Const.Int32  -> str "l"
          | FStar_Const.Int64  -> str "L"  in
        let ending =
          default_or_map FStar_Pprint.empty
            (fun uu____3642  ->
               match uu____3642 with
               | (s,w) ->
                   let uu____3647 = signedness s  in
                   let uu____3648 = width w  in
                   FStar_Pprint.op_Hat_Hat uu____3647 uu____3648)
            sign_width_opt
           in
        let uu____3649 = str repr  in
        FStar_Pprint.op_Hat_Hat uu____3649 ending
    | FStar_Const.Const_range r ->
        let uu____3651 = FStar_Range.string_of_range r  in str uu____3651
    | FStar_Const.Const_reify  -> str "reify"
    | FStar_Const.Const_reflect lid ->
        let uu____3653 = p_quident lid  in
        let uu____3654 =
          let uu____3655 =
            let uu____3656 = str "reflect"  in
            FStar_Pprint.op_Hat_Hat FStar_Pprint.dot uu____3656  in
          FStar_Pprint.op_Hat_Hat FStar_Pprint.qmark uu____3655  in
        FStar_Pprint.op_Hat_Hat uu____3653 uu____3654

and p_universe : FStar_Parser_AST.term -> FStar_Pprint.document =
  fun u  ->
    let uu____3658 = str "u#"  in
    let uu____3659 = p_atomicUniverse u  in
    FStar_Pprint.op_Hat_Hat uu____3658 uu____3659

and p_universeFrom : FStar_Parser_AST.term -> FStar_Pprint.document =
  fun u  ->
    let uu____3661 =
      let uu____3662 = unparen u  in uu____3662.FStar_Parser_AST.tm  in
    match uu____3661 with
    | FStar_Parser_AST.Op ("+",u1::u2::[]) ->
        let uu____3666 =
          let uu____3667 = p_universeFrom u1  in
          let uu____3668 =
            let uu____3669 = p_universeFrom u2  in
            FStar_Pprint.op_Hat_Slash_Hat FStar_Pprint.plus uu____3669  in
          FStar_Pprint.op_Hat_Slash_Hat uu____3667 uu____3668  in
        FStar_Pprint.group uu____3666
    | FStar_Parser_AST.App uu____3670 ->
        let uu____3674 = head_and_args u  in
        (match uu____3674 with
         | (head1,args) ->
             let uu____3688 =
               let uu____3689 = unparen head1  in
               uu____3689.FStar_Parser_AST.tm  in
             (match uu____3688 with
              | FStar_Parser_AST.Var maybe_max_lid when
                  FStar_Ident.lid_equals maybe_max_lid
                    FStar_Syntax_Const.max_lid
                  ->
                  let uu____3691 =
                    let uu____3692 = p_qlident FStar_Syntax_Const.max_lid  in
                    let uu____3693 =
                      FStar_Pprint.separate_map FStar_Pprint.space
                        (fun uu____3696  ->
                           match uu____3696 with
                           | (u1,uu____3700) -> p_atomicUniverse u1) args
                       in
                    op_Hat_Slash_Plus_Hat uu____3692 uu____3693  in
                  FStar_Pprint.group uu____3691
              | uu____3701 ->
                  let uu____3702 =
                    let uu____3703 = FStar_Parser_AST.term_to_string u  in
                    FStar_Util.format1 "Invalid term in universe context %s"
                      uu____3703
                     in
                  failwith uu____3702))
    | uu____3704 -> p_atomicUniverse u

and p_atomicUniverse : FStar_Parser_AST.term -> FStar_Pprint.document =
  fun u  ->
    let uu____3706 =
      let uu____3707 = unparen u  in uu____3707.FStar_Parser_AST.tm  in
    match uu____3706 with
    | FStar_Parser_AST.Wild  -> FStar_Pprint.underscore
    | FStar_Parser_AST.Const (FStar_Const.Const_int (r,sw)) ->
        p_constant (FStar_Const.Const_int (r, sw))
    | FStar_Parser_AST.Uvar uu____3719 -> p_univar u
    | FStar_Parser_AST.Paren u1 ->
        let uu____3721 = p_universeFrom u1  in
        soft_parens_with_nesting uu____3721
    | FStar_Parser_AST.Op ("+",_::_::[])|FStar_Parser_AST.App _ ->
        let uu____3726 = p_universeFrom u  in
        soft_parens_with_nesting uu____3726
    | uu____3727 ->
        let uu____3728 =
          let uu____3729 = FStar_Parser_AST.term_to_string u  in
          FStar_Util.format1 "Invalid term in universe context %s" uu____3729
           in
        failwith uu____3728

and p_univar : FStar_Parser_AST.term -> FStar_Pprint.document =
  fun u  ->
    let uu____3731 =
      let uu____3732 = unparen u  in uu____3732.FStar_Parser_AST.tm  in
    match uu____3731 with
    | FStar_Parser_AST.Uvar id -> str (FStar_Ident.text_of_id id)
    | uu____3734 ->
        let uu____3735 =
          let uu____3736 = FStar_Parser_AST.term_to_string u  in
          FStar_Util.format1 "Not a universe variable %s" uu____3736  in
        failwith uu____3735

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
           let uu____3758 =
             FStar_All.pipe_right decls (FStar_List.map decl_to_document)  in
           FStar_All.pipe_right uu____3758
             (FStar_Pprint.separate FStar_Pprint.hardline)
        in
     FStar_ST.write should_print_fs_typ_app false; res)
  
let comments_to_document :
  (Prims.string * FStar_Range.range) Prims.list -> FStar_Pprint.document =
  fun comments  ->
    FStar_Pprint.separate_map FStar_Pprint.hardline
      (fun uu____3777  ->
         match uu____3777 with | (comment,range) -> str comment) comments
  
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
           let uu____3824 =
             match ds with
             | {
                 FStar_Parser_AST.d = FStar_Parser_AST.Pragma
                   (FStar_Parser_AST.LightOff );
                 FStar_Parser_AST.drange = uu____3831;
                 FStar_Parser_AST.doc = uu____3832;
                 FStar_Parser_AST.quals = uu____3833;
                 FStar_Parser_AST.attrs = uu____3834;_}::uu____3835 ->
                 let d0 = FStar_List.hd ds  in
                 let uu____3839 =
                   let uu____3841 =
                     let uu____3843 = FStar_List.tl ds  in d :: uu____3843
                      in
                   d0 :: uu____3841  in
                 (uu____3839, (d0.FStar_Parser_AST.drange))
             | uu____3846 -> ((d :: ds), (d.FStar_Parser_AST.drange))  in
           (match uu____3824 with
            | (decls1,first_range) ->
                let extract_decl_range d1 = d1.FStar_Parser_AST.drange  in
                (FStar_ST.write comment_stack comments;
                 (let initial_comment =
                    let uu____3869 = FStar_Range.start_of_range first_range
                       in
                    place_comments_until_pos (Prims.parse_int "0")
                      (Prims.parse_int "1") uu____3869 FStar_Pprint.empty
                     in
                  let doc1 =
                    separate_map_with_comments FStar_Pprint.empty
                      FStar_Pprint.empty decl_to_document decls1
                      extract_decl_range
                     in
                  let comments1 = FStar_ST.read comment_stack  in
                  FStar_ST.write comment_stack [];
                  FStar_ST.write should_print_fs_typ_app false;
                  (let uu____3891 =
                     FStar_Pprint.op_Hat_Hat initial_comment doc1  in
                   (uu____3891, comments1))))))
  