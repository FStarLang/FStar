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
    let uu____44 = Prims.op_Negation (FStar_ST.read should_unparen)  in
    if uu____44
    then t
    else
      (match t.FStar_Parser_AST.tm with
       | FStar_Parser_AST.Paren t -> unparen t
       | uu____49 -> t)
  
let str : Prims.string -> FStar_Pprint.document =
  fun s  -> FStar_Pprint.doc_of_string s 
let default_or_map n f x = match x with | None  -> n | Some x' -> f x' 
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
  FStar_Pprint.group
    (let _0_393 =
       let _0_392 = FStar_Pprint.op_Hat_Hat sep break1  in
       FStar_Pprint.op_Hat_Hat FStar_Pprint.space _0_392  in
     FStar_Pprint.separate_map _0_393 f l)
  
let precede_break_separate_map prec sep f l =
  let _0_402 =
    let _0_396 = FStar_Pprint.op_Hat_Hat prec FStar_Pprint.space  in
    let _0_395 =
      let _0_394 = FStar_List.hd l  in FStar_All.pipe_right _0_394 f  in
    FStar_Pprint.precede _0_396 _0_395  in
  let _0_401 =
    let _0_400 = FStar_List.tl l  in
    FStar_Pprint.concat_map
      (fun x  ->
         let _0_399 =
           let _0_398 =
             let _0_397 = f x  in
             FStar_Pprint.op_Hat_Hat FStar_Pprint.space _0_397  in
           FStar_Pprint.op_Hat_Hat sep _0_398  in
         FStar_Pprint.op_Hat_Hat break1 _0_399) _0_400
     in
  FStar_Pprint.op_Hat_Hat _0_402 _0_401 
let concat_break_map f l =
  FStar_Pprint.group
    (FStar_Pprint.concat_map
       (fun x  -> let _0_403 = f x  in FStar_Pprint.op_Hat_Hat _0_403 break1)
       l)
  
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
    let _0_405 = str "begin"  in
    let _0_404 = str "end"  in
    FStar_Pprint.soft_surround (Prims.parse_int "2") (Prims.parse_int "1")
      _0_405 contents _0_404
  
let separate_map_or_flow sep f l =
  if (FStar_List.length l) < (Prims.parse_int "10")
  then FStar_Pprint.separate_map sep f l
  else FStar_Pprint.flow_map sep f l 
let soft_surround_separate_map n b void_ opening sep closing f xs =
  if xs = []
  then void_
  else
    (let _0_406 = FStar_Pprint.separate_map sep f xs  in
     FStar_Pprint.soft_surround n b opening _0_406 closing)
  
let doc_of_fsdoc :
  (Prims.string * (Prims.string * Prims.string) Prims.list) ->
    FStar_Pprint.document
  =
  fun uu____288  ->
    match uu____288 with
    | (comment,keywords) ->
        FStar_Pprint.group
          (FStar_Pprint.concat
             (let _0_414 = str comment  in
              let _0_413 =
                let _0_412 =
                  let _0_411 =
                    FStar_Pprint.separate_map FStar_Pprint.comma
                      (fun uu____304  ->
                         match uu____304 with
                         | (k,v) ->
                             FStar_Pprint.concat
                               (let _0_410 = str k  in
                                let _0_409 =
                                  let _0_408 =
                                    let _0_407 = str v  in [_0_407]  in
                                  FStar_Pprint.rarrow :: _0_408  in
                                _0_410 :: _0_409)) keywords
                     in
                  [_0_411]  in
                FStar_Pprint.space :: _0_412  in
              _0_414 :: _0_413))
  
let is_unit : FStar_Parser_AST.term -> Prims.bool =
  fun e  ->
    let uu____312 = (unparen e).FStar_Parser_AST.tm  in
    match uu____312 with
    | FStar_Parser_AST.Const (FStar_Const.Const_unit ) -> true
    | uu____313 -> false
  
let matches_var : FStar_Parser_AST.term -> FStar_Ident.ident -> Prims.bool =
  fun t  ->
    fun x  ->
      let uu____320 = (unparen t).FStar_Parser_AST.tm  in
      match uu____320 with
      | FStar_Parser_AST.Var y ->
          x.FStar_Ident.idText = (FStar_Ident.text_of_lid y)
      | uu____322 -> false
  
let is_tuple_constructor : FStar_Ident.lident -> Prims.bool =
  FStar_Syntax_Util.is_tuple_data_lid' 
let is_dtuple_constructor : FStar_Ident.lident -> Prims.bool =
  FStar_Syntax_Util.is_dtuple_data_lid' 
let is_list_structure :
  FStar_Ident.lident ->
    FStar_Ident.lident -> FStar_Parser_AST.term -> Prims.bool
  =
  fun cons_lid  ->
    fun nil_lid  ->
      let rec aux e =
        let uu____339 = (unparen e).FStar_Parser_AST.tm  in
        match uu____339 with
        | FStar_Parser_AST.Construct (lid,[]) ->
            FStar_Ident.lid_equals lid nil_lid
        | FStar_Parser_AST.Construct (lid,uu____347::(e2,uu____349)::[]) ->
            (FStar_Ident.lid_equals lid cons_lid) && (aux e2)
        | uu____361 -> false  in
      aux
  
let is_list : FStar_Parser_AST.term -> Prims.bool =
  is_list_structure FStar_Syntax_Const.cons_lid FStar_Syntax_Const.nil_lid 
let is_lex_list : FStar_Parser_AST.term -> Prims.bool =
  is_list_structure FStar_Syntax_Const.lexcons_lid
    FStar_Syntax_Const.lextop_lid
  
let rec extract_from_list :
  FStar_Parser_AST.term -> FStar_Parser_AST.term Prims.list =
  fun e  ->
    let uu____370 = (unparen e).FStar_Parser_AST.tm  in
    match uu____370 with
    | FStar_Parser_AST.Construct (uu____372,[]) -> []
    | FStar_Parser_AST.Construct
        (uu____378,(e1,FStar_Parser_AST.Nothing )::(e2,FStar_Parser_AST.Nothing
                                                    )::[])
        -> let _0_415 = extract_from_list e2  in e1 :: _0_415
    | uu____390 ->
        failwith
          (let _0_416 = FStar_Parser_AST.term_to_string e  in
           FStar_Util.format1 "Not a list %s" _0_416)
  
let is_array : FStar_Parser_AST.term -> Prims.bool =
  fun e  ->
    let uu____395 = (unparen e).FStar_Parser_AST.tm  in
    match uu____395 with
    | FStar_Parser_AST.App
        ({ FStar_Parser_AST.tm = FStar_Parser_AST.Var lid;
           FStar_Parser_AST.range = uu____397;
           FStar_Parser_AST.level = uu____398;_},l,FStar_Parser_AST.Nothing
         )
        ->
        (FStar_Ident.lid_equals lid FStar_Syntax_Const.array_mk_array_lid) &&
          (is_list l)
    | uu____400 -> false
  
let rec is_ref_set : FStar_Parser_AST.term -> Prims.bool =
  fun e  ->
    let uu____404 = (unparen e).FStar_Parser_AST.tm  in
    match uu____404 with
    | FStar_Parser_AST.Var maybe_empty_lid ->
        FStar_Ident.lid_equals maybe_empty_lid FStar_Syntax_Const.tset_empty
    | FStar_Parser_AST.App
        ({ FStar_Parser_AST.tm = FStar_Parser_AST.Var maybe_singleton_lid;
           FStar_Parser_AST.range = uu____407;
           FStar_Parser_AST.level = uu____408;_},{
                                                   FStar_Parser_AST.tm =
                                                     FStar_Parser_AST.App
                                                     ({
                                                        FStar_Parser_AST.tm =
                                                          FStar_Parser_AST.Var
                                                          maybe_ref_lid;
                                                        FStar_Parser_AST.range
                                                          = uu____410;
                                                        FStar_Parser_AST.level
                                                          = uu____411;_},e,FStar_Parser_AST.Nothing
                                                      );
                                                   FStar_Parser_AST.range =
                                                     uu____413;
                                                   FStar_Parser_AST.level =
                                                     uu____414;_},FStar_Parser_AST.Nothing
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
                FStar_Parser_AST.range = uu____416;
                FStar_Parser_AST.level = uu____417;_},e1,FStar_Parser_AST.Nothing
              );
           FStar_Parser_AST.range = uu____419;
           FStar_Parser_AST.level = uu____420;_},e2,FStar_Parser_AST.Nothing
         )
        ->
        ((FStar_Ident.lid_equals maybe_union_lid
            FStar_Syntax_Const.tset_union)
           && (is_ref_set e1))
          && (is_ref_set e2)
    | uu____422 -> false
  
let rec extract_from_ref_set :
  FStar_Parser_AST.term -> FStar_Parser_AST.term Prims.list =
  fun e  ->
    let uu____427 = (unparen e).FStar_Parser_AST.tm  in
    match uu____427 with
    | FStar_Parser_AST.Var uu____429 -> []
    | FStar_Parser_AST.App
        ({ FStar_Parser_AST.tm = FStar_Parser_AST.Var uu____430;
           FStar_Parser_AST.range = uu____431;
           FStar_Parser_AST.level = uu____432;_},{
                                                   FStar_Parser_AST.tm =
                                                     FStar_Parser_AST.App
                                                     ({
                                                        FStar_Parser_AST.tm =
                                                          FStar_Parser_AST.Var
                                                          uu____433;
                                                        FStar_Parser_AST.range
                                                          = uu____434;
                                                        FStar_Parser_AST.level
                                                          = uu____435;_},e,FStar_Parser_AST.Nothing
                                                      );
                                                   FStar_Parser_AST.range =
                                                     uu____437;
                                                   FStar_Parser_AST.level =
                                                     uu____438;_},FStar_Parser_AST.Nothing
         )
        -> [e]
    | FStar_Parser_AST.App
        ({
           FStar_Parser_AST.tm = FStar_Parser_AST.App
             ({ FStar_Parser_AST.tm = FStar_Parser_AST.Var uu____439;
                FStar_Parser_AST.range = uu____440;
                FStar_Parser_AST.level = uu____441;_},e1,FStar_Parser_AST.Nothing
              );
           FStar_Parser_AST.range = uu____443;
           FStar_Parser_AST.level = uu____444;_},e2,FStar_Parser_AST.Nothing
         )
        ->
        let _0_418 = extract_from_ref_set e1  in
        let _0_417 = extract_from_ref_set e2  in
        FStar_List.append _0_418 _0_417
    | uu____446 ->
        failwith
          (let _0_419 = FStar_Parser_AST.term_to_string e  in
           FStar_Util.format1 "Not a ref set %s" _0_419)
  
let is_general_application : FStar_Parser_AST.term -> Prims.bool =
  fun e  -> Prims.op_Negation ((is_array e) || (is_ref_set e)) 
let is_general_construction : FStar_Parser_AST.term -> Prims.bool =
  fun e  -> Prims.op_Negation ((is_list e) || (is_lex_list e)) 
let is_general_prefix_op : Prims.string -> Prims.bool = fun op  -> op <> "~" 
let head_and_args :
  FStar_Parser_AST.term ->
    (FStar_Parser_AST.term * (FStar_Parser_AST.term * FStar_Parser_AST.imp)
      Prims.list)
  =
  fun e  ->
    let rec aux e acc =
      let uu____483 = (unparen e).FStar_Parser_AST.tm  in
      match uu____483 with
      | FStar_Parser_AST.App (head,arg,imp) -> aux head ((arg, imp) :: acc)
      | uu____494 -> (e, acc)  in
    aux e []
  
type associativity =
  | Left 
  | Right 
  | NonAssoc 
let uu___is_Left : associativity -> Prims.bool =
  fun projectee  -> match projectee with | Left  -> true | uu____503 -> false 
let uu___is_Right : associativity -> Prims.bool =
  fun projectee  ->
    match projectee with | Right  -> true | uu____507 -> false
  
let uu___is_NonAssoc : associativity -> Prims.bool =
  fun projectee  ->
    match projectee with | NonAssoc  -> true | uu____511 -> false
  
type token = (FStar_Char.char,Prims.string) FStar_Util.either
type associativity_level = (associativity * token Prims.list)
let token_to_string :
  (FStar_BaseTypes.char,Prims.string) FStar_Util.either -> Prims.string =
  fun uu___128_521  ->
    match uu___128_521 with
    | FStar_Util.Inl c -> Prims.strcat (FStar_Util.string_of_char c) ".*"
    | FStar_Util.Inr s -> s
  
let matches_token :
  Prims.string ->
    (FStar_Char.char,Prims.string) FStar_Util.either -> Prims.bool
  =
  fun s  ->
    fun uu___129_533  ->
      match uu___129_533 with
      | FStar_Util.Inl c ->
          let _0_420 = FStar_String.get s (Prims.parse_int "0")  in
          _0_420 = c
      | FStar_Util.Inr s' -> s = s'
  
let matches_level s uu____554 =
  match uu____554 with
  | (assoc_levels,tokens) ->
      let _0_421 = FStar_List.tryFind (matches_token s) tokens  in
      _0_421 <> None
  
let opinfix4 uu____582 = (Right, [FStar_Util.Inr "**"]) 
let opinfix3 uu____597 =
  (Left, [FStar_Util.Inl '*'; FStar_Util.Inl '/'; FStar_Util.Inl '%']) 
let opinfix2 uu____616 = (Left, [FStar_Util.Inl '+'; FStar_Util.Inl '-']) 
let minus_lvl uu____633 = (Left, [FStar_Util.Inr "-"]) 
let opinfix1 uu____648 = (Right, [FStar_Util.Inl '@'; FStar_Util.Inl '^']) 
let pipe_right uu____665 = (Left, [FStar_Util.Inr "|>"]) 
let opinfix0d uu____680 = (Left, [FStar_Util.Inl '$']) 
let opinfix0c uu____695 =
  (Left, [FStar_Util.Inl '='; FStar_Util.Inl '<'; FStar_Util.Inl '>']) 
let equal uu____714 = (Left, [FStar_Util.Inr "="]) 
let opinfix0b uu____729 = (Left, [FStar_Util.Inl '&']) 
let opinfix0a uu____744 = (Left, [FStar_Util.Inl '|']) 
let colon_equals uu____759 = (NonAssoc, [FStar_Util.Inr ":="]) 
let amp uu____774 = (Right, [FStar_Util.Inr "&"]) 
let colon_colon uu____789 = (Right, [FStar_Util.Inr "::"]) 
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
  let levels_from_associativity l uu___130_886 =
    match uu___130_886 with
    | Left  -> (l, l, (l - (Prims.parse_int "1")))
    | Right  -> ((l - (Prims.parse_int "1")), l, l)
    | NonAssoc  -> (l, l, l)  in
  FStar_List.mapi
    (fun i  ->
       fun uu____904  ->
         match uu____904 with
         | (assoc,tokens) -> ((levels_from_associativity i assoc), tokens))
    level_associativity_spec
  
let assign_levels :
  associativity_level Prims.list ->
    Prims.string -> (Prims.int * Prims.int * Prims.int)
  =
  fun token_associativity_spec  ->
    fun s  ->
      let uu____946 = FStar_List.tryFind (matches_level s) level_table  in
      match uu____946 with
      | Some (assoc_levels,uu____971) -> assoc_levels
      | uu____992 -> failwith (Prims.strcat "Unrecognized operator " s)
  
let max : Prims.int -> Prims.int -> Prims.int =
  fun k1  -> fun k2  -> if k1 > k2 then k1 else k2 
let max_level l =
  let find_level_and_max n level =
    let uu____1048 =
      FStar_List.tryFind
        (fun uu____1066  ->
           match uu____1066 with
           | (uu____1075,tokens) -> tokens = (Prims.snd level)) level_table
       in
    match uu____1048 with
    | Some ((uu____1095,l,uu____1097),uu____1098) -> max n l
    | None  ->
        failwith
          (let _0_423 =
             let _0_422 = FStar_List.map token_to_string (Prims.snd level)
                in
             FStar_String.concat "," _0_422  in
           FStar_Util.format1 "Undefined associativity level %s" _0_423)
     in
  FStar_List.fold_left find_level_and_max (Prims.parse_int "0") l 
let levels : Prims.string -> (Prims.int * Prims.int * Prims.int) =
  assign_levels level_associativity_spec 
let operatorInfix0ad12 uu____1147 =
  [opinfix0a ();
  opinfix0b ();
  opinfix0c ();
  opinfix0d ();
  opinfix1 ();
  opinfix2 ()] 
let is_operatorInfix0ad12 : Prims.string -> Prims.bool =
  fun op  ->
    let _0_424 =
      FStar_List.tryFind (matches_level op) (operatorInfix0ad12 ())  in
    _0_424 <> None
  
let is_operatorInfix34 : Prims.string -> Prims.bool =
  let opinfix34 = [opinfix3 (); opinfix4 ()]  in
  fun op  ->
    let _0_425 = FStar_List.tryFind (matches_level op) opinfix34  in
    _0_425 <> None
  
let comment_stack :
  (Prims.string * FStar_Range.range) Prims.list FStar_ST.ref =
  FStar_Util.mk_ref [] 
let with_comment printer tm tmrange =
  let rec comments_before_pos acc print_pos lookahead_pos =
    let uu____1288 = FStar_ST.read comment_stack  in
    match uu____1288 with
    | [] -> (acc, false)
    | (comment,crange)::cs ->
        let uu____1309 = FStar_Range.range_before_pos crange print_pos  in
        if uu____1309
        then
          (FStar_ST.write comment_stack cs;
           (let _0_428 =
              let _0_427 =
                let _0_426 = str comment  in
                FStar_Pprint.op_Hat_Hat _0_426 FStar_Pprint.hardline  in
              FStar_Pprint.op_Hat_Hat acc _0_427  in
            comments_before_pos _0_428 print_pos lookahead_pos))
        else
          (let _0_429 = FStar_Range.range_before_pos crange lookahead_pos  in
           (acc, _0_429))
     in
  let uu____1319 =
    let _0_431 = FStar_Range.end_of_line (FStar_Range.start_of_range tmrange)
       in
    let _0_430 = FStar_Range.end_of_range tmrange  in
    comments_before_pos FStar_Pprint.empty _0_431 _0_430  in
  match uu____1319 with
  | (comments,has_lookahead) ->
      let printed_e = printer tm  in
      let comments =
        if has_lookahead
        then
          let pos = FStar_Range.end_of_range tmrange  in
          Prims.fst (comments_before_pos comments pos pos)
        else comments  in
      FStar_Pprint.group (FStar_Pprint.op_Hat_Hat comments printed_e)
  
let rec place_comments_until_pos :
  Prims.int ->
    Prims.int ->
      FStar_Range.pos -> FStar_Pprint.document -> FStar_Pprint.document
  =
  fun k  ->
    fun lbegin  ->
      fun pos_end  ->
        fun doc  ->
          let uu____1340 = FStar_ST.read comment_stack  in
          match uu____1340 with
          | (comment,crange)::cs when
              FStar_Range.range_before_pos crange pos_end ->
              (FStar_ST.write comment_stack cs;
               (let lnum =
                  let _0_433 =
                    let _0_432 =
                      FStar_Range.line_of_pos
                        (FStar_Range.start_of_range crange)
                       in
                    _0_432 - lbegin  in
                  max k _0_433  in
                let doc =
                  let _0_436 =
                    let _0_435 =
                      FStar_Pprint.repeat lnum FStar_Pprint.hardline  in
                    let _0_434 = str comment  in
                    FStar_Pprint.op_Hat_Hat _0_435 _0_434  in
                  FStar_Pprint.op_Hat_Hat doc _0_436  in
                let _0_437 =
                  FStar_Range.line_of_pos (FStar_Range.end_of_range crange)
                   in
                place_comments_until_pos (Prims.parse_int "1") _0_437 pos_end
                  doc))
          | uu____1365 ->
              let lnum =
                let _0_439 =
                  let _0_438 = FStar_Range.line_of_pos pos_end  in
                  _0_438 - lbegin  in
                max (Prims.parse_int "1") _0_439  in
              let _0_440 = FStar_Pprint.repeat lnum FStar_Pprint.hardline  in
              FStar_Pprint.op_Hat_Hat doc _0_440
  
let separate_map_with_comments prefix sep f xs extract_range =
  let fold_fun uu____1418 x =
    match uu____1418 with
    | (last_line,doc) ->
        let r = extract_range x  in
        let doc =
          let _0_441 = FStar_Range.start_of_range r  in
          place_comments_until_pos (Prims.parse_int "1") last_line _0_441 doc
           in
        let _0_445 = FStar_Range.line_of_pos (FStar_Range.end_of_range r)  in
        let _0_444 =
          let _0_443 =
            let _0_442 = f x  in FStar_Pprint.op_Hat_Hat sep _0_442  in
          FStar_Pprint.op_Hat_Hat doc _0_443  in
        (_0_445, _0_444)
     in
  let uu____1428 =
    let _0_447 = FStar_List.hd xs  in
    let _0_446 = FStar_List.tl xs  in (_0_447, _0_446)  in
  match uu____1428 with
  | (x,xs) ->
      let init =
        let _0_450 =
          FStar_Range.line_of_pos
            (FStar_Range.end_of_range (extract_range x))
           in
        let _0_449 =
          let _0_448 = f x  in FStar_Pprint.op_Hat_Hat prefix _0_448  in
        (_0_450, _0_449)  in
      Prims.snd (FStar_List.fold_left fold_fun init xs)
  
let rec p_decl : FStar_Parser_AST.decl -> FStar_Pprint.document =
  fun d  ->
    FStar_Pprint.group
      (let _0_457 = FStar_Pprint.optional p_fsdoc d.FStar_Parser_AST.doc  in
       let _0_456 =
         let _0_455 = p_attributes d.FStar_Parser_AST.attrs  in
         let _0_454 =
           let _0_453 = p_qualifiers d.FStar_Parser_AST.quals  in
           let _0_452 =
             let _0_451 = p_rawDecl d  in
             FStar_Pprint.op_Hat_Hat
               (if d.FStar_Parser_AST.quals = []
                then FStar_Pprint.empty
                else break1) _0_451
              in
           FStar_Pprint.op_Hat_Hat _0_453 _0_452  in
         FStar_Pprint.op_Hat_Hat _0_455 _0_454  in
       FStar_Pprint.op_Hat_Hat _0_457 _0_456)

and p_attributes : FStar_Parser_AST.attributes_ -> FStar_Pprint.document =
  fun attrs  ->
    let _0_460 =
      let _0_458 = str "@"  in
      FStar_Pprint.op_Hat_Hat FStar_Pprint.lbracket _0_458  in
    let _0_459 =
      FStar_Pprint.op_Hat_Hat FStar_Pprint.rbracket FStar_Pprint.hardline  in
    soft_surround_separate_map (Prims.parse_int "0") (Prims.parse_int "2")
      FStar_Pprint.empty _0_460 FStar_Pprint.space _0_459 p_atomicTerm attrs

and p_fsdoc : FStar_Parser_AST.fsdoc -> FStar_Pprint.document =
  fun uu____1691  ->
    match uu____1691 with
    | (doc,kwd_args) ->
        let kwd_args_doc =
          match kwd_args with
          | [] -> FStar_Pprint.empty
          | kwd_args ->
              let process_kwd_arg uu____1712 =
                match uu____1712 with
                | (kwd,arg) ->
                    let _0_465 = str "@"  in
                    let _0_464 =
                      let _0_463 = str kwd  in
                      let _0_462 =
                        let _0_461 = str arg  in
                        FStar_Pprint.op_Hat_Hat FStar_Pprint.space _0_461  in
                      FStar_Pprint.op_Hat_Hat _0_463 _0_462  in
                    FStar_Pprint.op_Hat_Hat _0_465 _0_464
                 in
              let _0_467 =
                let _0_466 =
                  FStar_Pprint.separate_map FStar_Pprint.hardline
                    process_kwd_arg kwd_args
                   in
                FStar_Pprint.op_Hat_Hat _0_466 FStar_Pprint.hardline  in
              FStar_Pprint.op_Hat_Hat FStar_Pprint.hardline _0_467
           in
        let _0_475 =
          let _0_474 =
            let _0_473 =
              let _0_472 =
                let _0_471 = str doc  in
                let _0_470 =
                  let _0_469 =
                    let _0_468 =
                      FStar_Pprint.op_Hat_Hat FStar_Pprint.rparen
                        FStar_Pprint.hardline
                       in
                    FStar_Pprint.op_Hat_Hat FStar_Pprint.star _0_468  in
                  FStar_Pprint.op_Hat_Hat kwd_args_doc _0_469  in
                FStar_Pprint.op_Hat_Hat _0_471 _0_470  in
              FStar_Pprint.op_Hat_Hat FStar_Pprint.star _0_472  in
            FStar_Pprint.op_Hat_Hat FStar_Pprint.star _0_473  in
          FStar_Pprint.op_Hat_Hat FStar_Pprint.lparen _0_474  in
        FStar_Pprint.op_Hat_Hat FStar_Pprint.hardline _0_475

and p_rawDecl : FStar_Parser_AST.decl -> FStar_Pprint.document =
  fun d  ->
    match d.FStar_Parser_AST.d with
    | FStar_Parser_AST.Open uid ->
        FStar_Pprint.group
          (let _0_477 = str "open"  in
           let _0_476 = p_quident uid  in
           FStar_Pprint.op_Hat_Slash_Hat _0_477 _0_476)
    | FStar_Parser_AST.Include uid ->
        FStar_Pprint.group
          (let _0_479 = str "include"  in
           let _0_478 = p_quident uid  in
           FStar_Pprint.op_Hat_Slash_Hat _0_479 _0_478)
    | FStar_Parser_AST.ModuleAbbrev (uid1,uid2) ->
        let _0_486 =
          let _0_484 = str "module"  in
          let _0_483 =
            let _0_482 =
              let _0_481 = p_uident uid1  in
              let _0_480 =
                FStar_Pprint.op_Hat_Hat FStar_Pprint.space
                  FStar_Pprint.equals
                 in
              FStar_Pprint.op_Hat_Hat _0_481 _0_480  in
            FStar_Pprint.op_Hat_Hat FStar_Pprint.space _0_482  in
          FStar_Pprint.op_Hat_Hat _0_484 _0_483  in
        let _0_485 = p_quident uid2  in op_Hat_Slash_Plus_Hat _0_486 _0_485
    | FStar_Parser_AST.TopLevelModule uid ->
        FStar_Pprint.group
          (let _0_489 = str "module"  in
           let _0_488 =
             let _0_487 = p_quident uid  in
             FStar_Pprint.op_Hat_Hat FStar_Pprint.space _0_487  in
           FStar_Pprint.op_Hat_Hat _0_489 _0_488)
    | FStar_Parser_AST.Tycon
        (true ,(FStar_Parser_AST.TyconAbbrev (uid,tpars,None ,t),None )::[])
        ->
        let effect_prefix_doc =
          let _0_492 = str "effect"  in
          let _0_491 =
            let _0_490 = p_uident uid  in
            FStar_Pprint.op_Hat_Hat FStar_Pprint.space _0_490  in
          FStar_Pprint.op_Hat_Hat _0_492 _0_491  in
        let _0_495 =
          let _0_493 = p_typars tpars  in
          FStar_Pprint.surround (Prims.parse_int "2") (Prims.parse_int "1")
            effect_prefix_doc _0_493 FStar_Pprint.equals
           in
        let _0_494 = p_typ t  in op_Hat_Slash_Plus_Hat _0_495 _0_494
    | FStar_Parser_AST.Tycon (false ,tcdefs) ->
        let _0_497 = str "type"  in
        let _0_496 = str "and"  in
        precede_break_separate_map _0_497 _0_496 p_fsdocTypeDeclPairs tcdefs
    | FStar_Parser_AST.TopLevelLet (q,lbs) ->
        let let_doc =
          let _0_500 = str "let"  in
          let _0_499 =
            let _0_498 = p_letqualifier q  in
            FStar_Pprint.op_Hat_Hat _0_498 FStar_Pprint.space  in
          FStar_Pprint.op_Hat_Hat _0_500 _0_499  in
        let _0_502 =
          let _0_501 = str "and"  in
          FStar_Pprint.op_Hat_Hat _0_501 FStar_Pprint.space  in
        separate_map_with_comments let_doc _0_502 p_letbinding lbs
          (fun uu____1766  ->
             match uu____1766 with
             | (p,t) ->
                 FStar_Range.union_ranges p.FStar_Parser_AST.prange
                   t.FStar_Parser_AST.range)
    | FStar_Parser_AST.Val (lid,t) ->
        let _0_509 =
          let _0_507 = str "val"  in
          let _0_506 =
            let _0_505 =
              let _0_504 = p_lident lid  in
              let _0_503 =
                FStar_Pprint.op_Hat_Hat FStar_Pprint.space FStar_Pprint.colon
                 in
              FStar_Pprint.op_Hat_Hat _0_504 _0_503  in
            FStar_Pprint.op_Hat_Hat FStar_Pprint.space _0_505  in
          FStar_Pprint.op_Hat_Hat _0_507 _0_506  in
        let _0_508 = p_typ t  in op_Hat_Slash_Plus_Hat _0_509 _0_508
    | FStar_Parser_AST.Assume (id,t) ->
        let decl_keyword =
          let uu____1776 =
            let _0_510 =
              FStar_Util.char_at id.FStar_Ident.idText (Prims.parse_int "0")
               in
            FStar_All.pipe_right _0_510 FStar_Util.is_upper  in
          if uu____1776
          then FStar_Pprint.empty
          else
            (let _0_511 = str "val"  in
             FStar_Pprint.op_Hat_Hat _0_511 FStar_Pprint.space)
           in
        let _0_516 =
          let _0_514 =
            let _0_513 = p_ident id  in
            let _0_512 =
              FStar_Pprint.op_Hat_Hat FStar_Pprint.space FStar_Pprint.colon
               in
            FStar_Pprint.op_Hat_Hat _0_513 _0_512  in
          FStar_Pprint.op_Hat_Hat decl_keyword _0_514  in
        let _0_515 = p_typ t  in op_Hat_Slash_Plus_Hat _0_516 _0_515
    | FStar_Parser_AST.Exception (uid,t_opt) ->
        let _0_523 = str "exception"  in
        let _0_522 =
          let _0_521 =
            let _0_520 = p_uident uid  in
            let _0_519 =
              FStar_Pprint.optional
                (fun t  ->
                   let _0_518 = str "of"  in
                   let _0_517 = p_typ t  in
                   op_Hat_Slash_Plus_Hat _0_518 _0_517) t_opt
               in
            FStar_Pprint.op_Hat_Hat _0_520 _0_519  in
          FStar_Pprint.op_Hat_Hat FStar_Pprint.space _0_521  in
        FStar_Pprint.op_Hat_Hat _0_523 _0_522
    | FStar_Parser_AST.NewEffect ne ->
        let _0_526 = str "new_effect"  in
        let _0_525 =
          let _0_524 = p_newEffect ne  in
          FStar_Pprint.op_Hat_Hat FStar_Pprint.space _0_524  in
        FStar_Pprint.op_Hat_Hat _0_526 _0_525
    | FStar_Parser_AST.SubEffect se ->
        let _0_529 = str "sub_effect"  in
        let _0_528 =
          let _0_527 = p_subEffect se  in
          FStar_Pprint.op_Hat_Hat FStar_Pprint.space _0_527  in
        FStar_Pprint.op_Hat_Hat _0_529 _0_528
    | FStar_Parser_AST.NewEffectForFree ne ->
        let _0_532 = str "new_effect_for_free"  in
        let _0_531 =
          let _0_530 = p_newEffect ne  in
          FStar_Pprint.op_Hat_Hat FStar_Pprint.space _0_530  in
        FStar_Pprint.op_Hat_Hat _0_532 _0_531
    | FStar_Parser_AST.Pragma p -> p_pragma p
    | FStar_Parser_AST.Fsdoc doc ->
        let _0_533 = p_fsdoc doc  in
        FStar_Pprint.op_Hat_Hat _0_533 FStar_Pprint.hardline
    | FStar_Parser_AST.Main uu____1788 ->
        failwith "*Main declaration* : Is that really still in use ??"
    | FStar_Parser_AST.Tycon (true ,uu____1789) ->
        failwith
          "Effect abbreviation is expected to be defined by an abbreviation"

and p_pragma : FStar_Parser_AST.pragma -> FStar_Pprint.document =
  fun uu___131_1798  ->
    match uu___131_1798 with
    | FStar_Parser_AST.SetOptions s ->
        let _0_536 = str "#set-options"  in
        let _0_535 =
          let _0_534 = FStar_Pprint.dquotes (str s)  in
          FStar_Pprint.op_Hat_Hat FStar_Pprint.space _0_534  in
        FStar_Pprint.op_Hat_Hat _0_536 _0_535
    | FStar_Parser_AST.ResetOptions s_opt ->
        let _0_539 = str "#reset-options"  in
        let _0_538 =
          FStar_Pprint.optional
            (fun s  ->
               let _0_537 = FStar_Pprint.dquotes (str s)  in
               FStar_Pprint.op_Hat_Hat FStar_Pprint.space _0_537) s_opt
           in
        FStar_Pprint.op_Hat_Hat _0_539 _0_538
    | FStar_Parser_AST.LightOff  ->
        (FStar_ST.write should_print_fs_typ_app true; str "#light \"off\"")

and p_typars : FStar_Parser_AST.binder Prims.list -> FStar_Pprint.document =
  fun bs  -> p_binders true bs

and p_fsdocTypeDeclPairs :
  (FStar_Parser_AST.tycon * FStar_Parser_AST.fsdoc Prims.option) ->
    FStar_Pprint.document
  =
  fun uu____1808  ->
    match uu____1808 with
    | (typedecl,fsdoc_opt) ->
        let _0_541 = FStar_Pprint.optional p_fsdoc fsdoc_opt  in
        let _0_540 = p_typeDecl typedecl  in
        FStar_Pprint.op_Hat_Hat _0_541 _0_540

and p_typeDecl : FStar_Parser_AST.tycon -> FStar_Pprint.document =
  fun uu___132_1816  ->
    match uu___132_1816 with
    | FStar_Parser_AST.TyconAbstract (lid,bs,typ_opt) ->
        let empty' uu____1827 = FStar_Pprint.empty  in
        p_typeDeclPrefix lid bs typ_opt empty'
    | FStar_Parser_AST.TyconAbbrev (lid,bs,typ_opt,t) ->
        let f uu____1839 =
          let _0_542 = p_typ t  in prefix2 FStar_Pprint.equals _0_542  in
        p_typeDeclPrefix lid bs typ_opt f
    | FStar_Parser_AST.TyconRecord (lid,bs,typ_opt,record_field_decls) ->
        let p_recordFieldAndComments uu____1865 =
          match uu____1865 with
          | (lid,t,doc_opt) ->
              let _0_543 =
                FStar_Range.extend_to_end_of_line t.FStar_Parser_AST.range
                 in
              with_comment p_recordFieldDecl (lid, t, doc_opt) _0_543
           in
        let p_fields uu____1883 =
          let _0_546 =
            let _0_545 =
              braces_with_nesting
                (let _0_544 =
                   FStar_Pprint.op_Hat_Hat FStar_Pprint.semi break1  in
                 FStar_Pprint.separate_map _0_544 p_recordFieldAndComments
                   record_field_decls)
               in
            FStar_Pprint.op_Hat_Hat FStar_Pprint.space _0_545  in
          FStar_Pprint.op_Hat_Hat FStar_Pprint.equals _0_546  in
        p_typeDeclPrefix lid bs typ_opt p_fields
    | FStar_Parser_AST.TyconVariant (lid,bs,typ_opt,ct_decls) ->
        let p_constructorBranchAndComments uu____1919 =
          match uu____1919 with
          | (uid,t_opt,doc_opt,use_of) ->
              let range =
                FStar_Range.extend_to_end_of_line
                  (let _0_547 =
                     FStar_Util.map_opt t_opt
                       (fun t  -> t.FStar_Parser_AST.range)
                      in
                   FStar_Util.dflt uid.FStar_Ident.idRange _0_547)
                 in
              let p_constructorBranch decl =
                FStar_Pprint.group
                  (let _0_549 =
                     let _0_548 = p_constructorDecl decl  in
                     FStar_Pprint.op_Hat_Hat FStar_Pprint.space _0_548  in
                   FStar_Pprint.op_Hat_Hat FStar_Pprint.bar _0_549)
                 in
              with_comment p_constructorBranch (uid, t_opt, doc_opt, use_of)
                range
           in
        let datacon_doc uu____1963 =
          FStar_Pprint.group
            (FStar_Pprint.separate_map break1 p_constructorBranchAndComments
               ct_decls)
           in
        p_typeDeclPrefix lid bs typ_opt
          (fun uu____1970  ->
             let _0_550 = datacon_doc ()  in
             prefix2 FStar_Pprint.equals _0_550)

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
            let _0_553 = p_ident lid  in
            let _0_552 =
              let _0_551 = cont ()  in
              FStar_Pprint.op_Hat_Hat FStar_Pprint.space _0_551  in
            FStar_Pprint.op_Hat_Hat _0_553 _0_552
          else
            (let binders_doc =
               let _0_558 = p_typars bs  in
               let _0_557 =
                 FStar_Pprint.optional
                   (fun t  ->
                      let _0_556 =
                        let _0_555 =
                          let _0_554 = p_typ t  in
                          FStar_Pprint.op_Hat_Hat FStar_Pprint.space _0_554
                           in
                        FStar_Pprint.op_Hat_Hat FStar_Pprint.colon _0_555  in
                      FStar_Pprint.op_Hat_Hat break1 _0_556) typ_opt
                  in
               FStar_Pprint.op_Hat_Hat _0_558 _0_557  in
             let _0_560 = p_ident lid  in
             let _0_559 = cont ()  in
             FStar_Pprint.surround (Prims.parse_int "2")
               (Prims.parse_int "1") _0_560 binders_doc _0_559)

and p_recordFieldDecl :
  (FStar_Ident.ident * FStar_Parser_AST.term * FStar_Parser_AST.fsdoc
    Prims.option) -> FStar_Pprint.document
  =
  fun uu____1984  ->
    match uu____1984 with
    | (lid,t,doc_opt) ->
        FStar_Pprint.group
          (let _0_565 = FStar_Pprint.optional p_fsdoc doc_opt  in
           let _0_564 =
             let _0_563 = p_lident lid  in
             let _0_562 =
               let _0_561 = p_typ t  in
               FStar_Pprint.op_Hat_Hat FStar_Pprint.colon _0_561  in
             FStar_Pprint.op_Hat_Hat _0_563 _0_562  in
           FStar_Pprint.op_Hat_Hat _0_565 _0_564)

and p_constructorDecl :
  (FStar_Ident.ident * FStar_Parser_AST.term Prims.option *
    FStar_Parser_AST.fsdoc Prims.option * Prims.bool) ->
    FStar_Pprint.document
  =
  fun uu____1994  ->
    match uu____1994 with
    | (uid,t_opt,doc_opt,use_of) ->
        let sep = if use_of then str "of" else FStar_Pprint.colon  in
        let uid_doc = p_uident uid  in
        let _0_572 = FStar_Pprint.optional p_fsdoc doc_opt  in
        let _0_571 =
          let _0_570 = FStar_Pprint.break_ (Prims.parse_int "0")  in
          let _0_569 =
            default_or_map uid_doc
              (fun t  ->
                 let _0_568 =
                   let _0_566 =
                     FStar_Pprint.op_Hat_Hat FStar_Pprint.space sep  in
                   FStar_Pprint.op_Hat_Hat uid_doc _0_566  in
                 let _0_567 = p_typ t  in op_Hat_Slash_Plus_Hat _0_568 _0_567)
              t_opt
             in
          FStar_Pprint.op_Hat_Hat _0_570 _0_569  in
        FStar_Pprint.op_Hat_Hat _0_572 _0_571

and p_letbinding :
  (FStar_Parser_AST.pattern * FStar_Parser_AST.term) -> FStar_Pprint.document
  =
  fun uu____2013  ->
    match uu____2013 with
    | (pat,e) ->
        let pat_doc =
          let uu____2019 =
            match pat.FStar_Parser_AST.pat with
            | FStar_Parser_AST.PatAscribed (pat,t) ->
                let _0_576 =
                  let _0_575 =
                    FStar_Pprint.group
                      (let _0_574 =
                         let _0_573 = p_tmArrow p_tmNoEq t  in
                         FStar_Pprint.op_Hat_Hat FStar_Pprint.space _0_573
                          in
                       FStar_Pprint.op_Hat_Hat FStar_Pprint.colon _0_574)
                     in
                  FStar_Pprint.op_Hat_Hat break1 _0_575  in
                (pat, _0_576)
            | uu____2026 -> (pat, FStar_Pprint.empty)  in
          match uu____2019 with
          | (pat,ascr_doc) ->
              (match pat.FStar_Parser_AST.pat with
               | FStar_Parser_AST.PatApp
                   ({
                      FStar_Parser_AST.pat = FStar_Parser_AST.PatVar
                        (x,uu____2030);
                      FStar_Parser_AST.prange = uu____2031;_},pats)
                   ->
                   let _0_579 = p_lident x  in
                   let _0_578 =
                     let _0_577 =
                       FStar_Pprint.separate_map break1 p_atomicPattern pats
                        in
                     FStar_Pprint.op_Hat_Hat _0_577 ascr_doc  in
                   FStar_Pprint.surround (Prims.parse_int "2")
                     (Prims.parse_int "1") _0_579 _0_578 FStar_Pprint.equals
               | uu____2037 ->
                   FStar_Pprint.group
                     (let _0_581 = p_tuplePattern pat  in
                      let _0_580 =
                        FStar_Pprint.op_Hat_Slash_Hat ascr_doc
                          FStar_Pprint.equals
                         in
                      FStar_Pprint.op_Hat_Hat _0_581 _0_580))
           in
        let _0_582 = p_term e  in prefix2 pat_doc _0_582

and p_newEffect : FStar_Parser_AST.effect_decl -> FStar_Pprint.document =
  fun uu___133_2038  ->
    match uu___133_2038 with
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
        let _0_586 = p_uident uid  in
        let _0_585 = p_binders true bs  in
        let _0_584 =
          let _0_583 = p_simpleTerm t  in prefix2 FStar_Pprint.equals _0_583
           in
        FStar_Pprint.surround (Prims.parse_int "2") (Prims.parse_int "1")
          _0_586 _0_585 _0_584

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
            braces_with_nesting
              (let _0_596 =
                 FStar_Pprint.group
                   (let _0_590 = p_uident uid  in
                    let _0_589 = p_binders true bs  in
                    let _0_588 =
                      let _0_587 = p_typ t  in
                      prefix2 FStar_Pprint.colon _0_587  in
                    FStar_Pprint.surround (Prims.parse_int "2")
                      (Prims.parse_int "1") _0_590 _0_589 _0_588)
                  in
               let _0_595 =
                 let _0_594 =
                   let _0_592 = str "with"  in
                   let _0_591 =
                     separate_break_map FStar_Pprint.semi p_effectDecl
                       eff_decls
                      in
                   prefix2 _0_592 _0_591  in
                 let _0_593 = p_actionDecls action_decls  in
                 FStar_Pprint.op_Hat_Hat _0_594 _0_593  in
               FStar_Pprint.op_Hat_Slash_Hat _0_596 _0_595)

and p_actionDecls : FStar_Parser_AST.decl Prims.list -> FStar_Pprint.document
  =
  fun uu___134_2067  ->
    match uu___134_2067 with
    | [] -> FStar_Pprint.empty
    | l ->
        let _0_599 =
          let _0_598 = str "and actions"  in
          let _0_597 = separate_break_map FStar_Pprint.semi p_effectDecl l
             in
          prefix2 _0_598 _0_597  in
        FStar_Pprint.op_Hat_Hat break1 _0_599

and p_effectDecl : FStar_Parser_AST.decl -> FStar_Pprint.document =
  fun d  ->
    match d.FStar_Parser_AST.d with
    | FStar_Parser_AST.Tycon
        (false ,(FStar_Parser_AST.TyconAbbrev (lid,[],None ,e),None )::[]) ->
        let _0_603 =
          let _0_601 = p_lident lid  in
          let _0_600 =
            FStar_Pprint.op_Hat_Hat FStar_Pprint.space FStar_Pprint.equals
             in
          FStar_Pprint.op_Hat_Hat _0_601 _0_600  in
        let _0_602 = p_simpleTerm e  in prefix2 _0_603 _0_602
    | uu____2087 ->
        failwith
          (let _0_604 = FStar_Parser_AST.decl_to_string d  in
           FStar_Util.format1
             "Not a declaration of an effect member... or at least I hope so : %s"
             _0_604)

and p_subEffect : FStar_Parser_AST.lift -> FStar_Pprint.document =
  fun lift  ->
    let lift_op_doc =
      let lifts =
        match lift.FStar_Parser_AST.lift_op with
        | FStar_Parser_AST.NonReifiableLift t -> [("lift_wp", t)]
        | FStar_Parser_AST.ReifiableLift (t1,t2) ->
            [("lif_wp", t1); ("lift", t2)]
        | FStar_Parser_AST.LiftForFree t -> [("lift", t)]  in
      let p_lift uu____2120 =
        match uu____2120 with
        | (kwd,t) ->
            let _0_608 =
              let _0_606 = str kwd  in
              let _0_605 =
                FStar_Pprint.op_Hat_Hat FStar_Pprint.space
                  FStar_Pprint.equals
                 in
              FStar_Pprint.op_Hat_Hat _0_606 _0_605  in
            let _0_607 = p_simpleTerm t  in prefix2 _0_608 _0_607
         in
      separate_break_map FStar_Pprint.semi p_lift lifts  in
    let _0_616 =
      let _0_613 =
        let _0_611 = p_quident lift.FStar_Parser_AST.msource  in
        let _0_610 =
          let _0_609 = str "~>"  in
          FStar_Pprint.op_Hat_Hat FStar_Pprint.space _0_609  in
        FStar_Pprint.op_Hat_Hat _0_611 _0_610  in
      let _0_612 = p_quident lift.FStar_Parser_AST.mdest  in
      prefix2 _0_613 _0_612  in
    let _0_615 =
      let _0_614 = braces_with_nesting lift_op_doc  in
      FStar_Pprint.op_Hat_Hat FStar_Pprint.space _0_614  in
    FStar_Pprint.op_Hat_Hat _0_616 _0_615

and p_qualifier : FStar_Parser_AST.qualifier -> FStar_Pprint.document =
  fun uu___135_2127  ->
    match uu___135_2127 with
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
    FStar_Pprint.group (FStar_Pprint.separate_map break1 p_qualifier qs)

and p_letqualifier : FStar_Parser_AST.let_qualifier -> FStar_Pprint.document
  =
  fun uu___136_2129  ->
    match uu___136_2129 with
    | FStar_Parser_AST.Rec  ->
        let _0_617 = str "rec"  in
        FStar_Pprint.op_Hat_Hat FStar_Pprint.space _0_617
    | FStar_Parser_AST.Mutable  ->
        let _0_618 = str "mutable"  in
        FStar_Pprint.op_Hat_Hat FStar_Pprint.space _0_618
    | FStar_Parser_AST.NoLetQualifier  -> FStar_Pprint.empty

and p_aqual : FStar_Parser_AST.arg_qualifier -> FStar_Pprint.document =
  fun uu___137_2130  ->
    match uu___137_2130 with
    | FStar_Parser_AST.Implicit  -> str "#"
    | FStar_Parser_AST.Equality  -> str "$"

and p_disjunctivePattern : FStar_Parser_AST.pattern -> FStar_Pprint.document
  =
  fun p  ->
    match p.FStar_Parser_AST.pat with
    | FStar_Parser_AST.PatOr pats ->
        FStar_Pprint.group
          (let _0_620 =
             let _0_619 =
               FStar_Pprint.op_Hat_Hat FStar_Pprint.bar FStar_Pprint.space
                in
             FStar_Pprint.op_Hat_Hat break1 _0_619  in
           FStar_Pprint.separate_map _0_620 p_tuplePattern pats)
    | uu____2134 -> p_tuplePattern p

and p_tuplePattern : FStar_Parser_AST.pattern -> FStar_Pprint.document =
  fun p  ->
    match p.FStar_Parser_AST.pat with
    | FStar_Parser_AST.PatTuple (pats,false ) ->
        FStar_Pprint.group
          (let _0_621 = FStar_Pprint.op_Hat_Hat FStar_Pprint.comma break1  in
           FStar_Pprint.separate_map _0_621 p_constructorPattern pats)
    | uu____2139 -> p_constructorPattern p

and p_constructorPattern : FStar_Parser_AST.pattern -> FStar_Pprint.document
  =
  fun p  ->
    match p.FStar_Parser_AST.pat with
    | FStar_Parser_AST.PatApp
        ({ FStar_Parser_AST.pat = FStar_Parser_AST.PatName maybe_cons_lid;
           FStar_Parser_AST.prange = uu____2142;_},hd::tl::[])
        when
        FStar_Ident.lid_equals maybe_cons_lid FStar_Syntax_Const.cons_lid ->
        let _0_624 =
          FStar_Pprint.op_Hat_Hat FStar_Pprint.colon FStar_Pprint.colon  in
        let _0_623 = p_constructorPattern hd  in
        let _0_622 = p_constructorPattern tl  in infix0 _0_624 _0_623 _0_622
    | FStar_Parser_AST.PatApp
        ({ FStar_Parser_AST.pat = FStar_Parser_AST.PatName uid;
           FStar_Parser_AST.prange = uu____2147;_},pats)
        ->
        let _0_626 = p_quident uid  in
        let _0_625 = FStar_Pprint.separate_map break1 p_atomicPattern pats
           in
        prefix2 _0_626 _0_625
    | uu____2151 -> p_atomicPattern p

and p_atomicPattern : FStar_Parser_AST.pattern -> FStar_Pprint.document =
  fun p  ->
    match p.FStar_Parser_AST.pat with
    | FStar_Parser_AST.PatAscribed (pat,t) ->
        let uu____2155 =
          let _0_627 = (unparen t).FStar_Parser_AST.tm  in
          ((pat.FStar_Parser_AST.pat), _0_627)  in
        (match uu____2155 with
         | (FStar_Parser_AST.PatVar (lid,aqual),FStar_Parser_AST.Refine
            ({ FStar_Parser_AST.b = FStar_Parser_AST.Annotated (lid',t);
               FStar_Parser_AST.brange = uu____2162;
               FStar_Parser_AST.blevel = uu____2163;
               FStar_Parser_AST.aqual = uu____2164;_},phi))
             when lid.FStar_Ident.idText = lid'.FStar_Ident.idText ->
             soft_parens_with_nesting
               (let _0_628 = p_ident lid  in p_refinement aqual _0_628 t phi)
         | (FStar_Parser_AST.PatWild ,FStar_Parser_AST.Refine
            ({ FStar_Parser_AST.b = FStar_Parser_AST.NoName t;
               FStar_Parser_AST.brange = uu____2169;
               FStar_Parser_AST.blevel = uu____2170;
               FStar_Parser_AST.aqual = uu____2171;_},phi))
             ->
             soft_parens_with_nesting
               (p_refinement None FStar_Pprint.underscore t phi)
         | uu____2173 ->
             soft_parens_with_nesting
               (let _0_633 = p_tuplePattern pat  in
                let _0_632 =
                  let _0_631 = FStar_Pprint.break_ (Prims.parse_int "0")  in
                  let _0_630 =
                    let _0_629 = p_typ t  in
                    FStar_Pprint.op_Hat_Hat FStar_Pprint.colon _0_629  in
                  FStar_Pprint.op_Hat_Hat _0_631 _0_630  in
                FStar_Pprint.op_Hat_Hat _0_633 _0_632))
    | FStar_Parser_AST.PatList pats ->
        let _0_634 = separate_break_map FStar_Pprint.semi p_tuplePattern pats
           in
        FStar_Pprint.surround (Prims.parse_int "2") (Prims.parse_int "0")
          FStar_Pprint.lbracket _0_634 FStar_Pprint.rbracket
    | FStar_Parser_AST.PatRecord pats ->
        let p_recordFieldPat uu____2187 =
          match uu____2187 with
          | (lid,pat) ->
              let _0_636 = p_qlident lid  in
              let _0_635 = p_tuplePattern pat  in
              infix2 FStar_Pprint.equals _0_636 _0_635
           in
        soft_braces_with_nesting
          (separate_break_map FStar_Pprint.semi p_recordFieldPat pats)
    | FStar_Parser_AST.PatTuple (pats,true ) ->
        let _0_639 =
          FStar_Pprint.op_Hat_Hat FStar_Pprint.lparen FStar_Pprint.bar  in
        let _0_638 =
          separate_break_map FStar_Pprint.comma p_constructorPattern pats  in
        let _0_637 =
          FStar_Pprint.op_Hat_Hat FStar_Pprint.bar FStar_Pprint.rparen  in
        FStar_Pprint.surround (Prims.parse_int "2") (Prims.parse_int "1")
          _0_639 _0_638 _0_637
    | FStar_Parser_AST.PatTvar (tv,arg_qualifier_opt) -> p_tvar tv
    | FStar_Parser_AST.PatOp op ->
        let _0_643 =
          let _0_642 =
            let _0_641 = str op  in
            let _0_640 =
              FStar_Pprint.op_Hat_Hat FStar_Pprint.space FStar_Pprint.rparen
               in
            FStar_Pprint.op_Hat_Hat _0_641 _0_640  in
          FStar_Pprint.op_Hat_Hat FStar_Pprint.space _0_642  in
        FStar_Pprint.op_Hat_Hat FStar_Pprint.lparen _0_643
    | FStar_Parser_AST.PatWild  -> FStar_Pprint.underscore
    | FStar_Parser_AST.PatConst c -> p_constant c
    | FStar_Parser_AST.PatVar (lid,aqual) ->
        let _0_645 = FStar_Pprint.optional p_aqual aqual  in
        let _0_644 = p_lident lid  in FStar_Pprint.op_Hat_Hat _0_645 _0_644
    | FStar_Parser_AST.PatName uid -> p_quident uid
    | FStar_Parser_AST.PatOr uu____2209 -> failwith "Inner or pattern !"
    | FStar_Parser_AST.PatApp
      ({ FStar_Parser_AST.pat = FStar_Parser_AST.PatName _;
         FStar_Parser_AST.prange = _;_},_)|FStar_Parser_AST.PatTuple
      (_,false ) -> soft_parens_with_nesting (p_tuplePattern p)
    | uu____2217 ->
        failwith
          (let _0_646 = FStar_Parser_AST.pat_to_string p  in
           FStar_Util.format1 "Invalid pattern %s" _0_646)

and p_binder : Prims.bool -> FStar_Parser_AST.binder -> FStar_Pprint.document
  =
  fun is_atomic  ->
    fun b  ->
      match b.FStar_Parser_AST.b with
      | FStar_Parser_AST.Variable lid ->
          let _0_648 = FStar_Pprint.optional p_aqual b.FStar_Parser_AST.aqual
             in
          let _0_647 = p_lident lid  in FStar_Pprint.op_Hat_Hat _0_648 _0_647
      | FStar_Parser_AST.TVariable lid -> p_lident lid
      | FStar_Parser_AST.Annotated (lid,t) ->
          let doc =
            let uu____2225 = (unparen t).FStar_Parser_AST.tm  in
            match uu____2225 with
            | FStar_Parser_AST.Refine
                ({ FStar_Parser_AST.b = FStar_Parser_AST.Annotated (lid',t);
                   FStar_Parser_AST.brange = uu____2228;
                   FStar_Parser_AST.blevel = uu____2229;
                   FStar_Parser_AST.aqual = uu____2230;_},phi)
                when lid.FStar_Ident.idText = lid'.FStar_Ident.idText ->
                let _0_649 = p_ident lid  in
                p_refinement b.FStar_Parser_AST.aqual _0_649 t phi
            | uu____2232 ->
                let _0_656 =
                  FStar_Pprint.optional p_aqual b.FStar_Parser_AST.aqual  in
                let _0_655 =
                  let _0_654 = p_lident lid  in
                  let _0_653 =
                    let _0_652 =
                      let _0_651 = FStar_Pprint.break_ (Prims.parse_int "0")
                         in
                      let _0_650 = p_tmFormula t  in
                      FStar_Pprint.op_Hat_Hat _0_651 _0_650  in
                    FStar_Pprint.op_Hat_Hat FStar_Pprint.colon _0_652  in
                  FStar_Pprint.op_Hat_Hat _0_654 _0_653  in
                FStar_Pprint.op_Hat_Hat _0_656 _0_655
             in
          if is_atomic
          then
            FStar_Pprint.group
              (let _0_657 = FStar_Pprint.op_Hat_Hat doc FStar_Pprint.rparen
                  in
               FStar_Pprint.op_Hat_Hat FStar_Pprint.lparen _0_657)
          else FStar_Pprint.group doc
      | FStar_Parser_AST.TAnnotated uu____2234 ->
          failwith "Is this still used ?"
      | FStar_Parser_AST.NoName t ->
          let uu____2238 = (unparen t).FStar_Parser_AST.tm  in
          (match uu____2238 with
           | FStar_Parser_AST.Refine
               ({ FStar_Parser_AST.b = FStar_Parser_AST.NoName t;
                  FStar_Parser_AST.brange = uu____2240;
                  FStar_Parser_AST.blevel = uu____2241;
                  FStar_Parser_AST.aqual = uu____2242;_},phi)
               ->
               if is_atomic
               then
                 FStar_Pprint.group
                   (let _0_659 =
                      let _0_658 =
                        p_refinement b.FStar_Parser_AST.aqual
                          FStar_Pprint.underscore t phi
                         in
                      FStar_Pprint.op_Hat_Hat _0_658 FStar_Pprint.rparen  in
                    FStar_Pprint.op_Hat_Hat FStar_Pprint.lparen _0_659)
               else
                 FStar_Pprint.group
                   (p_refinement b.FStar_Parser_AST.aqual
                      FStar_Pprint.underscore t phi)
           | uu____2245 -> if is_atomic then p_atomicTerm t else p_appTerm t)

and p_refinement :
  FStar_Parser_AST.arg_qualifier Prims.option ->
    FStar_Pprint.document ->
      FStar_Parser_AST.term -> FStar_Parser_AST.term -> FStar_Pprint.document
  =
  fun aqual_opt  ->
    fun binder  ->
      fun t  ->
        fun phi  ->
          let _0_665 = FStar_Pprint.optional p_aqual aqual_opt  in
          let _0_664 =
            let _0_663 =
              let _0_662 =
                let _0_661 = p_appTerm t  in
                let _0_660 = soft_braces_with_nesting (p_noSeqTerm phi)  in
                FStar_Pprint.op_Hat_Hat _0_661 _0_660  in
              FStar_Pprint.op_Hat_Hat FStar_Pprint.colon _0_662  in
            FStar_Pprint.op_Hat_Hat binder _0_663  in
          FStar_Pprint.op_Hat_Hat _0_665 _0_664

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
    let uu____2264 = (unparen e).FStar_Parser_AST.tm  in
    match uu____2264 with
    | FStar_Parser_AST.Seq (e1,e2) ->
        let _0_668 =
          FStar_Pprint.group
            (let _0_666 = p_noSeqTerm e1  in
             FStar_Pprint.op_Hat_Hat _0_666 FStar_Pprint.semi)
           in
        let _0_667 = p_term e2  in
        FStar_Pprint.op_Hat_Slash_Hat _0_668 _0_667
    | uu____2267 -> FStar_Pprint.group (p_noSeqTerm e)

and p_noSeqTerm : FStar_Parser_AST.term -> FStar_Pprint.document =
  fun e  -> with_comment p_noSeqTerm' e e.FStar_Parser_AST.range

and p_noSeqTerm' : FStar_Parser_AST.term -> FStar_Pprint.document =
  fun e  ->
    let uu____2270 = (unparen e).FStar_Parser_AST.tm  in
    match uu____2270 with
    | FStar_Parser_AST.Ascribed (e,t) ->
        FStar_Pprint.group
          (let _0_672 = p_tmIff e  in
           let _0_671 =
             let _0_670 =
               let _0_669 = p_typ t  in
               FStar_Pprint.op_Hat_Slash_Hat FStar_Pprint.colon _0_669  in
             FStar_Pprint.op_Hat_Hat FStar_Pprint.langle _0_670  in
           FStar_Pprint.op_Hat_Slash_Hat _0_672 _0_671)
    | FStar_Parser_AST.Op (op,e1::e2::e3::[]) when op = ".()<-" ->
        FStar_Pprint.group
          (let _0_679 =
             FStar_Pprint.group
               (let _0_677 = p_atomicTermNotQUident e1  in
                let _0_676 =
                  let _0_675 =
                    let _0_674 = soft_parens_with_nesting (p_term e2)  in
                    let _0_673 =
                      FStar_Pprint.op_Hat_Hat FStar_Pprint.space
                        FStar_Pprint.larrow
                       in
                    FStar_Pprint.op_Hat_Hat _0_674 _0_673  in
                  FStar_Pprint.op_Hat_Hat FStar_Pprint.dot _0_675  in
                FStar_Pprint.op_Hat_Hat _0_677 _0_676)
              in
           let _0_678 = jump2 (p_noSeqTerm e3)  in
           FStar_Pprint.op_Hat_Hat _0_679 _0_678)
    | FStar_Parser_AST.Op (op,e1::e2::e3::[]) when op = ".[]<-" ->
        FStar_Pprint.group
          (let _0_686 =
             FStar_Pprint.group
               (let _0_684 = p_atomicTermNotQUident e1  in
                let _0_683 =
                  let _0_682 =
                    let _0_681 = soft_brackets_with_nesting (p_term e2)  in
                    let _0_680 =
                      FStar_Pprint.op_Hat_Hat FStar_Pprint.space
                        FStar_Pprint.larrow
                       in
                    FStar_Pprint.op_Hat_Hat _0_681 _0_680  in
                  FStar_Pprint.op_Hat_Hat FStar_Pprint.dot _0_682  in
                FStar_Pprint.op_Hat_Hat _0_684 _0_683)
              in
           let _0_685 = jump2 (p_noSeqTerm e3)  in
           FStar_Pprint.op_Hat_Hat _0_686 _0_685)
    | FStar_Parser_AST.Requires (e,wtf) ->
        FStar_Pprint.group
          (let _0_688 = str "requires"  in
           let _0_687 = p_typ e  in
           FStar_Pprint.op_Hat_Slash_Hat _0_688 _0_687)
    | FStar_Parser_AST.Ensures (e,wtf) ->
        FStar_Pprint.group
          (let _0_690 = str "ensures"  in
           let _0_689 = p_typ e  in
           FStar_Pprint.op_Hat_Slash_Hat _0_690 _0_689)
    | FStar_Parser_AST.Attributes es ->
        FStar_Pprint.group
          (let _0_692 = str "attributes"  in
           let _0_691 = FStar_Pprint.separate_map break1 p_atomicTerm es  in
           FStar_Pprint.op_Hat_Slash_Hat _0_692 _0_691)
    | FStar_Parser_AST.If (e1,e2,e3) ->
        let uu____2298 = is_unit e3  in
        if uu____2298
        then
          FStar_Pprint.group
            (let _0_698 =
               let _0_694 = str "if"  in
               let _0_693 = p_noSeqTerm e1  in
               op_Hat_Slash_Plus_Hat _0_694 _0_693  in
             let _0_697 =
               let _0_696 = str "then"  in
               let _0_695 = p_noSeqTerm e2  in
               op_Hat_Slash_Plus_Hat _0_696 _0_695  in
             FStar_Pprint.op_Hat_Slash_Hat _0_698 _0_697)
        else
          (let e2_doc =
             let uu____2301 = (unparen e2).FStar_Parser_AST.tm  in
             match uu____2301 with
             | FStar_Parser_AST.If (uu____2302,uu____2303,e3) when is_unit e3
                 -> soft_parens_with_nesting (p_noSeqTerm e2)
             | uu____2305 -> p_noSeqTerm e2  in
           FStar_Pprint.group
             (let _0_707 =
                let _0_700 = str "if"  in
                let _0_699 = p_noSeqTerm e1  in
                op_Hat_Slash_Plus_Hat _0_700 _0_699  in
              let _0_706 =
                let _0_705 =
                  let _0_701 = str "then"  in
                  op_Hat_Slash_Plus_Hat _0_701 e2_doc  in
                let _0_704 =
                  let _0_703 = str "else"  in
                  let _0_702 = p_noSeqTerm e3  in
                  op_Hat_Slash_Plus_Hat _0_703 _0_702  in
                FStar_Pprint.op_Hat_Slash_Hat _0_705 _0_704  in
              FStar_Pprint.op_Hat_Slash_Hat _0_707 _0_706))
    | FStar_Parser_AST.TryWith (e,branches) ->
        FStar_Pprint.group
          (let _0_713 =
             let _0_709 = str "try"  in
             let _0_708 = p_noSeqTerm e  in prefix2 _0_709 _0_708  in
           let _0_712 =
             let _0_711 = str "with"  in
             let _0_710 =
               FStar_Pprint.separate_map FStar_Pprint.hardline
                 p_patternBranch branches
                in
             FStar_Pprint.op_Hat_Slash_Hat _0_711 _0_710  in
           FStar_Pprint.op_Hat_Slash_Hat _0_713 _0_712)
    | FStar_Parser_AST.Match (e,branches) ->
        FStar_Pprint.group
          (let _0_718 =
             let _0_716 = str "match"  in
             let _0_715 = p_noSeqTerm e  in
             let _0_714 = str "with"  in
             FStar_Pprint.surround (Prims.parse_int "2")
               (Prims.parse_int "1") _0_716 _0_715 _0_714
              in
           let _0_717 =
             FStar_Pprint.separate_map FStar_Pprint.hardline p_patternBranch
               branches
              in
           FStar_Pprint.op_Hat_Slash_Hat _0_718 _0_717)
    | FStar_Parser_AST.LetOpen (uid,e) ->
        FStar_Pprint.group
          (let _0_723 =
             let _0_721 = str "let open"  in
             let _0_720 = p_quident uid  in
             let _0_719 = str "in"  in
             FStar_Pprint.surround (Prims.parse_int "2")
               (Prims.parse_int "1") _0_721 _0_720 _0_719
              in
           let _0_722 = p_term e  in
           FStar_Pprint.op_Hat_Slash_Hat _0_723 _0_722)
    | FStar_Parser_AST.Let (q,lbs,e) ->
        let let_doc =
          let _0_725 = str "let"  in
          let _0_724 = p_letqualifier q  in
          FStar_Pprint.op_Hat_Hat _0_725 _0_724  in
        let _0_730 =
          FStar_Pprint.group
            (let _0_728 =
               let _0_726 = str "and"  in
               precede_break_separate_map let_doc _0_726 p_letbinding lbs  in
             let _0_727 = str "in"  in
             FStar_Pprint.op_Hat_Slash_Hat _0_728 _0_727)
           in
        let _0_729 = p_term e  in FStar_Pprint.op_Hat_Slash_Hat _0_730 _0_729
    | FStar_Parser_AST.Abs
        ({ FStar_Parser_AST.pat = FStar_Parser_AST.PatVar (x,typ_opt);
           FStar_Parser_AST.prange = uu____2354;_}::[],{
                                                         FStar_Parser_AST.tm
                                                           =
                                                           FStar_Parser_AST.Match
                                                           (maybe_x,branches);
                                                         FStar_Parser_AST.range
                                                           = uu____2357;
                                                         FStar_Parser_AST.level
                                                           = uu____2358;_})
        when matches_var maybe_x x ->
        FStar_Pprint.group
          (let _0_732 = str "function"  in
           let _0_731 =
             FStar_Pprint.separate_map FStar_Pprint.hardline p_patternBranch
               branches
              in
           FStar_Pprint.op_Hat_Slash_Hat _0_732 _0_731)
    | FStar_Parser_AST.Assign (id,e) ->
        FStar_Pprint.group
          (let _0_735 = p_lident id  in
           let _0_734 =
             let _0_733 = p_noSeqTerm e  in
             FStar_Pprint.op_Hat_Slash_Hat FStar_Pprint.larrow _0_733  in
           FStar_Pprint.op_Hat_Slash_Hat _0_735 _0_734)
    | uu____2378 -> p_typ e

and p_typ : FStar_Parser_AST.term -> FStar_Pprint.document =
  fun e  -> with_comment p_typ' e e.FStar_Parser_AST.range

and p_typ' : FStar_Parser_AST.term -> FStar_Pprint.document =
  fun e  ->
    let uu____2381 = (unparen e).FStar_Parser_AST.tm  in
    match uu____2381 with
    | FStar_Parser_AST.QForall (bs,trigger,e1)|FStar_Parser_AST.QExists
      (bs,trigger,e1) ->
        let _0_742 =
          let _0_738 =
            let _0_736 = p_quantifier e  in
            FStar_Pprint.op_Hat_Hat _0_736 FStar_Pprint.space  in
          let _0_737 = p_binders true bs  in
          FStar_Pprint.soft_surround (Prims.parse_int "2")
            (Prims.parse_int "0") _0_738 _0_737 FStar_Pprint.dot
           in
        let _0_741 =
          let _0_740 = p_trigger trigger  in
          let _0_739 = p_noSeqTerm e1  in
          FStar_Pprint.op_Hat_Hat _0_740 _0_739  in
        prefix2 _0_742 _0_741
    | uu____2397 -> p_simpleTerm e

and p_quantifier : FStar_Parser_AST.term -> FStar_Pprint.document =
  fun e  ->
    let uu____2399 = (unparen e).FStar_Parser_AST.tm  in
    match uu____2399 with
    | FStar_Parser_AST.QForall uu____2400 -> str "forall"
    | FStar_Parser_AST.QExists uu____2407 -> str "exists"
    | uu____2414 ->
        failwith "Imposible : p_quantifier called on a non-quantifier term"

and p_trigger :
  FStar_Parser_AST.term Prims.list Prims.list -> FStar_Pprint.document =
  fun uu___138_2415  ->
    match uu___138_2415 with
    | [] -> FStar_Pprint.empty
    | pats ->
        let _0_748 =
          let _0_747 =
            let _0_746 = str "pattern"  in
            let _0_745 =
              let _0_744 = jump2 (p_disjunctivePats pats)  in
              let _0_743 = FStar_Pprint.op_Hat_Hat FStar_Pprint.rbrace break1
                 in
              FStar_Pprint.op_Hat_Slash_Hat _0_744 _0_743  in
            FStar_Pprint.op_Hat_Slash_Hat _0_746 _0_745  in
          FStar_Pprint.op_Hat_Hat FStar_Pprint.colon _0_747  in
        FStar_Pprint.op_Hat_Hat FStar_Pprint.lbrace _0_748

and p_disjunctivePats :
  FStar_Parser_AST.term Prims.list Prims.list -> FStar_Pprint.document =
  fun pats  ->
    let _0_749 = str "\\/"  in
    FStar_Pprint.separate_map _0_749 p_conjunctivePats pats

and p_conjunctivePats :
  FStar_Parser_AST.term Prims.list -> FStar_Pprint.document =
  fun pats  ->
    FStar_Pprint.group
      (FStar_Pprint.separate_map FStar_Pprint.semi p_appTerm pats)

and p_simpleTerm : FStar_Parser_AST.term -> FStar_Pprint.document =
  fun e  ->
    let uu____2429 = (unparen e).FStar_Parser_AST.tm  in
    match uu____2429 with
    | FStar_Parser_AST.Abs (pats,e) ->
        let _0_754 =
          let _0_752 = str "fun"  in
          let _0_751 =
            let _0_750 =
              FStar_Pprint.separate_map break1 p_atomicPattern pats  in
            FStar_Pprint.op_Hat_Slash_Hat _0_750 FStar_Pprint.rarrow  in
          op_Hat_Slash_Plus_Hat _0_752 _0_751  in
        let _0_753 = p_term e  in op_Hat_Slash_Plus_Hat _0_754 _0_753
    | uu____2434 -> p_tmIff e

and p_maybeFocusArrow : Prims.bool -> FStar_Pprint.document =
  fun b  -> if b then str "~>" else FStar_Pprint.rarrow

and p_patternBranch :
  (FStar_Parser_AST.pattern * FStar_Parser_AST.term Prims.option *
    FStar_Parser_AST.term) -> FStar_Pprint.document
  =
  fun uu____2437  ->
    match uu____2437 with
    | (pat,when_opt,e) ->
        let maybe_paren =
          let uu____2450 = (unparen e).FStar_Parser_AST.tm  in
          match uu____2450 with
          | FStar_Parser_AST.Match _|FStar_Parser_AST.TryWith _ ->
              soft_begin_end_with_nesting
          | FStar_Parser_AST.Abs
              ({
                 FStar_Parser_AST.pat = FStar_Parser_AST.PatVar
                   (x,uu____2456);
                 FStar_Parser_AST.prange = uu____2457;_}::[],{
                                                               FStar_Parser_AST.tm
                                                                 =
                                                                 FStar_Parser_AST.Match
                                                                 (maybe_x,uu____2459);
                                                               FStar_Parser_AST.range
                                                                 = uu____2460;
                                                               FStar_Parser_AST.level
                                                                 = uu____2461;_})
              when matches_var maybe_x x -> soft_begin_end_with_nesting
          | uu____2475 -> (fun x  -> x)  in
        FStar_Pprint.group
          (let _0_761 =
             FStar_Pprint.group
               (let _0_759 =
                  let _0_758 =
                    let _0_757 = p_disjunctivePattern pat  in
                    let _0_756 =
                      let _0_755 = p_maybeWhen when_opt  in
                      FStar_Pprint.op_Hat_Hat _0_755 FStar_Pprint.rarrow  in
                    op_Hat_Slash_Plus_Hat _0_757 _0_756  in
                  FStar_Pprint.op_Hat_Hat FStar_Pprint.space _0_758  in
                FStar_Pprint.op_Hat_Hat FStar_Pprint.bar _0_759)
              in
           let _0_760 = maybe_paren (p_term e)  in
           op_Hat_Slash_Plus_Hat _0_761 _0_760)

and p_maybeWhen : FStar_Parser_AST.term Prims.option -> FStar_Pprint.document
  =
  fun uu___139_2477  ->
    match uu___139_2477 with
    | None  -> FStar_Pprint.empty
    | Some e ->
        let _0_764 = str "when"  in
        let _0_763 =
          let _0_762 = p_tmFormula e  in
          FStar_Pprint.op_Hat_Hat _0_762 FStar_Pprint.space  in
        op_Hat_Slash_Plus_Hat _0_764 _0_763

and p_tmIff : FStar_Parser_AST.term -> FStar_Pprint.document =
  fun e  ->
    let uu____2481 = (unparen e).FStar_Parser_AST.tm  in
    match uu____2481 with
    | FStar_Parser_AST.Op ("<==>",e1::e2::[]) ->
        let _0_767 = str "<==>"  in
        let _0_766 = p_tmImplies e1  in
        let _0_765 = p_tmIff e2  in infix0 _0_767 _0_766 _0_765
    | uu____2485 -> p_tmImplies e

and p_tmImplies : FStar_Parser_AST.term -> FStar_Pprint.document =
  fun e  ->
    let uu____2487 = (unparen e).FStar_Parser_AST.tm  in
    match uu____2487 with
    | FStar_Parser_AST.Op ("==>",e1::e2::[]) ->
        let _0_770 = str "==>"  in
        let _0_769 = p_tmArrow p_tmFormula e1  in
        let _0_768 = p_tmImplies e2  in infix0 _0_770 _0_769 _0_768
    | uu____2491 -> p_tmArrow p_tmFormula e

and p_tmArrow :
  (FStar_Parser_AST.term -> FStar_Pprint.document) ->
    FStar_Parser_AST.term -> FStar_Pprint.document
  =
  fun p_Tm  ->
    fun e  ->
      let uu____2496 = (unparen e).FStar_Parser_AST.tm  in
      match uu____2496 with
      | FStar_Parser_AST.Product (bs,tgt) ->
          FStar_Pprint.group
            (let _0_775 =
               FStar_Pprint.concat_map
                 (fun b  ->
                    let _0_773 = p_binder false b  in
                    let _0_772 =
                      let _0_771 =
                        FStar_Pprint.op_Hat_Hat FStar_Pprint.rarrow break1
                         in
                      FStar_Pprint.op_Hat_Hat FStar_Pprint.space _0_771  in
                    FStar_Pprint.op_Hat_Hat _0_773 _0_772) bs
                in
             let _0_774 = p_tmArrow p_Tm tgt  in
             FStar_Pprint.op_Hat_Hat _0_775 _0_774)
      | uu____2502 -> p_Tm e

and p_tmFormula : FStar_Parser_AST.term -> FStar_Pprint.document =
  fun e  ->
    let uu____2504 = (unparen e).FStar_Parser_AST.tm  in
    match uu____2504 with
    | FStar_Parser_AST.Op ("\\/",e1::e2::[]) ->
        let _0_778 = str "\\/"  in
        let _0_777 = p_tmFormula e1  in
        let _0_776 = p_tmConjunction e2  in infix0 _0_778 _0_777 _0_776
    | uu____2508 -> p_tmConjunction e

and p_tmConjunction : FStar_Parser_AST.term -> FStar_Pprint.document =
  fun e  ->
    let uu____2510 = (unparen e).FStar_Parser_AST.tm  in
    match uu____2510 with
    | FStar_Parser_AST.Op ("/\\",e1::e2::[]) ->
        let _0_781 = str "/\\"  in
        let _0_780 = p_tmConjunction e1  in
        let _0_779 = p_tmTuple e2  in infix0 _0_781 _0_780 _0_779
    | uu____2514 -> p_tmTuple e

and p_tmTuple : FStar_Parser_AST.term -> FStar_Pprint.document =
  fun e  -> with_comment p_tmTuple' e e.FStar_Parser_AST.range

and p_tmTuple' : FStar_Parser_AST.term -> FStar_Pprint.document =
  fun e  ->
    let uu____2517 = (unparen e).FStar_Parser_AST.tm  in
    match uu____2517 with
    | FStar_Parser_AST.Construct (lid,args) when is_tuple_constructor lid ->
        let _0_782 = FStar_Pprint.op_Hat_Hat FStar_Pprint.comma break1  in
        FStar_Pprint.separate_map _0_782
          (fun uu____2528  ->
             match uu____2528 with | (e,uu____2532) -> p_tmEq e) args
    | uu____2533 -> p_tmEq e

and paren_if :
  Prims.int -> Prims.int -> FStar_Pprint.document -> FStar_Pprint.document =
  fun curr  ->
    fun mine  ->
      fun doc  ->
        if mine <= curr
        then doc
        else
          FStar_Pprint.group
            (let _0_783 = FStar_Pprint.op_Hat_Hat doc FStar_Pprint.rparen  in
             FStar_Pprint.op_Hat_Hat FStar_Pprint.lparen _0_783)

and p_tmEq : FStar_Parser_AST.term -> FStar_Pprint.document =
  fun e  ->
    let n =
      max_level
        (FStar_List.append [colon_equals (); pipe_right ()]
           (operatorInfix0ad12 ()))
       in
    p_tmEq' n e

and p_tmEq' : Prims.int -> FStar_Parser_AST.term -> FStar_Pprint.document =
  fun curr  ->
    fun e  ->
      let uu____2562 = (unparen e).FStar_Parser_AST.tm  in
      match uu____2562 with
      | FStar_Parser_AST.Op (op,e1::e2::[]) when
          ((is_operatorInfix0ad12 op) || (op = "=")) || (op = "|>") ->
          let uu____2567 = levels op  in
          (match uu____2567 with
           | (left,mine,right) ->
               let _0_787 =
                 let _0_786 = str op  in
                 let _0_785 = p_tmEq' left e1  in
                 let _0_784 = p_tmEq' right e2  in
                 infix0 _0_786 _0_785 _0_784  in
               paren_if curr mine _0_787)
      | FStar_Parser_AST.Op (":=",e1::e2::[]) ->
          FStar_Pprint.group
            (let _0_792 = p_tmEq e1  in
             let _0_791 =
               let _0_790 =
                 let _0_789 =
                   let _0_788 = p_tmEq e2  in
                   op_Hat_Slash_Plus_Hat FStar_Pprint.equals _0_788  in
                 FStar_Pprint.op_Hat_Hat FStar_Pprint.colon _0_789  in
               FStar_Pprint.op_Hat_Hat FStar_Pprint.space _0_790  in
             FStar_Pprint.op_Hat_Hat _0_792 _0_791)
      | uu____2577 -> p_tmNoEq e

and p_tmNoEq : FStar_Parser_AST.term -> FStar_Pprint.document =
  fun e  ->
    let n = max_level [colon_colon (); amp (); opinfix3 (); opinfix4 ()]  in
    p_tmNoEq' n e

and p_tmNoEq' : Prims.int -> FStar_Parser_AST.term -> FStar_Pprint.document =
  fun curr  ->
    fun e  ->
      let uu____2607 = (unparen e).FStar_Parser_AST.tm  in
      match uu____2607 with
      | FStar_Parser_AST.Construct (lid,(e1,uu____2610)::(e2,uu____2612)::[])
          when
          (FStar_Ident.lid_equals lid FStar_Syntax_Const.cons_lid) &&
            (Prims.op_Negation (is_list e))
          ->
          let op = "::"  in
          let uu____2623 = levels op  in
          (match uu____2623 with
           | (left,mine,right) ->
               let _0_796 =
                 let _0_795 = str op  in
                 let _0_794 = p_tmNoEq' left e1  in
                 let _0_793 = p_tmNoEq' right e2  in
                 infix0 _0_795 _0_794 _0_793  in
               paren_if curr mine _0_796)
      | FStar_Parser_AST.Sum (binders,res) ->
          let op = "&"  in
          let uu____2635 = levels op  in
          (match uu____2635 with
           | (left,mine,right) ->
               let p_dsumfst b =
                 let _0_800 = p_binder false b  in
                 let _0_799 =
                   let _0_798 =
                     let _0_797 = str "&"  in
                     FStar_Pprint.op_Hat_Hat _0_797 break1  in
                   FStar_Pprint.op_Hat_Hat FStar_Pprint.space _0_798  in
                 FStar_Pprint.op_Hat_Hat _0_800 _0_799  in
               let _0_803 =
                 let _0_802 = FStar_Pprint.concat_map p_dsumfst binders  in
                 let _0_801 = p_tmNoEq' right res  in
                 FStar_Pprint.op_Hat_Hat _0_802 _0_801  in
               paren_if curr mine _0_803)
      | FStar_Parser_AST.Op (op,e1::e2::[]) when is_operatorInfix34 op ->
          let uu____2650 = levels op  in
          (match uu____2650 with
           | (left,mine,right) ->
               let _0_807 =
                 let _0_806 = str op  in
                 let _0_805 = p_tmNoEq' left e1  in
                 let _0_804 = p_tmNoEq' right e2  in
                 infix0 _0_806 _0_805 _0_804  in
               paren_if curr mine _0_807)
      | FStar_Parser_AST.Op ("-",e::[]) ->
          let uu____2659 = levels "-"  in
          (match uu____2659 with
           | (left,mine,right) ->
               let _0_808 = p_tmNoEq' mine e  in
               FStar_Pprint.op_Hat_Slash_Hat FStar_Pprint.minus _0_808)
      | FStar_Parser_AST.NamedTyp (lid,e) ->
          FStar_Pprint.group
            (let _0_811 = p_lidentOrUnderscore lid  in
             let _0_810 =
               let _0_809 = p_appTerm e  in
               FStar_Pprint.op_Hat_Slash_Hat FStar_Pprint.colon _0_809  in
             FStar_Pprint.op_Hat_Slash_Hat _0_811 _0_810)
      | FStar_Parser_AST.Refine (b,phi) -> p_refinedBinder b phi
      | FStar_Parser_AST.Record (with_opt,record_fields) ->
          braces_with_nesting
            (let _0_814 =
               default_or_map FStar_Pprint.empty p_with_clause with_opt  in
             let _0_813 =
               let _0_812 = FStar_Pprint.op_Hat_Hat FStar_Pprint.semi break1
                  in
               FStar_Pprint.separate_map _0_812 p_simpleDef record_fields  in
             FStar_Pprint.op_Hat_Hat _0_814 _0_813)
      | FStar_Parser_AST.Op ("~",e::[]) ->
          FStar_Pprint.group
            (let _0_816 = str "~"  in
             let _0_815 = p_atomicTerm e  in
             FStar_Pprint.op_Hat_Hat _0_816 _0_815)
      | uu____2684 -> p_appTerm e

and p_with_clause : FStar_Parser_AST.term -> FStar_Pprint.document =
  fun e  ->
    let _0_820 = p_appTerm e  in
    let _0_819 =
      let _0_818 =
        let _0_817 = str "with"  in FStar_Pprint.op_Hat_Hat _0_817 break1  in
      FStar_Pprint.op_Hat_Hat FStar_Pprint.space _0_818  in
    FStar_Pprint.op_Hat_Hat _0_820 _0_819

and p_refinedBinder :
  FStar_Parser_AST.binder -> FStar_Parser_AST.term -> FStar_Pprint.document =
  fun b  ->
    fun phi  ->
      match b.FStar_Parser_AST.b with
      | FStar_Parser_AST.Annotated (lid,t) ->
          soft_parens_with_nesting
            (let _0_821 = p_lident lid  in
             p_refinement b.FStar_Parser_AST.aqual _0_821 t phi)
      | FStar_Parser_AST.TAnnotated uu____2690 ->
          failwith "Is this still used ?"
      | FStar_Parser_AST.Variable _
        |FStar_Parser_AST.TVariable _|FStar_Parser_AST.NoName _ ->
          failwith
            (let _0_822 = FStar_Parser_AST.binder_to_string b  in
             FStar_Util.format1
               "Imposible : a refined binder ought to be annotated %s" _0_822)

and p_simpleDef :
  (FStar_Ident.lid * FStar_Parser_AST.term) -> FStar_Pprint.document =
  fun uu____2696  ->
    match uu____2696 with
    | (lid,e) ->
        FStar_Pprint.group
          (let _0_825 = p_qlident lid  in
           let _0_824 =
             let _0_823 = p_tmIff e  in
             FStar_Pprint.op_Hat_Slash_Hat FStar_Pprint.equals _0_823  in
           FStar_Pprint.op_Hat_Slash_Hat _0_825 _0_824)

and p_appTerm : FStar_Parser_AST.term -> FStar_Pprint.document =
  fun e  ->
    let uu____2702 = (unparen e).FStar_Parser_AST.tm  in
    match uu____2702 with
    | FStar_Parser_AST.App uu____2703 when is_general_application e ->
        let uu____2707 = head_and_args e  in
        (match uu____2707 with
         | (head,args) ->
             let uu____2721 =
               let uu____2727 = FStar_ST.read should_print_fs_typ_app  in
               if uu____2727
               then
                 let uu____2735 =
                   FStar_Util.take
                     (fun uu____2746  ->
                        match uu____2746 with
                        | (uu____2749,aq) -> aq = FStar_Parser_AST.FsTypApp)
                     args
                    in
                 match uu____2735 with
                 | (fs_typ_args,args) ->
                     let _0_829 =
                       let _0_828 = p_indexingTerm head  in
                       let _0_827 =
                         let _0_826 =
                           FStar_Pprint.op_Hat_Hat FStar_Pprint.comma break1
                            in
                         soft_surround_separate_map (Prims.parse_int "2")
                           (Prims.parse_int "0") FStar_Pprint.empty
                           FStar_Pprint.langle _0_826 FStar_Pprint.rangle
                           p_fsTypArg fs_typ_args
                          in
                       FStar_Pprint.op_Hat_Hat _0_828 _0_827  in
                     (_0_829, args)
               else (let _0_830 = p_indexingTerm head  in (_0_830, args))  in
             (match uu____2721 with
              | (head_doc,args) ->
                  FStar_Pprint.group
                    (let _0_831 =
                       FStar_Pprint.op_Hat_Hat head_doc FStar_Pprint.space
                        in
                     soft_surround_separate_map (Prims.parse_int "2")
                       (Prims.parse_int "0") head_doc _0_831 break1
                       FStar_Pprint.empty p_argTerm args)))
    | FStar_Parser_AST.Construct (lid,args) when
        (is_general_construction e) &&
          (Prims.op_Negation (is_dtuple_constructor lid))
        ->
        (match args with
         | [] -> p_quident lid
         | arg::[] ->
             FStar_Pprint.group
               (let _0_833 = p_quident lid  in
                let _0_832 = p_argTerm arg  in
                FStar_Pprint.op_Hat_Slash_Hat _0_833 _0_832)
         | hd::tl ->
             FStar_Pprint.group
               (let _0_837 =
                  FStar_Pprint.group
                    (let _0_835 = p_quident lid  in
                     let _0_834 = p_argTerm hd  in prefix2 _0_835 _0_834)
                   in
                let _0_836 =
                  jump2 (FStar_Pprint.separate_map break1 p_argTerm tl)  in
                FStar_Pprint.op_Hat_Hat _0_837 _0_836))
    | uu____2817 -> p_indexingTerm e

and p_argTerm :
  (FStar_Parser_AST.term * FStar_Parser_AST.imp) -> FStar_Pprint.document =
  fun arg_imp  ->
    match arg_imp with
    | ({ FStar_Parser_AST.tm = FStar_Parser_AST.Uvar uu____2821;
         FStar_Parser_AST.range = uu____2822;
         FStar_Parser_AST.level = uu____2823;_},FStar_Parser_AST.UnivApp
       ) -> p_univar (Prims.fst arg_imp)
    | (u,FStar_Parser_AST.UnivApp ) -> p_universe u
    | (e,FStar_Parser_AST.FsTypApp ) ->
        (FStar_Util.print_warning
           "Unexpected FsTypApp, output might not be formatted correctly.\n";
         (let _0_838 = p_indexingTerm e  in
          FStar_Pprint.surround (Prims.parse_int "2") (Prims.parse_int "1")
            FStar_Pprint.langle _0_838 FStar_Pprint.rangle))
    | (e,FStar_Parser_AST.Hash ) ->
        let _0_840 = str "#"  in
        let _0_839 = p_indexingTerm e  in
        FStar_Pprint.op_Hat_Hat _0_840 _0_839
    | (e,FStar_Parser_AST.Nothing ) -> p_indexingTerm e

and p_fsTypArg :
  (FStar_Parser_AST.term * FStar_Parser_AST.imp) -> FStar_Pprint.document =
  fun uu____2829  ->
    match uu____2829 with | (e,uu____2833) -> p_indexingTerm e

and p_indexingTerm_aux :
  (FStar_Parser_AST.term -> FStar_Pprint.document) ->
    FStar_Parser_AST.term -> FStar_Pprint.document
  =
  fun exit  ->
    fun e  ->
      let uu____2838 = (unparen e).FStar_Parser_AST.tm  in
      match uu____2838 with
      | FStar_Parser_AST.Op (".()",e1::e2::[]) ->
          FStar_Pprint.group
            (let _0_843 = p_indexingTerm_aux p_atomicTermNotQUident e1  in
             let _0_842 =
               let _0_841 = soft_parens_with_nesting (p_term e2)  in
               FStar_Pprint.op_Hat_Hat FStar_Pprint.dot _0_841  in
             FStar_Pprint.op_Hat_Hat _0_843 _0_842)
      | FStar_Parser_AST.Op (".[]",e1::e2::[]) ->
          FStar_Pprint.group
            (let _0_846 = p_indexingTerm_aux p_atomicTermNotQUident e1  in
             let _0_845 =
               let _0_844 = soft_brackets_with_nesting (p_term e2)  in
               FStar_Pprint.op_Hat_Hat FStar_Pprint.dot _0_844  in
             FStar_Pprint.op_Hat_Hat _0_846 _0_845)
      | uu____2845 -> exit e

and p_indexingTerm : FStar_Parser_AST.term -> FStar_Pprint.document =
  fun e  -> p_indexingTerm_aux p_atomicTerm e

and p_atomicTerm : FStar_Parser_AST.term -> FStar_Pprint.document =
  fun e  ->
    let uu____2848 = (unparen e).FStar_Parser_AST.tm  in
    match uu____2848 with
    | FStar_Parser_AST.LetOpen (lid,e) ->
        let _0_849 = p_quident lid  in
        let _0_848 =
          let _0_847 = soft_parens_with_nesting (p_term e)  in
          FStar_Pprint.op_Hat_Hat FStar_Pprint.dot _0_847  in
        FStar_Pprint.op_Hat_Hat _0_849 _0_848
    | FStar_Parser_AST.Name lid -> p_quident lid
    | FStar_Parser_AST.Op (op,e::[]) when is_general_prefix_op op ->
        let _0_851 = str op  in
        let _0_850 = p_atomicTerm e  in FStar_Pprint.op_Hat_Hat _0_851 _0_850
    | uu____2855 -> p_atomicTermNotQUident e

and p_atomicTermNotQUident : FStar_Parser_AST.term -> FStar_Pprint.document =
  fun e  ->
    let uu____2857 = (unparen e).FStar_Parser_AST.tm  in
    match uu____2857 with
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
    | FStar_Parser_AST.Op (op,e::[]) when is_general_prefix_op op ->
        let _0_853 = str op  in
        let _0_852 = p_atomicTermNotQUident e  in
        FStar_Pprint.op_Hat_Hat _0_853 _0_852
    | FStar_Parser_AST.Op (op,[]) ->
        let _0_857 =
          let _0_856 =
            let _0_855 = str op  in
            let _0_854 =
              FStar_Pprint.op_Hat_Hat FStar_Pprint.space FStar_Pprint.rparen
               in
            FStar_Pprint.op_Hat_Hat _0_855 _0_854  in
          FStar_Pprint.op_Hat_Hat FStar_Pprint.space _0_856  in
        FStar_Pprint.op_Hat_Hat FStar_Pprint.lparen _0_857
    | FStar_Parser_AST.Construct (lid,args) when is_dtuple_constructor lid ->
        let _0_862 =
          FStar_Pprint.op_Hat_Hat FStar_Pprint.lparen FStar_Pprint.bar  in
        let _0_861 =
          let _0_859 = FStar_Pprint.op_Hat_Hat FStar_Pprint.comma break1  in
          let _0_858 = FStar_List.map Prims.fst args  in
          FStar_Pprint.separate_map _0_859 p_tmEq _0_858  in
        let _0_860 =
          FStar_Pprint.op_Hat_Hat FStar_Pprint.bar FStar_Pprint.rparen  in
        FStar_Pprint.surround (Prims.parse_int "2") (Prims.parse_int "1")
          _0_862 _0_861 _0_860
    | FStar_Parser_AST.Project (e,lid) ->
        FStar_Pprint.group
          (let _0_865 = p_atomicTermNotQUident e  in
           let _0_864 =
             let _0_863 = p_qlident lid  in
             FStar_Pprint.op_Hat_Hat FStar_Pprint.dot _0_863  in
           FStar_Pprint.prefix (Prims.parse_int "2") (Prims.parse_int "0")
             _0_865 _0_864)
    | uu____2880 -> p_projectionLHS e

and p_projectionLHS : FStar_Parser_AST.term -> FStar_Pprint.document =
  fun e  ->
    let uu____2882 = (unparen e).FStar_Parser_AST.tm  in
    match uu____2882 with
    | FStar_Parser_AST.Var lid -> p_qlident lid
    | FStar_Parser_AST.Projector (constr_lid,field_lid) ->
        let _0_869 = p_quident constr_lid  in
        let _0_868 =
          let _0_867 =
            let _0_866 = p_lident field_lid  in
            FStar_Pprint.op_Hat_Hat FStar_Pprint.dot _0_866  in
          FStar_Pprint.op_Hat_Hat FStar_Pprint.qmark _0_867  in
        FStar_Pprint.op_Hat_Hat _0_869 _0_868
    | FStar_Parser_AST.Discrim constr_lid ->
        let _0_870 = p_quident constr_lid  in
        FStar_Pprint.op_Hat_Hat _0_870 FStar_Pprint.qmark
    | FStar_Parser_AST.Paren e -> soft_parens_with_nesting (p_term e)
    | uu____2888 when is_array e ->
        let es = extract_from_list e  in
        let _0_874 =
          FStar_Pprint.op_Hat_Hat FStar_Pprint.lbracket FStar_Pprint.bar  in
        let _0_873 =
          let _0_871 = FStar_Pprint.op_Hat_Hat FStar_Pprint.semi break1  in
          separate_map_or_flow _0_871 p_noSeqTerm es  in
        let _0_872 =
          FStar_Pprint.op_Hat_Hat FStar_Pprint.bar FStar_Pprint.rbracket  in
        FStar_Pprint.surround (Prims.parse_int "2") (Prims.parse_int "0")
          _0_874 _0_873 _0_872
    | uu____2891 when is_list e ->
        let _0_877 =
          let _0_876 = FStar_Pprint.op_Hat_Hat FStar_Pprint.semi break1  in
          let _0_875 = extract_from_list e  in
          separate_map_or_flow _0_876 p_noSeqTerm _0_875  in
        FStar_Pprint.surround (Prims.parse_int "2") (Prims.parse_int "0")
          FStar_Pprint.lbracket _0_877 FStar_Pprint.rbracket
    | uu____2892 when is_lex_list e ->
        let _0_881 =
          FStar_Pprint.op_Hat_Hat FStar_Pprint.percent FStar_Pprint.lbracket
           in
        let _0_880 =
          let _0_879 = FStar_Pprint.op_Hat_Hat FStar_Pprint.semi break1  in
          let _0_878 = extract_from_list e  in
          separate_map_or_flow _0_879 p_noSeqTerm _0_878  in
        FStar_Pprint.surround (Prims.parse_int "2") (Prims.parse_int "1")
          _0_881 _0_880 FStar_Pprint.rbracket
    | uu____2893 when is_ref_set e ->
        let es = extract_from_ref_set e  in
        let _0_884 =
          FStar_Pprint.op_Hat_Hat FStar_Pprint.bang FStar_Pprint.lbrace  in
        let _0_883 =
          let _0_882 = FStar_Pprint.op_Hat_Hat FStar_Pprint.comma break1  in
          separate_map_or_flow _0_882 p_appTerm es  in
        FStar_Pprint.surround (Prims.parse_int "2") (Prims.parse_int "0")
          _0_884 _0_883 FStar_Pprint.rbrace
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
        -> soft_parens_with_nesting (p_term e)
    | FStar_Parser_AST.Labeled uu____2924 -> failwith "Not valid in universe"

and p_constant : FStar_Const.sconst -> FStar_Pprint.document =
  fun uu___142_2928  ->
    match uu___142_2928 with
    | FStar_Const.Const_effect  -> str "Effect"
    | FStar_Const.Const_unit  -> str "()"
    | FStar_Const.Const_bool b -> FStar_Pprint.doc_of_bool b
    | FStar_Const.Const_float x -> str (FStar_Util.string_of_float x)
    | FStar_Const.Const_char x ->
        FStar_Pprint.squotes (FStar_Pprint.doc_of_char x)
    | FStar_Const.Const_string (bytes,uu____2933) ->
        FStar_Pprint.dquotes (str (FStar_Util.string_of_bytes bytes))
    | FStar_Const.Const_bytearray (bytes,uu____2937) ->
        let _0_886 =
          FStar_Pprint.dquotes (str (FStar_Util.string_of_bytes bytes))  in
        let _0_885 = str "B"  in FStar_Pprint.op_Hat_Hat _0_886 _0_885
    | FStar_Const.Const_int (repr,sign_width_opt) ->
        let signedness uu___140_2951 =
          match uu___140_2951 with
          | FStar_Const.Unsigned  -> str "u"
          | FStar_Const.Signed  -> FStar_Pprint.empty  in
        let width uu___141_2955 =
          match uu___141_2955 with
          | FStar_Const.Int8  -> str "y"
          | FStar_Const.Int16  -> str "s"
          | FStar_Const.Int32  -> str "l"
          | FStar_Const.Int64  -> str "L"  in
        let ending =
          default_or_map FStar_Pprint.empty
            (fun uu____2959  ->
               match uu____2959 with
               | (s,w) ->
                   let _0_888 = signedness s  in
                   let _0_887 = width w  in
                   FStar_Pprint.op_Hat_Hat _0_888 _0_887) sign_width_opt
           in
        let _0_889 = str repr  in FStar_Pprint.op_Hat_Hat _0_889 ending
    | FStar_Const.Const_range r -> str (FStar_Range.string_of_range r)
    | FStar_Const.Const_reify  -> str "reify"
    | FStar_Const.Const_reflect lid ->
        let _0_893 = p_quident lid  in
        let _0_892 =
          let _0_891 =
            let _0_890 = str "reflect"  in
            FStar_Pprint.op_Hat_Hat FStar_Pprint.dot _0_890  in
          FStar_Pprint.op_Hat_Hat FStar_Pprint.qmark _0_891  in
        FStar_Pprint.op_Hat_Hat _0_893 _0_892

and p_universe : FStar_Parser_AST.term -> FStar_Pprint.document =
  fun u  ->
    let _0_895 = str "u#"  in
    let _0_894 = p_atomicUniverse u  in FStar_Pprint.op_Hat_Hat _0_895 _0_894

and p_universeFrom : FStar_Parser_AST.term -> FStar_Pprint.document =
  fun u  ->
    let uu____2968 = (unparen u).FStar_Parser_AST.tm  in
    match uu____2968 with
    | FStar_Parser_AST.Op ("+",u1::u2::[]) ->
        FStar_Pprint.group
          (let _0_898 = p_universeFrom u1  in
           let _0_897 =
             let _0_896 = p_universeFrom u2  in
             FStar_Pprint.op_Hat_Slash_Hat FStar_Pprint.plus _0_896  in
           FStar_Pprint.op_Hat_Slash_Hat _0_898 _0_897)
    | FStar_Parser_AST.App uu____2972 ->
        let uu____2976 = head_and_args u  in
        (match uu____2976 with
         | (head,args) ->
             let uu____2990 = (unparen head).FStar_Parser_AST.tm  in
             (match uu____2990 with
              | FStar_Parser_AST.Var maybe_max_lid when
                  FStar_Ident.lid_equals maybe_max_lid
                    FStar_Syntax_Const.max_lid
                  ->
                  FStar_Pprint.group
                    (let _0_900 = p_qlident FStar_Syntax_Const.max_lid  in
                     let _0_899 =
                       FStar_Pprint.separate_map FStar_Pprint.space
                         (fun uu____2994  ->
                            match uu____2994 with
                            | (u,uu____2998) -> p_atomicUniverse u) args
                        in
                     op_Hat_Slash_Plus_Hat _0_900 _0_899)
              | uu____2999 ->
                  failwith
                    (let _0_901 = FStar_Parser_AST.term_to_string u  in
                     FStar_Util.format1 "Invalid term in universe context %s"
                       _0_901)))
    | uu____3000 -> p_atomicUniverse u

and p_atomicUniverse : FStar_Parser_AST.term -> FStar_Pprint.document =
  fun u  ->
    let uu____3002 = (unparen u).FStar_Parser_AST.tm  in
    match uu____3002 with
    | FStar_Parser_AST.Wild  -> FStar_Pprint.underscore
    | FStar_Parser_AST.Const (FStar_Const.Const_int (r,sw)) ->
        p_constant (FStar_Const.Const_int (r, sw))
    | FStar_Parser_AST.Uvar uu____3014 -> p_univar u
    | FStar_Parser_AST.Paren u -> soft_parens_with_nesting (p_universeFrom u)
    | FStar_Parser_AST.Op ("+",_::_::[])|FStar_Parser_AST.App _ ->
        soft_parens_with_nesting (p_universeFrom u)
    | uu____3020 ->
        failwith
          (let _0_902 = FStar_Parser_AST.term_to_string u  in
           FStar_Util.format1 "Invalid term in universe context %s" _0_902)

and p_univar : FStar_Parser_AST.term -> FStar_Pprint.document =
  fun u  ->
    let uu____3022 = (unparen u).FStar_Parser_AST.tm  in
    match uu____3022 with
    | FStar_Parser_AST.Uvar id -> str (FStar_Ident.text_of_id id)
    | uu____3024 ->
        failwith
          (let _0_903 = FStar_Parser_AST.term_to_string u  in
           FStar_Util.format1 "Not a universe variable %s" _0_903)

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
           let _0_904 =
             FStar_All.pipe_right decls (FStar_List.map decl_to_document)  in
           FStar_All.pipe_right _0_904
             (FStar_Pprint.separate FStar_Pprint.hardline)
        in
     FStar_ST.write should_print_fs_typ_app false; res)
  
let comments_to_document :
  (Prims.string * FStar_Range.range) Prims.list -> FStar_Pprint.document =
  fun comments  ->
    FStar_Pprint.separate_map FStar_Pprint.hardline
      (fun uu____3063  ->
         match uu____3063 with | (comment,range) -> str comment) comments
  
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
           let uu____3110 =
             match ds with
             | {
                 FStar_Parser_AST.d = FStar_Parser_AST.Pragma
                   (FStar_Parser_AST.LightOff );
                 FStar_Parser_AST.drange = uu____3117;
                 FStar_Parser_AST.doc = uu____3118;
                 FStar_Parser_AST.quals = uu____3119;
                 FStar_Parser_AST.attrs = uu____3120;_}::uu____3121 ->
                 let d0 = FStar_List.hd ds  in
                 let _0_907 =
                   let _0_906 = let _0_905 = FStar_List.tl ds  in d :: _0_905
                      in
                   d0 :: _0_906  in
                 (_0_907, (d0.FStar_Parser_AST.drange))
             | uu____3126 -> ((d :: ds), (d.FStar_Parser_AST.drange))  in
           (match uu____3110 with
            | (decls,first_range) ->
                let extract_decl_range d = d.FStar_Parser_AST.drange  in
                (FStar_ST.write comment_stack comments;
                 (let initial_comment =
                    let _0_908 = FStar_Range.start_of_range first_range  in
                    place_comments_until_pos (Prims.parse_int "0")
                      (Prims.parse_int "1") _0_908 FStar_Pprint.empty
                     in
                  let doc =
                    separate_map_with_comments FStar_Pprint.empty
                      FStar_Pprint.empty decl_to_document decls
                      extract_decl_range
                     in
                  let comments = FStar_ST.read comment_stack  in
                  FStar_ST.write comment_stack [];
                  FStar_ST.write should_print_fs_typ_app false;
                  (let _0_909 = FStar_Pprint.op_Hat_Hat initial_comment doc
                      in
                   (_0_909, comments))))))
  