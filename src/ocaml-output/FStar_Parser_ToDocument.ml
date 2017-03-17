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
    match uu____44 with
    | true  -> t
    | uu____47 ->
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
    (let _0_327 =
       let _0_326 = FStar_Pprint.op_Hat_Hat sep break1  in
       FStar_Pprint.op_Hat_Hat FStar_Pprint.space _0_326  in
     FStar_Pprint.separate_map _0_327 f l)
  
let precede_break_separate_map prec sep f l =
  let _0_336 =
    let _0_330 = FStar_Pprint.op_Hat_Hat prec FStar_Pprint.space  in
    let _0_329 =
      let _0_328 = FStar_List.hd l  in FStar_All.pipe_right _0_328 f  in
    FStar_Pprint.precede _0_330 _0_329  in
  let _0_335 =
    let _0_334 = FStar_List.tl l  in
    FStar_Pprint.concat_map
      (fun x  ->
         let _0_333 =
           let _0_332 =
             let _0_331 = f x  in
             FStar_Pprint.op_Hat_Hat FStar_Pprint.space _0_331  in
           FStar_Pprint.op_Hat_Hat sep _0_332  in
         FStar_Pprint.op_Hat_Hat break1 _0_333) _0_334
     in
  FStar_Pprint.op_Hat_Hat _0_336 _0_335 
let concat_break_map f l =
  FStar_Pprint.group
    (FStar_Pprint.concat_map
       (fun x  -> let _0_337 = f x  in FStar_Pprint.op_Hat_Hat _0_337 break1)
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
    let _0_339 = str "begin"  in
    let _0_338 = str "end"  in
    FStar_Pprint.soft_surround (Prims.parse_int "2") (Prims.parse_int "1")
      _0_339 contents _0_338
  
let separate_map_or_flow sep f l =
  match (FStar_List.length l) < (Prims.parse_int "10") with
  | true  -> FStar_Pprint.separate_map sep f l
  | uu____229 -> FStar_Pprint.flow_map sep f l 
let soft_surround_separate_map n b void_ opening sep closing f xs =
  match xs = [] with
  | true  -> void_
  | uu____280 ->
      let _0_340 = FStar_Pprint.separate_map sep f xs  in
      FStar_Pprint.soft_surround n b opening _0_340 closing
  
let doc_of_fsdoc :
  (Prims.string * (Prims.string * Prims.string) Prims.list) ->
    FStar_Pprint.document
  =
  fun uu____288  ->
    match uu____288 with
    | (comment,keywords) ->
        FStar_Pprint.group
          (FStar_Pprint.concat
             (let _0_348 = str comment  in
              let _0_347 =
                let _0_346 =
                  let _0_345 =
                    FStar_Pprint.separate_map FStar_Pprint.comma
                      (fun uu____304  ->
                         match uu____304 with
                         | (k,v) ->
                             FStar_Pprint.concat
                               (let _0_344 = str k  in
                                let _0_343 =
                                  let _0_342 =
                                    let _0_341 = str v  in [_0_341]  in
                                  FStar_Pprint.rarrow :: _0_342  in
                                _0_344 :: _0_343)) keywords
                     in
                  [_0_345]  in
                FStar_Pprint.space :: _0_346  in
              _0_348 :: _0_347))
  
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
  fun cons_lid1  ->
    fun nil_lid1  ->
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
        (uu____418,(e1,FStar_Parser_AST.Nothing )::(e2,FStar_Parser_AST.Nothing
                                                    )::[])
        -> let _0_349 = extract_from_list e2  in e1 :: _0_349
    | uu____390 ->
        failwith
          (let _0_350 = FStar_Parser_AST.term_to_string e  in
           FStar_Util.format1 "Not a list %s" _0_350)
  
let is_array : FStar_Parser_AST.term -> Prims.bool =
  fun e  ->
    let uu____395 = (unparen e).FStar_Parser_AST.tm  in
    match uu____395 with
    | FStar_Parser_AST.App
        ({ FStar_Parser_AST.tm = FStar_Parser_AST.Var lid;
           FStar_Parser_AST.range = uu____442;
           FStar_Parser_AST.level = uu____443;_},l,FStar_Parser_AST.Nothing
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
    | uu____422 -> false
  
let rec extract_from_ref_set :
  FStar_Parser_AST.term -> FStar_Parser_AST.term Prims.list =
  fun e  ->
    let uu____427 = (unparen e).FStar_Parser_AST.tm  in
    match uu____427 with
    | FStar_Parser_AST.Var uu____429 -> []
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
        let _0_352 = extract_from_ref_set e1  in
        let _0_351 = extract_from_ref_set e2  in
        FStar_List.append _0_352 _0_351
    | uu____446 ->
        failwith
          (let _0_353 = FStar_Parser_AST.term_to_string e  in
           FStar_Util.format1 "Not a ref set %s" _0_353)
  
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
          let _0_354 = FStar_String.get s (Prims.parse_int "0")  in
          _0_354 = c
      | FStar_Util.Inr s' -> s = s'
  
let matches_level s uu____554 =
  match uu____554 with
  | (assoc_levels,tokens) ->
      let _0_355 = FStar_List.tryFind (matches_token s) tokens  in
      _0_355 <> None
  
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
      let uu____946 = FStar_List.tryFind (matches_level s) level_table  in
      match uu____946 with
      | Some (assoc_levels,uu____971) -> assoc_levels
      | uu____992 -> failwith (Prims.strcat "Unrecognized operator " s)
  
let max : Prims.int -> Prims.int -> Prims.int =
  fun k1  -> fun k2  -> match k1 > k2 with | true  -> k1 | uu____1011 -> k2 
let max_level l =
  let find_level_and_max n1 level =
    let uu____1109 =
      FStar_List.tryFind
        (fun uu____1066  ->
           match uu____1066 with
           | (uu____1075,tokens) -> tokens = (Prims.snd level)) level_table
       in
    match uu____1048 with
    | Some ((uu____1095,l,uu____1097),uu____1098) -> max n l
    | None  ->
        failwith
          (let _0_357 =
             let _0_356 = FStar_List.map token_to_string (Prims.snd level)
                in
             FStar_String.concat "," _0_356  in
           FStar_Util.format1 "Undefined associativity level %s" _0_357)
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
    let _0_358 =
      FStar_List.tryFind (matches_level op) (operatorInfix0ad12 ())  in
    _0_358 <> None
  
let is_operatorInfix34 : Prims.string -> Prims.bool =
  let opinfix34 = [opinfix3 (); opinfix4 ()]  in
  fun op  ->
    let _0_359 = FStar_List.tryFind (matches_level op) opinfix34  in
    _0_359 <> None
  
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
        (match uu____1309 with
         | true  ->
             (FStar_ST.write comment_stack cs;
              (let _0_362 =
                 let _0_361 =
                   let _0_360 = str comment  in
                   FStar_Pprint.op_Hat_Hat _0_360 FStar_Pprint.hardline  in
                 FStar_Pprint.op_Hat_Hat acc _0_361  in
               comments_before_pos _0_362 print_pos lookahead_pos))
         | uu____1318 ->
             let _0_363 = FStar_Range.range_before_pos crange lookahead_pos
                in
             (acc, _0_363))
     in
  let uu____1319 =
    let _0_365 = FStar_Range.end_of_line (FStar_Range.start_of_range tmrange)
       in
    let _0_364 = FStar_Range.end_of_range tmrange  in
    comments_before_pos FStar_Pprint.empty _0_365 _0_364  in
  match uu____1319 with
  | (comments,has_lookahead) ->
      let printed_e = printer tm  in
      let comments =
        match has_lookahead with
        | true  ->
            let pos = FStar_Range.end_of_range tmrange  in
            Prims.fst (comments_before_pos comments pos pos)
        | uu____1327 -> comments  in
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
                  let _0_367 =
                    let _0_366 =
                      FStar_Range.line_of_pos
                        (FStar_Range.start_of_range crange)
                       in
                    _0_366 - lbegin  in
                  max k _0_367  in
                let doc =
                  let _0_370 =
                    let _0_369 =
                      FStar_Pprint.repeat lnum FStar_Pprint.hardline  in
                    let _0_368 = str comment  in
                    FStar_Pprint.op_Hat_Hat _0_369 _0_368  in
                  FStar_Pprint.op_Hat_Hat doc _0_370  in
                let _0_371 =
                  FStar_Range.line_of_pos (FStar_Range.end_of_range crange)
                   in
                place_comments_until_pos (Prims.parse_int "1") _0_371 pos_end
                  doc))
          | uu____1365 ->
              let lnum =
                let _0_373 =
                  let _0_372 = FStar_Range.line_of_pos pos_end  in
                  _0_372 - lbegin  in
                max (Prims.parse_int "1") _0_373  in
              let _0_374 = FStar_Pprint.repeat lnum FStar_Pprint.hardline  in
              FStar_Pprint.op_Hat_Hat doc _0_374
  
let separate_map_with_comments prefix sep f xs extract_range =
  let fold_fun uu____1418 x =
    match uu____1418 with
    | (last_line,doc) ->
        let r = extract_range x  in
        let doc =
          let _0_375 = FStar_Range.start_of_range r  in
          place_comments_until_pos (Prims.parse_int "1") last_line _0_375 doc
           in
        let _0_379 = FStar_Range.line_of_pos (FStar_Range.end_of_range r)  in
        let _0_378 =
          let _0_377 =
            let _0_376 = f x  in FStar_Pprint.op_Hat_Hat sep _0_376  in
          FStar_Pprint.op_Hat_Hat doc _0_377  in
        (_0_379, _0_378)
     in
  let uu____1428 =
    let _0_381 = FStar_List.hd xs  in
    let _0_380 = FStar_List.tl xs  in (_0_381, _0_380)  in
  match uu____1428 with
  | (x,xs) ->
      let init =
        let _0_384 =
          FStar_Range.line_of_pos
            (FStar_Range.end_of_range (extract_range x))
           in
        let _0_383 =
          let _0_382 = f x  in FStar_Pprint.op_Hat_Hat prefix _0_382  in
        (_0_384, _0_383)  in
      Prims.snd (FStar_List.fold_left fold_fun init xs)
  
let rec p_decl : FStar_Parser_AST.decl -> FStar_Pprint.document =
  fun d  ->
    FStar_Pprint.group
      (let _0_391 = FStar_Pprint.optional p_fsdoc d.FStar_Parser_AST.doc  in
       let _0_390 =
         let _0_389 = p_attributes d.FStar_Parser_AST.attrs  in
         let _0_388 =
           let _0_387 = p_qualifiers d.FStar_Parser_AST.quals  in
           let _0_386 =
             let _0_385 = p_rawDecl d  in
             FStar_Pprint.op_Hat_Hat
               (match d.FStar_Parser_AST.quals = [] with
                | true  -> FStar_Pprint.empty
                | uu____1689 -> break1) _0_385
              in
           FStar_Pprint.op_Hat_Hat _0_387 _0_386  in
         FStar_Pprint.op_Hat_Hat _0_389 _0_388  in
       FStar_Pprint.op_Hat_Hat _0_391 _0_390)

and p_attributes : FStar_Parser_AST.attributes_ -> FStar_Pprint.document =
  fun attrs  ->
    let _0_394 =
      let _0_392 = str "@"  in
      FStar_Pprint.op_Hat_Hat FStar_Pprint.lbracket _0_392  in
    let _0_393 =
      FStar_Pprint.op_Hat_Hat FStar_Pprint.rbracket FStar_Pprint.hardline  in
    soft_surround_separate_map (Prims.parse_int "0") (Prims.parse_int "2")
      FStar_Pprint.empty _0_394 FStar_Pprint.space _0_393 p_atomicTerm attrs

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
                    let _0_399 = str "@"  in
                    let _0_398 =
                      let _0_397 = str kwd  in
                      let _0_396 =
                        let _0_395 = str arg  in
                        FStar_Pprint.op_Hat_Hat FStar_Pprint.space _0_395  in
                      FStar_Pprint.op_Hat_Hat _0_397 _0_396  in
                    FStar_Pprint.op_Hat_Hat _0_399 _0_398
                 in
              let _0_401 =
                let _0_400 =
                  FStar_Pprint.separate_map FStar_Pprint.hardline
                    process_kwd_arg kwd_args
                   in
                FStar_Pprint.op_Hat_Hat _0_400 FStar_Pprint.hardline  in
              FStar_Pprint.op_Hat_Hat FStar_Pprint.hardline _0_401
           in
        let _0_409 =
          let _0_408 =
            let _0_407 =
              let _0_406 =
                let _0_405 = str doc  in
                let _0_404 =
                  let _0_403 =
                    let _0_402 =
                      FStar_Pprint.op_Hat_Hat FStar_Pprint.rparen
                        FStar_Pprint.hardline
                       in
                    FStar_Pprint.op_Hat_Hat FStar_Pprint.star _0_402  in
                  FStar_Pprint.op_Hat_Hat kwd_args_doc _0_403  in
                FStar_Pprint.op_Hat_Hat _0_405 _0_404  in
              FStar_Pprint.op_Hat_Hat FStar_Pprint.star _0_406  in
            FStar_Pprint.op_Hat_Hat FStar_Pprint.star _0_407  in
          FStar_Pprint.op_Hat_Hat FStar_Pprint.lparen _0_408  in
        FStar_Pprint.op_Hat_Hat FStar_Pprint.hardline _0_409

and p_rawDecl : FStar_Parser_AST.decl -> FStar_Pprint.document =
  fun d  ->
    match d.FStar_Parser_AST.d with
    | FStar_Parser_AST.Open uid ->
        FStar_Pprint.group
          (let _0_411 = str "open"  in
           let _0_410 = p_quident uid  in
           FStar_Pprint.op_Hat_Slash_Hat _0_411 _0_410)
    | FStar_Parser_AST.Include uid ->
        FStar_Pprint.group
          (let _0_413 = str "include"  in
           let _0_412 = p_quident uid  in
           FStar_Pprint.op_Hat_Slash_Hat _0_413 _0_412)
    | FStar_Parser_AST.ModuleAbbrev (uid1,uid2) ->
        let _0_420 =
          let _0_418 = str "module"  in
          let _0_417 =
            let _0_416 =
              let _0_415 = p_uident uid1  in
              let _0_414 =
                FStar_Pprint.op_Hat_Hat FStar_Pprint.space
                  FStar_Pprint.equals
                 in
              FStar_Pprint.op_Hat_Hat _0_415 _0_414  in
            FStar_Pprint.op_Hat_Hat FStar_Pprint.space _0_416  in
          FStar_Pprint.op_Hat_Hat _0_418 _0_417  in
        let _0_419 = p_quident uid2  in op_Hat_Slash_Plus_Hat _0_420 _0_419
    | FStar_Parser_AST.TopLevelModule uid ->
        FStar_Pprint.group
          (let _0_423 = str "module"  in
           let _0_422 =
             let _0_421 = p_quident uid  in
             FStar_Pprint.op_Hat_Hat FStar_Pprint.space _0_421  in
           FStar_Pprint.op_Hat_Hat _0_423 _0_422)
    | FStar_Parser_AST.Tycon
        (true ,(FStar_Parser_AST.TyconAbbrev (uid,tpars,None ,t),None )::[])
        ->
        let effect_prefix_doc =
          let _0_426 = str "effect"  in
          let _0_425 =
            let _0_424 = p_uident uid  in
            FStar_Pprint.op_Hat_Hat FStar_Pprint.space _0_424  in
          FStar_Pprint.op_Hat_Hat _0_426 _0_425  in
        let _0_429 =
          let _0_427 = p_typars tpars  in
          FStar_Pprint.surround (Prims.parse_int "2") (Prims.parse_int "1")
            effect_prefix_doc _0_427 FStar_Pprint.equals
           in
        let _0_428 = p_typ t  in op_Hat_Slash_Plus_Hat _0_429 _0_428
    | FStar_Parser_AST.Tycon (false ,tcdefs) ->
        let _0_431 = str "type"  in
        let _0_430 = str "and"  in
        precede_break_separate_map _0_431 _0_430 p_fsdocTypeDeclPairs tcdefs
    | FStar_Parser_AST.TopLevelLet (q,lbs) ->
        let let_doc =
          let _0_434 = str "let"  in
          let _0_433 =
            let _0_432 = p_letqualifier q  in
            FStar_Pprint.op_Hat_Hat _0_432 FStar_Pprint.space  in
          FStar_Pprint.op_Hat_Hat _0_434 _0_433  in
        let _0_436 =
          let _0_435 = str "and"  in
          FStar_Pprint.op_Hat_Hat _0_435 FStar_Pprint.space  in
        separate_map_with_comments let_doc _0_436 p_letbinding lbs
          (fun uu____1766  ->
             match uu____1766 with
             | (p,t) ->
                 FStar_Range.union_ranges p.FStar_Parser_AST.prange
                   t.FStar_Parser_AST.range)
    | FStar_Parser_AST.Val (lid,t) ->
        let _0_443 =
          let _0_441 = str "val"  in
          let _0_440 =
            let _0_439 =
              let _0_438 = p_lident lid  in
              let _0_437 =
                FStar_Pprint.op_Hat_Hat FStar_Pprint.space FStar_Pprint.colon
                 in
              FStar_Pprint.op_Hat_Hat _0_438 _0_437  in
            FStar_Pprint.op_Hat_Hat FStar_Pprint.space _0_439  in
          FStar_Pprint.op_Hat_Hat _0_441 _0_440  in
        let _0_442 = p_typ t  in op_Hat_Slash_Plus_Hat _0_443 _0_442
    | FStar_Parser_AST.Assume (id,t) ->
        let decl_keyword =
          let uu____1776 =
            let _0_444 =
              FStar_Util.char_at id.FStar_Ident.idText (Prims.parse_int "0")
               in
            FStar_All.pipe_right _0_444 FStar_Util.is_upper  in
          match uu____1776 with
          | true  -> FStar_Pprint.empty
          | uu____1777 ->
              let _0_445 = str "val"  in
              FStar_Pprint.op_Hat_Hat _0_445 FStar_Pprint.space
           in
        let _0_450 =
          let _0_448 =
            let _0_447 = p_ident id  in
            let _0_446 =
              FStar_Pprint.op_Hat_Hat FStar_Pprint.space FStar_Pprint.colon
               in
            FStar_Pprint.op_Hat_Hat _0_447 _0_446  in
          FStar_Pprint.op_Hat_Hat decl_keyword _0_448  in
        let _0_449 = p_typ t  in op_Hat_Slash_Plus_Hat _0_450 _0_449
    | FStar_Parser_AST.Exception (uid,t_opt) ->
        let _0_457 = str "exception"  in
        let _0_456 =
          let _0_455 =
            let _0_454 = p_uident uid  in
            let _0_453 =
              FStar_Pprint.optional
                (fun t  ->
                   let _0_452 = str "of"  in
                   let _0_451 = p_typ t  in
                   op_Hat_Slash_Plus_Hat _0_452 _0_451) t_opt
               in
            FStar_Pprint.op_Hat_Hat _0_454 _0_453  in
          FStar_Pprint.op_Hat_Hat FStar_Pprint.space _0_455  in
        FStar_Pprint.op_Hat_Hat _0_457 _0_456
    | FStar_Parser_AST.NewEffect ne ->
        let _0_460 = str "new_effect"  in
        let _0_459 =
          let _0_458 = p_newEffect ne  in
          FStar_Pprint.op_Hat_Hat FStar_Pprint.space _0_458  in
        FStar_Pprint.op_Hat_Hat _0_460 _0_459
    | FStar_Parser_AST.SubEffect se ->
        let _0_463 = str "sub_effect"  in
        let _0_462 =
          let _0_461 = p_subEffect se  in
          FStar_Pprint.op_Hat_Hat FStar_Pprint.space _0_461  in
        FStar_Pprint.op_Hat_Hat _0_463 _0_462
    | FStar_Parser_AST.NewEffectForFree ne ->
        let _0_466 = str "new_effect_for_free"  in
        let _0_465 =
          let _0_464 = p_newEffect ne  in
          FStar_Pprint.op_Hat_Hat FStar_Pprint.space _0_464  in
        FStar_Pprint.op_Hat_Hat _0_466 _0_465
    | FStar_Parser_AST.Pragma p -> p_pragma p
    | FStar_Parser_AST.Fsdoc doc ->
        let _0_467 = p_fsdoc doc  in
        FStar_Pprint.op_Hat_Hat _0_467 FStar_Pprint.hardline
    | FStar_Parser_AST.Main uu____1788 ->
        failwith "*Main declaration* : Is that really still in use ??"
    | FStar_Parser_AST.Tycon (true ,uu____2000) ->
        failwith
          "Effect abbreviation is expected to be defined by an abbreviation"

and p_pragma : FStar_Parser_AST.pragma -> FStar_Pprint.document =
  fun uu___117_1798  ->
    match uu___117_1798 with
    | FStar_Parser_AST.SetOptions s ->
        let _0_470 = str "#set-options"  in
        let _0_469 =
          let _0_468 = FStar_Pprint.dquotes (str s)  in
          FStar_Pprint.op_Hat_Hat FStar_Pprint.space _0_468  in
        FStar_Pprint.op_Hat_Hat _0_470 _0_469
    | FStar_Parser_AST.ResetOptions s_opt ->
        let _0_473 = str "#reset-options"  in
        let _0_472 =
          FStar_Pprint.optional
            (fun s  ->
               let _0_471 = FStar_Pprint.dquotes (str s)  in
               FStar_Pprint.op_Hat_Hat FStar_Pprint.space _0_471) s_opt
           in
        FStar_Pprint.op_Hat_Hat _0_473 _0_472
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
        let _0_475 = FStar_Pprint.optional p_fsdoc fsdoc_opt  in
        let _0_474 = p_typeDecl typedecl  in
        FStar_Pprint.op_Hat_Hat _0_475 _0_474

and p_typeDecl : FStar_Parser_AST.tycon -> FStar_Pprint.document =
  fun uu___118_1816  ->
    match uu___118_1816 with
    | FStar_Parser_AST.TyconAbstract (lid,bs,typ_opt) ->
        let empty' uu____1827 = FStar_Pprint.empty  in
        p_typeDeclPrefix lid bs typ_opt empty'
    | FStar_Parser_AST.TyconAbbrev (lid,bs,typ_opt,t) ->
        let f uu____1839 =
          let _0_476 = p_typ t  in prefix2 FStar_Pprint.equals _0_476  in
        p_typeDeclPrefix lid bs typ_opt f
    | FStar_Parser_AST.TyconRecord (lid,bs,typ_opt,record_field_decls) ->
        let p_recordFieldAndComments uu____1865 =
          match uu____1865 with
          | (lid,t,doc_opt) ->
              let _0_477 =
                FStar_Range.extend_to_end_of_line t.FStar_Parser_AST.range
                 in
              with_comment p_recordFieldDecl (lid, t, doc_opt) _0_477
           in
        let p_fields uu____1883 =
          let _0_480 =
            let _0_479 =
              braces_with_nesting
                (let _0_478 =
                   FStar_Pprint.op_Hat_Hat FStar_Pprint.semi break1  in
                 FStar_Pprint.separate_map _0_478 p_recordFieldAndComments
                   record_field_decls)
               in
            FStar_Pprint.op_Hat_Hat FStar_Pprint.space _0_479  in
          FStar_Pprint.op_Hat_Hat FStar_Pprint.equals _0_480  in
        p_typeDeclPrefix lid bs typ_opt p_fields
    | FStar_Parser_AST.TyconVariant (lid,bs,typ_opt,ct_decls) ->
        let p_constructorBranchAndComments uu____2146 =
          match uu____2146 with
          | (uid,t_opt,doc_opt,use_of) ->
              let range =
                FStar_Range.extend_to_end_of_line
                  (let _0_481 =
                     FStar_Util.map_opt t_opt
                       (fun t  -> t.FStar_Parser_AST.range)
                      in
                   FStar_Util.dflt uid.FStar_Ident.idRange _0_481)
                 in
              let p_constructorBranch decl =
                FStar_Pprint.group
                  (let _0_483 =
                     let _0_482 = p_constructorDecl decl  in
                     FStar_Pprint.op_Hat_Hat FStar_Pprint.space _0_482  in
                   FStar_Pprint.op_Hat_Hat FStar_Pprint.bar _0_483)
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
             let _0_484 = datacon_doc ()  in
             prefix2 FStar_Pprint.equals _0_484)

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
          match (bs = []) && (typ_opt = None) with
          | true  ->
              let _0_487 = p_ident lid  in
              let _0_486 =
                let _0_485 = cont ()  in
                FStar_Pprint.op_Hat_Hat FStar_Pprint.space _0_485  in
              FStar_Pprint.op_Hat_Hat _0_487 _0_486
          | uu____1981 ->
              let binders_doc =
                let _0_492 = p_typars bs  in
                let _0_491 =
                  FStar_Pprint.optional
                    (fun t  ->
                       let _0_490 =
                         let _0_489 =
                           let _0_488 = p_typ t  in
                           FStar_Pprint.op_Hat_Hat FStar_Pprint.space _0_488
                            in
                         FStar_Pprint.op_Hat_Hat FStar_Pprint.colon _0_489
                          in
                       FStar_Pprint.op_Hat_Hat break1 _0_490) typ_opt
                   in
                FStar_Pprint.op_Hat_Hat _0_492 _0_491  in
              let _0_494 = p_ident lid  in
              let _0_493 = cont ()  in
              FStar_Pprint.surround (Prims.parse_int "2")
                (Prims.parse_int "1") _0_494 binders_doc _0_493

and p_recordFieldDecl :
  (FStar_Ident.ident * FStar_Parser_AST.term * FStar_Parser_AST.fsdoc
    Prims.option) -> FStar_Pprint.document
  =
  fun uu____2229  ->
    match uu____2229 with
    | (lid,t,doc_opt) ->
        FStar_Pprint.group
          (let _0_499 = FStar_Pprint.optional p_fsdoc doc_opt  in
           let _0_498 =
             let _0_497 = p_lident lid  in
             let _0_496 =
               let _0_495 = p_typ t  in
               FStar_Pprint.op_Hat_Hat FStar_Pprint.colon _0_495  in
             FStar_Pprint.op_Hat_Hat _0_497 _0_496  in
           FStar_Pprint.op_Hat_Hat _0_499 _0_498)

and p_constructorDecl :
  (FStar_Ident.ident * FStar_Parser_AST.term Prims.option *
    FStar_Parser_AST.fsdoc Prims.option * Prims.bool) ->
    FStar_Pprint.document
  =
  fun uu____2245  ->
    match uu____2245 with
    | (uid,t_opt,doc_opt,use_of) ->
        let sep =
          match use_of with
          | true  -> str "of"
          | uu____2010 -> FStar_Pprint.colon  in
        let uid_doc = p_uident uid  in
        let _0_504 = FStar_Pprint.optional p_fsdoc doc_opt  in
        let _0_503 =
          default_or_map uid_doc
            (fun t  ->
               let _0_502 =
                 let _0_500 = FStar_Pprint.op_Hat_Hat FStar_Pprint.space sep
                    in
                 FStar_Pprint.op_Hat_Hat uid_doc _0_500  in
               let _0_501 = p_typ t  in op_Hat_Slash_Plus_Hat _0_502 _0_501)
            t_opt
           in
        FStar_Pprint.op_Hat_Hat _0_504 _0_503

and p_letbinding :
  (FStar_Parser_AST.pattern * FStar_Parser_AST.term) -> FStar_Pprint.document
  =
  fun uu____2271  ->
    match uu____2271 with
    | (pat,e) ->
        let pat_doc =
          let uu____2277 =
            match pat.FStar_Parser_AST.pat with
            | FStar_Parser_AST.PatAscribed (pat,t) ->
                let _0_508 =
                  let _0_507 =
                    FStar_Pprint.group
                      (let _0_506 =
                         let _0_505 = p_tmArrow p_tmNoEq t  in
                         FStar_Pprint.op_Hat_Hat FStar_Pprint.space _0_505
                          in
                       FStar_Pprint.op_Hat_Hat FStar_Pprint.colon _0_506)
                     in
                  FStar_Pprint.op_Hat_Hat break1 _0_507  in
                (pat, _0_508)
            | uu____2026 -> (pat, FStar_Pprint.empty)  in
          match uu____2019 with
          | (pat,ascr_doc) ->
              (match pat.FStar_Parser_AST.pat with
               | FStar_Parser_AST.PatApp
                   ({
                      FStar_Parser_AST.pat = FStar_Parser_AST.PatVar
                        (x,uu____2293);
                      FStar_Parser_AST.prange = uu____2294;_},pats)
                   ->
                   let _0_511 = p_lident x  in
                   let _0_510 =
                     let _0_509 =
                       FStar_Pprint.separate_map break1 p_atomicPattern pats
                        in
                     FStar_Pprint.op_Hat_Hat _0_509 ascr_doc  in
                   FStar_Pprint.surround (Prims.parse_int "2")
                     (Prims.parse_int "1") _0_511 _0_510 FStar_Pprint.equals
               | uu____2037 ->
                   FStar_Pprint.group
                     (let _0_513 = p_tuplePattern pat  in
                      let _0_512 =
                        FStar_Pprint.op_Hat_Slash_Hat ascr_doc
                          FStar_Pprint.equals
                         in
                      FStar_Pprint.op_Hat_Hat _0_513 _0_512))
           in
        let _0_514 = p_term e  in prefix2 pat_doc _0_514

and p_newEffect : FStar_Parser_AST.effect_decl -> FStar_Pprint.document =
  fun uu___119_2038  ->
    match uu___119_2038 with
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
        let _0_518 = p_uident uid  in
        let _0_517 = p_binders true bs  in
        let _0_516 =
          let _0_515 = p_simpleTerm t  in prefix2 FStar_Pprint.equals _0_515
           in
        FStar_Pprint.surround (Prims.parse_int "2") (Prims.parse_int "1")
          _0_518 _0_517 _0_516

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
          fun action_decls  ->
            braces_with_nesting
              (let _0_528 =
                 FStar_Pprint.group
                   (let _0_522 = p_uident uid  in
                    let _0_521 = p_binders true bs  in
                    let _0_520 =
                      let _0_519 = p_typ t  in
                      prefix2 FStar_Pprint.colon _0_519  in
                    FStar_Pprint.surround (Prims.parse_int "2")
                      (Prims.parse_int "1") _0_522 _0_521 _0_520)
                  in
               let _0_527 =
                 let _0_526 =
                   let _0_524 = str "with"  in
                   let _0_523 =
                     separate_break_map FStar_Pprint.semi p_effectDecl
                       eff_decls
                      in
                   prefix2 _0_524 _0_523  in
                 let _0_525 = p_actionDecls action_decls  in
                 FStar_Pprint.op_Hat_Hat _0_526 _0_525  in
               FStar_Pprint.op_Hat_Slash_Hat _0_528 _0_527)

and p_actionDecls : FStar_Parser_AST.decl Prims.list -> FStar_Pprint.document
  =
  fun uu___120_2067  ->
    match uu___120_2067 with
    | [] -> FStar_Pprint.empty
    | l ->
        let _0_531 =
          let _0_530 = str "and actions"  in
          let _0_529 = separate_break_map FStar_Pprint.semi p_effectDecl l
             in
          prefix2 _0_530 _0_529  in
        FStar_Pprint.op_Hat_Hat break1 _0_531

and p_effectDecl : FStar_Parser_AST.decl -> FStar_Pprint.document =
  fun d  ->
    match d.FStar_Parser_AST.d with
    | FStar_Parser_AST.Tycon
        (false ,(FStar_Parser_AST.TyconAbbrev (lid,[],None ,e),None )::[]) ->
        let _0_535 =
          let _0_533 = p_lident lid  in
          let _0_532 =
            FStar_Pprint.op_Hat_Hat FStar_Pprint.space FStar_Pprint.equals
             in
          FStar_Pprint.op_Hat_Hat _0_533 _0_532  in
        let _0_534 = p_simpleTerm e  in prefix2 _0_535 _0_534
    | uu____2087 ->
        failwith
          (let _0_536 = FStar_Parser_AST.decl_to_string d  in
           FStar_Util.format1
             "Not a declaration of an effect member... or at least I hope so : %s"
             _0_536)

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
            let _0_540 =
              let _0_538 = str kwd  in
              let _0_537 =
                FStar_Pprint.op_Hat_Hat FStar_Pprint.space
                  FStar_Pprint.equals
                 in
              FStar_Pprint.op_Hat_Hat _0_538 _0_537  in
            let _0_539 = p_simpleTerm t  in prefix2 _0_540 _0_539
         in
      separate_break_map FStar_Pprint.semi p_lift lifts  in
    let _0_548 =
      let _0_545 =
        let _0_543 = p_quident lift.FStar_Parser_AST.msource  in
        let _0_542 =
          let _0_541 = str "~>"  in
          FStar_Pprint.op_Hat_Hat FStar_Pprint.space _0_541  in
        FStar_Pprint.op_Hat_Hat _0_543 _0_542  in
      let _0_544 = p_quident lift.FStar_Parser_AST.mdest  in
      prefix2 _0_545 _0_544  in
    let _0_547 =
      let _0_546 = braces_with_nesting lift_op_doc  in
      FStar_Pprint.op_Hat_Hat FStar_Pprint.space _0_546  in
    FStar_Pprint.op_Hat_Hat _0_548 _0_547

and p_qualifier : FStar_Parser_AST.qualifier -> FStar_Pprint.document =
  fun uu___121_2127  ->
    match uu___121_2127 with
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
  fun uu___122_2129  ->
    match uu___122_2129 with
    | FStar_Parser_AST.Rec  ->
        let _0_549 = str "rec"  in
        FStar_Pprint.op_Hat_Hat FStar_Pprint.space _0_549
    | FStar_Parser_AST.Mutable  ->
        let _0_550 = str "mutable"  in
        FStar_Pprint.op_Hat_Hat FStar_Pprint.space _0_550
    | FStar_Parser_AST.NoLetQualifier  -> FStar_Pprint.empty

and p_aqual : FStar_Parser_AST.arg_qualifier -> FStar_Pprint.document =
  fun uu___123_2130  ->
    match uu___123_2130 with
    | FStar_Parser_AST.Implicit  -> str "#"
    | FStar_Parser_AST.Equality  -> str "$"

and p_disjunctivePattern : FStar_Parser_AST.pattern -> FStar_Pprint.document
  =
  fun p  ->
    match p.FStar_Parser_AST.pat with
    | FStar_Parser_AST.PatOr pats ->
        FStar_Pprint.group
          (let _0_552 =
             let _0_551 =
               FStar_Pprint.op_Hat_Hat FStar_Pprint.bar FStar_Pprint.space
                in
             FStar_Pprint.op_Hat_Hat break1 _0_551  in
           FStar_Pprint.separate_map _0_552 p_tuplePattern pats)
    | uu____2134 -> p_tuplePattern p

and p_tuplePattern : FStar_Parser_AST.pattern -> FStar_Pprint.document =
  fun p  ->
    match p.FStar_Parser_AST.pat with
    | FStar_Parser_AST.PatTuple (pats,false ) ->
        FStar_Pprint.group
          (let _0_553 = FStar_Pprint.op_Hat_Hat FStar_Pprint.comma break1  in
           FStar_Pprint.separate_map _0_553 p_constructorPattern pats)
    | uu____2139 -> p_constructorPattern p

and p_constructorPattern : FStar_Parser_AST.pattern -> FStar_Pprint.document
  =
  fun p  ->
    match p.FStar_Parser_AST.pat with
    | FStar_Parser_AST.PatApp
        ({ FStar_Parser_AST.pat = FStar_Parser_AST.PatName maybe_cons_lid;
           FStar_Parser_AST.prange = uu____2443;_},hd1::tl1::[])
        when
        FStar_Ident.lid_equals maybe_cons_lid FStar_Syntax_Const.cons_lid ->
        let _0_556 =
          FStar_Pprint.op_Hat_Hat FStar_Pprint.colon FStar_Pprint.colon  in
        let _0_555 = p_constructorPattern hd  in
        let _0_554 = p_constructorPattern tl  in infix0 _0_556 _0_555 _0_554
    | FStar_Parser_AST.PatApp
        ({ FStar_Parser_AST.pat = FStar_Parser_AST.PatName uid;
           FStar_Parser_AST.prange = uu____2451;_},pats)
        ->
        let _0_558 = p_quident uid  in
        let _0_557 = FStar_Pprint.separate_map break1 p_atomicPattern pats
           in
        prefix2 _0_558 _0_557
    | uu____2151 -> p_atomicPattern p

and p_atomicPattern : FStar_Parser_AST.pattern -> FStar_Pprint.document =
  fun p  ->
    match p.FStar_Parser_AST.pat with
    | FStar_Parser_AST.PatAscribed (pat,t) ->
        let uu____2155 =
          let _0_559 = (unparen t).FStar_Parser_AST.tm  in
          ((pat.FStar_Parser_AST.pat), _0_559)  in
        (match uu____2155 with
         | (FStar_Parser_AST.PatVar (lid,aqual),FStar_Parser_AST.Refine
            ({ FStar_Parser_AST.b = FStar_Parser_AST.Annotated (lid',t1);
               FStar_Parser_AST.brange = uu____2470;
               FStar_Parser_AST.blevel = uu____2471;
               FStar_Parser_AST.aqual = uu____2472;_},phi))
             when lid.FStar_Ident.idText = lid'.FStar_Ident.idText ->
             soft_parens_with_nesting
               (let _0_560 = p_ident lid  in p_refinement aqual _0_560 t phi)
         | (FStar_Parser_AST.PatWild ,FStar_Parser_AST.Refine
            ({ FStar_Parser_AST.b = FStar_Parser_AST.NoName t1;
               FStar_Parser_AST.brange = uu____2479;
               FStar_Parser_AST.blevel = uu____2480;
               FStar_Parser_AST.aqual = uu____2481;_},phi))
             ->
             soft_parens_with_nesting
               (p_refinement None FStar_Pprint.underscore t phi)
         | uu____2173 ->
             soft_parens_with_nesting
               (let _0_565 = p_tuplePattern pat  in
                let _0_564 =
                  let _0_563 = FStar_Pprint.break_ (Prims.parse_int "0")  in
                  let _0_562 =
                    let _0_561 = p_typ t  in
                    FStar_Pprint.op_Hat_Hat FStar_Pprint.colon _0_561  in
                  FStar_Pprint.op_Hat_Hat _0_563 _0_562  in
                FStar_Pprint.op_Hat_Hat _0_565 _0_564))
    | FStar_Parser_AST.PatList pats ->
        let _0_566 = separate_break_map FStar_Pprint.semi p_tuplePattern pats
           in
        FStar_Pprint.surround (Prims.parse_int "2") (Prims.parse_int "0")
          FStar_Pprint.lbracket uu____2495 FStar_Pprint.rbracket
    | FStar_Parser_AST.PatRecord pats ->
        let p_recordFieldPat uu____2505 =
          match uu____2505 with
          | (lid,pat) ->
              let _0_568 = p_qlident lid  in
              let _0_567 = p_tuplePattern pat  in
              infix2 FStar_Pprint.equals _0_568 _0_567
           in
        soft_braces_with_nesting
          (separate_break_map FStar_Pprint.semi p_recordFieldPat pats)
    | FStar_Parser_AST.PatTuple (pats,true ) ->
        let _0_571 =
          FStar_Pprint.op_Hat_Hat FStar_Pprint.lparen FStar_Pprint.bar  in
        let _0_570 =
          separate_break_map FStar_Pprint.comma p_constructorPattern pats  in
        let _0_569 =
          FStar_Pprint.op_Hat_Hat FStar_Pprint.bar FStar_Pprint.rparen  in
        FStar_Pprint.surround (Prims.parse_int "2") (Prims.parse_int "1")
          uu____2518 uu____2519 uu____2520
    | FStar_Parser_AST.PatTvar (tv,arg_qualifier_opt) -> p_tvar tv
    | FStar_Parser_AST.PatOp op ->
        let _0_575 =
          let _0_574 =
            let _0_573 = str op  in
            let _0_572 =
              FStar_Pprint.op_Hat_Hat FStar_Pprint.space FStar_Pprint.rparen
               in
            FStar_Pprint.op_Hat_Hat _0_573 _0_572  in
          FStar_Pprint.op_Hat_Hat FStar_Pprint.space _0_574  in
        FStar_Pprint.op_Hat_Hat FStar_Pprint.lparen _0_575
    | FStar_Parser_AST.PatWild  -> FStar_Pprint.underscore
    | FStar_Parser_AST.PatConst c -> p_constant c
    | FStar_Parser_AST.PatVar (lid,aqual) ->
        let _0_577 = FStar_Pprint.optional p_aqual aqual  in
        let _0_576 = p_lident lid  in FStar_Pprint.op_Hat_Hat _0_577 _0_576
    | FStar_Parser_AST.PatName uid -> p_quident uid
    | FStar_Parser_AST.PatOr uu____2539 -> failwith "Inner or pattern !"
    | FStar_Parser_AST.PatApp
      ({ FStar_Parser_AST.pat = FStar_Parser_AST.PatName _;
         FStar_Parser_AST.prange = _;_},_)|FStar_Parser_AST.PatTuple
      (_,false ) -> soft_parens_with_nesting (p_tuplePattern p)
    | uu____2217 ->
        failwith
          (let _0_578 = FStar_Parser_AST.pat_to_string p  in
           FStar_Util.format1 "Invalid pattern %s" _0_578)

and p_binder : Prims.bool -> FStar_Parser_AST.binder -> FStar_Pprint.document
  =
  fun is_atomic  ->
    fun b  ->
      match b.FStar_Parser_AST.b with
      | FStar_Parser_AST.Variable lid ->
          let _0_580 = FStar_Pprint.optional p_aqual b.FStar_Parser_AST.aqual
             in
          let _0_579 = p_lident lid  in FStar_Pprint.op_Hat_Hat _0_580 _0_579
      | FStar_Parser_AST.TVariable lid -> p_lident lid
      | FStar_Parser_AST.Annotated (lid,t) ->
          let doc =
            let uu____2225 = (unparen t).FStar_Parser_AST.tm  in
            match uu____2225 with
            | FStar_Parser_AST.Refine
                ({ FStar_Parser_AST.b = FStar_Parser_AST.Annotated (lid',t1);
                   FStar_Parser_AST.brange = uu____2564;
                   FStar_Parser_AST.blevel = uu____2565;
                   FStar_Parser_AST.aqual = uu____2566;_},phi)
                when lid.FStar_Ident.idText = lid'.FStar_Ident.idText ->
                let _0_581 = p_ident lid  in
                p_refinement b.FStar_Parser_AST.aqual _0_581 t phi
            | uu____2232 ->
                let _0_588 =
                  FStar_Pprint.optional p_aqual b.FStar_Parser_AST.aqual  in
                let _0_587 =
                  let _0_586 = p_lident lid  in
                  let _0_585 =
                    let _0_584 =
                      let _0_583 = FStar_Pprint.break_ (Prims.parse_int "0")
                         in
                      let _0_582 = p_tmFormula t  in
                      FStar_Pprint.op_Hat_Hat _0_583 _0_582  in
                    FStar_Pprint.op_Hat_Hat FStar_Pprint.colon _0_584  in
                  FStar_Pprint.op_Hat_Hat _0_586 _0_585  in
                FStar_Pprint.op_Hat_Hat _0_588 _0_587
             in
          (match is_atomic with
           | true  ->
               FStar_Pprint.group
                 (let _0_589 =
                    FStar_Pprint.op_Hat_Hat doc FStar_Pprint.rparen  in
                  FStar_Pprint.op_Hat_Hat FStar_Pprint.lparen _0_589)
           | uu____2233 -> FStar_Pprint.group doc)
      | FStar_Parser_AST.TAnnotated uu____2234 ->
          failwith "Is this still used ?"
      | FStar_Parser_AST.NoName t ->
          let uu____2238 = (unparen t).FStar_Parser_AST.tm  in
          (match uu____2238 with
           | FStar_Parser_AST.Refine
               ({ FStar_Parser_AST.b = FStar_Parser_AST.NoName t1;
                  FStar_Parser_AST.brange = uu____2587;
                  FStar_Parser_AST.blevel = uu____2588;
                  FStar_Parser_AST.aqual = uu____2589;_},phi)
               ->
               (match is_atomic with
                | true  ->
                    FStar_Pprint.group
                      (let _0_591 =
                         let _0_590 =
                           p_refinement b.FStar_Parser_AST.aqual
                             FStar_Pprint.underscore t phi
                            in
                         FStar_Pprint.op_Hat_Hat _0_590 FStar_Pprint.rparen
                          in
                       FStar_Pprint.op_Hat_Hat FStar_Pprint.lparen _0_591)
                | uu____2244 ->
                    FStar_Pprint.group
                      (p_refinement b.FStar_Parser_AST.aqual
                         FStar_Pprint.underscore t phi))
           | uu____2245 ->
               (match is_atomic with
                | true  -> p_atomicTerm t
                | uu____2246 -> p_appTerm t))

and p_refinement :
  FStar_Parser_AST.arg_qualifier Prims.option ->
    FStar_Pprint.document ->
      FStar_Parser_AST.term -> FStar_Parser_AST.term -> FStar_Pprint.document
  =
  fun aqual_opt  ->
    fun binder  ->
      fun t  ->
        fun phi  ->
          let _0_597 = FStar_Pprint.optional p_aqual aqual_opt  in
          let _0_596 =
            let _0_595 =
              let _0_594 =
                let _0_593 = p_appTerm t  in
                let _0_592 = soft_braces_with_nesting (p_noSeqTerm phi)  in
                FStar_Pprint.op_Hat_Hat _0_593 _0_592  in
              FStar_Pprint.op_Hat_Hat FStar_Pprint.colon _0_594  in
            FStar_Pprint.op_Hat_Hat binder _0_595  in
          FStar_Pprint.op_Hat_Hat _0_597 _0_596

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
    match FStar_Util.starts_with FStar_Ident.reserved_prefix
            id.FStar_Ident.idText
    with
    | true  -> FStar_Pprint.underscore
    | uu____2262 -> p_lident id

and p_term : FStar_Parser_AST.term -> FStar_Pprint.document =
  fun e  ->
    let uu____2264 = (unparen e).FStar_Parser_AST.tm  in
    match uu____2264 with
    | FStar_Parser_AST.Seq (e1,e2) ->
        let _0_600 =
          FStar_Pprint.group
            (let _0_598 = p_noSeqTerm e1  in
             FStar_Pprint.op_Hat_Hat _0_598 FStar_Pprint.semi)
           in
        let _0_599 = p_term e2  in
        FStar_Pprint.op_Hat_Slash_Hat _0_600 _0_599
    | uu____2267 -> FStar_Pprint.group (p_noSeqTerm e)

and p_noSeqTerm : FStar_Parser_AST.term -> FStar_Pprint.document =
  fun e  -> with_comment p_noSeqTerm' e e.FStar_Parser_AST.range

and p_noSeqTerm' : FStar_Parser_AST.term -> FStar_Pprint.document =
  fun e  ->
    let uu____2270 = (unparen e).FStar_Parser_AST.tm  in
    match uu____2270 with
    | FStar_Parser_AST.Ascribed (e,t) ->
        FStar_Pprint.group
          (let _0_604 = p_tmIff e  in
           let _0_603 =
             let _0_602 =
               let _0_601 = p_typ t  in
               FStar_Pprint.op_Hat_Slash_Hat FStar_Pprint.colon _0_601  in
             FStar_Pprint.op_Hat_Hat FStar_Pprint.langle _0_602  in
           FStar_Pprint.op_Hat_Slash_Hat _0_604 _0_603)
    | FStar_Parser_AST.Op (op,e1::e2::e3::[]) when op = ".()<-" ->
        FStar_Pprint.group
          (let _0_611 =
             FStar_Pprint.group
               (let _0_609 = p_atomicTermNotQUident e1  in
                let _0_608 =
                  let _0_607 =
                    let _0_606 = soft_parens_with_nesting (p_term e2)  in
                    let _0_605 =
                      FStar_Pprint.op_Hat_Hat FStar_Pprint.space
                        FStar_Pprint.larrow
                       in
                    FStar_Pprint.op_Hat_Hat _0_606 _0_605  in
                  FStar_Pprint.op_Hat_Hat FStar_Pprint.dot _0_607  in
                FStar_Pprint.op_Hat_Hat _0_609 _0_608)
              in
           let _0_610 = jump2 (p_noSeqTerm e3)  in
           FStar_Pprint.op_Hat_Hat _0_611 _0_610)
    | FStar_Parser_AST.Op (op,e1::e2::e3::[]) when op = ".[]<-" ->
        FStar_Pprint.group
          (let _0_618 =
             FStar_Pprint.group
               (let _0_616 = p_atomicTermNotQUident e1  in
                let _0_615 =
                  let _0_614 =
                    let _0_613 = soft_brackets_with_nesting (p_term e2)  in
                    let _0_612 =
                      FStar_Pprint.op_Hat_Hat FStar_Pprint.space
                        FStar_Pprint.larrow
                       in
                    FStar_Pprint.op_Hat_Hat _0_613 _0_612  in
                  FStar_Pprint.op_Hat_Hat FStar_Pprint.dot _0_614  in
                FStar_Pprint.op_Hat_Hat _0_616 _0_615)
              in
           let _0_617 = jump2 (p_noSeqTerm e3)  in
           FStar_Pprint.op_Hat_Hat _0_618 _0_617)
    | FStar_Parser_AST.Requires (e,wtf) ->
        FStar_Pprint.group
          (let _0_620 = str "requires"  in
           let _0_619 = p_typ e  in
           FStar_Pprint.op_Hat_Slash_Hat _0_620 _0_619)
    | FStar_Parser_AST.Ensures (e,wtf) ->
        FStar_Pprint.group
          (let _0_622 = str "ensures"  in
           let _0_621 = p_typ e  in
           FStar_Pprint.op_Hat_Slash_Hat _0_622 _0_621)
    | FStar_Parser_AST.Attributes es ->
        FStar_Pprint.group
          (let _0_624 = str "attributes"  in
           let _0_623 = FStar_Pprint.separate_map break1 p_atomicTerm es  in
           FStar_Pprint.op_Hat_Slash_Hat _0_624 _0_623)
    | FStar_Parser_AST.If (e1,e2,e3) ->
        let uu____2298 = is_unit e3  in
        (match uu____2298 with
         | true  ->
             FStar_Pprint.group
               (let _0_630 =
                  let _0_626 = str "if"  in
                  let _0_625 = p_noSeqTerm e1  in
                  op_Hat_Slash_Plus_Hat _0_626 _0_625  in
                let _0_629 =
                  let _0_628 = str "then"  in
                  let _0_627 = p_noSeqTerm e2  in
                  op_Hat_Slash_Plus_Hat _0_628 _0_627  in
                FStar_Pprint.op_Hat_Slash_Hat _0_630 _0_629)
         | uu____2299 ->
             let e2_doc =
               let uu____2301 = (unparen e2).FStar_Parser_AST.tm  in
               match uu____2301 with
               | FStar_Parser_AST.If (uu____2302,uu____2303,e3) when
                   is_unit e3 -> soft_parens_with_nesting (p_noSeqTerm e2)
               | uu____2305 -> p_noSeqTerm e2  in
             FStar_Pprint.group
               (let _0_639 =
                  let _0_632 = str "if"  in
                  let _0_631 = p_noSeqTerm e1  in
                  op_Hat_Slash_Plus_Hat _0_632 _0_631  in
                let _0_638 =
                  let _0_637 =
                    let _0_633 = str "then"  in
                    op_Hat_Slash_Plus_Hat _0_633 e2_doc  in
                  let _0_636 =
                    let _0_635 = str "else"  in
                    let _0_634 = p_noSeqTerm e3  in
                    op_Hat_Slash_Plus_Hat _0_635 _0_634  in
                  FStar_Pprint.op_Hat_Slash_Hat _0_637 _0_636  in
                FStar_Pprint.op_Hat_Slash_Hat _0_639 _0_638))
    | FStar_Parser_AST.TryWith (e,branches) ->
        FStar_Pprint.group
          (let _0_645 =
             let _0_641 = str "try"  in
             let _0_640 = p_noSeqTerm e  in prefix2 _0_641 _0_640  in
           let _0_644 =
             let _0_643 = str "with"  in
             let _0_642 =
               FStar_Pprint.separate_map FStar_Pprint.hardline
                 p_patternBranch branches
                in
             FStar_Pprint.op_Hat_Slash_Hat _0_643 _0_642  in
           FStar_Pprint.op_Hat_Slash_Hat _0_645 _0_644)
    | FStar_Parser_AST.Match (e,branches) ->
        FStar_Pprint.group
          (let _0_650 =
             let _0_648 = str "match"  in
             let _0_647 = p_noSeqTerm e  in
             let _0_646 = str "with"  in
             FStar_Pprint.surround (Prims.parse_int "2")
               (Prims.parse_int "1") _0_648 _0_647 _0_646
              in
           let _0_649 =
             FStar_Pprint.separate_map FStar_Pprint.hardline p_patternBranch
               branches
              in
           FStar_Pprint.op_Hat_Slash_Hat _0_650 _0_649)
    | FStar_Parser_AST.LetOpen (uid,e) ->
        FStar_Pprint.group
          (let _0_655 =
             let _0_653 = str "let open"  in
             let _0_652 = p_quident uid  in
             let _0_651 = str "in"  in
             FStar_Pprint.surround (Prims.parse_int "2")
               (Prims.parse_int "1") _0_653 _0_652 _0_651
              in
           let _0_654 = p_term e  in
           FStar_Pprint.op_Hat_Slash_Hat _0_655 _0_654)
    | FStar_Parser_AST.Let (q,lbs,e) ->
        let let_doc =
          let _0_657 = str "let"  in
          let _0_656 = p_letqualifier q  in
          FStar_Pprint.op_Hat_Hat _0_657 _0_656  in
        let _0_662 =
          FStar_Pprint.group
            (let _0_660 =
               let _0_658 = str "and"  in
               precede_break_separate_map let_doc _0_658 p_letbinding lbs  in
             let _0_659 = str "in"  in
             FStar_Pprint.op_Hat_Slash_Hat _0_660 _0_659)
           in
        let _0_661 = p_term e  in FStar_Pprint.op_Hat_Slash_Hat _0_662 _0_661
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
        FStar_Pprint.group
          (let _0_664 = str "function"  in
           let _0_663 =
             FStar_Pprint.separate_map FStar_Pprint.hardline p_patternBranch
               branches
              in
           FStar_Pprint.op_Hat_Slash_Hat _0_664 _0_663)
    | FStar_Parser_AST.Assign (id,e) ->
        FStar_Pprint.group
          (let _0_667 = p_lident id  in
           let _0_666 =
             let _0_665 = p_noSeqTerm e  in
             FStar_Pprint.op_Hat_Slash_Hat FStar_Pprint.larrow _0_665  in
           FStar_Pprint.op_Hat_Slash_Hat _0_667 _0_666)
    | uu____2378 -> p_typ e

and p_typ : FStar_Parser_AST.term -> FStar_Pprint.document =
  fun e  -> with_comment p_typ' e e.FStar_Parser_AST.range

and p_typ' : FStar_Parser_AST.term -> FStar_Pprint.document =
  fun e  ->
    let uu____2381 = (unparen e).FStar_Parser_AST.tm  in
    match uu____2381 with
    | FStar_Parser_AST.QForall (bs,trigger,e1)|FStar_Parser_AST.QExists
      (bs,trigger,e1) ->
        let _0_674 =
          let _0_670 =
            let _0_668 = p_quantifier e  in
            FStar_Pprint.op_Hat_Hat _0_668 FStar_Pprint.space  in
          let _0_669 = p_binders true bs  in
          FStar_Pprint.soft_surround (Prims.parse_int "2")
            (Prims.parse_int "0") _0_670 _0_669 FStar_Pprint.dot
           in
        let _0_673 =
          let _0_672 = p_trigger trigger  in
          let _0_671 = p_noSeqTerm e1  in
          FStar_Pprint.op_Hat_Hat _0_672 _0_671  in
        prefix2 _0_674 _0_673
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
  fun uu___135_2892  ->
    match uu___135_2892 with
    | [] -> FStar_Pprint.empty
    | pats ->
        let _0_680 =
          let _0_679 =
            let _0_678 = str "pattern"  in
            let _0_677 =
              let _0_676 = jump2 (p_disjunctivePats pats)  in
              let _0_675 = FStar_Pprint.op_Hat_Hat FStar_Pprint.rbrace break1
                 in
              FStar_Pprint.op_Hat_Slash_Hat _0_676 _0_675  in
            FStar_Pprint.op_Hat_Slash_Hat _0_678 _0_677  in
          FStar_Pprint.op_Hat_Hat FStar_Pprint.colon _0_679  in
        FStar_Pprint.op_Hat_Hat FStar_Pprint.lbrace _0_680

and p_disjunctivePats :
  FStar_Parser_AST.term Prims.list Prims.list -> FStar_Pprint.document =
  fun pats  ->
    let _0_681 = str "\\/"  in
    FStar_Pprint.separate_map _0_681 p_conjunctivePats pats

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
        let _0_686 =
          let _0_684 = str "fun"  in
          let _0_683 =
            let _0_682 =
              FStar_Pprint.separate_map break1 p_atomicPattern pats  in
            FStar_Pprint.op_Hat_Slash_Hat _0_682 FStar_Pprint.rarrow  in
          op_Hat_Slash_Plus_Hat _0_684 _0_683  in
        let _0_685 = p_term e  in op_Hat_Slash_Plus_Hat _0_686 _0_685
    | uu____2434 -> p_tmIff e

and p_maybeFocusArrow : Prims.bool -> FStar_Pprint.document =
  fun b  ->
    match b with | true  -> str "~>" | uu____2436 -> FStar_Pprint.rarrow

and p_patternBranch :
  (FStar_Parser_AST.pattern * FStar_Parser_AST.term Prims.option *
    FStar_Parser_AST.term) -> FStar_Pprint.document
  =
  fun uu____2929  ->
    match uu____2929 with
    | (pat,when_opt,e) ->
        let maybe_paren =
          let uu____2450 = (unparen e).FStar_Parser_AST.tm  in
          match uu____2450 with
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
          | uu____2475 -> (fun x  -> x)  in
        FStar_Pprint.group
          (let _0_693 =
             FStar_Pprint.group
               (let _0_691 =
                  let _0_690 =
                    let _0_689 = p_disjunctivePattern pat  in
                    let _0_688 =
                      let _0_687 = p_maybeWhen when_opt  in
                      FStar_Pprint.op_Hat_Hat _0_687 FStar_Pprint.rarrow  in
                    op_Hat_Slash_Plus_Hat _0_689 _0_688  in
                  FStar_Pprint.op_Hat_Hat FStar_Pprint.space _0_690  in
                FStar_Pprint.op_Hat_Hat FStar_Pprint.bar _0_691)
              in
           let _0_692 = maybe_paren (p_term e)  in
           op_Hat_Slash_Plus_Hat _0_693 _0_692)

and p_maybeWhen : FStar_Parser_AST.term Prims.option -> FStar_Pprint.document
  =
  fun uu___136_2980  ->
    match uu___136_2980 with
    | None  -> FStar_Pprint.empty
    | Some e ->
        let _0_696 = str "when"  in
        let _0_695 =
          let _0_694 = p_tmFormula e  in
          FStar_Pprint.op_Hat_Hat _0_694 FStar_Pprint.space  in
        op_Hat_Slash_Plus_Hat _0_696 _0_695

and p_tmIff : FStar_Parser_AST.term -> FStar_Pprint.document =
  fun e  ->
    let uu____2481 = (unparen e).FStar_Parser_AST.tm  in
    match uu____2481 with
    | FStar_Parser_AST.Op ("<==>",e1::e2::[]) ->
        let _0_699 = str "<==>"  in
        let _0_698 = p_tmImplies e1  in
        let _0_697 = p_tmIff e2  in infix0 _0_699 _0_698 _0_697
    | uu____2485 -> p_tmImplies e

and p_tmImplies : FStar_Parser_AST.term -> FStar_Pprint.document =
  fun e  ->
    let uu____2487 = (unparen e).FStar_Parser_AST.tm  in
    match uu____2487 with
    | FStar_Parser_AST.Op ("==>",e1::e2::[]) ->
        let _0_702 = str "==>"  in
        let _0_701 = p_tmArrow p_tmFormula e1  in
        let _0_700 = p_tmImplies e2  in infix0 _0_702 _0_701 _0_700
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
            (let _0_707 =
               FStar_Pprint.concat_map
                 (fun b  ->
                    let _0_705 = p_binder false b  in
                    let _0_704 =
                      let _0_703 =
                        FStar_Pprint.op_Hat_Hat FStar_Pprint.rarrow break1
                         in
                      FStar_Pprint.op_Hat_Hat FStar_Pprint.space _0_703  in
                    FStar_Pprint.op_Hat_Hat _0_705 _0_704) bs
                in
             let _0_706 = p_tmArrow p_Tm tgt  in
             FStar_Pprint.op_Hat_Hat _0_707 _0_706)
      | uu____2502 -> p_Tm e

and p_tmFormula : FStar_Parser_AST.term -> FStar_Pprint.document =
  fun e  ->
    let uu____2504 = (unparen e).FStar_Parser_AST.tm  in
    match uu____2504 with
    | FStar_Parser_AST.Op ("\\/",e1::e2::[]) ->
        let _0_710 = str "\\/"  in
        let _0_709 = p_tmFormula e1  in
        let _0_708 = p_tmConjunction e2  in infix0 _0_710 _0_709 _0_708
    | uu____2508 -> p_tmConjunction e

and p_tmConjunction : FStar_Parser_AST.term -> FStar_Pprint.document =
  fun e  ->
    let uu____2510 = (unparen e).FStar_Parser_AST.tm  in
    match uu____2510 with
    | FStar_Parser_AST.Op ("/\\",e1::e2::[]) ->
        let _0_713 = str "/\\"  in
        let _0_712 = p_tmConjunction e1  in
        let _0_711 = p_tmTuple e2  in infix0 _0_713 _0_712 _0_711
    | uu____2514 -> p_tmTuple e

and p_tmTuple : FStar_Parser_AST.term -> FStar_Pprint.document =
  fun e  -> with_comment p_tmTuple' e e.FStar_Parser_AST.range

and p_tmTuple' : FStar_Parser_AST.term -> FStar_Pprint.document =
  fun e  ->
    let uu____2517 = (unparen e).FStar_Parser_AST.tm  in
    match uu____2517 with
    | FStar_Parser_AST.Construct (lid,args) when is_tuple_constructor lid ->
        let _0_714 = FStar_Pprint.op_Hat_Hat FStar_Pprint.comma break1  in
        FStar_Pprint.separate_map _0_714
          (fun uu____2528  ->
             match uu____2528 with | (e,uu____2532) -> p_tmEq e) args
    | uu____2533 -> p_tmEq e

and paren_if :
  Prims.int -> Prims.int -> FStar_Pprint.document -> FStar_Pprint.document =
  fun curr  ->
    fun mine  ->
      fun doc  ->
        match mine <= curr with
        | true  -> doc
        | uu____2537 ->
            FStar_Pprint.group
              (let _0_715 = FStar_Pprint.op_Hat_Hat doc FStar_Pprint.rparen
                  in
               FStar_Pprint.op_Hat_Hat FStar_Pprint.lparen _0_715)

and p_tmEq : FStar_Parser_AST.term -> FStar_Pprint.document =
  fun e  ->
    let n1 =
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
               let _0_719 =
                 let _0_718 = str op  in
                 let _0_717 = p_tmEq' left e1  in
                 let _0_716 = p_tmEq' right e2  in
                 infix0 _0_718 _0_717 _0_716  in
               paren_if curr mine _0_719)
      | FStar_Parser_AST.Op (":=",e1::e2::[]) ->
          FStar_Pprint.group
            (let _0_724 = p_tmEq e1  in
             let _0_723 =
               let _0_722 =
                 let _0_721 =
                   let _0_720 = p_tmEq e2  in
                   op_Hat_Slash_Plus_Hat FStar_Pprint.equals _0_720  in
                 FStar_Pprint.op_Hat_Hat FStar_Pprint.colon _0_721  in
               FStar_Pprint.op_Hat_Hat FStar_Pprint.space _0_722  in
             FStar_Pprint.op_Hat_Hat _0_724 _0_723)
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
            (let uu____3167 = is_list e in Prims.op_Negation uu____3167)
          ->
          let op = "::"  in
          let uu____2623 = levels op  in
          (match uu____2623 with
           | (left,mine,right) ->
               let _0_728 =
                 let _0_727 = str op  in
                 let _0_726 = p_tmNoEq' left e1  in
                 let _0_725 = p_tmNoEq' right e2  in
                 infix0 _0_727 _0_726 _0_725  in
               paren_if curr mine _0_728)
      | FStar_Parser_AST.Sum (binders,res) ->
          let op = "&"  in
          let uu____2635 = levels op  in
          (match uu____2635 with
           | (left,mine,right) ->
               let p_dsumfst b =
                 let _0_732 = p_binder false b  in
                 let _0_731 =
                   let _0_730 =
                     let _0_729 = str "&"  in
                     FStar_Pprint.op_Hat_Hat _0_729 break1  in
                   FStar_Pprint.op_Hat_Hat FStar_Pprint.space _0_730  in
                 FStar_Pprint.op_Hat_Hat _0_732 _0_731  in
               let _0_735 =
                 let _0_734 = FStar_Pprint.concat_map p_dsumfst binders  in
                 let _0_733 = p_tmNoEq' right res  in
                 FStar_Pprint.op_Hat_Hat _0_734 _0_733  in
               paren_if curr mine _0_735)
      | FStar_Parser_AST.Op (op,e1::e2::[]) when is_operatorInfix34 op ->
          let uu____2650 = levels op  in
          (match uu____2650 with
           | (left,mine,right) ->
               let _0_739 =
                 let _0_738 = str op  in
                 let _0_737 = p_tmNoEq' left e1  in
                 let _0_736 = p_tmNoEq' right e2  in
                 infix0 _0_738 _0_737 _0_736  in
               paren_if curr mine _0_739)
      | FStar_Parser_AST.Op ("-",e::[]) ->
          let uu____2659 = levels "-"  in
          (match uu____2659 with
           | (left,mine,right) ->
               let _0_740 = p_tmNoEq' mine e  in
               FStar_Pprint.op_Hat_Slash_Hat FStar_Pprint.minus _0_740)
      | FStar_Parser_AST.NamedTyp (lid,e) ->
          FStar_Pprint.group
            (let _0_743 = p_lidentOrUnderscore lid  in
             let _0_742 =
               let _0_741 = p_appTerm e  in
               FStar_Pprint.op_Hat_Slash_Hat FStar_Pprint.colon _0_741  in
             FStar_Pprint.op_Hat_Slash_Hat _0_743 _0_742)
      | FStar_Parser_AST.Refine (b,phi) -> p_refinedBinder b phi
      | FStar_Parser_AST.Record (with_opt,record_fields) ->
          braces_with_nesting
            (let _0_746 =
               default_or_map FStar_Pprint.empty p_with_clause with_opt  in
             let _0_745 =
               let _0_744 = FStar_Pprint.op_Hat_Hat FStar_Pprint.semi break1
                  in
               FStar_Pprint.separate_map _0_744 p_simpleDef record_fields  in
             FStar_Pprint.op_Hat_Hat _0_746 _0_745)
      | FStar_Parser_AST.Op ("~",e::[]) ->
          FStar_Pprint.group
            (let _0_748 = str "~"  in
             let _0_747 = p_atomicTerm e  in
             FStar_Pprint.op_Hat_Hat _0_748 _0_747)
      | uu____2684 -> p_appTerm e

and p_with_clause : FStar_Parser_AST.term -> FStar_Pprint.document =
  fun e  ->
    let _0_752 = p_appTerm e  in
    let _0_751 =
      let _0_750 =
        let _0_749 = str "with"  in FStar_Pprint.op_Hat_Hat _0_749 break1  in
      FStar_Pprint.op_Hat_Hat FStar_Pprint.space _0_750  in
    FStar_Pprint.op_Hat_Hat _0_752 _0_751

and p_refinedBinder :
  FStar_Parser_AST.binder -> FStar_Parser_AST.term -> FStar_Pprint.document =
  fun b  ->
    fun phi  ->
      match b.FStar_Parser_AST.b with
      | FStar_Parser_AST.Annotated (lid,t) ->
          soft_parens_with_nesting
            (let _0_753 = p_lident lid  in
             p_refinement b.FStar_Parser_AST.aqual _0_753 t phi)
      | FStar_Parser_AST.TAnnotated uu____2690 ->
          failwith "Is this still used ?"
      | FStar_Parser_AST.Variable _
        |FStar_Parser_AST.TVariable _|FStar_Parser_AST.NoName _ ->
          failwith
            (let _0_754 = FStar_Parser_AST.binder_to_string b  in
             FStar_Util.format1
               "Imposible : a refined binder ought to be annotated %s" _0_754)

and p_simpleDef :
  (FStar_Ident.lid * FStar_Parser_AST.term) -> FStar_Pprint.document =
  fun uu____2696  ->
    match uu____2696 with
    | (lid,e) ->
        FStar_Pprint.group
          (let _0_757 = p_qlident lid  in
           let _0_756 =
             let _0_755 = p_tmIff e  in
             FStar_Pprint.op_Hat_Slash_Hat FStar_Pprint.equals _0_755  in
           FStar_Pprint.op_Hat_Slash_Hat _0_757 _0_756)

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
               match uu____2727 with
               | true  ->
                   let uu____2735 =
                     FStar_Util.take
                       (fun uu____2746  ->
                          match uu____2746 with
                          | (uu____2749,aq) -> aq = FStar_Parser_AST.FsTypApp)
                       args
                      in
                   (match uu____2735 with
                    | (fs_typ_args,args) ->
                        let _0_761 =
                          let _0_760 = p_indexingTerm head  in
                          let _0_759 =
                            let _0_758 =
                              FStar_Pprint.op_Hat_Hat FStar_Pprint.comma
                                break1
                               in
                            soft_surround_separate_map (Prims.parse_int "2")
                              (Prims.parse_int "0") FStar_Pprint.empty
                              FStar_Pprint.langle _0_758 FStar_Pprint.rangle
                              p_fsTypArg fs_typ_args
                             in
                          FStar_Pprint.op_Hat_Hat _0_760 _0_759  in
                        (_0_761, args))
               | uu____2775 ->
                   let _0_762 = p_indexingTerm head  in (_0_762, args)
                in
             (match uu____2721 with
              | (head_doc,args) ->
                  FStar_Pprint.group
                    (let _0_763 =
                       FStar_Pprint.op_Hat_Hat head_doc FStar_Pprint.space
                        in
                     soft_surround_separate_map (Prims.parse_int "2")
                       (Prims.parse_int "0") head_doc _0_763 break1
                       FStar_Pprint.empty p_argTerm args)))
    | FStar_Parser_AST.Construct (lid,args) when
        (is_general_construction e) &&
          (Prims.op_Negation (is_dtuple_constructor lid))
        ->
        (match args with
         | [] -> p_quident lid
         | arg::[] ->
             FStar_Pprint.group
               (let _0_765 = p_quident lid  in
                let _0_764 = p_argTerm arg  in
                FStar_Pprint.op_Hat_Slash_Hat _0_765 _0_764)
         | hd::tl ->
             FStar_Pprint.group
               (let _0_769 =
                  FStar_Pprint.group
                    (let _0_767 = p_quident lid  in
                     let _0_766 = p_argTerm hd  in prefix2 _0_767 _0_766)
                   in
                let _0_768 =
                  jump2 (FStar_Pprint.separate_map break1 p_argTerm tl)  in
                FStar_Pprint.op_Hat_Hat _0_769 _0_768))
    | uu____2817 -> p_indexingTerm e

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
         (let _0_770 = p_indexingTerm e  in
          FStar_Pprint.surround (Prims.parse_int "2") (Prims.parse_int "1")
            FStar_Pprint.langle uu____3430 FStar_Pprint.rangle))
    | (e,FStar_Parser_AST.Hash ) ->
        let _0_772 = str "#"  in
        let _0_771 = p_indexingTerm e  in
        FStar_Pprint.op_Hat_Hat _0_772 _0_771
    | (e,FStar_Parser_AST.Nothing ) -> p_indexingTerm e

and p_fsTypArg :
  (FStar_Parser_AST.term * FStar_Parser_AST.imp) -> FStar_Pprint.document =
  fun uu____2829  ->
    match uu____2829 with | (e,uu____2833) -> p_indexingTerm e

and p_indexingTerm_aux :
  (FStar_Parser_AST.term -> FStar_Pprint.document) ->
    FStar_Parser_AST.term -> FStar_Pprint.document
  =
  fun exit1  ->
    fun e  ->
      let uu____2838 = (unparen e).FStar_Parser_AST.tm  in
      match uu____2838 with
      | FStar_Parser_AST.Op (".()",e1::e2::[]) ->
          FStar_Pprint.group
            (let _0_775 = p_indexingTerm_aux p_atomicTermNotQUident e1  in
             let _0_774 =
               let _0_773 = soft_parens_with_nesting (p_term e2)  in
               FStar_Pprint.op_Hat_Hat FStar_Pprint.dot _0_773  in
             FStar_Pprint.op_Hat_Hat _0_775 _0_774)
      | FStar_Parser_AST.Op (".[]",e1::e2::[]) ->
          FStar_Pprint.group
            (let _0_778 = p_indexingTerm_aux p_atomicTermNotQUident e1  in
             let _0_777 =
               let _0_776 = soft_brackets_with_nesting (p_term e2)  in
               FStar_Pprint.op_Hat_Hat FStar_Pprint.dot _0_776  in
             FStar_Pprint.op_Hat_Hat _0_778 _0_777)
      | uu____2845 -> exit e

and p_indexingTerm : FStar_Parser_AST.term -> FStar_Pprint.document =
  fun e  -> p_indexingTerm_aux p_atomicTerm e

and p_atomicTerm : FStar_Parser_AST.term -> FStar_Pprint.document =
  fun e  ->
    let uu____2848 = (unparen e).FStar_Parser_AST.tm  in
    match uu____2848 with
    | FStar_Parser_AST.LetOpen (lid,e) ->
        let _0_781 = p_quident lid  in
        let _0_780 =
          let _0_779 = soft_parens_with_nesting (p_term e)  in
          FStar_Pprint.op_Hat_Hat FStar_Pprint.dot _0_779  in
        FStar_Pprint.op_Hat_Hat _0_781 _0_780
    | FStar_Parser_AST.Name lid -> p_quident lid
    | FStar_Parser_AST.Op (op,e::[]) when is_general_prefix_op op ->
        let _0_783 = str op  in
        let _0_782 = p_atomicTerm e  in FStar_Pprint.op_Hat_Hat _0_783 _0_782
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
        let _0_785 = str op  in
        let _0_784 = p_atomicTermNotQUident e  in
        FStar_Pprint.op_Hat_Hat _0_785 _0_784
    | FStar_Parser_AST.Op (op,[]) ->
        let _0_789 =
          let _0_788 =
            let _0_787 = str op  in
            let _0_786 =
              FStar_Pprint.op_Hat_Hat FStar_Pprint.space FStar_Pprint.rparen
               in
            FStar_Pprint.op_Hat_Hat _0_787 _0_786  in
          FStar_Pprint.op_Hat_Hat FStar_Pprint.space _0_788  in
        FStar_Pprint.op_Hat_Hat FStar_Pprint.lparen _0_789
    | FStar_Parser_AST.Construct (lid,args) when is_dtuple_constructor lid ->
        let _0_794 =
          FStar_Pprint.op_Hat_Hat FStar_Pprint.lparen FStar_Pprint.bar  in
        let _0_793 =
          let _0_791 = FStar_Pprint.op_Hat_Hat FStar_Pprint.comma break1  in
          let _0_790 = FStar_List.map Prims.fst args  in
          FStar_Pprint.separate_map _0_791 p_tmEq _0_790  in
        let _0_792 =
          FStar_Pprint.op_Hat_Hat FStar_Pprint.bar FStar_Pprint.rparen  in
        FStar_Pprint.surround (Prims.parse_int "2") (Prims.parse_int "1")
          _0_794 _0_793 _0_792
    | FStar_Parser_AST.Project (e,lid) ->
        FStar_Pprint.group
          (let _0_797 = p_atomicTermNotQUident e  in
           let _0_796 =
             let _0_795 = p_qlident lid  in
             FStar_Pprint.op_Hat_Hat FStar_Pprint.dot _0_795  in
           FStar_Pprint.prefix (Prims.parse_int "2") (Prims.parse_int "0")
             _0_797 _0_796)
    | uu____2880 -> p_projectionLHS e

and p_projectionLHS : FStar_Parser_AST.term -> FStar_Pprint.document =
  fun e  ->
    let uu____2882 = (unparen e).FStar_Parser_AST.tm  in
    match uu____2882 with
    | FStar_Parser_AST.Var lid -> p_qlident lid
    | FStar_Parser_AST.Projector (constr_lid,field_lid) ->
        let _0_801 = p_quident constr_lid  in
        let _0_800 =
          let _0_799 =
            let _0_798 = p_lident field_lid  in
            FStar_Pprint.op_Hat_Hat FStar_Pprint.dot _0_798  in
          FStar_Pprint.op_Hat_Hat FStar_Pprint.qmark _0_799  in
        FStar_Pprint.op_Hat_Hat _0_801 _0_800
    | FStar_Parser_AST.Discrim constr_lid ->
        let _0_802 = p_quident constr_lid  in
        FStar_Pprint.op_Hat_Hat _0_802 FStar_Pprint.qmark
    | FStar_Parser_AST.Paren e -> soft_parens_with_nesting (p_term e)
    | uu____2888 when is_array e ->
        let es = extract_from_list e  in
        let _0_806 =
          FStar_Pprint.op_Hat_Hat FStar_Pprint.lbracket FStar_Pprint.bar  in
        let _0_805 =
          let _0_803 = FStar_Pprint.op_Hat_Hat FStar_Pprint.semi break1  in
          separate_map_or_flow _0_803 p_noSeqTerm es  in
        let _0_804 =
          FStar_Pprint.op_Hat_Hat FStar_Pprint.bar FStar_Pprint.rbracket  in
        FStar_Pprint.surround (Prims.parse_int "2") (Prims.parse_int "0")
          _0_806 _0_805 _0_804
    | uu____2891 when is_list e ->
        let _0_809 =
          let _0_808 = FStar_Pprint.op_Hat_Hat FStar_Pprint.semi break1  in
          let _0_807 = extract_from_list e  in
          separate_map_or_flow _0_808 p_noSeqTerm _0_807  in
        FStar_Pprint.surround (Prims.parse_int "2") (Prims.parse_int "0")
          FStar_Pprint.lbracket _0_809 FStar_Pprint.rbracket
    | uu____2892 when is_lex_list e ->
        let _0_813 =
          FStar_Pprint.op_Hat_Hat FStar_Pprint.percent FStar_Pprint.lbracket
           in
        let _0_812 =
          let _0_811 = FStar_Pprint.op_Hat_Hat FStar_Pprint.semi break1  in
          let _0_810 = extract_from_list e  in
          separate_map_or_flow _0_811 p_noSeqTerm _0_810  in
        FStar_Pprint.surround (Prims.parse_int "2") (Prims.parse_int "1")
          _0_813 _0_812 FStar_Pprint.rbracket
    | uu____2893 when is_ref_set e ->
        let es = extract_from_ref_set e  in
        let _0_816 =
          FStar_Pprint.op_Hat_Hat FStar_Pprint.bang FStar_Pprint.lbrace  in
        let _0_815 =
          let _0_814 = FStar_Pprint.op_Hat_Hat FStar_Pprint.comma break1  in
          separate_map_or_flow _0_814 p_appTerm es  in
        FStar_Pprint.surround (Prims.parse_int "2") (Prims.parse_int "0")
          uu____3557 uu____3558 FStar_Pprint.rbrace
    | FStar_Parser_AST.Op (op,args) when
        let uu____3564 = handleable_op op args in
        Prims.op_Negation uu____3564 ->
        let uu____3565 =
          let uu____3566 =
            let uu____3567 =
              let uu____3568 =
                let uu____3569 =
                  FStar_Util.string_of_int (FStar_List.length args) in
                Prims.strcat uu____3569
                  " arguments couldn't be handled by the pretty printer" in
              Prims.strcat " with " uu____3568 in
            Prims.strcat op uu____3567 in
          Prims.strcat "Operation " uu____3566 in
        failwith uu____3565
    | FStar_Parser_AST.Uvar uu____3573 ->
        failwith "Unexpected universe variable out of universe context"
    | FStar_Parser_AST.Labeled uu____3574 -> failwith "Not valid in universe"
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
  fun uu___128_2928  ->
    match uu___128_2928 with
    | FStar_Const.Const_effect  -> str "Effect"
    | FStar_Const.Const_unit  -> str "()"
    | FStar_Const.Const_bool b -> FStar_Pprint.doc_of_bool b
    | FStar_Const.Const_float x -> str (FStar_Util.string_of_float x)
    | FStar_Const.Const_char x ->
        FStar_Pprint.squotes (FStar_Pprint.doc_of_char x)
    | FStar_Const.Const_string (bytes,uu____2933) ->
        FStar_Pprint.dquotes (str (FStar_Util.string_of_bytes bytes))
    | FStar_Const.Const_bytearray (bytes,uu____2937) ->
        let _0_818 =
          FStar_Pprint.dquotes (str (FStar_Util.string_of_bytes bytes))  in
        let _0_817 = str "B"  in FStar_Pprint.op_Hat_Hat _0_818 _0_817
    | FStar_Const.Const_int (repr,sign_width_opt) ->
        let signedness uu___137_3634 =
          match uu___137_3634 with
          | FStar_Const.Unsigned  -> str "u"
          | FStar_Const.Signed  -> FStar_Pprint.empty  in
        let width uu___127_2955 =
          match uu___127_2955 with
          | FStar_Const.Int8  -> str "y"
          | FStar_Const.Int16  -> str "s"
          | FStar_Const.Int32  -> str "l"
          | FStar_Const.Int64  -> str "L"  in
        let ending =
          default_or_map FStar_Pprint.empty
            (fun uu____3642  ->
               match uu____3642 with
               | (s,w) ->
                   let _0_820 = signedness s  in
                   let _0_819 = width w  in
                   FStar_Pprint.op_Hat_Hat _0_820 _0_819) sign_width_opt
           in
        let _0_821 = str repr  in FStar_Pprint.op_Hat_Hat _0_821 ending
    | FStar_Const.Const_range r -> str (FStar_Range.string_of_range r)
    | FStar_Const.Const_reify  -> str "reify"
    | FStar_Const.Const_reflect lid ->
        let _0_825 = p_quident lid  in
        let _0_824 =
          let _0_823 =
            let _0_822 = str "reflect"  in
            FStar_Pprint.op_Hat_Hat FStar_Pprint.dot _0_822  in
          FStar_Pprint.op_Hat_Hat FStar_Pprint.qmark _0_823  in
        FStar_Pprint.op_Hat_Hat _0_825 _0_824

and p_universe : FStar_Parser_AST.term -> FStar_Pprint.document =
  fun u  ->
    let _0_827 = str "u#"  in
    let _0_826 = p_atomicUniverse u  in FStar_Pprint.op_Hat_Hat _0_827 _0_826

and p_universeFrom : FStar_Parser_AST.term -> FStar_Pprint.document =
  fun u  ->
    let uu____2968 = (unparen u).FStar_Parser_AST.tm  in
    match uu____2968 with
    | FStar_Parser_AST.Op ("+",u1::u2::[]) ->
        FStar_Pprint.group
          (let _0_830 = p_universeFrom u1  in
           let _0_829 =
             let _0_828 = p_universeFrom u2  in
             FStar_Pprint.op_Hat_Slash_Hat FStar_Pprint.plus _0_828  in
           FStar_Pprint.op_Hat_Slash_Hat _0_830 _0_829)
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
                    (let _0_832 = p_qlident FStar_Syntax_Const.max_lid  in
                     let _0_831 =
                       FStar_Pprint.separate_map FStar_Pprint.space
                         (fun uu____2994  ->
                            match uu____2994 with
                            | (u,uu____2998) -> p_atomicUniverse u) args
                        in
                     op_Hat_Slash_Plus_Hat _0_832 _0_831)
              | uu____2999 ->
                  failwith
                    (let _0_833 = FStar_Parser_AST.term_to_string u  in
                     FStar_Util.format1 "Invalid term in universe context %s"
                       _0_833)))
    | uu____3000 -> p_atomicUniverse u

and p_atomicUniverse : FStar_Parser_AST.term -> FStar_Pprint.document =
  fun u  ->
    let uu____3002 = (unparen u).FStar_Parser_AST.tm  in
    match uu____3002 with
    | FStar_Parser_AST.Wild  -> FStar_Pprint.underscore
    | FStar_Parser_AST.Const (FStar_Const.Const_int (r,sw)) ->
        p_constant (FStar_Const.Const_int (r, sw))
    | FStar_Parser_AST.Uvar uu____3719 -> p_univar u
    | FStar_Parser_AST.Paren u1 ->
        let uu____3721 = p_universeFrom u1 in
        soft_parens_with_nesting uu____3721
    | FStar_Parser_AST.Op ("+",_::_::[])|FStar_Parser_AST.App _ ->
        soft_parens_with_nesting (p_universeFrom u)
    | uu____3020 ->
        failwith
          (let _0_834 = FStar_Parser_AST.term_to_string u  in
           FStar_Util.format1 "Invalid term in universe context %s" _0_834)

and p_univar : FStar_Parser_AST.term -> FStar_Pprint.document =
  fun u  ->
    let uu____3022 = (unparen u).FStar_Parser_AST.tm  in
    match uu____3022 with
    | FStar_Parser_AST.Uvar id -> str (FStar_Ident.text_of_id id)
    | uu____3024 ->
        failwith
          (let _0_835 = FStar_Parser_AST.term_to_string u  in
           FStar_Util.format1 "Not a universe variable %s" _0_835)

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
           let _0_836 =
             FStar_All.pipe_right decls (FStar_List.map decl_to_document)  in
           FStar_All.pipe_right _0_836
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
           let uu____3824 =
             match ds with
             | {
                 FStar_Parser_AST.d = FStar_Parser_AST.Pragma
                   (FStar_Parser_AST.LightOff );
                 FStar_Parser_AST.drange = uu____3117;
                 FStar_Parser_AST.doc = uu____3118;
                 FStar_Parser_AST.quals = uu____3119;
                 FStar_Parser_AST.attrs = uu____3120;_}::uu____3121 ->
                 let d0 = FStar_List.hd ds  in
                 let _0_839 =
                   let _0_838 = let _0_837 = FStar_List.tl ds  in d :: _0_837
                      in
                   d0 :: _0_838  in
                 (_0_839, (d0.FStar_Parser_AST.drange))
             | uu____3126 -> ((d :: ds), (d.FStar_Parser_AST.drange))  in
           (match uu____3110 with
            | (decls,first_range) ->
                let extract_decl_range d = d.FStar_Parser_AST.drange  in
                (FStar_ST.write comment_stack comments;
                 (let initial_comment =
                    let _0_840 = FStar_Range.start_of_range first_range  in
                    place_comments_until_pos (Prims.parse_int "0")
                      (Prims.parse_int "1") _0_840 FStar_Pprint.empty
                     in
                  let doc =
                    separate_map_with_comments FStar_Pprint.empty
                      FStar_Pprint.empty decl_to_document decls
                      extract_decl_range
                     in
                  let comments = FStar_ST.read comment_stack  in
                  FStar_ST.write comment_stack [];
                  FStar_ST.write should_print_fs_typ_app false;
                  (let _0_841 = FStar_Pprint.op_Hat_Hat initial_comment doc
                      in
                   (_0_841, comments))))))
  