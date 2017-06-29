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
let default_or_map n1 f x =
  match x with
  | FStar_Pervasives_Native.None  -> n1
  | FStar_Pervasives_Native.Some x' -> f x' 
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
  (Prims.string,(Prims.string,Prims.string) FStar_Pervasives_Native.tuple2
                  Prims.list)
    FStar_Pervasives_Native.tuple2 -> FStar_Pprint.document
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
  FStar_Parser_Const.is_tuple_data_lid' 
let is_dtuple_constructor : FStar_Ident.lident -> Prims.bool =
  FStar_Parser_Const.is_dtuple_data_lid' 
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
  is_list_structure FStar_Parser_Const.cons_lid FStar_Parser_Const.nil_lid 
let is_lex_list : FStar_Parser_AST.term -> Prims.bool =
  is_list_structure FStar_Parser_Const.lexcons_lid
    FStar_Parser_Const.lextop_lid
  
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
        (FStar_Ident.lid_equals lid FStar_Parser_Const.array_mk_array_lid) &&
          (is_list l)
    | uu____445 -> false
  
let rec is_ref_set : FStar_Parser_AST.term -> Prims.bool =
  fun e  ->
    let uu____449 =
      let uu____450 = unparen e  in uu____450.FStar_Parser_AST.tm  in
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
  
let is_general_prefix_op : FStar_Ident.ident -> Prims.bool =
  fun op  ->
    let op_starting_char =
      FStar_Util.char_at (FStar_Ident.text_of_id op) (Prims.parse_int "0")
       in
    ((op_starting_char = '!') || (op_starting_char = '?')) ||
      ((op_starting_char = '~') && ((FStar_Ident.text_of_id op) <> "~"))
  
let head_and_args :
  FStar_Parser_AST.term ->
    (FStar_Parser_AST.term,(FStar_Parser_AST.term,FStar_Parser_AST.imp)
                             FStar_Pervasives_Native.tuple2 Prims.list)
      FStar_Pervasives_Native.tuple2
  =
  fun e  ->
    let rec aux e1 acc =
      let uu____539 =
        let uu____540 = unparen e1  in uu____540.FStar_Parser_AST.tm  in
      match uu____539 with
      | FStar_Parser_AST.App (head1,arg,imp) -> aux head1 ((arg, imp) :: acc)
      | uu____551 -> (e1, acc)  in
    aux e []
  
type associativity =
  | Left 
  | Right 
  | NonAssoc 
let uu___is_Left : associativity -> Prims.bool =
  fun projectee  -> match projectee with | Left  -> true | uu____560 -> false 
let uu___is_Right : associativity -> Prims.bool =
  fun projectee  ->
    match projectee with | Right  -> true | uu____564 -> false
  
let uu___is_NonAssoc : associativity -> Prims.bool =
  fun projectee  ->
    match projectee with | NonAssoc  -> true | uu____568 -> false
  
type token = (FStar_Char.char,Prims.string) FStar_Util.either
type associativity_level =
  (associativity,token Prims.list) FStar_Pervasives_Native.tuple2
let token_to_string :
  (FStar_BaseTypes.char,Prims.string) FStar_Util.either -> Prims.string =
  fun uu___95_578  ->
    match uu___95_578 with
    | FStar_Util.Inl c -> Prims.strcat (FStar_Util.string_of_char c) ".*"
    | FStar_Util.Inr s -> s
  
let matches_token :
  Prims.string ->
    (FStar_Char.char,Prims.string) FStar_Util.either -> Prims.bool
  =
  fun s  ->
    fun uu___96_590  ->
      match uu___96_590 with
      | FStar_Util.Inl c ->
          let uu____594 = FStar_String.get s (Prims.parse_int "0")  in
          uu____594 = c
      | FStar_Util.Inr s' -> s = s'
  
let matches_level s uu____612 =
  match uu____612 with
  | (assoc_levels,tokens) ->
      let uu____626 = FStar_List.tryFind (matches_token s) tokens  in
      uu____626 <> FStar_Pervasives_Native.None
  
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
let level_associativity_spec :
  (associativity,(FStar_Char.char,Prims.string) FStar_Util.either Prims.list)
    FStar_Pervasives_Native.tuple2 Prims.list
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
  ((Prims.int,Prims.int,Prims.int) FStar_Pervasives_Native.tuple3,(FStar_Char.char,
                                                                    Prims.string)
                                                                    FStar_Util.either
                                                                    Prims.list)
    FStar_Pervasives_Native.tuple2 Prims.list
  =
  let levels_from_associativity l uu___97_948 =
    match uu___97_948 with
    | Left  -> (l, l, (l - (Prims.parse_int "1")))
    | Right  -> ((l - (Prims.parse_int "1")), l, l)
    | NonAssoc  -> (l, l, l)  in
  FStar_List.mapi
    (fun i  ->
       fun uu____966  ->
         match uu____966 with
         | (assoc1,tokens) -> ((levels_from_associativity i assoc1), tokens))
    level_associativity_spec
  
let assign_levels :
  associativity_level Prims.list ->
    Prims.string ->
      (Prims.int,Prims.int,Prims.int) FStar_Pervasives_Native.tuple3
  =
  fun token_associativity_spec  ->
    fun s  ->
      let uu____1008 = FStar_List.tryFind (matches_level s) level_table  in
      match uu____1008 with
      | FStar_Pervasives_Native.Some (assoc_levels,uu____1033) ->
          assoc_levels
      | uu____1054 -> failwith (Prims.strcat "Unrecognized operator " s)
  
let max : Prims.int -> Prims.int -> Prims.int =
  fun k1  -> fun k2  -> if k1 > k2 then k1 else k2 
let max_level l =
  let find_level_and_max n1 level =
    let uu____1110 =
      FStar_List.tryFind
        (fun uu____1128  ->
           match uu____1128 with
           | (uu____1137,tokens) ->
               tokens = (FStar_Pervasives_Native.snd level)) level_table
       in
    match uu____1110 with
    | FStar_Pervasives_Native.Some ((uu____1157,l1,uu____1159),uu____1160) ->
        max n1 l1
    | FStar_Pervasives_Native.None  ->
        let uu____1186 =
          let uu____1187 =
            let uu____1188 =
              FStar_List.map token_to_string
                (FStar_Pervasives_Native.snd level)
               in
            FStar_String.concat "," uu____1188  in
          FStar_Util.format1 "Undefined associativity level %s" uu____1187
           in
        failwith uu____1186
     in
  FStar_List.fold_left find_level_and_max (Prims.parse_int "0") l 
let levels :
  Prims.string ->
    (Prims.int,Prims.int,Prims.int) FStar_Pervasives_Native.tuple3
  = assign_levels level_associativity_spec 
let operatorInfix0ad12 uu____1213 =
  [opinfix0a ();
  opinfix0b ();
  opinfix0c ();
  opinfix0d ();
  opinfix1 ();
  opinfix2 ()] 
let is_operatorInfix0ad12 : FStar_Ident.ident -> Prims.bool =
  fun op  ->
    let uu____1252 =
      let uu____1259 =
        FStar_All.pipe_left matches_level (FStar_Ident.text_of_id op)  in
      FStar_List.tryFind uu____1259 (operatorInfix0ad12 ())  in
    uu____1252 <> FStar_Pervasives_Native.None
  
let is_operatorInfix34 : FStar_Ident.ident -> Prims.bool =
  let opinfix34 = [opinfix3 (); opinfix4 ()]  in
  fun op  ->
    let uu____1315 =
      let uu____1322 =
        FStar_All.pipe_left matches_level (FStar_Ident.text_of_id op)  in
      FStar_List.tryFind uu____1322 opinfix34  in
    uu____1315 <> FStar_Pervasives_Native.None
  
let handleable_args_length : FStar_Ident.ident -> Prims.int =
  fun op  ->
    let op_s = FStar_Ident.text_of_id op  in
    let uu____1357 =
      (is_general_prefix_op op) || (FStar_List.mem op_s ["-"; "~"])  in
    if uu____1357
    then (Prims.parse_int "1")
    else
      (let uu____1359 =
         ((is_operatorInfix0ad12 op) || (is_operatorInfix34 op)) ||
           (FStar_List.mem op_s
              ["<==>"; "==>"; "\\/"; "/\\"; "="; "|>"; ":="; ".()"; ".[]"])
          in
       if uu____1359
       then (Prims.parse_int "2")
       else
         if FStar_List.mem op_s [".()<-"; ".[]<-"]
         then (Prims.parse_int "3")
         else (Prims.parse_int "0"))
  
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
let comment_stack :
  (Prims.string,FStar_Range.range) FStar_Pervasives_Native.tuple2 Prims.list
    FStar_ST.ref
  = FStar_Util.mk_ref [] 
let with_comment printer tm tmrange =
  let rec comments_before_pos acc print_pos lookahead_pos =
    let uu____1423 = FStar_ST.read comment_stack  in
    match uu____1423 with
    | [] -> (acc, false)
    | (comment,crange)::cs ->
        let uu____1444 = FStar_Range.range_before_pos crange print_pos  in
        if uu____1444
        then
          (FStar_ST.write comment_stack cs;
           (let uu____1453 =
              let uu____1454 =
                let uu____1455 = str comment  in
                FStar_Pprint.op_Hat_Hat uu____1455 FStar_Pprint.hardline  in
              FStar_Pprint.op_Hat_Hat acc uu____1454  in
            comments_before_pos uu____1453 print_pos lookahead_pos))
        else
          (let uu____1457 = FStar_Range.range_before_pos crange lookahead_pos
              in
           (acc, uu____1457))
     in
  let uu____1458 =
    let uu____1461 =
      let uu____1462 = FStar_Range.start_of_range tmrange  in
      FStar_Range.end_of_line uu____1462  in
    let uu____1463 = FStar_Range.end_of_range tmrange  in
    comments_before_pos FStar_Pprint.empty uu____1461 uu____1463  in
  match uu____1458 with
  | (comments,has_lookahead) ->
      let printed_e = printer tm  in
      let comments1 =
        if has_lookahead
        then
          let pos = FStar_Range.end_of_range tmrange  in
          let uu____1469 = comments_before_pos comments pos pos  in
          FStar_Pervasives_Native.fst uu____1469
        else comments  in
      let uu____1473 = FStar_Pprint.op_Hat_Hat comments1 printed_e  in
      FStar_Pprint.group uu____1473
  
let rec place_comments_until_pos :
  Prims.int ->
    Prims.int ->
      FStar_Range.pos -> FStar_Pprint.document -> FStar_Pprint.document
  =
  fun k  ->
    fun lbegin  ->
      fun pos_end  ->
        fun doc1  ->
          let uu____1486 = FStar_ST.read comment_stack  in
          match uu____1486 with
          | (comment,crange)::cs when
              FStar_Range.range_before_pos crange pos_end ->
              (FStar_ST.write comment_stack cs;
               (let lnum =
                  let uu____1510 =
                    let uu____1511 =
                      let uu____1512 = FStar_Range.start_of_range crange  in
                      FStar_Range.line_of_pos uu____1512  in
                    uu____1511 - lbegin  in
                  max k uu____1510  in
                let doc2 =
                  let uu____1514 =
                    let uu____1515 =
                      FStar_Pprint.repeat lnum FStar_Pprint.hardline  in
                    let uu____1516 = str comment  in
                    FStar_Pprint.op_Hat_Hat uu____1515 uu____1516  in
                  FStar_Pprint.op_Hat_Hat doc1 uu____1514  in
                let uu____1517 =
                  let uu____1518 = FStar_Range.end_of_range crange  in
                  FStar_Range.line_of_pos uu____1518  in
                place_comments_until_pos (Prims.parse_int "1") uu____1517
                  pos_end doc2))
          | uu____1519 ->
              let lnum =
                let uu____1524 =
                  let uu____1525 = FStar_Range.line_of_pos pos_end  in
                  uu____1525 - lbegin  in
                max (Prims.parse_int "1") uu____1524  in
              let uu____1526 = FStar_Pprint.repeat lnum FStar_Pprint.hardline
                 in
              FStar_Pprint.op_Hat_Hat doc1 uu____1526
  
let separate_map_with_comments prefix1 sep f xs extract_range =
  let fold_fun uu____1575 x =
    match uu____1575 with
    | (last_line,doc1) ->
        let r = extract_range x  in
        let doc2 =
          let uu____1585 = FStar_Range.start_of_range r  in
          place_comments_until_pos (Prims.parse_int "1") last_line uu____1585
            doc1
           in
        let uu____1586 =
          let uu____1587 = FStar_Range.end_of_range r  in
          FStar_Range.line_of_pos uu____1587  in
        let uu____1588 =
          let uu____1589 =
            let uu____1590 = f x  in FStar_Pprint.op_Hat_Hat sep uu____1590
             in
          FStar_Pprint.op_Hat_Hat doc2 uu____1589  in
        (uu____1586, uu____1588)
     in
  let uu____1591 =
    let uu____1595 = FStar_List.hd xs  in
    let uu____1596 = FStar_List.tl xs  in (uu____1595, uu____1596)  in
  match uu____1591 with
  | (x,xs1) ->
      let init1 =
        let uu____1606 =
          let uu____1607 =
            let uu____1608 = extract_range x  in
            FStar_Range.end_of_range uu____1608  in
          FStar_Range.line_of_pos uu____1607  in
        let uu____1609 =
          let uu____1610 = f x  in FStar_Pprint.op_Hat_Hat prefix1 uu____1610
           in
        (uu____1606, uu____1609)  in
      let uu____1611 = FStar_List.fold_left fold_fun init1 xs1  in
      FStar_Pervasives_Native.snd uu____1611
  
let rec p_decl : FStar_Parser_AST.decl -> FStar_Pprint.document =
  fun d  ->
    let uu____1855 =
      let uu____1856 = FStar_Pprint.optional p_fsdoc d.FStar_Parser_AST.doc
         in
      let uu____1857 =
        let uu____1858 = p_attributes d.FStar_Parser_AST.attrs  in
        let uu____1859 =
          let uu____1860 = p_qualifiers d.FStar_Parser_AST.quals  in
          let uu____1861 =
            let uu____1862 = p_rawDecl d  in
            FStar_Pprint.op_Hat_Hat
              (if d.FStar_Parser_AST.quals = []
               then FStar_Pprint.empty
               else break1) uu____1862
             in
          FStar_Pprint.op_Hat_Hat uu____1860 uu____1861  in
        FStar_Pprint.op_Hat_Hat uu____1858 uu____1859  in
      FStar_Pprint.op_Hat_Hat uu____1856 uu____1857  in
    FStar_Pprint.group uu____1855

and p_attributes : FStar_Parser_AST.attributes_ -> FStar_Pprint.document =
  fun attrs  ->
    let uu____1865 =
      let uu____1866 = str "@"  in
      FStar_Pprint.op_Hat_Hat FStar_Pprint.lbracket uu____1866  in
    let uu____1867 =
      FStar_Pprint.op_Hat_Hat FStar_Pprint.rbracket FStar_Pprint.hardline  in
    soft_surround_separate_map (Prims.parse_int "0") (Prims.parse_int "2")
      FStar_Pprint.empty uu____1865 FStar_Pprint.space uu____1867
      p_atomicTerm attrs

and p_fsdoc : FStar_Parser_AST.fsdoc -> FStar_Pprint.document =
  fun uu____1868  ->
    match uu____1868 with
    | (doc1,kwd_args) ->
        let kwd_args_doc =
          match kwd_args with
          | [] -> FStar_Pprint.empty
          | kwd_args1 ->
              let process_kwd_arg uu____1889 =
                match uu____1889 with
                | (kwd1,arg) ->
                    let uu____1894 = str "@"  in
                    let uu____1895 =
                      let uu____1896 = str kwd1  in
                      let uu____1897 =
                        let uu____1898 = str arg  in
                        FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____1898
                         in
                      FStar_Pprint.op_Hat_Hat uu____1896 uu____1897  in
                    FStar_Pprint.op_Hat_Hat uu____1894 uu____1895
                 in
              let uu____1899 =
                let uu____1900 =
                  FStar_Pprint.separate_map FStar_Pprint.hardline
                    process_kwd_arg kwd_args1
                   in
                FStar_Pprint.op_Hat_Hat uu____1900 FStar_Pprint.hardline  in
              FStar_Pprint.op_Hat_Hat FStar_Pprint.hardline uu____1899
           in
        let uu____1903 =
          let uu____1904 =
            let uu____1905 =
              let uu____1906 =
                let uu____1907 = str doc1  in
                let uu____1908 =
                  let uu____1909 =
                    let uu____1910 =
                      FStar_Pprint.op_Hat_Hat FStar_Pprint.rparen
                        FStar_Pprint.hardline
                       in
                    FStar_Pprint.op_Hat_Hat FStar_Pprint.star uu____1910  in
                  FStar_Pprint.op_Hat_Hat kwd_args_doc uu____1909  in
                FStar_Pprint.op_Hat_Hat uu____1907 uu____1908  in
              FStar_Pprint.op_Hat_Hat FStar_Pprint.star uu____1906  in
            FStar_Pprint.op_Hat_Hat FStar_Pprint.star uu____1905  in
          FStar_Pprint.op_Hat_Hat FStar_Pprint.lparen uu____1904  in
        FStar_Pprint.op_Hat_Hat FStar_Pprint.hardline uu____1903

and p_rawDecl : FStar_Parser_AST.decl -> FStar_Pprint.document =
  fun d  ->
    match d.FStar_Parser_AST.d with
    | FStar_Parser_AST.Open uid ->
        let uu____1913 =
          let uu____1914 = str "open"  in
          let uu____1915 = p_quident uid  in
          FStar_Pprint.op_Hat_Slash_Hat uu____1914 uu____1915  in
        FStar_Pprint.group uu____1913
    | FStar_Parser_AST.Include uid ->
        let uu____1917 =
          let uu____1918 = str "include"  in
          let uu____1919 = p_quident uid  in
          FStar_Pprint.op_Hat_Slash_Hat uu____1918 uu____1919  in
        FStar_Pprint.group uu____1917
    | FStar_Parser_AST.ModuleAbbrev (uid1,uid2) ->
        let uu____1922 =
          let uu____1923 = str "module"  in
          let uu____1924 =
            let uu____1925 =
              let uu____1926 = p_uident uid1  in
              let uu____1927 =
                FStar_Pprint.op_Hat_Hat FStar_Pprint.space
                  FStar_Pprint.equals
                 in
              FStar_Pprint.op_Hat_Hat uu____1926 uu____1927  in
            FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____1925  in
          FStar_Pprint.op_Hat_Hat uu____1923 uu____1924  in
        let uu____1928 = p_quident uid2  in
        op_Hat_Slash_Plus_Hat uu____1922 uu____1928
    | FStar_Parser_AST.TopLevelModule uid ->
        let uu____1930 =
          let uu____1931 = str "module"  in
          let uu____1932 =
            let uu____1933 = p_quident uid  in
            FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____1933  in
          FStar_Pprint.op_Hat_Hat uu____1931 uu____1932  in
        FStar_Pprint.group uu____1930
    | FStar_Parser_AST.Tycon
        (true
         ,(FStar_Parser_AST.TyconAbbrev
           (uid,tpars,FStar_Pervasives_Native.None ,t),FStar_Pervasives_Native.None
           )::[])
        ->
        let effect_prefix_doc =
          let uu____1952 = str "effect"  in
          let uu____1953 =
            let uu____1954 = p_uident uid  in
            FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____1954  in
          FStar_Pprint.op_Hat_Hat uu____1952 uu____1953  in
        let uu____1955 =
          let uu____1956 = p_typars tpars  in
          FStar_Pprint.surround (Prims.parse_int "2") (Prims.parse_int "1")
            effect_prefix_doc uu____1956 FStar_Pprint.equals
           in
        let uu____1957 = p_typ t  in
        op_Hat_Slash_Plus_Hat uu____1955 uu____1957
    | FStar_Parser_AST.Tycon (false ,tcdefs) ->
        let uu____1967 = str "type"  in
        let uu____1968 = str "and"  in
        precede_break_separate_map uu____1967 uu____1968 p_fsdocTypeDeclPairs
          tcdefs
    | FStar_Parser_AST.TopLevelLet (q,lbs) ->
        let let_doc =
          let uu____1981 = str "let"  in
          let uu____1982 =
            let uu____1983 = p_letqualifier q  in
            FStar_Pprint.op_Hat_Hat uu____1983 FStar_Pprint.space  in
          FStar_Pprint.op_Hat_Hat uu____1981 uu____1982  in
        let uu____1984 =
          let uu____1985 = str "and"  in
          FStar_Pprint.op_Hat_Hat uu____1985 FStar_Pprint.space  in
        separate_map_with_comments let_doc uu____1984 p_letbinding lbs
          (fun uu____1988  ->
             match uu____1988 with
             | (p,t) ->
                 FStar_Range.union_ranges p.FStar_Parser_AST.prange
                   t.FStar_Parser_AST.range)
    | FStar_Parser_AST.Val (lid,t) ->
        let uu____1995 =
          let uu____1996 = str "val"  in
          let uu____1997 =
            let uu____1998 =
              let uu____1999 = p_lident lid  in
              let uu____2000 =
                FStar_Pprint.op_Hat_Hat FStar_Pprint.space FStar_Pprint.colon
                 in
              FStar_Pprint.op_Hat_Hat uu____1999 uu____2000  in
            FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____1998  in
          FStar_Pprint.op_Hat_Hat uu____1996 uu____1997  in
        let uu____2001 = p_typ t  in
        op_Hat_Slash_Plus_Hat uu____1995 uu____2001
    | FStar_Parser_AST.Assume (id,t) ->
        let decl_keyword =
          let uu____2005 =
            let uu____2006 =
              FStar_Util.char_at id.FStar_Ident.idText (Prims.parse_int "0")
               in
            FStar_All.pipe_right uu____2006 FStar_Util.is_upper  in
          if uu____2005
          then FStar_Pprint.empty
          else
            (let uu____2008 = str "val"  in
             FStar_Pprint.op_Hat_Hat uu____2008 FStar_Pprint.space)
           in
        let uu____2009 =
          let uu____2010 =
            let uu____2011 = p_ident id  in
            let uu____2012 =
              FStar_Pprint.op_Hat_Hat FStar_Pprint.space FStar_Pprint.colon
               in
            FStar_Pprint.op_Hat_Hat uu____2011 uu____2012  in
          FStar_Pprint.op_Hat_Hat decl_keyword uu____2010  in
        let uu____2013 = p_typ t  in
        op_Hat_Slash_Plus_Hat uu____2009 uu____2013
    | FStar_Parser_AST.Exception (uid,t_opt) ->
        let uu____2018 = str "exception"  in
        let uu____2019 =
          let uu____2020 =
            let uu____2021 = p_uident uid  in
            let uu____2022 =
              FStar_Pprint.optional
                (fun t  ->
                   let uu____2024 = str "of"  in
                   let uu____2025 = p_typ t  in
                   op_Hat_Slash_Plus_Hat uu____2024 uu____2025) t_opt
               in
            FStar_Pprint.op_Hat_Hat uu____2021 uu____2022  in
          FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____2020  in
        FStar_Pprint.op_Hat_Hat uu____2018 uu____2019
    | FStar_Parser_AST.NewEffect ne ->
        let uu____2027 = str "new_effect"  in
        let uu____2028 =
          let uu____2029 = p_newEffect ne  in
          FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____2029  in
        FStar_Pprint.op_Hat_Hat uu____2027 uu____2028
    | FStar_Parser_AST.SubEffect se ->
        let uu____2031 = str "sub_effect"  in
        let uu____2032 =
          let uu____2033 = p_subEffect se  in
          FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____2033  in
        FStar_Pprint.op_Hat_Hat uu____2031 uu____2032
    | FStar_Parser_AST.Pragma p -> p_pragma p
    | FStar_Parser_AST.Fsdoc doc1 ->
        let uu____2036 = p_fsdoc doc1  in
        FStar_Pprint.op_Hat_Hat uu____2036 FStar_Pprint.hardline
    | FStar_Parser_AST.Main uu____2037 ->
        failwith "*Main declaration* : Is that really still in use ??"
    | FStar_Parser_AST.Tycon (true ,uu____2038) ->
        failwith
          "Effect abbreviation is expected to be defined by an abbreviation"

and p_pragma : FStar_Parser_AST.pragma -> FStar_Pprint.document =
  fun uu___98_2047  ->
    match uu___98_2047 with
    | FStar_Parser_AST.SetOptions s ->
        let uu____2049 = str "#set-options"  in
        let uu____2050 =
          let uu____2051 =
            let uu____2052 = str s  in FStar_Pprint.dquotes uu____2052  in
          FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____2051  in
        FStar_Pprint.op_Hat_Hat uu____2049 uu____2050
    | FStar_Parser_AST.ResetOptions s_opt ->
        let uu____2055 = str "#reset-options"  in
        let uu____2056 =
          FStar_Pprint.optional
            (fun s  ->
               let uu____2058 =
                 let uu____2059 = str s  in FStar_Pprint.dquotes uu____2059
                  in
               FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____2058) s_opt
           in
        FStar_Pprint.op_Hat_Hat uu____2055 uu____2056
    | FStar_Parser_AST.LightOff  ->
        (FStar_ST.write should_print_fs_typ_app true; str "#light \"off\"")

and p_typars : FStar_Parser_AST.binder Prims.list -> FStar_Pprint.document =
  fun bs  -> p_binders true bs

and p_fsdocTypeDeclPairs :
  (FStar_Parser_AST.tycon,FStar_Parser_AST.fsdoc
                            FStar_Pervasives_Native.option)
    FStar_Pervasives_Native.tuple2 -> FStar_Pprint.document
  =
  fun uu____2065  ->
    match uu____2065 with
    | (typedecl,fsdoc_opt) ->
        let uu____2073 = FStar_Pprint.optional p_fsdoc fsdoc_opt  in
        let uu____2074 = p_typeDecl typedecl  in
        FStar_Pprint.op_Hat_Hat uu____2073 uu____2074

and p_typeDecl : FStar_Parser_AST.tycon -> FStar_Pprint.document =
  fun uu___99_2075  ->
    match uu___99_2075 with
    | FStar_Parser_AST.TyconAbstract (lid,bs,typ_opt) ->
        let empty' uu____2086 = FStar_Pprint.empty  in
        p_typeDeclPrefix lid bs typ_opt empty'
    | FStar_Parser_AST.TyconAbbrev (lid,bs,typ_opt,t) ->
        let f uu____2098 =
          let uu____2099 = p_typ t  in prefix2 FStar_Pprint.equals uu____2099
           in
        p_typeDeclPrefix lid bs typ_opt f
    | FStar_Parser_AST.TyconRecord (lid,bs,typ_opt,record_field_decls) ->
        let p_recordFieldAndComments uu____2125 =
          match uu____2125 with
          | (lid1,t,doc_opt) ->
              let uu____2135 =
                FStar_Range.extend_to_end_of_line t.FStar_Parser_AST.range
                 in
              with_comment p_recordFieldDecl (lid1, t, doc_opt) uu____2135
           in
        let p_fields uu____2144 =
          let uu____2145 =
            let uu____2146 =
              let uu____2147 =
                let uu____2148 =
                  FStar_Pprint.op_Hat_Hat FStar_Pprint.semi break1  in
                FStar_Pprint.separate_map uu____2148 p_recordFieldAndComments
                  record_field_decls
                 in
              braces_with_nesting uu____2147  in
            FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____2146  in
          FStar_Pprint.op_Hat_Hat FStar_Pprint.equals uu____2145  in
        p_typeDeclPrefix lid bs typ_opt p_fields
    | FStar_Parser_AST.TyconVariant (lid,bs,typ_opt,ct_decls) ->
        let p_constructorBranchAndComments uu____2184 =
          match uu____2184 with
          | (uid,t_opt,doc_opt,use_of) ->
              let range =
                let uu____2200 =
                  let uu____2201 =
                    FStar_Util.map_opt t_opt
                      (fun t  -> t.FStar_Parser_AST.range)
                     in
                  FStar_Util.dflt uid.FStar_Ident.idRange uu____2201  in
                FStar_Range.extend_to_end_of_line uu____2200  in
              let p_constructorBranch decl =
                let uu____2220 =
                  let uu____2221 =
                    let uu____2222 = p_constructorDecl decl  in
                    FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____2222  in
                  FStar_Pprint.op_Hat_Hat FStar_Pprint.bar uu____2221  in
                FStar_Pprint.group uu____2220  in
              with_comment p_constructorBranch (uid, t_opt, doc_opt, use_of)
                range
           in
        let datacon_doc uu____2234 =
          let uu____2235 =
            FStar_Pprint.separate_map break1 p_constructorBranchAndComments
              ct_decls
             in
          FStar_Pprint.group uu____2235  in
        p_typeDeclPrefix lid bs typ_opt
          (fun uu____2242  ->
             let uu____2243 = datacon_doc ()  in
             prefix2 FStar_Pprint.equals uu____2243)

and p_typeDeclPrefix :
  FStar_Ident.ident ->
    FStar_Parser_AST.binder Prims.list ->
      FStar_Parser_AST.knd FStar_Pervasives_Native.option ->
        (Prims.unit -> FStar_Pprint.document) -> FStar_Pprint.document
  =
  fun lid  ->
    fun bs  ->
      fun typ_opt  ->
        fun cont  ->
          if (bs = []) && (typ_opt = FStar_Pervasives_Native.None)
          then
            let uu____2254 = p_ident lid  in
            let uu____2255 =
              let uu____2256 = cont ()  in
              FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____2256  in
            FStar_Pprint.op_Hat_Hat uu____2254 uu____2255
          else
            (let binders_doc =
               let uu____2259 = p_typars bs  in
               let uu____2260 =
                 FStar_Pprint.optional
                   (fun t  ->
                      let uu____2262 =
                        let uu____2263 =
                          let uu____2264 = p_typ t  in
                          FStar_Pprint.op_Hat_Hat FStar_Pprint.space
                            uu____2264
                           in
                        FStar_Pprint.op_Hat_Hat FStar_Pprint.colon uu____2263
                         in
                      FStar_Pprint.op_Hat_Hat break1 uu____2262) typ_opt
                  in
               FStar_Pprint.op_Hat_Hat uu____2259 uu____2260  in
             let uu____2265 = p_ident lid  in
             let uu____2266 = cont ()  in
             FStar_Pprint.surround (Prims.parse_int "2")
               (Prims.parse_int "1") uu____2265 binders_doc uu____2266)

and p_recordFieldDecl :
  (FStar_Ident.ident,FStar_Parser_AST.term,FStar_Parser_AST.fsdoc
                                             FStar_Pervasives_Native.option)
    FStar_Pervasives_Native.tuple3 -> FStar_Pprint.document
  =
  fun uu____2267  ->
    match uu____2267 with
    | (lid,t,doc_opt) ->
        let uu____2277 =
          let uu____2278 = FStar_Pprint.optional p_fsdoc doc_opt  in
          let uu____2279 =
            let uu____2280 = p_lident lid  in
            let uu____2281 =
              let uu____2282 = p_typ t  in
              FStar_Pprint.op_Hat_Hat FStar_Pprint.colon uu____2282  in
            FStar_Pprint.op_Hat_Hat uu____2280 uu____2281  in
          FStar_Pprint.op_Hat_Hat uu____2278 uu____2279  in
        FStar_Pprint.group uu____2277

and p_constructorDecl :
  (FStar_Ident.ident,FStar_Parser_AST.term FStar_Pervasives_Native.option,
    FStar_Parser_AST.fsdoc FStar_Pervasives_Native.option,Prims.bool)
    FStar_Pervasives_Native.tuple4 -> FStar_Pprint.document
  =
  fun uu____2283  ->
    match uu____2283 with
    | (uid,t_opt,doc_opt,use_of) ->
        let sep = if use_of then str "of" else FStar_Pprint.colon  in
        let uid_doc = p_uident uid  in
        let uu____2301 = FStar_Pprint.optional p_fsdoc doc_opt  in
        let uu____2302 =
          let uu____2303 = FStar_Pprint.break_ (Prims.parse_int "0")  in
          let uu____2304 =
            default_or_map uid_doc
              (fun t  ->
                 let uu____2306 =
                   let uu____2307 =
                     FStar_Pprint.op_Hat_Hat FStar_Pprint.space sep  in
                   FStar_Pprint.op_Hat_Hat uid_doc uu____2307  in
                 let uu____2308 = p_typ t  in
                 op_Hat_Slash_Plus_Hat uu____2306 uu____2308) t_opt
             in
          FStar_Pprint.op_Hat_Hat uu____2303 uu____2304  in
        FStar_Pprint.op_Hat_Hat uu____2301 uu____2302

and p_letbinding :
  (FStar_Parser_AST.pattern,FStar_Parser_AST.term)
    FStar_Pervasives_Native.tuple2 -> FStar_Pprint.document
  =
  fun uu____2309  ->
    match uu____2309 with
    | (pat,e) ->
        let pat_doc =
          let uu____2315 =
            match pat.FStar_Parser_AST.pat with
            | FStar_Parser_AST.PatAscribed (pat1,t) ->
                let uu____2322 =
                  let uu____2323 =
                    let uu____2324 =
                      let uu____2325 =
                        let uu____2326 = p_tmArrow p_tmNoEq t  in
                        FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____2326
                         in
                      FStar_Pprint.op_Hat_Hat FStar_Pprint.colon uu____2325
                       in
                    FStar_Pprint.group uu____2324  in
                  FStar_Pprint.op_Hat_Hat break1 uu____2323  in
                (pat1, uu____2322)
            | uu____2327 -> (pat, FStar_Pprint.empty)  in
          match uu____2315 with
          | (pat1,ascr_doc) ->
              (match pat1.FStar_Parser_AST.pat with
               | FStar_Parser_AST.PatApp
                   ({
                      FStar_Parser_AST.pat = FStar_Parser_AST.PatVar
                        (x,uu____2331);
                      FStar_Parser_AST.prange = uu____2332;_},pats)
                   ->
                   let uu____2338 = p_lident x  in
                   let uu____2339 =
                     let uu____2340 =
                       FStar_Pprint.separate_map break1 p_atomicPattern pats
                        in
                     FStar_Pprint.op_Hat_Hat uu____2340 ascr_doc  in
                   FStar_Pprint.surround (Prims.parse_int "2")
                     (Prims.parse_int "1") uu____2338 uu____2339
                     FStar_Pprint.equals
               | uu____2341 ->
                   let uu____2342 =
                     let uu____2343 = p_tuplePattern pat1  in
                     let uu____2344 =
                       FStar_Pprint.op_Hat_Slash_Hat ascr_doc
                         FStar_Pprint.equals
                        in
                     FStar_Pprint.op_Hat_Hat uu____2343 uu____2344  in
                   FStar_Pprint.group uu____2342)
           in
        let uu____2345 = p_term e  in prefix2 pat_doc uu____2345

and p_newEffect : FStar_Parser_AST.effect_decl -> FStar_Pprint.document =
  fun uu___100_2346  ->
    match uu___100_2346 with
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
        let uu____2364 = p_uident uid  in
        let uu____2365 = p_binders true bs  in
        let uu____2366 =
          let uu____2367 = p_simpleTerm t  in
          prefix2 FStar_Pprint.equals uu____2367  in
        FStar_Pprint.surround (Prims.parse_int "2") (Prims.parse_int "1")
          uu____2364 uu____2365 uu____2366

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
          let uu____2374 =
            let uu____2375 =
              let uu____2376 =
                let uu____2377 = p_uident uid  in
                let uu____2378 = p_binders true bs  in
                let uu____2379 =
                  let uu____2380 = p_typ t  in
                  prefix2 FStar_Pprint.colon uu____2380  in
                FStar_Pprint.surround (Prims.parse_int "2")
                  (Prims.parse_int "1") uu____2377 uu____2378 uu____2379
                 in
              FStar_Pprint.group uu____2376  in
            let uu____2381 =
              let uu____2382 = str "with"  in
              let uu____2383 =
                separate_break_map FStar_Pprint.semi p_effectDecl eff_decls
                 in
              prefix2 uu____2382 uu____2383  in
            FStar_Pprint.op_Hat_Slash_Hat uu____2375 uu____2381  in
          braces_with_nesting uu____2374

and p_effectDecl : FStar_Parser_AST.decl -> FStar_Pprint.document =
  fun d  ->
    match d.FStar_Parser_AST.d with
    | FStar_Parser_AST.Tycon
        (false
         ,(FStar_Parser_AST.TyconAbbrev
           (lid,[],FStar_Pervasives_Native.None ,e),FStar_Pervasives_Native.None
           )::[])
        ->
        let uu____2400 =
          let uu____2401 = p_lident lid  in
          let uu____2402 =
            FStar_Pprint.op_Hat_Hat FStar_Pprint.space FStar_Pprint.equals
             in
          FStar_Pprint.op_Hat_Hat uu____2401 uu____2402  in
        let uu____2403 = p_simpleTerm e  in prefix2 uu____2400 uu____2403
    | uu____2404 ->
        let uu____2405 =
          let uu____2406 = FStar_Parser_AST.decl_to_string d  in
          FStar_Util.format1
            "Not a declaration of an effect member... or at least I hope so : %s"
            uu____2406
           in
        failwith uu____2405

and p_subEffect : FStar_Parser_AST.lift -> FStar_Pprint.document =
  fun lift  ->
    let lift_op_doc =
      let lifts =
        match lift.FStar_Parser_AST.lift_op with
        | FStar_Parser_AST.NonReifiableLift t -> [("lift_wp", t)]
        | FStar_Parser_AST.ReifiableLift (t1,t2) ->
            [("lif_wp", t1); ("lift", t2)]
        | FStar_Parser_AST.LiftForFree t -> [("lift", t)]  in
      let p_lift uu____2439 =
        match uu____2439 with
        | (kwd1,t) ->
            let uu____2444 =
              let uu____2445 = str kwd1  in
              let uu____2446 =
                FStar_Pprint.op_Hat_Hat FStar_Pprint.space
                  FStar_Pprint.equals
                 in
              FStar_Pprint.op_Hat_Hat uu____2445 uu____2446  in
            let uu____2447 = p_simpleTerm t  in prefix2 uu____2444 uu____2447
         in
      separate_break_map FStar_Pprint.semi p_lift lifts  in
    let uu____2450 =
      let uu____2451 =
        let uu____2452 = p_quident lift.FStar_Parser_AST.msource  in
        let uu____2453 =
          let uu____2454 = str "~>"  in
          FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____2454  in
        FStar_Pprint.op_Hat_Hat uu____2452 uu____2453  in
      let uu____2455 = p_quident lift.FStar_Parser_AST.mdest  in
      prefix2 uu____2451 uu____2455  in
    let uu____2456 =
      let uu____2457 = braces_with_nesting lift_op_doc  in
      FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____2457  in
    FStar_Pprint.op_Hat_Hat uu____2450 uu____2456

and p_qualifier : FStar_Parser_AST.qualifier -> FStar_Pprint.document =
  fun uu___101_2458  ->
    match uu___101_2458 with
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
    let uu____2460 = FStar_Pprint.separate_map break1 p_qualifier qs  in
    FStar_Pprint.group uu____2460

and p_letqualifier : FStar_Parser_AST.let_qualifier -> FStar_Pprint.document
  =
  fun uu___102_2461  ->
    match uu___102_2461 with
    | FStar_Parser_AST.Rec  ->
        let uu____2462 = str "rec"  in
        FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____2462
    | FStar_Parser_AST.Mutable  ->
        let uu____2463 = str "mutable"  in
        FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____2463
    | FStar_Parser_AST.NoLetQualifier  -> FStar_Pprint.empty

and p_aqual : FStar_Parser_AST.arg_qualifier -> FStar_Pprint.document =
  fun uu___103_2464  ->
    match uu___103_2464 with
    | FStar_Parser_AST.Implicit  -> str "#"
    | FStar_Parser_AST.Equality  -> str "$"

and p_disjunctivePattern : FStar_Parser_AST.pattern -> FStar_Pprint.document
  =
  fun p  ->
    match p.FStar_Parser_AST.pat with
    | FStar_Parser_AST.PatOr pats ->
        let uu____2468 =
          let uu____2469 =
            let uu____2470 =
              FStar_Pprint.op_Hat_Hat FStar_Pprint.bar FStar_Pprint.space  in
            FStar_Pprint.op_Hat_Hat break1 uu____2470  in
          FStar_Pprint.separate_map uu____2469 p_tuplePattern pats  in
        FStar_Pprint.group uu____2468
    | uu____2471 -> p_tuplePattern p

and p_tuplePattern : FStar_Parser_AST.pattern -> FStar_Pprint.document =
  fun p  ->
    match p.FStar_Parser_AST.pat with
    | FStar_Parser_AST.PatTuple (pats,false ) ->
        let uu____2476 =
          let uu____2477 = FStar_Pprint.op_Hat_Hat FStar_Pprint.comma break1
             in
          FStar_Pprint.separate_map uu____2477 p_constructorPattern pats  in
        FStar_Pprint.group uu____2476
    | uu____2478 -> p_constructorPattern p

and p_constructorPattern : FStar_Parser_AST.pattern -> FStar_Pprint.document
  =
  fun p  ->
    match p.FStar_Parser_AST.pat with
    | FStar_Parser_AST.PatApp
        ({ FStar_Parser_AST.pat = FStar_Parser_AST.PatName maybe_cons_lid;
           FStar_Parser_AST.prange = uu____2481;_},hd1::tl1::[])
        when
        FStar_Ident.lid_equals maybe_cons_lid FStar_Parser_Const.cons_lid ->
        let uu____2485 =
          FStar_Pprint.op_Hat_Hat FStar_Pprint.colon FStar_Pprint.colon  in
        let uu____2486 = p_constructorPattern hd1  in
        let uu____2487 = p_constructorPattern tl1  in
        infix0 uu____2485 uu____2486 uu____2487
    | FStar_Parser_AST.PatApp
        ({ FStar_Parser_AST.pat = FStar_Parser_AST.PatName uid;
           FStar_Parser_AST.prange = uu____2489;_},pats)
        ->
        let uu____2493 = p_quident uid  in
        let uu____2494 =
          FStar_Pprint.separate_map break1 p_atomicPattern pats  in
        prefix2 uu____2493 uu____2494
    | uu____2495 -> p_atomicPattern p

and p_atomicPattern : FStar_Parser_AST.pattern -> FStar_Pprint.document =
  fun p  ->
    match p.FStar_Parser_AST.pat with
    | FStar_Parser_AST.PatAscribed (pat,t) ->
        let uu____2499 =
          let uu____2502 =
            let uu____2503 = unparen t  in uu____2503.FStar_Parser_AST.tm  in
          ((pat.FStar_Parser_AST.pat), uu____2502)  in
        (match uu____2499 with
         | (FStar_Parser_AST.PatVar (lid,aqual),FStar_Parser_AST.Refine
            ({ FStar_Parser_AST.b = FStar_Parser_AST.Annotated (lid',t1);
               FStar_Parser_AST.brange = uu____2508;
               FStar_Parser_AST.blevel = uu____2509;
               FStar_Parser_AST.aqual = uu____2510;_},phi))
             when lid.FStar_Ident.idText = lid'.FStar_Ident.idText ->
             let uu____2514 =
               let uu____2515 = p_ident lid  in
               p_refinement aqual uu____2515 t1 phi  in
             soft_parens_with_nesting uu____2514
         | (FStar_Parser_AST.PatWild ,FStar_Parser_AST.Refine
            ({ FStar_Parser_AST.b = FStar_Parser_AST.NoName t1;
               FStar_Parser_AST.brange = uu____2517;
               FStar_Parser_AST.blevel = uu____2518;
               FStar_Parser_AST.aqual = uu____2519;_},phi))
             ->
             let uu____2521 =
               p_refinement FStar_Pervasives_Native.None
                 FStar_Pprint.underscore t1 phi
                in
             soft_parens_with_nesting uu____2521
         | uu____2522 ->
             let uu____2525 =
               let uu____2526 = p_tuplePattern pat  in
               let uu____2527 =
                 let uu____2528 = FStar_Pprint.break_ (Prims.parse_int "0")
                    in
                 let uu____2529 =
                   let uu____2530 = p_typ t  in
                   FStar_Pprint.op_Hat_Hat FStar_Pprint.colon uu____2530  in
                 FStar_Pprint.op_Hat_Hat uu____2528 uu____2529  in
               FStar_Pprint.op_Hat_Hat uu____2526 uu____2527  in
             soft_parens_with_nesting uu____2525)
    | FStar_Parser_AST.PatList pats ->
        let uu____2533 =
          separate_break_map FStar_Pprint.semi p_tuplePattern pats  in
        FStar_Pprint.surround (Prims.parse_int "2") (Prims.parse_int "0")
          FStar_Pprint.lbracket uu____2533 FStar_Pprint.rbracket
    | FStar_Parser_AST.PatRecord pats ->
        let p_recordFieldPat uu____2543 =
          match uu____2543 with
          | (lid,pat) ->
              let uu____2548 = p_qlident lid  in
              let uu____2549 = p_tuplePattern pat  in
              infix2 FStar_Pprint.equals uu____2548 uu____2549
           in
        let uu____2550 =
          separate_break_map FStar_Pprint.semi p_recordFieldPat pats  in
        soft_braces_with_nesting uu____2550
    | FStar_Parser_AST.PatTuple (pats,true ) ->
        let uu____2556 =
          FStar_Pprint.op_Hat_Hat FStar_Pprint.lparen FStar_Pprint.bar  in
        let uu____2557 =
          separate_break_map FStar_Pprint.comma p_constructorPattern pats  in
        let uu____2558 =
          FStar_Pprint.op_Hat_Hat FStar_Pprint.bar FStar_Pprint.rparen  in
        FStar_Pprint.surround (Prims.parse_int "2") (Prims.parse_int "1")
          uu____2556 uu____2557 uu____2558
    | FStar_Parser_AST.PatTvar (tv,arg_qualifier_opt) -> p_tvar tv
    | FStar_Parser_AST.PatOp op ->
        let uu____2565 =
          let uu____2566 =
            let uu____2567 = str (FStar_Ident.text_of_id op)  in
            let uu____2568 =
              FStar_Pprint.op_Hat_Hat FStar_Pprint.space FStar_Pprint.rparen
               in
            FStar_Pprint.op_Hat_Hat uu____2567 uu____2568  in
          FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____2566  in
        FStar_Pprint.op_Hat_Hat FStar_Pprint.lparen uu____2565
    | FStar_Parser_AST.PatWild  -> FStar_Pprint.underscore
    | FStar_Parser_AST.PatConst c -> p_constant c
    | FStar_Parser_AST.PatVar (lid,aqual) ->
        let uu____2574 = FStar_Pprint.optional p_aqual aqual  in
        let uu____2575 = p_lident lid  in
        FStar_Pprint.op_Hat_Hat uu____2574 uu____2575
    | FStar_Parser_AST.PatName uid -> p_quident uid
    | FStar_Parser_AST.PatOr uu____2577 -> failwith "Inner or pattern !"
    | FStar_Parser_AST.PatApp
        ({ FStar_Parser_AST.pat = FStar_Parser_AST.PatName uu____2579;
           FStar_Parser_AST.prange = uu____2580;_},uu____2581)
        ->
        let uu____2584 = p_tuplePattern p  in
        soft_parens_with_nesting uu____2584
    | FStar_Parser_AST.PatTuple (uu____2585,false ) ->
        let uu____2588 = p_tuplePattern p  in
        soft_parens_with_nesting uu____2588
    | uu____2589 ->
        let uu____2590 =
          let uu____2591 = FStar_Parser_AST.pat_to_string p  in
          FStar_Util.format1 "Invalid pattern %s" uu____2591  in
        failwith uu____2590

and p_binder : Prims.bool -> FStar_Parser_AST.binder -> FStar_Pprint.document
  =
  fun is_atomic  ->
    fun b  ->
      match b.FStar_Parser_AST.b with
      | FStar_Parser_AST.Variable lid ->
          let uu____2595 =
            FStar_Pprint.optional p_aqual b.FStar_Parser_AST.aqual  in
          let uu____2596 = p_lident lid  in
          FStar_Pprint.op_Hat_Hat uu____2595 uu____2596
      | FStar_Parser_AST.TVariable lid -> p_lident lid
      | FStar_Parser_AST.Annotated (lid,t) ->
          let doc1 =
            let uu____2601 =
              let uu____2602 = unparen t  in uu____2602.FStar_Parser_AST.tm
               in
            match uu____2601 with
            | FStar_Parser_AST.Refine
                ({ FStar_Parser_AST.b = FStar_Parser_AST.Annotated (lid',t1);
                   FStar_Parser_AST.brange = uu____2605;
                   FStar_Parser_AST.blevel = uu____2606;
                   FStar_Parser_AST.aqual = uu____2607;_},phi)
                when lid.FStar_Ident.idText = lid'.FStar_Ident.idText ->
                let uu____2609 = p_ident lid  in
                p_refinement b.FStar_Parser_AST.aqual uu____2609 t1 phi
            | uu____2610 ->
                let uu____2611 =
                  FStar_Pprint.optional p_aqual b.FStar_Parser_AST.aqual  in
                let uu____2612 =
                  let uu____2613 = p_lident lid  in
                  let uu____2614 =
                    let uu____2615 =
                      let uu____2616 =
                        FStar_Pprint.break_ (Prims.parse_int "0")  in
                      let uu____2617 = p_tmFormula t  in
                      FStar_Pprint.op_Hat_Hat uu____2616 uu____2617  in
                    FStar_Pprint.op_Hat_Hat FStar_Pprint.colon uu____2615  in
                  FStar_Pprint.op_Hat_Hat uu____2613 uu____2614  in
                FStar_Pprint.op_Hat_Hat uu____2611 uu____2612
             in
          if is_atomic
          then
            let uu____2618 =
              let uu____2619 =
                FStar_Pprint.op_Hat_Hat doc1 FStar_Pprint.rparen  in
              FStar_Pprint.op_Hat_Hat FStar_Pprint.lparen uu____2619  in
            FStar_Pprint.group uu____2618
          else FStar_Pprint.group doc1
      | FStar_Parser_AST.TAnnotated uu____2621 ->
          failwith "Is this still used ?"
      | FStar_Parser_AST.NoName t ->
          let uu____2625 =
            let uu____2626 = unparen t  in uu____2626.FStar_Parser_AST.tm  in
          (match uu____2625 with
           | FStar_Parser_AST.Refine
               ({ FStar_Parser_AST.b = FStar_Parser_AST.NoName t1;
                  FStar_Parser_AST.brange = uu____2628;
                  FStar_Parser_AST.blevel = uu____2629;
                  FStar_Parser_AST.aqual = uu____2630;_},phi)
               ->
               if is_atomic
               then
                 let uu____2632 =
                   let uu____2633 =
                     let uu____2634 =
                       p_refinement b.FStar_Parser_AST.aqual
                         FStar_Pprint.underscore t1 phi
                        in
                     FStar_Pprint.op_Hat_Hat uu____2634 FStar_Pprint.rparen
                      in
                   FStar_Pprint.op_Hat_Hat FStar_Pprint.lparen uu____2633  in
                 FStar_Pprint.group uu____2632
               else
                 (let uu____2636 =
                    p_refinement b.FStar_Parser_AST.aqual
                      FStar_Pprint.underscore t1 phi
                     in
                  FStar_Pprint.group uu____2636)
           | uu____2637 -> if is_atomic then p_atomicTerm t else p_appTerm t)

and p_refinement :
  FStar_Parser_AST.arg_qualifier FStar_Pervasives_Native.option ->
    FStar_Pprint.document ->
      FStar_Parser_AST.term -> FStar_Parser_AST.term -> FStar_Pprint.document
  =
  fun aqual_opt  ->
    fun binder  ->
      fun t  ->
        fun phi  ->
          let uu____2644 = FStar_Pprint.optional p_aqual aqual_opt  in
          let uu____2645 =
            let uu____2646 =
              let uu____2647 =
                let uu____2648 = p_appTerm t  in
                let uu____2649 =
                  let uu____2650 = p_noSeqTerm phi  in
                  soft_braces_with_nesting uu____2650  in
                FStar_Pprint.op_Hat_Hat uu____2648 uu____2649  in
              FStar_Pprint.op_Hat_Hat FStar_Pprint.colon uu____2647  in
            FStar_Pprint.op_Hat_Hat binder uu____2646  in
          FStar_Pprint.op_Hat_Hat uu____2644 uu____2645

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
    let uu____2663 =
      let uu____2664 = unparen e  in uu____2664.FStar_Parser_AST.tm  in
    match uu____2663 with
    | FStar_Parser_AST.Seq (e1,e2) ->
        let uu____2667 =
          let uu____2668 =
            let uu____2669 = p_noSeqTerm e1  in
            FStar_Pprint.op_Hat_Hat uu____2669 FStar_Pprint.semi  in
          FStar_Pprint.group uu____2668  in
        let uu____2670 = p_term e2  in
        FStar_Pprint.op_Hat_Slash_Hat uu____2667 uu____2670
    | FStar_Parser_AST.Bind (x,e1,e2) ->
        let uu____2674 =
          let uu____2675 =
            let uu____2676 =
              let uu____2677 = p_lident x  in
              let uu____2678 =
                FStar_Pprint.op_Hat_Hat FStar_Pprint.space
                  FStar_Pprint.long_left_arrow
                 in
              FStar_Pprint.op_Hat_Hat uu____2677 uu____2678  in
            let uu____2679 =
              let uu____2680 = p_noSeqTerm e1  in
              let uu____2681 =
                FStar_Pprint.op_Hat_Hat FStar_Pprint.space FStar_Pprint.semi
                 in
              FStar_Pprint.op_Hat_Hat uu____2680 uu____2681  in
            op_Hat_Slash_Plus_Hat uu____2676 uu____2679  in
          FStar_Pprint.group uu____2675  in
        let uu____2682 = p_term e2  in
        FStar_Pprint.op_Hat_Slash_Hat uu____2674 uu____2682
    | uu____2683 ->
        let uu____2684 = p_noSeqTerm e  in FStar_Pprint.group uu____2684

and p_noSeqTerm : FStar_Parser_AST.term -> FStar_Pprint.document =
  fun e  -> with_comment p_noSeqTerm' e e.FStar_Parser_AST.range

and p_noSeqTerm' : FStar_Parser_AST.term -> FStar_Pprint.document =
  fun e  ->
    let uu____2687 =
      let uu____2688 = unparen e  in uu____2688.FStar_Parser_AST.tm  in
    match uu____2687 with
    | FStar_Parser_AST.Ascribed (e1,t,FStar_Pervasives_Native.None ) ->
        let uu____2692 =
          let uu____2693 = p_tmIff e1  in
          let uu____2694 =
            let uu____2695 =
              let uu____2696 = p_typ t  in
              FStar_Pprint.op_Hat_Slash_Hat FStar_Pprint.colon uu____2696  in
            FStar_Pprint.op_Hat_Hat FStar_Pprint.langle uu____2695  in
          FStar_Pprint.op_Hat_Slash_Hat uu____2693 uu____2694  in
        FStar_Pprint.group uu____2692
    | FStar_Parser_AST.Ascribed (e1,t,FStar_Pervasives_Native.Some tac) ->
        let uu____2701 =
          let uu____2702 = p_tmIff e1  in
          let uu____2703 =
            let uu____2704 =
              let uu____2705 =
                let uu____2706 = p_typ t  in
                let uu____2707 =
                  let uu____2708 = str "by"  in
                  let uu____2709 = p_typ tac  in
                  FStar_Pprint.op_Hat_Slash_Hat uu____2708 uu____2709  in
                FStar_Pprint.op_Hat_Slash_Hat uu____2706 uu____2707  in
              FStar_Pprint.op_Hat_Slash_Hat FStar_Pprint.colon uu____2705  in
            FStar_Pprint.op_Hat_Hat FStar_Pprint.langle uu____2704  in
          FStar_Pprint.op_Hat_Slash_Hat uu____2702 uu____2703  in
        FStar_Pprint.group uu____2701
    | FStar_Parser_AST.Op
        ({ FStar_Ident.idText = ".()<-"; FStar_Ident.idRange = uu____2710;_},e1::e2::e3::[])
        ->
        let uu____2715 =
          let uu____2716 =
            let uu____2717 =
              let uu____2718 = p_atomicTermNotQUident e1  in
              let uu____2719 =
                let uu____2720 =
                  let uu____2721 =
                    let uu____2722 = p_term e2  in
                    soft_parens_with_nesting uu____2722  in
                  let uu____2723 =
                    FStar_Pprint.op_Hat_Hat FStar_Pprint.space
                      FStar_Pprint.larrow
                     in
                  FStar_Pprint.op_Hat_Hat uu____2721 uu____2723  in
                FStar_Pprint.op_Hat_Hat FStar_Pprint.dot uu____2720  in
              FStar_Pprint.op_Hat_Hat uu____2718 uu____2719  in
            FStar_Pprint.group uu____2717  in
          let uu____2724 =
            let uu____2725 = p_noSeqTerm e3  in jump2 uu____2725  in
          FStar_Pprint.op_Hat_Hat uu____2716 uu____2724  in
        FStar_Pprint.group uu____2715
    | FStar_Parser_AST.Op
        ({ FStar_Ident.idText = ".[]<-"; FStar_Ident.idRange = uu____2726;_},e1::e2::e3::[])
        ->
        let uu____2731 =
          let uu____2732 =
            let uu____2733 =
              let uu____2734 = p_atomicTermNotQUident e1  in
              let uu____2735 =
                let uu____2736 =
                  let uu____2737 =
                    let uu____2738 = p_term e2  in
                    soft_brackets_with_nesting uu____2738  in
                  let uu____2739 =
                    FStar_Pprint.op_Hat_Hat FStar_Pprint.space
                      FStar_Pprint.larrow
                     in
                  FStar_Pprint.op_Hat_Hat uu____2737 uu____2739  in
                FStar_Pprint.op_Hat_Hat FStar_Pprint.dot uu____2736  in
              FStar_Pprint.op_Hat_Hat uu____2734 uu____2735  in
            FStar_Pprint.group uu____2733  in
          let uu____2740 =
            let uu____2741 = p_noSeqTerm e3  in jump2 uu____2741  in
          FStar_Pprint.op_Hat_Hat uu____2732 uu____2740  in
        FStar_Pprint.group uu____2731
    | FStar_Parser_AST.Requires (e1,wtf) ->
        let uu____2747 =
          let uu____2748 = str "requires"  in
          let uu____2749 = p_typ e1  in
          FStar_Pprint.op_Hat_Slash_Hat uu____2748 uu____2749  in
        FStar_Pprint.group uu____2747
    | FStar_Parser_AST.Ensures (e1,wtf) ->
        let uu____2755 =
          let uu____2756 = str "ensures"  in
          let uu____2757 = p_typ e1  in
          FStar_Pprint.op_Hat_Slash_Hat uu____2756 uu____2757  in
        FStar_Pprint.group uu____2755
    | FStar_Parser_AST.Attributes es ->
        let uu____2760 =
          let uu____2761 = str "attributes"  in
          let uu____2762 = FStar_Pprint.separate_map break1 p_atomicTerm es
             in
          FStar_Pprint.op_Hat_Slash_Hat uu____2761 uu____2762  in
        FStar_Pprint.group uu____2760
    | FStar_Parser_AST.If (e1,e2,e3) ->
        let uu____2766 = is_unit e3  in
        if uu____2766
        then
          let uu____2767 =
            let uu____2768 =
              let uu____2769 = str "if"  in
              let uu____2770 = p_noSeqTerm e1  in
              op_Hat_Slash_Plus_Hat uu____2769 uu____2770  in
            let uu____2771 =
              let uu____2772 = str "then"  in
              let uu____2773 = p_noSeqTerm e2  in
              op_Hat_Slash_Plus_Hat uu____2772 uu____2773  in
            FStar_Pprint.op_Hat_Slash_Hat uu____2768 uu____2771  in
          FStar_Pprint.group uu____2767
        else
          (let e2_doc =
             let uu____2776 =
               let uu____2777 = unparen e2  in uu____2777.FStar_Parser_AST.tm
                in
             match uu____2776 with
             | FStar_Parser_AST.If (uu____2778,uu____2779,e31) when
                 is_unit e31 ->
                 let uu____2781 = p_noSeqTerm e2  in
                 soft_parens_with_nesting uu____2781
             | uu____2782 -> p_noSeqTerm e2  in
           let uu____2783 =
             let uu____2784 =
               let uu____2785 = str "if"  in
               let uu____2786 = p_noSeqTerm e1  in
               op_Hat_Slash_Plus_Hat uu____2785 uu____2786  in
             let uu____2787 =
               let uu____2788 =
                 let uu____2789 = str "then"  in
                 op_Hat_Slash_Plus_Hat uu____2789 e2_doc  in
               let uu____2790 =
                 let uu____2791 = str "else"  in
                 let uu____2792 = p_noSeqTerm e3  in
                 op_Hat_Slash_Plus_Hat uu____2791 uu____2792  in
               FStar_Pprint.op_Hat_Slash_Hat uu____2788 uu____2790  in
             FStar_Pprint.op_Hat_Slash_Hat uu____2784 uu____2787  in
           FStar_Pprint.group uu____2783)
    | FStar_Parser_AST.TryWith (e1,branches) ->
        let uu____2805 =
          let uu____2806 =
            let uu____2807 = str "try"  in
            let uu____2808 = p_noSeqTerm e1  in prefix2 uu____2807 uu____2808
             in
          let uu____2809 =
            let uu____2810 = str "with"  in
            let uu____2811 =
              FStar_Pprint.separate_map FStar_Pprint.hardline p_patternBranch
                branches
               in
            FStar_Pprint.op_Hat_Slash_Hat uu____2810 uu____2811  in
          FStar_Pprint.op_Hat_Slash_Hat uu____2806 uu____2809  in
        FStar_Pprint.group uu____2805
    | FStar_Parser_AST.Match (e1,branches) ->
        let uu____2828 =
          let uu____2829 =
            let uu____2830 = str "match"  in
            let uu____2831 = p_noSeqTerm e1  in
            let uu____2832 = str "with"  in
            FStar_Pprint.surround (Prims.parse_int "2") (Prims.parse_int "1")
              uu____2830 uu____2831 uu____2832
             in
          let uu____2833 =
            FStar_Pprint.separate_map FStar_Pprint.hardline p_patternBranch
              branches
             in
          FStar_Pprint.op_Hat_Slash_Hat uu____2829 uu____2833  in
        FStar_Pprint.group uu____2828
    | FStar_Parser_AST.LetOpen (uid,e1) ->
        let uu____2840 =
          let uu____2841 =
            let uu____2842 = str "let open"  in
            let uu____2843 = p_quident uid  in
            let uu____2844 = str "in"  in
            FStar_Pprint.surround (Prims.parse_int "2") (Prims.parse_int "1")
              uu____2842 uu____2843 uu____2844
             in
          let uu____2845 = p_term e1  in
          FStar_Pprint.op_Hat_Slash_Hat uu____2841 uu____2845  in
        FStar_Pprint.group uu____2840
    | FStar_Parser_AST.Let (q,lbs,e1) ->
        let let_doc =
          let uu____2856 = str "let"  in
          let uu____2857 = p_letqualifier q  in
          FStar_Pprint.op_Hat_Hat uu____2856 uu____2857  in
        let uu____2858 =
          let uu____2859 =
            let uu____2860 =
              let uu____2861 = str "and"  in
              precede_break_separate_map let_doc uu____2861 p_letbinding lbs
               in
            let uu____2864 = str "in"  in
            FStar_Pprint.op_Hat_Slash_Hat uu____2860 uu____2864  in
          FStar_Pprint.group uu____2859  in
        let uu____2865 = p_term e1  in
        FStar_Pprint.op_Hat_Slash_Hat uu____2858 uu____2865
    | FStar_Parser_AST.Abs
        ({ FStar_Parser_AST.pat = FStar_Parser_AST.PatVar (x,typ_opt);
           FStar_Parser_AST.prange = uu____2868;_}::[],{
                                                         FStar_Parser_AST.tm
                                                           =
                                                           FStar_Parser_AST.Match
                                                           (maybe_x,branches);
                                                         FStar_Parser_AST.range
                                                           = uu____2871;
                                                         FStar_Parser_AST.level
                                                           = uu____2872;_})
        when matches_var maybe_x x ->
        let uu____2886 =
          let uu____2887 = str "function"  in
          let uu____2888 =
            FStar_Pprint.separate_map FStar_Pprint.hardline p_patternBranch
              branches
             in
          FStar_Pprint.op_Hat_Slash_Hat uu____2887 uu____2888  in
        FStar_Pprint.group uu____2886
    | FStar_Parser_AST.Assign (id,e1) ->
        let uu____2895 =
          let uu____2896 = p_lident id  in
          let uu____2897 =
            let uu____2898 = p_noSeqTerm e1  in
            FStar_Pprint.op_Hat_Slash_Hat FStar_Pprint.larrow uu____2898  in
          FStar_Pprint.op_Hat_Slash_Hat uu____2896 uu____2897  in
        FStar_Pprint.group uu____2895
    | uu____2899 -> p_typ e

and p_typ : FStar_Parser_AST.term -> FStar_Pprint.document =
  fun e  -> with_comment p_typ' e e.FStar_Parser_AST.range

and p_typ' : FStar_Parser_AST.term -> FStar_Pprint.document =
  fun e  ->
    let uu____2902 =
      let uu____2903 = unparen e  in uu____2903.FStar_Parser_AST.tm  in
    match uu____2902 with
    | FStar_Parser_AST.QForall (bs,trigger,e1) ->
        let uu____2913 =
          let uu____2914 =
            let uu____2915 = p_quantifier e  in
            FStar_Pprint.op_Hat_Hat uu____2915 FStar_Pprint.space  in
          let uu____2916 = p_binders true bs  in
          FStar_Pprint.soft_surround (Prims.parse_int "2")
            (Prims.parse_int "0") uu____2914 uu____2916 FStar_Pprint.dot
           in
        let uu____2917 =
          let uu____2918 = p_trigger trigger  in
          let uu____2919 = p_noSeqTerm e1  in
          FStar_Pprint.op_Hat_Hat uu____2918 uu____2919  in
        prefix2 uu____2913 uu____2917
    | FStar_Parser_AST.QExists (bs,trigger,e1) ->
        let uu____2929 =
          let uu____2930 =
            let uu____2931 = p_quantifier e  in
            FStar_Pprint.op_Hat_Hat uu____2931 FStar_Pprint.space  in
          let uu____2932 = p_binders true bs  in
          FStar_Pprint.soft_surround (Prims.parse_int "2")
            (Prims.parse_int "0") uu____2930 uu____2932 FStar_Pprint.dot
           in
        let uu____2933 =
          let uu____2934 = p_trigger trigger  in
          let uu____2935 = p_noSeqTerm e1  in
          FStar_Pprint.op_Hat_Hat uu____2934 uu____2935  in
        prefix2 uu____2929 uu____2933
    | uu____2936 -> p_simpleTerm e

and p_quantifier : FStar_Parser_AST.term -> FStar_Pprint.document =
  fun e  ->
    let uu____2938 =
      let uu____2939 = unparen e  in uu____2939.FStar_Parser_AST.tm  in
    match uu____2938 with
    | FStar_Parser_AST.QForall uu____2940 -> str "forall"
    | FStar_Parser_AST.QExists uu____2947 -> str "exists"
    | uu____2954 ->
        failwith "Imposible : p_quantifier called on a non-quantifier term"

and p_trigger :
  FStar_Parser_AST.term Prims.list Prims.list -> FStar_Pprint.document =
  fun uu___104_2955  ->
    match uu___104_2955 with
    | [] -> FStar_Pprint.empty
    | pats ->
        let uu____2962 =
          let uu____2963 =
            let uu____2964 = str "pattern"  in
            let uu____2965 =
              let uu____2966 =
                let uu____2967 = p_disjunctivePats pats  in jump2 uu____2967
                 in
              let uu____2968 =
                FStar_Pprint.op_Hat_Hat FStar_Pprint.rbrace break1  in
              FStar_Pprint.op_Hat_Slash_Hat uu____2966 uu____2968  in
            FStar_Pprint.op_Hat_Slash_Hat uu____2964 uu____2965  in
          FStar_Pprint.op_Hat_Hat FStar_Pprint.colon uu____2963  in
        FStar_Pprint.op_Hat_Hat FStar_Pprint.lbrace uu____2962

and p_disjunctivePats :
  FStar_Parser_AST.term Prims.list Prims.list -> FStar_Pprint.document =
  fun pats  ->
    let uu____2972 = str "\\/"  in
    FStar_Pprint.separate_map uu____2972 p_conjunctivePats pats

and p_conjunctivePats :
  FStar_Parser_AST.term Prims.list -> FStar_Pprint.document =
  fun pats  ->
    let uu____2976 =
      FStar_Pprint.separate_map FStar_Pprint.semi p_appTerm pats  in
    FStar_Pprint.group uu____2976

and p_simpleTerm : FStar_Parser_AST.term -> FStar_Pprint.document =
  fun e  ->
    let uu____2978 =
      let uu____2979 = unparen e  in uu____2979.FStar_Parser_AST.tm  in
    match uu____2978 with
    | FStar_Parser_AST.Abs (pats,e1) ->
        let uu____2984 =
          let uu____2985 = str "fun"  in
          let uu____2986 =
            let uu____2987 =
              FStar_Pprint.separate_map break1 p_atomicPattern pats  in
            FStar_Pprint.op_Hat_Slash_Hat uu____2987 FStar_Pprint.rarrow  in
          op_Hat_Slash_Plus_Hat uu____2985 uu____2986  in
        let uu____2988 = p_term e1  in
        op_Hat_Slash_Plus_Hat uu____2984 uu____2988
    | uu____2989 -> p_tmIff e

and p_maybeFocusArrow : Prims.bool -> FStar_Pprint.document =
  fun b  -> if b then str "~>" else FStar_Pprint.rarrow

and p_patternBranch :
  (FStar_Parser_AST.pattern,FStar_Parser_AST.term
                              FStar_Pervasives_Native.option,FStar_Parser_AST.term)
    FStar_Pervasives_Native.tuple3 -> FStar_Pprint.document
  =
  fun uu____2992  ->
    match uu____2992 with
    | (pat,when_opt,e) ->
        let maybe_paren =
          let uu____3005 =
            let uu____3006 = unparen e  in uu____3006.FStar_Parser_AST.tm  in
          match uu____3005 with
          | FStar_Parser_AST.Match uu____3009 -> soft_begin_end_with_nesting
          | FStar_Parser_AST.TryWith uu____3017 ->
              soft_begin_end_with_nesting
          | FStar_Parser_AST.Abs
              ({
                 FStar_Parser_AST.pat = FStar_Parser_AST.PatVar
                   (x,uu____3026);
                 FStar_Parser_AST.prange = uu____3027;_}::[],{
                                                               FStar_Parser_AST.tm
                                                                 =
                                                                 FStar_Parser_AST.Match
                                                                 (maybe_x,uu____3029);
                                                               FStar_Parser_AST.range
                                                                 = uu____3030;
                                                               FStar_Parser_AST.level
                                                                 = uu____3031;_})
              when matches_var maybe_x x -> soft_begin_end_with_nesting
          | uu____3045 -> (fun x  -> x)  in
        let uu____3047 =
          let uu____3048 =
            let uu____3049 =
              let uu____3050 =
                let uu____3051 =
                  let uu____3052 = p_disjunctivePattern pat  in
                  let uu____3053 =
                    let uu____3054 = p_maybeWhen when_opt  in
                    FStar_Pprint.op_Hat_Hat uu____3054 FStar_Pprint.rarrow
                     in
                  op_Hat_Slash_Plus_Hat uu____3052 uu____3053  in
                FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____3051  in
              FStar_Pprint.op_Hat_Hat FStar_Pprint.bar uu____3050  in
            FStar_Pprint.group uu____3049  in
          let uu____3055 =
            let uu____3056 = p_term e  in maybe_paren uu____3056  in
          op_Hat_Slash_Plus_Hat uu____3048 uu____3055  in
        FStar_Pprint.group uu____3047

and p_maybeWhen :
  FStar_Parser_AST.term FStar_Pervasives_Native.option ->
    FStar_Pprint.document
  =
  fun uu___105_3057  ->
    match uu___105_3057 with
    | FStar_Pervasives_Native.None  -> FStar_Pprint.empty
    | FStar_Pervasives_Native.Some e ->
        let uu____3060 = str "when"  in
        let uu____3061 =
          let uu____3062 = p_tmFormula e  in
          FStar_Pprint.op_Hat_Hat uu____3062 FStar_Pprint.space  in
        op_Hat_Slash_Plus_Hat uu____3060 uu____3061

and p_tmIff : FStar_Parser_AST.term -> FStar_Pprint.document =
  fun e  ->
    let uu____3064 =
      let uu____3065 = unparen e  in uu____3065.FStar_Parser_AST.tm  in
    match uu____3064 with
    | FStar_Parser_AST.Op
        ({ FStar_Ident.idText = "<==>"; FStar_Ident.idRange = uu____3066;_},e1::e2::[])
        ->
        let uu____3070 = str "<==>"  in
        let uu____3071 = p_tmImplies e1  in
        let uu____3072 = p_tmIff e2  in
        infix0 uu____3070 uu____3071 uu____3072
    | uu____3073 -> p_tmImplies e

and p_tmImplies : FStar_Parser_AST.term -> FStar_Pprint.document =
  fun e  ->
    let uu____3075 =
      let uu____3076 = unparen e  in uu____3076.FStar_Parser_AST.tm  in
    match uu____3075 with
    | FStar_Parser_AST.Op
        ({ FStar_Ident.idText = "==>"; FStar_Ident.idRange = uu____3077;_},e1::e2::[])
        ->
        let uu____3081 = str "==>"  in
        let uu____3082 = p_tmArrow p_tmFormula e1  in
        let uu____3083 = p_tmImplies e2  in
        infix0 uu____3081 uu____3082 uu____3083
    | uu____3084 -> p_tmArrow p_tmFormula e

and p_tmArrow :
  (FStar_Parser_AST.term -> FStar_Pprint.document) ->
    FStar_Parser_AST.term -> FStar_Pprint.document
  =
  fun p_Tm  ->
    fun e  ->
      let uu____3089 =
        let uu____3090 = unparen e  in uu____3090.FStar_Parser_AST.tm  in
      match uu____3089 with
      | FStar_Parser_AST.Product (bs,tgt) ->
          let uu____3095 =
            let uu____3096 =
              FStar_Pprint.concat_map
                (fun b  ->
                   let uu____3098 = p_binder false b  in
                   let uu____3099 =
                     let uu____3100 =
                       FStar_Pprint.op_Hat_Hat FStar_Pprint.rarrow break1  in
                     FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____3100
                      in
                   FStar_Pprint.op_Hat_Hat uu____3098 uu____3099) bs
               in
            let uu____3101 = p_tmArrow p_Tm tgt  in
            FStar_Pprint.op_Hat_Hat uu____3096 uu____3101  in
          FStar_Pprint.group uu____3095
      | uu____3102 -> p_Tm e

and p_tmFormula : FStar_Parser_AST.term -> FStar_Pprint.document =
  fun e  ->
    let uu____3104 =
      let uu____3105 = unparen e  in uu____3105.FStar_Parser_AST.tm  in
    match uu____3104 with
    | FStar_Parser_AST.Op
        ({ FStar_Ident.idText = "\\/"; FStar_Ident.idRange = uu____3106;_},e1::e2::[])
        ->
        let uu____3110 = str "\\/"  in
        let uu____3111 = p_tmFormula e1  in
        let uu____3112 = p_tmConjunction e2  in
        infix0 uu____3110 uu____3111 uu____3112
    | uu____3113 -> p_tmConjunction e

and p_tmConjunction : FStar_Parser_AST.term -> FStar_Pprint.document =
  fun e  ->
    let uu____3115 =
      let uu____3116 = unparen e  in uu____3116.FStar_Parser_AST.tm  in
    match uu____3115 with
    | FStar_Parser_AST.Op
        ({ FStar_Ident.idText = "/\\"; FStar_Ident.idRange = uu____3117;_},e1::e2::[])
        ->
        let uu____3121 = str "/\\"  in
        let uu____3122 = p_tmConjunction e1  in
        let uu____3123 = p_tmTuple e2  in
        infix0 uu____3121 uu____3122 uu____3123
    | uu____3124 -> p_tmTuple e

and p_tmTuple : FStar_Parser_AST.term -> FStar_Pprint.document =
  fun e  -> with_comment p_tmTuple' e e.FStar_Parser_AST.range

and p_tmTuple' : FStar_Parser_AST.term -> FStar_Pprint.document =
  fun e  ->
    let uu____3127 =
      let uu____3128 = unparen e  in uu____3128.FStar_Parser_AST.tm  in
    match uu____3127 with
    | FStar_Parser_AST.Construct (lid,args) when is_tuple_constructor lid ->
        let uu____3137 = FStar_Pprint.op_Hat_Hat FStar_Pprint.comma break1
           in
        FStar_Pprint.separate_map uu____3137
          (fun uu____3140  ->
             match uu____3140 with | (e1,uu____3144) -> p_tmEq e1) args
    | uu____3145 -> p_tmEq e

and paren_if :
  Prims.int -> Prims.int -> FStar_Pprint.document -> FStar_Pprint.document =
  fun curr  ->
    fun mine  ->
      fun doc1  ->
        if mine <= curr
        then doc1
        else
          (let uu____3150 =
             let uu____3151 =
               FStar_Pprint.op_Hat_Hat doc1 FStar_Pprint.rparen  in
             FStar_Pprint.op_Hat_Hat FStar_Pprint.lparen uu____3151  in
           FStar_Pprint.group uu____3150)

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
      let uu____3176 =
        let uu____3177 = unparen e  in uu____3177.FStar_Parser_AST.tm  in
      match uu____3176 with
      | FStar_Parser_AST.Op (op,e1::e2::[]) when
          ((is_operatorInfix0ad12 op) || ((FStar_Ident.text_of_id op) = "="))
            || ((FStar_Ident.text_of_id op) = "|>")
          ->
          let op1 = FStar_Ident.text_of_id op  in
          let uu____3183 = levels op1  in
          (match uu____3183 with
           | (left1,mine,right1) ->
               let uu____3190 =
                 let uu____3191 = FStar_All.pipe_left str op1  in
                 let uu____3192 = p_tmEq' left1 e1  in
                 let uu____3193 = p_tmEq' right1 e2  in
                 infix0 uu____3191 uu____3192 uu____3193  in
               paren_if curr mine uu____3190)
      | FStar_Parser_AST.Op
          ({ FStar_Ident.idText = ":="; FStar_Ident.idRange = uu____3194;_},e1::e2::[])
          ->
          let uu____3198 =
            let uu____3199 = p_tmEq e1  in
            let uu____3200 =
              let uu____3201 =
                let uu____3202 =
                  let uu____3203 = p_tmEq e2  in
                  op_Hat_Slash_Plus_Hat FStar_Pprint.equals uu____3203  in
                FStar_Pprint.op_Hat_Hat FStar_Pprint.colon uu____3202  in
              FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____3201  in
            FStar_Pprint.op_Hat_Hat uu____3199 uu____3200  in
          FStar_Pprint.group uu____3198
      | FStar_Parser_AST.Op
          ({ FStar_Ident.idText = "-"; FStar_Ident.idRange = uu____3204;_},e1::[])
          ->
          let uu____3207 = levels "-"  in
          (match uu____3207 with
           | (left1,mine,right1) ->
               let uu____3214 = p_tmEq' mine e1  in
               FStar_Pprint.op_Hat_Slash_Hat FStar_Pprint.minus uu____3214)
      | uu____3215 -> p_tmNoEq e

and p_tmNoEq : FStar_Parser_AST.term -> FStar_Pprint.document =
  fun e  ->
    let n1 = max_level [colon_colon (); amp (); opinfix3 (); opinfix4 ()]  in
    p_tmNoEq' n1 e

and p_tmNoEq' : Prims.int -> FStar_Parser_AST.term -> FStar_Pprint.document =
  fun curr  ->
    fun e  ->
      let uu____3245 =
        let uu____3246 = unparen e  in uu____3246.FStar_Parser_AST.tm  in
      match uu____3245 with
      | FStar_Parser_AST.Construct (lid,(e1,uu____3249)::(e2,uu____3251)::[])
          when
          (FStar_Ident.lid_equals lid FStar_Parser_Const.cons_lid) &&
            (let uu____3261 = is_list e  in Prims.op_Negation uu____3261)
          ->
          let op = "::"  in
          let uu____3263 = levels op  in
          (match uu____3263 with
           | (left1,mine,right1) ->
               let uu____3270 =
                 let uu____3271 = str op  in
                 let uu____3272 = p_tmNoEq' left1 e1  in
                 let uu____3273 = p_tmNoEq' right1 e2  in
                 infix0 uu____3271 uu____3272 uu____3273  in
               paren_if curr mine uu____3270)
      | FStar_Parser_AST.Sum (binders,res) ->
          let op = "&"  in
          let uu____3279 = levels op  in
          (match uu____3279 with
           | (left1,mine,right1) ->
               let p_dsumfst b =
                 let uu____3290 = p_binder false b  in
                 let uu____3291 =
                   let uu____3292 =
                     let uu____3293 = str op  in
                     FStar_Pprint.op_Hat_Hat uu____3293 break1  in
                   FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____3292  in
                 FStar_Pprint.op_Hat_Hat uu____3290 uu____3291  in
               let uu____3294 =
                 let uu____3295 = FStar_Pprint.concat_map p_dsumfst binders
                    in
                 let uu____3296 = p_tmNoEq' right1 res  in
                 FStar_Pprint.op_Hat_Hat uu____3295 uu____3296  in
               paren_if curr mine uu____3294)
      | FStar_Parser_AST.Op (op,e1::e2::[]) when is_operatorInfix34 op ->
          let op1 = FStar_Ident.text_of_id op  in
          let uu____3302 = levels op1  in
          (match uu____3302 with
           | (left1,mine,right1) ->
               let uu____3309 =
                 let uu____3310 = str op1  in
                 let uu____3311 = p_tmNoEq' left1 e1  in
                 let uu____3312 = p_tmNoEq' right1 e2  in
                 infix0 uu____3310 uu____3311 uu____3312  in
               paren_if curr mine uu____3309)
      | FStar_Parser_AST.NamedTyp (lid,e1) ->
          let uu____3315 =
            let uu____3316 = p_lidentOrUnderscore lid  in
            let uu____3317 =
              let uu____3318 = p_appTerm e1  in
              FStar_Pprint.op_Hat_Slash_Hat FStar_Pprint.colon uu____3318  in
            FStar_Pprint.op_Hat_Slash_Hat uu____3316 uu____3317  in
          FStar_Pprint.group uu____3315
      | FStar_Parser_AST.Refine (b,phi) -> p_refinedBinder b phi
      | FStar_Parser_AST.Record (with_opt,record_fields) ->
          let uu____3331 =
            let uu____3332 =
              default_or_map FStar_Pprint.empty p_with_clause with_opt  in
            let uu____3333 =
              let uu____3334 =
                FStar_Pprint.op_Hat_Hat FStar_Pprint.semi break1  in
              FStar_Pprint.separate_map uu____3334 p_simpleDef record_fields
               in
            FStar_Pprint.op_Hat_Hat uu____3332 uu____3333  in
          braces_with_nesting uu____3331
      | FStar_Parser_AST.Op
          ({ FStar_Ident.idText = "~"; FStar_Ident.idRange = uu____3337;_},e1::[])
          ->
          let uu____3340 =
            let uu____3341 = str "~"  in
            let uu____3342 = p_atomicTerm e1  in
            FStar_Pprint.op_Hat_Hat uu____3341 uu____3342  in
          FStar_Pprint.group uu____3340
      | uu____3343 -> p_appTerm e

and p_with_clause : FStar_Parser_AST.term -> FStar_Pprint.document =
  fun e  ->
    let uu____3345 = p_appTerm e  in
    let uu____3346 =
      let uu____3347 =
        let uu____3348 = str "with"  in
        FStar_Pprint.op_Hat_Hat uu____3348 break1  in
      FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____3347  in
    FStar_Pprint.op_Hat_Hat uu____3345 uu____3346

and p_refinedBinder :
  FStar_Parser_AST.binder -> FStar_Parser_AST.term -> FStar_Pprint.document =
  fun b  ->
    fun phi  ->
      match b.FStar_Parser_AST.b with
      | FStar_Parser_AST.Annotated (lid,t) ->
          let uu____3353 =
            let uu____3354 = p_lident lid  in
            p_refinement b.FStar_Parser_AST.aqual uu____3354 t phi  in
          soft_parens_with_nesting uu____3353
      | FStar_Parser_AST.TAnnotated uu____3355 ->
          failwith "Is this still used ?"
      | FStar_Parser_AST.Variable uu____3358 ->
          let uu____3359 =
            let uu____3360 = FStar_Parser_AST.binder_to_string b  in
            FStar_Util.format1
              "Imposible : a refined binder ought to be annotated %s"
              uu____3360
             in
          failwith uu____3359
      | FStar_Parser_AST.TVariable uu____3361 ->
          let uu____3362 =
            let uu____3363 = FStar_Parser_AST.binder_to_string b  in
            FStar_Util.format1
              "Imposible : a refined binder ought to be annotated %s"
              uu____3363
             in
          failwith uu____3362
      | FStar_Parser_AST.NoName uu____3364 ->
          let uu____3365 =
            let uu____3366 = FStar_Parser_AST.binder_to_string b  in
            FStar_Util.format1
              "Imposible : a refined binder ought to be annotated %s"
              uu____3366
             in
          failwith uu____3365

and p_simpleDef :
  (FStar_Ident.lid,FStar_Parser_AST.term) FStar_Pervasives_Native.tuple2 ->
    FStar_Pprint.document
  =
  fun uu____3367  ->
    match uu____3367 with
    | (lid,e) ->
        let uu____3372 =
          let uu____3373 = p_qlident lid  in
          let uu____3374 =
            let uu____3375 = p_tmIff e  in
            FStar_Pprint.op_Hat_Slash_Hat FStar_Pprint.equals uu____3375  in
          FStar_Pprint.op_Hat_Slash_Hat uu____3373 uu____3374  in
        FStar_Pprint.group uu____3372

and p_appTerm : FStar_Parser_AST.term -> FStar_Pprint.document =
  fun e  ->
    let uu____3377 =
      let uu____3378 = unparen e  in uu____3378.FStar_Parser_AST.tm  in
    match uu____3377 with
    | FStar_Parser_AST.App uu____3379 when is_general_application e ->
        let uu____3383 = head_and_args e  in
        (match uu____3383 with
         | (head1,args) ->
             let uu____3397 =
               let uu____3403 = FStar_ST.read should_print_fs_typ_app  in
               if uu____3403
               then
                 let uu____3411 =
                   FStar_Util.take
                     (fun uu____3422  ->
                        match uu____3422 with
                        | (uu____3425,aq) -> aq = FStar_Parser_AST.FsTypApp)
                     args
                    in
                 match uu____3411 with
                 | (fs_typ_args,args1) ->
                     let uu____3446 =
                       let uu____3447 = p_indexingTerm head1  in
                       let uu____3448 =
                         let uu____3449 =
                           FStar_Pprint.op_Hat_Hat FStar_Pprint.comma break1
                            in
                         soft_surround_separate_map (Prims.parse_int "2")
                           (Prims.parse_int "0") FStar_Pprint.empty
                           FStar_Pprint.langle uu____3449 FStar_Pprint.rangle
                           p_fsTypArg fs_typ_args
                          in
                       FStar_Pprint.op_Hat_Hat uu____3447 uu____3448  in
                     (uu____3446, args1)
               else
                 (let uu____3456 = p_indexingTerm head1  in
                  (uu____3456, args))
                in
             (match uu____3397 with
              | (head_doc,args1) ->
                  let uu____3468 =
                    let uu____3469 =
                      FStar_Pprint.op_Hat_Hat head_doc FStar_Pprint.space  in
                    soft_surround_separate_map (Prims.parse_int "2")
                      (Prims.parse_int "0") head_doc uu____3469 break1
                      FStar_Pprint.empty p_argTerm args1
                     in
                  FStar_Pprint.group uu____3468))
    | FStar_Parser_AST.Construct (lid,args) when
        (is_general_construction e) &&
          (let uu____3480 = is_dtuple_constructor lid  in
           Prims.op_Negation uu____3480)
        ->
        (match args with
         | [] -> p_quident lid
         | arg::[] ->
             let uu____3490 =
               let uu____3491 = p_quident lid  in
               let uu____3492 = p_argTerm arg  in
               FStar_Pprint.op_Hat_Slash_Hat uu____3491 uu____3492  in
             FStar_Pprint.group uu____3490
         | hd1::tl1 ->
             let uu____3502 =
               let uu____3503 =
                 let uu____3504 =
                   let uu____3505 = p_quident lid  in
                   let uu____3506 = p_argTerm hd1  in
                   prefix2 uu____3505 uu____3506  in
                 FStar_Pprint.group uu____3504  in
               let uu____3507 =
                 let uu____3508 =
                   FStar_Pprint.separate_map break1 p_argTerm tl1  in
                 jump2 uu____3508  in
               FStar_Pprint.op_Hat_Hat uu____3503 uu____3507  in
             FStar_Pprint.group uu____3502)
    | uu____3511 -> p_indexingTerm e

and p_argTerm :
  (FStar_Parser_AST.term,FStar_Parser_AST.imp) FStar_Pervasives_Native.tuple2
    -> FStar_Pprint.document
  =
  fun arg_imp  ->
    match arg_imp with
    | (u,FStar_Parser_AST.UnivApp ) -> p_universe u
    | (e,FStar_Parser_AST.FsTypApp ) ->
        (FStar_Util.print_warning
           "Unexpected FsTypApp, output might not be formatted correctly.\n";
         (let uu____3518 = p_indexingTerm e  in
          FStar_Pprint.surround (Prims.parse_int "2") (Prims.parse_int "1")
            FStar_Pprint.langle uu____3518 FStar_Pprint.rangle))
    | (e,FStar_Parser_AST.Hash ) ->
        let uu____3520 = str "#"  in
        let uu____3521 = p_indexingTerm e  in
        FStar_Pprint.op_Hat_Hat uu____3520 uu____3521
    | (e,FStar_Parser_AST.Nothing ) -> p_indexingTerm e

and p_fsTypArg :
  (FStar_Parser_AST.term,FStar_Parser_AST.imp) FStar_Pervasives_Native.tuple2
    -> FStar_Pprint.document
  =
  fun uu____3523  ->
    match uu____3523 with | (e,uu____3527) -> p_indexingTerm e

and p_indexingTerm_aux :
  (FStar_Parser_AST.term -> FStar_Pprint.document) ->
    FStar_Parser_AST.term -> FStar_Pprint.document
  =
  fun exit1  ->
    fun e  ->
      let uu____3532 =
        let uu____3533 = unparen e  in uu____3533.FStar_Parser_AST.tm  in
      match uu____3532 with
      | FStar_Parser_AST.Op
          ({ FStar_Ident.idText = ".()"; FStar_Ident.idRange = uu____3534;_},e1::e2::[])
          ->
          let uu____3538 =
            let uu____3539 = p_indexingTerm_aux p_atomicTermNotQUident e1  in
            let uu____3540 =
              let uu____3541 =
                let uu____3542 = p_term e2  in
                soft_parens_with_nesting uu____3542  in
              FStar_Pprint.op_Hat_Hat FStar_Pprint.dot uu____3541  in
            FStar_Pprint.op_Hat_Hat uu____3539 uu____3540  in
          FStar_Pprint.group uu____3538
      | FStar_Parser_AST.Op
          ({ FStar_Ident.idText = ".[]"; FStar_Ident.idRange = uu____3543;_},e1::e2::[])
          ->
          let uu____3547 =
            let uu____3548 = p_indexingTerm_aux p_atomicTermNotQUident e1  in
            let uu____3549 =
              let uu____3550 =
                let uu____3551 = p_term e2  in
                soft_brackets_with_nesting uu____3551  in
              FStar_Pprint.op_Hat_Hat FStar_Pprint.dot uu____3550  in
            FStar_Pprint.op_Hat_Hat uu____3548 uu____3549  in
          FStar_Pprint.group uu____3547
      | uu____3552 -> exit1 e

and p_indexingTerm : FStar_Parser_AST.term -> FStar_Pprint.document =
  fun e  -> p_indexingTerm_aux p_atomicTerm e

and p_atomicTerm : FStar_Parser_AST.term -> FStar_Pprint.document =
  fun e  ->
    let uu____3555 =
      let uu____3556 = unparen e  in uu____3556.FStar_Parser_AST.tm  in
    match uu____3555 with
    | FStar_Parser_AST.LetOpen (lid,e1) ->
        let uu____3559 = p_quident lid  in
        let uu____3560 =
          let uu____3561 =
            let uu____3562 = p_term e1  in
            soft_parens_with_nesting uu____3562  in
          FStar_Pprint.op_Hat_Hat FStar_Pprint.dot uu____3561  in
        FStar_Pprint.op_Hat_Hat uu____3559 uu____3560
    | FStar_Parser_AST.Name lid -> p_quident lid
    | FStar_Parser_AST.Op (op,e1::[]) when is_general_prefix_op op ->
        let uu____3567 = str (FStar_Ident.text_of_id op)  in
        let uu____3568 = p_atomicTerm e1  in
        FStar_Pprint.op_Hat_Hat uu____3567 uu____3568
    | uu____3569 -> p_atomicTermNotQUident e

and p_atomicTermNotQUident : FStar_Parser_AST.term -> FStar_Pprint.document =
  fun e  ->
    let uu____3571 =
      let uu____3572 = unparen e  in uu____3572.FStar_Parser_AST.tm  in
    match uu____3571 with
    | FStar_Parser_AST.Wild  -> FStar_Pprint.underscore
    | FStar_Parser_AST.Var lid when
        FStar_Ident.lid_equals lid FStar_Parser_Const.assert_lid ->
        str "assert"
    | FStar_Parser_AST.Tvar tv -> p_tvar tv
    | FStar_Parser_AST.Const c ->
        (match c with
         | FStar_Const.Const_char x when x = '\n' -> str "0x0Az"
         | uu____3577 -> p_constant c)
    | FStar_Parser_AST.Name lid when
        FStar_Ident.lid_equals lid FStar_Parser_Const.true_lid -> str "True"
    | FStar_Parser_AST.Name lid when
        FStar_Ident.lid_equals lid FStar_Parser_Const.false_lid ->
        str "False"
    | FStar_Parser_AST.Op (op,e1::[]) when is_general_prefix_op op ->
        let uu____3583 = str (FStar_Ident.text_of_id op)  in
        let uu____3584 = p_atomicTermNotQUident e1  in
        FStar_Pprint.op_Hat_Hat uu____3583 uu____3584
    | FStar_Parser_AST.Op (op,[]) ->
        let uu____3587 =
          let uu____3588 =
            let uu____3589 = str (FStar_Ident.text_of_id op)  in
            let uu____3590 =
              FStar_Pprint.op_Hat_Hat FStar_Pprint.space FStar_Pprint.rparen
               in
            FStar_Pprint.op_Hat_Hat uu____3589 uu____3590  in
          FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____3588  in
        FStar_Pprint.op_Hat_Hat FStar_Pprint.lparen uu____3587
    | FStar_Parser_AST.Construct (lid,args) when is_dtuple_constructor lid ->
        let uu____3599 =
          FStar_Pprint.op_Hat_Hat FStar_Pprint.lparen FStar_Pprint.bar  in
        let uu____3600 =
          let uu____3601 = FStar_Pprint.op_Hat_Hat FStar_Pprint.comma break1
             in
          let uu____3602 = FStar_List.map FStar_Pervasives_Native.fst args
             in
          FStar_Pprint.separate_map uu____3601 p_tmEq uu____3602  in
        let uu____3606 =
          FStar_Pprint.op_Hat_Hat FStar_Pprint.bar FStar_Pprint.rparen  in
        FStar_Pprint.surround (Prims.parse_int "2") (Prims.parse_int "1")
          uu____3599 uu____3600 uu____3606
    | FStar_Parser_AST.Project (e1,lid) ->
        let uu____3609 =
          let uu____3610 = p_atomicTermNotQUident e1  in
          let uu____3611 =
            let uu____3612 = p_qlident lid  in
            FStar_Pprint.op_Hat_Hat FStar_Pprint.dot uu____3612  in
          FStar_Pprint.prefix (Prims.parse_int "2") (Prims.parse_int "0")
            uu____3610 uu____3611
           in
        FStar_Pprint.group uu____3609
    | uu____3613 -> p_projectionLHS e

and p_projectionLHS : FStar_Parser_AST.term -> FStar_Pprint.document =
  fun e  ->
    let uu____3615 =
      let uu____3616 = unparen e  in uu____3616.FStar_Parser_AST.tm  in
    match uu____3615 with
    | FStar_Parser_AST.Var lid -> p_qlident lid
    | FStar_Parser_AST.Projector (constr_lid,field_lid) ->
        let uu____3620 = p_quident constr_lid  in
        let uu____3621 =
          let uu____3622 =
            let uu____3623 = p_lident field_lid  in
            FStar_Pprint.op_Hat_Hat FStar_Pprint.dot uu____3623  in
          FStar_Pprint.op_Hat_Hat FStar_Pprint.qmark uu____3622  in
        FStar_Pprint.op_Hat_Hat uu____3620 uu____3621
    | FStar_Parser_AST.Discrim constr_lid ->
        let uu____3625 = p_quident constr_lid  in
        FStar_Pprint.op_Hat_Hat uu____3625 FStar_Pprint.qmark
    | FStar_Parser_AST.Paren e1 ->
        let uu____3627 = p_term e1  in soft_parens_with_nesting uu____3627
    | uu____3628 when is_array e ->
        let es = extract_from_list e  in
        let uu____3631 =
          FStar_Pprint.op_Hat_Hat FStar_Pprint.lbracket FStar_Pprint.bar  in
        let uu____3632 =
          let uu____3633 = FStar_Pprint.op_Hat_Hat FStar_Pprint.semi break1
             in
          separate_map_or_flow uu____3633 p_noSeqTerm es  in
        let uu____3634 =
          FStar_Pprint.op_Hat_Hat FStar_Pprint.bar FStar_Pprint.rbracket  in
        FStar_Pprint.surround (Prims.parse_int "2") (Prims.parse_int "0")
          uu____3631 uu____3632 uu____3634
    | uu____3635 when is_list e ->
        let uu____3636 =
          let uu____3637 = FStar_Pprint.op_Hat_Hat FStar_Pprint.semi break1
             in
          let uu____3638 = extract_from_list e  in
          separate_map_or_flow uu____3637 p_noSeqTerm uu____3638  in
        FStar_Pprint.surround (Prims.parse_int "2") (Prims.parse_int "0")
          FStar_Pprint.lbracket uu____3636 FStar_Pprint.rbracket
    | uu____3640 when is_lex_list e ->
        let uu____3641 =
          FStar_Pprint.op_Hat_Hat FStar_Pprint.percent FStar_Pprint.lbracket
           in
        let uu____3642 =
          let uu____3643 = FStar_Pprint.op_Hat_Hat FStar_Pprint.semi break1
             in
          let uu____3644 = extract_from_list e  in
          separate_map_or_flow uu____3643 p_noSeqTerm uu____3644  in
        FStar_Pprint.surround (Prims.parse_int "2") (Prims.parse_int "1")
          uu____3641 uu____3642 FStar_Pprint.rbracket
    | uu____3646 when is_ref_set e ->
        let es = extract_from_ref_set e  in
        let uu____3649 =
          FStar_Pprint.op_Hat_Hat FStar_Pprint.bang FStar_Pprint.lbrace  in
        let uu____3650 =
          let uu____3651 = FStar_Pprint.op_Hat_Hat FStar_Pprint.comma break1
             in
          separate_map_or_flow uu____3651 p_appTerm es  in
        FStar_Pprint.surround (Prims.parse_int "2") (Prims.parse_int "0")
          uu____3649 uu____3650 FStar_Pprint.rbrace
    | FStar_Parser_AST.Labeled (e1,s,b) ->
        let uu____3655 = str (Prims.strcat "(*" (Prims.strcat s "*)"))  in
        let uu____3656 = p_term e1  in
        FStar_Pprint.op_Hat_Slash_Hat uu____3655 uu____3656
    | FStar_Parser_AST.Op (op,args) when
        let uu____3661 = handleable_op op args  in
        Prims.op_Negation uu____3661 ->
        let uu____3662 =
          let uu____3663 =
            let uu____3664 =
              let uu____3665 =
                let uu____3666 =
                  FStar_Util.string_of_int (FStar_List.length args)  in
                Prims.strcat uu____3666
                  " arguments couldn't be handled by the pretty printer"
                 in
              Prims.strcat " with " uu____3665  in
            Prims.strcat (FStar_Ident.text_of_id op) uu____3664  in
          Prims.strcat "Operation " uu____3663  in
        failwith uu____3662
    | FStar_Parser_AST.Uvar uu____3670 ->
        failwith "Unexpected universe variable out of universe context"
    | FStar_Parser_AST.Wild  ->
        let uu____3671 = p_term e  in soft_parens_with_nesting uu____3671
    | FStar_Parser_AST.Const uu____3672 ->
        let uu____3673 = p_term e  in soft_parens_with_nesting uu____3673
    | FStar_Parser_AST.Op uu____3674 ->
        let uu____3678 = p_term e  in soft_parens_with_nesting uu____3678
    | FStar_Parser_AST.Tvar uu____3679 ->
        let uu____3680 = p_term e  in soft_parens_with_nesting uu____3680
    | FStar_Parser_AST.Var uu____3681 ->
        let uu____3682 = p_term e  in soft_parens_with_nesting uu____3682
    | FStar_Parser_AST.Name uu____3683 ->
        let uu____3684 = p_term e  in soft_parens_with_nesting uu____3684
    | FStar_Parser_AST.Construct uu____3685 ->
        let uu____3691 = p_term e  in soft_parens_with_nesting uu____3691
    | FStar_Parser_AST.Abs uu____3692 ->
        let uu____3696 = p_term e  in soft_parens_with_nesting uu____3696
    | FStar_Parser_AST.App uu____3697 ->
        let uu____3701 = p_term e  in soft_parens_with_nesting uu____3701
    | FStar_Parser_AST.Let uu____3702 ->
        let uu____3709 = p_term e  in soft_parens_with_nesting uu____3709
    | FStar_Parser_AST.LetOpen uu____3710 ->
        let uu____3713 = p_term e  in soft_parens_with_nesting uu____3713
    | FStar_Parser_AST.Seq uu____3714 ->
        let uu____3717 = p_term e  in soft_parens_with_nesting uu____3717
    | FStar_Parser_AST.Bind uu____3718 ->
        let uu____3722 = p_term e  in soft_parens_with_nesting uu____3722
    | FStar_Parser_AST.If uu____3723 ->
        let uu____3727 = p_term e  in soft_parens_with_nesting uu____3727
    | FStar_Parser_AST.Match uu____3728 ->
        let uu____3736 = p_term e  in soft_parens_with_nesting uu____3736
    | FStar_Parser_AST.TryWith uu____3737 ->
        let uu____3745 = p_term e  in soft_parens_with_nesting uu____3745
    | FStar_Parser_AST.Ascribed uu____3746 ->
        let uu____3751 = p_term e  in soft_parens_with_nesting uu____3751
    | FStar_Parser_AST.Record uu____3752 ->
        let uu____3759 = p_term e  in soft_parens_with_nesting uu____3759
    | FStar_Parser_AST.Project uu____3760 ->
        let uu____3763 = p_term e  in soft_parens_with_nesting uu____3763
    | FStar_Parser_AST.Product uu____3764 ->
        let uu____3768 = p_term e  in soft_parens_with_nesting uu____3768
    | FStar_Parser_AST.Sum uu____3769 ->
        let uu____3773 = p_term e  in soft_parens_with_nesting uu____3773
    | FStar_Parser_AST.QForall uu____3774 ->
        let uu____3781 = p_term e  in soft_parens_with_nesting uu____3781
    | FStar_Parser_AST.QExists uu____3782 ->
        let uu____3789 = p_term e  in soft_parens_with_nesting uu____3789
    | FStar_Parser_AST.Refine uu____3790 ->
        let uu____3793 = p_term e  in soft_parens_with_nesting uu____3793
    | FStar_Parser_AST.NamedTyp uu____3794 ->
        let uu____3797 = p_term e  in soft_parens_with_nesting uu____3797
    | FStar_Parser_AST.Requires uu____3798 ->
        let uu____3802 = p_term e  in soft_parens_with_nesting uu____3802
    | FStar_Parser_AST.Ensures uu____3803 ->
        let uu____3807 = p_term e  in soft_parens_with_nesting uu____3807
    | FStar_Parser_AST.Assign uu____3808 ->
        let uu____3811 = p_term e  in soft_parens_with_nesting uu____3811
    | FStar_Parser_AST.Attributes uu____3812 ->
        let uu____3814 = p_term e  in soft_parens_with_nesting uu____3814

and p_constant : FStar_Const.sconst -> FStar_Pprint.document =
  fun uu___108_3815  ->
    match uu___108_3815 with
    | FStar_Const.Const_effect  -> str "Effect"
    | FStar_Const.Const_unit  -> str "()"
    | FStar_Const.Const_bool b -> FStar_Pprint.doc_of_bool b
    | FStar_Const.Const_float x -> str (FStar_Util.string_of_float x)
    | FStar_Const.Const_char x ->
        let uu____3819 = FStar_Pprint.doc_of_char x  in
        FStar_Pprint.squotes uu____3819
    | FStar_Const.Const_string (bytes,uu____3821) ->
        let uu____3824 = str (FStar_Util.string_of_bytes bytes)  in
        FStar_Pprint.dquotes uu____3824
    | FStar_Const.Const_bytearray (bytes,uu____3826) ->
        let uu____3829 =
          let uu____3830 = str (FStar_Util.string_of_bytes bytes)  in
          FStar_Pprint.dquotes uu____3830  in
        let uu____3831 = str "B"  in
        FStar_Pprint.op_Hat_Hat uu____3829 uu____3831
    | FStar_Const.Const_int (repr,sign_width_opt) ->
        let signedness uu___106_3843 =
          match uu___106_3843 with
          | FStar_Const.Unsigned  -> str "u"
          | FStar_Const.Signed  -> FStar_Pprint.empty  in
        let width uu___107_3847 =
          match uu___107_3847 with
          | FStar_Const.Int8  -> str "y"
          | FStar_Const.Int16  -> str "s"
          | FStar_Const.Int32  -> str "l"
          | FStar_Const.Int64  -> str "L"  in
        let ending =
          default_or_map FStar_Pprint.empty
            (fun uu____3851  ->
               match uu____3851 with
               | (s,w) ->
                   let uu____3856 = signedness s  in
                   let uu____3857 = width w  in
                   FStar_Pprint.op_Hat_Hat uu____3856 uu____3857)
            sign_width_opt
           in
        let uu____3858 = str repr  in
        FStar_Pprint.op_Hat_Hat uu____3858 ending
    | FStar_Const.Const_range r ->
        let uu____3860 = FStar_Range.string_of_range r  in str uu____3860
    | FStar_Const.Const_reify  -> str "reify"
    | FStar_Const.Const_reflect lid ->
        let uu____3862 = p_quident lid  in
        let uu____3863 =
          let uu____3864 =
            let uu____3865 = str "reflect"  in
            FStar_Pprint.op_Hat_Hat FStar_Pprint.dot uu____3865  in
          FStar_Pprint.op_Hat_Hat FStar_Pprint.qmark uu____3864  in
        FStar_Pprint.op_Hat_Hat uu____3862 uu____3863

and p_universe : FStar_Parser_AST.term -> FStar_Pprint.document =
  fun u  ->
    let uu____3867 = str "u#"  in
    let uu____3868 = p_atomicUniverse u  in
    FStar_Pprint.op_Hat_Hat uu____3867 uu____3868

and p_universeFrom : FStar_Parser_AST.term -> FStar_Pprint.document =
  fun u  ->
    let uu____3870 =
      let uu____3871 = unparen u  in uu____3871.FStar_Parser_AST.tm  in
    match uu____3870 with
    | FStar_Parser_AST.Op
        ({ FStar_Ident.idText = "+"; FStar_Ident.idRange = uu____3872;_},u1::u2::[])
        ->
        let uu____3876 =
          let uu____3877 = p_universeFrom u1  in
          let uu____3878 =
            let uu____3879 = p_universeFrom u2  in
            FStar_Pprint.op_Hat_Slash_Hat FStar_Pprint.plus uu____3879  in
          FStar_Pprint.op_Hat_Slash_Hat uu____3877 uu____3878  in
        FStar_Pprint.group uu____3876
    | FStar_Parser_AST.App uu____3880 ->
        let uu____3884 = head_and_args u  in
        (match uu____3884 with
         | (head1,args) ->
             let uu____3898 =
               let uu____3899 = unparen head1  in
               uu____3899.FStar_Parser_AST.tm  in
             (match uu____3898 with
              | FStar_Parser_AST.Var maybe_max_lid when
                  FStar_Ident.lid_equals maybe_max_lid
                    FStar_Parser_Const.max_lid
                  ->
                  let uu____3901 =
                    let uu____3902 = p_qlident FStar_Parser_Const.max_lid  in
                    let uu____3903 =
                      FStar_Pprint.separate_map FStar_Pprint.space
                        (fun uu____3906  ->
                           match uu____3906 with
                           | (u1,uu____3910) -> p_atomicUniverse u1) args
                       in
                    op_Hat_Slash_Plus_Hat uu____3902 uu____3903  in
                  FStar_Pprint.group uu____3901
              | uu____3911 ->
                  let uu____3912 =
                    let uu____3913 = FStar_Parser_AST.term_to_string u  in
                    FStar_Util.format1 "Invalid term in universe context %s"
                      uu____3913
                     in
                  failwith uu____3912))
    | uu____3914 -> p_atomicUniverse u

and p_atomicUniverse : FStar_Parser_AST.term -> FStar_Pprint.document =
  fun u  ->
    let uu____3916 =
      let uu____3917 = unparen u  in uu____3917.FStar_Parser_AST.tm  in
    match uu____3916 with
    | FStar_Parser_AST.Wild  -> FStar_Pprint.underscore
    | FStar_Parser_AST.Const (FStar_Const.Const_int (r,sw)) ->
        p_constant (FStar_Const.Const_int (r, sw))
    | FStar_Parser_AST.Uvar id -> str (FStar_Ident.text_of_id id)
    | FStar_Parser_AST.Paren u1 ->
        let uu____3931 = p_universeFrom u1  in
        soft_parens_with_nesting uu____3931
    | FStar_Parser_AST.Op
        ({ FStar_Ident.idText = "+"; FStar_Ident.idRange = uu____3932;_},uu____3933::uu____3934::[])
        ->
        let uu____3936 = p_universeFrom u  in
        soft_parens_with_nesting uu____3936
    | FStar_Parser_AST.App uu____3937 ->
        let uu____3941 = p_universeFrom u  in
        soft_parens_with_nesting uu____3941
    | uu____3942 ->
        let uu____3943 =
          let uu____3944 = FStar_Parser_AST.term_to_string u  in
          FStar_Util.format1 "Invalid term in universe context %s" uu____3944
           in
        failwith uu____3943

let term_to_document : FStar_Parser_AST.term -> FStar_Pprint.document =
  fun e  -> p_term e 
let decl_to_document : FStar_Parser_AST.decl -> FStar_Pprint.document =
  fun e  -> p_decl e 
let pat_to_document : FStar_Parser_AST.pattern -> FStar_Pprint.document =
  fun p  -> p_disjunctivePattern p 
let binder_to_document : FStar_Parser_AST.binder -> FStar_Pprint.document =
  fun b  -> p_binder true b 
let modul_to_document : FStar_Parser_AST.modul -> FStar_Pprint.document =
  fun m  ->
    FStar_ST.write should_print_fs_typ_app false;
    (let res =
       match m with
       | FStar_Parser_AST.Module (uu____3964,decls) ->
           let uu____3968 =
             FStar_All.pipe_right decls (FStar_List.map decl_to_document)  in
           FStar_All.pipe_right uu____3968
             (FStar_Pprint.separate FStar_Pprint.hardline)
       | FStar_Parser_AST.Interface (uu____3973,decls,uu____3975) ->
           let uu____3978 =
             FStar_All.pipe_right decls (FStar_List.map decl_to_document)  in
           FStar_All.pipe_right uu____3978
             (FStar_Pprint.separate FStar_Pprint.hardline)
        in
     FStar_ST.write should_print_fs_typ_app false; res)
  
let comments_to_document :
  (Prims.string,FStar_Range.range) FStar_Pervasives_Native.tuple2 Prims.list
    -> FStar_Pprint.document
  =
  fun comments  ->
    FStar_Pprint.separate_map FStar_Pprint.hardline
      (fun uu____3997  ->
         match uu____3997 with | (comment,range) -> str comment) comments
  
let modul_with_comments_to_document :
  FStar_Parser_AST.modul ->
    (Prims.string,FStar_Range.range) FStar_Pervasives_Native.tuple2
      Prims.list ->
      (FStar_Pprint.document,(Prims.string,FStar_Range.range)
                               FStar_Pervasives_Native.tuple2 Prims.list)
        FStar_Pervasives_Native.tuple2
  =
  fun m  ->
    fun comments  ->
      let decls =
        match m with
        | FStar_Parser_AST.Module (uu____4022,decls) -> decls
        | FStar_Parser_AST.Interface (uu____4026,decls,uu____4028) -> decls
         in
      FStar_ST.write should_print_fs_typ_app false;
      (match decls with
       | [] -> (FStar_Pprint.empty, comments)
       | d::ds ->
           let uu____4045 =
             match ds with
             | {
                 FStar_Parser_AST.d = FStar_Parser_AST.Pragma
                   (FStar_Parser_AST.LightOff );
                 FStar_Parser_AST.drange = uu____4052;
                 FStar_Parser_AST.doc = uu____4053;
                 FStar_Parser_AST.quals = uu____4054;
                 FStar_Parser_AST.attrs = uu____4055;_}::uu____4056 ->
                 let d0 = FStar_List.hd ds  in
                 let uu____4060 =
                   let uu____4062 =
                     let uu____4064 = FStar_List.tl ds  in d :: uu____4064
                      in
                   d0 :: uu____4062  in
                 (uu____4060, (d0.FStar_Parser_AST.drange))
             | uu____4067 -> ((d :: ds), (d.FStar_Parser_AST.drange))  in
           (match uu____4045 with
            | (decls1,first_range) ->
                let extract_decl_range d1 = d1.FStar_Parser_AST.drange  in
                (FStar_ST.write comment_stack comments;
                 (let initial_comment =
                    let uu____4090 = FStar_Range.start_of_range first_range
                       in
                    place_comments_until_pos (Prims.parse_int "0")
                      (Prims.parse_int "1") uu____4090 FStar_Pprint.empty
                     in
                  let doc1 =
                    separate_map_with_comments FStar_Pprint.empty
                      FStar_Pprint.empty decl_to_document decls1
                      extract_decl_range
                     in
                  let comments1 = FStar_ST.read comment_stack  in
                  FStar_ST.write comment_stack [];
                  FStar_ST.write should_print_fs_typ_app false;
                  (let uu____4112 =
                     FStar_Pprint.op_Hat_Hat initial_comment doc1  in
                   (uu____4112, comments1))))))
  