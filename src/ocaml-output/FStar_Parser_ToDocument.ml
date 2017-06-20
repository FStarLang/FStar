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
    let uu____50 =
      let uu____51 = FStar_ST.read should_unparen  in
      Prims.op_Negation uu____51  in
    if uu____50
    then t
    else
      (match t.FStar_Parser_AST.tm with
       | FStar_Parser_AST.Paren t1 -> unparen t1
       | uu____56 -> t)
  
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
  let uu____159 =
    let uu____160 =
      let uu____161 = FStar_Pprint.op_Hat_Hat sep break1  in
      FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____161  in
    FStar_Pprint.separate_map uu____160 f l  in
  FStar_Pprint.group uu____159 
let precede_break_separate_map prec sep f l =
  let uu____196 =
    let uu____197 = FStar_Pprint.op_Hat_Hat prec FStar_Pprint.space  in
    let uu____198 =
      let uu____199 = FStar_List.hd l  in FStar_All.pipe_right uu____199 f
       in
    FStar_Pprint.precede uu____197 uu____198  in
  let uu____200 =
    let uu____201 = FStar_List.tl l  in
    FStar_Pprint.concat_map
      (fun x  ->
         let uu____204 =
           let uu____205 =
             let uu____206 = f x  in
             FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____206  in
           FStar_Pprint.op_Hat_Hat sep uu____205  in
         FStar_Pprint.op_Hat_Hat break1 uu____204) uu____201
     in
  FStar_Pprint.op_Hat_Hat uu____196 uu____200 
let concat_break_map f l =
  let uu____229 =
    FStar_Pprint.concat_map
      (fun x  ->
         let uu____231 = f x  in FStar_Pprint.op_Hat_Hat uu____231 break1) l
     in
  FStar_Pprint.group uu____229 
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
    let uu____260 = str "begin"  in
    let uu____261 = str "end"  in
    FStar_Pprint.soft_surround (Prims.parse_int "2") (Prims.parse_int "1")
      uu____260 contents uu____261
  
let separate_map_or_flow sep f l =
  if (FStar_List.length l) < (Prims.parse_int "10")
  then FStar_Pprint.separate_map sep f l
  else FStar_Pprint.flow_map sep f l 
let soft_surround_separate_map n1 b void_ opening sep closing f xs =
  if xs = []
  then void_
  else
    (let uu____357 = FStar_Pprint.separate_map sep f xs  in
     FStar_Pprint.soft_surround n1 b opening uu____357 closing)
  
let doc_of_fsdoc :
  (Prims.string * (Prims.string * Prims.string) Prims.list) ->
    FStar_Pprint.document
  =
  fun uu____366  ->
    match uu____366 with
    | (comment,keywords1) ->
        let uu____380 =
          let uu____381 =
            let uu____383 = str comment  in
            let uu____384 =
              let uu____386 =
                let uu____388 =
                  FStar_Pprint.separate_map FStar_Pprint.comma
                    (fun uu____391  ->
                       match uu____391 with
                       | (k,v1) ->
                           let uu____396 =
                             let uu____398 = str k  in
                             let uu____399 =
                               let uu____401 =
                                 let uu____403 = str v1  in [uu____403]  in
                               FStar_Pprint.rarrow :: uu____401  in
                             uu____398 :: uu____399  in
                           FStar_Pprint.concat uu____396) keywords1
                   in
                [uu____388]  in
              FStar_Pprint.space :: uu____386  in
            uu____383 :: uu____384  in
          FStar_Pprint.concat uu____381  in
        FStar_Pprint.group uu____380
  
let is_unit : FStar_Parser_AST.term -> Prims.bool =
  fun e  ->
    let uu____408 =
      let uu____409 = unparen e  in uu____409.FStar_Parser_AST.tm  in
    match uu____408 with
    | FStar_Parser_AST.Const (FStar_Const.Const_unit ) -> true
    | uu____410 -> false
  
let matches_var : FStar_Parser_AST.term -> FStar_Ident.ident -> Prims.bool =
  fun t  ->
    fun x  ->
      let uu____419 =
        let uu____420 = unparen t  in uu____420.FStar_Parser_AST.tm  in
      match uu____419 with
      | FStar_Parser_AST.Var y ->
          x.FStar_Ident.idText = (FStar_Ident.text_of_lid y)
      | uu____422 -> false
  
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
        let uu____444 =
          let uu____445 = unparen e  in uu____445.FStar_Parser_AST.tm  in
        match uu____444 with
        | FStar_Parser_AST.Construct (lid,[]) ->
            FStar_Ident.lid_equals lid nil_lid1
        | FStar_Parser_AST.Construct (lid,uu____453::(e2,uu____455)::[]) ->
            (FStar_Ident.lid_equals lid cons_lid1) && (aux e2)
        | uu____467 -> false  in
      aux
  
let is_list : FStar_Parser_AST.term -> Prims.bool =
  is_list_structure FStar_Parser_Const.cons_lid FStar_Parser_Const.nil_lid 
let is_lex_list : FStar_Parser_AST.term -> Prims.bool =
  is_list_structure FStar_Parser_Const.lexcons_lid
    FStar_Parser_Const.lextop_lid
  
let rec extract_from_list :
  FStar_Parser_AST.term -> FStar_Parser_AST.term Prims.list =
  fun e  ->
    let uu____479 =
      let uu____480 = unparen e  in uu____480.FStar_Parser_AST.tm  in
    match uu____479 with
    | FStar_Parser_AST.Construct (uu____482,[]) -> []
    | FStar_Parser_AST.Construct
        (uu____488,(e1,FStar_Parser_AST.Nothing )::(e2,FStar_Parser_AST.Nothing
                                                    )::[])
        -> let uu____500 = extract_from_list e2  in e1 :: uu____500
    | uu____502 ->
        let uu____503 =
          let uu____504 = FStar_Parser_AST.term_to_string e  in
          FStar_Util.format1 "Not a list %s" uu____504  in
        failwith uu____503
  
let is_array : FStar_Parser_AST.term -> Prims.bool =
  fun e  ->
    let uu____510 =
      let uu____511 = unparen e  in uu____511.FStar_Parser_AST.tm  in
    match uu____510 with
    | FStar_Parser_AST.App
        ({ FStar_Parser_AST.tm = FStar_Parser_AST.Var lid;
           FStar_Parser_AST.range = uu____513;
           FStar_Parser_AST.level = uu____514;_},l,FStar_Parser_AST.Nothing
         )
        ->
        (FStar_Ident.lid_equals lid FStar_Parser_Const.array_mk_array_lid) &&
          (is_list l)
    | uu____516 -> false
  
let rec is_ref_set : FStar_Parser_AST.term -> Prims.bool =
  fun e  ->
    let uu____521 =
      let uu____522 = unparen e  in uu____522.FStar_Parser_AST.tm  in
    match uu____521 with
    | FStar_Parser_AST.Var maybe_empty_lid ->
        FStar_Ident.lid_equals maybe_empty_lid FStar_Parser_Const.tset_empty
    | FStar_Parser_AST.App
        ({ FStar_Parser_AST.tm = FStar_Parser_AST.Var maybe_singleton_lid;
           FStar_Parser_AST.range = uu____525;
           FStar_Parser_AST.level = uu____526;_},{
                                                   FStar_Parser_AST.tm =
                                                     FStar_Parser_AST.App
                                                     ({
                                                        FStar_Parser_AST.tm =
                                                          FStar_Parser_AST.Var
                                                          maybe_ref_lid;
                                                        FStar_Parser_AST.range
                                                          = uu____528;
                                                        FStar_Parser_AST.level
                                                          = uu____529;_},e1,FStar_Parser_AST.Nothing
                                                      );
                                                   FStar_Parser_AST.range =
                                                     uu____531;
                                                   FStar_Parser_AST.level =
                                                     uu____532;_},FStar_Parser_AST.Nothing
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
                FStar_Parser_AST.range = uu____534;
                FStar_Parser_AST.level = uu____535;_},e1,FStar_Parser_AST.Nothing
              );
           FStar_Parser_AST.range = uu____537;
           FStar_Parser_AST.level = uu____538;_},e2,FStar_Parser_AST.Nothing
         )
        ->
        ((FStar_Ident.lid_equals maybe_union_lid
            FStar_Parser_Const.tset_union)
           && (is_ref_set e1))
          && (is_ref_set e2)
    | uu____540 -> false
  
let rec extract_from_ref_set :
  FStar_Parser_AST.term -> FStar_Parser_AST.term Prims.list =
  fun e  ->
    let uu____546 =
      let uu____547 = unparen e  in uu____547.FStar_Parser_AST.tm  in
    match uu____546 with
    | FStar_Parser_AST.Var uu____549 -> []
    | FStar_Parser_AST.App
        ({ FStar_Parser_AST.tm = FStar_Parser_AST.Var uu____550;
           FStar_Parser_AST.range = uu____551;
           FStar_Parser_AST.level = uu____552;_},{
                                                   FStar_Parser_AST.tm =
                                                     FStar_Parser_AST.App
                                                     ({
                                                        FStar_Parser_AST.tm =
                                                          FStar_Parser_AST.Var
                                                          uu____553;
                                                        FStar_Parser_AST.range
                                                          = uu____554;
                                                        FStar_Parser_AST.level
                                                          = uu____555;_},e1,FStar_Parser_AST.Nothing
                                                      );
                                                   FStar_Parser_AST.range =
                                                     uu____557;
                                                   FStar_Parser_AST.level =
                                                     uu____558;_},FStar_Parser_AST.Nothing
         )
        -> [e1]
    | FStar_Parser_AST.App
        ({
           FStar_Parser_AST.tm = FStar_Parser_AST.App
             ({ FStar_Parser_AST.tm = FStar_Parser_AST.Var uu____559;
                FStar_Parser_AST.range = uu____560;
                FStar_Parser_AST.level = uu____561;_},e1,FStar_Parser_AST.Nothing
              );
           FStar_Parser_AST.range = uu____563;
           FStar_Parser_AST.level = uu____564;_},e2,FStar_Parser_AST.Nothing
         )
        ->
        let uu____566 = extract_from_ref_set e1  in
        let uu____568 = extract_from_ref_set e2  in
        FStar_List.append uu____566 uu____568
    | uu____570 ->
        let uu____571 =
          let uu____572 = FStar_Parser_AST.term_to_string e  in
          FStar_Util.format1 "Not a ref set %s" uu____572  in
        failwith uu____571
  
let is_general_application : FStar_Parser_AST.term -> Prims.bool =
  fun e  ->
    let uu____578 = (is_array e) || (is_ref_set e)  in
    Prims.op_Negation uu____578
  
let is_general_construction : FStar_Parser_AST.term -> Prims.bool =
  fun e  ->
    let uu____583 = (is_list e) || (is_lex_list e)  in
    Prims.op_Negation uu____583
  
let is_general_prefix_op : FStar_Ident.ident -> Prims.bool =
  fun op  ->
    let op_starting_char =
      FStar_Util.char_at (FStar_Ident.text_of_id op) (Prims.parse_int "0")
       in
    ((op_starting_char = '!') || (op_starting_char = '?')) ||
      ((op_starting_char = '~') && ((FStar_Ident.text_of_id op) <> "~"))
  
let head_and_args :
  FStar_Parser_AST.term ->
    (FStar_Parser_AST.term * (FStar_Parser_AST.term * FStar_Parser_AST.imp)
      Prims.list)
  =
  fun e  ->
    let rec aux e1 acc =
      let uu____616 =
        let uu____617 = unparen e1  in uu____617.FStar_Parser_AST.tm  in
      match uu____616 with
      | FStar_Parser_AST.App (head1,arg,imp) -> aux head1 ((arg, imp) :: acc)
      | uu____628 -> (e1, acc)  in
    aux e []
  
type associativity =
  | Left 
  | Right 
  | NonAssoc 
let uu___is_Left : associativity -> Prims.bool =
  fun projectee  -> match projectee with | Left  -> true | uu____638 -> false 
let uu___is_Right : associativity -> Prims.bool =
  fun projectee  ->
    match projectee with | Right  -> true | uu____643 -> false
  
let uu___is_NonAssoc : associativity -> Prims.bool =
  fun projectee  ->
    match projectee with | NonAssoc  -> true | uu____648 -> false
  
type token = (FStar_Char.char,Prims.string) FStar_Util.either
type associativity_level = (associativity * token Prims.list)
let token_to_string :
  (FStar_BaseTypes.char,Prims.string) FStar_Util.either -> Prims.string =
  fun uu___95_659  ->
    match uu___95_659 with
    | FStar_Util.Inl c -> Prims.strcat (FStar_Util.string_of_char c) ".*"
    | FStar_Util.Inr s -> s
  
let matches_token :
  Prims.string ->
    (FStar_Char.char,Prims.string) FStar_Util.either -> Prims.bool
  =
  fun s  ->
    fun uu___96_673  ->
      match uu___96_673 with
      | FStar_Util.Inl c ->
          let uu____677 = FStar_String.get s (Prims.parse_int "0")  in
          uu____677 = c
      | FStar_Util.Inr s' -> s = s'
  
let matches_level s uu____698 =
  match uu____698 with
  | (assoc_levels,tokens) ->
      let uu____712 = FStar_List.tryFind (matches_token s) tokens  in
      uu____712 <> None
  
let opinfix4 uu____731 = (Right, [FStar_Util.Inr "**"]) 
let opinfix3 uu____747 =
  (Left, [FStar_Util.Inl '*'; FStar_Util.Inl '/'; FStar_Util.Inl '%']) 
let opinfix2 uu____767 = (Left, [FStar_Util.Inl '+'; FStar_Util.Inl '-']) 
let minus_lvl uu____785 = (Left, [FStar_Util.Inr "-"]) 
let opinfix1 uu____801 = (Right, [FStar_Util.Inl '@'; FStar_Util.Inl '^']) 
let pipe_right uu____819 = (Left, [FStar_Util.Inr "|>"]) 
let opinfix0d uu____835 = (Left, [FStar_Util.Inl '$']) 
let opinfix0c uu____851 =
  (Left, [FStar_Util.Inl '='; FStar_Util.Inl '<'; FStar_Util.Inl '>']) 
let equal uu____871 = (Left, [FStar_Util.Inr "="]) 
let opinfix0b uu____887 = (Left, [FStar_Util.Inl '&']) 
let opinfix0a uu____903 = (Left, [FStar_Util.Inl '|']) 
let colon_equals uu____919 = (NonAssoc, [FStar_Util.Inr ":="]) 
let amp uu____935 = (Right, [FStar_Util.Inr "&"]) 
let colon_colon uu____951 = (Right, [FStar_Util.Inr "::"]) 
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
  let levels_from_associativity l uu___97_1048 =
    match uu___97_1048 with
    | Left  -> (l, l, (l - (Prims.parse_int "1")))
    | Right  -> ((l - (Prims.parse_int "1")), l, l)
    | NonAssoc  -> (l, l, l)  in
  FStar_List.mapi
    (fun i  ->
       fun uu____1066  ->
         match uu____1066 with
         | (assoc1,tokens) -> ((levels_from_associativity i assoc1), tokens))
    level_associativity_spec
  
let assign_levels :
  associativity_level Prims.list ->
    Prims.string -> (Prims.int * Prims.int * Prims.int)
  =
  fun token_associativity_spec  ->
    fun s  ->
      let uu____1110 = FStar_List.tryFind (matches_level s) level_table  in
      match uu____1110 with
      | Some (assoc_levels,uu____1135) -> assoc_levels
      | uu____1156 -> failwith (Prims.strcat "Unrecognized operator " s)
  
let max : Prims.int -> Prims.int -> Prims.int =
  fun k1  -> fun k2  -> if k1 > k2 then k1 else k2 
let max_level l =
  let find_level_and_max n1 level =
    let uu____1216 =
      FStar_List.tryFind
        (fun uu____1234  ->
           match uu____1234 with
           | (uu____1243,tokens) -> tokens = (snd level)) level_table
       in
    match uu____1216 with
    | Some ((uu____1263,l1,uu____1265),uu____1266) -> max n1 l1
    | None  ->
        let uu____1292 =
          let uu____1293 =
            let uu____1294 = FStar_List.map token_to_string (snd level)  in
            FStar_String.concat "," uu____1294  in
          FStar_Util.format1 "Undefined associativity level %s" uu____1293
           in
        failwith uu____1292
     in
  FStar_List.fold_left find_level_and_max (Prims.parse_int "0") l 
let levels : Prims.string -> (Prims.int * Prims.int * Prims.int) =
  assign_levels level_associativity_spec 
let operatorInfix0ad12 uu____1321 =
  [opinfix0a ();
  opinfix0b ();
  opinfix0c ();
  opinfix0d ();
  opinfix1 ();
  opinfix2 ()] 
let is_operatorInfix0ad12 : FStar_Ident.ident -> Prims.bool =
  fun op  ->
    let uu____1361 =
      let uu____1368 =
        FStar_All.pipe_left matches_level (FStar_Ident.text_of_id op)  in
      FStar_List.tryFind uu____1368 (operatorInfix0ad12 ())  in
    uu____1361 <> None
  
let is_operatorInfix34 : FStar_Ident.ident -> Prims.bool =
  let opinfix34 = [opinfix3 (); opinfix4 ()]  in
  fun op  ->
    let uu____1425 =
      let uu____1432 =
        FStar_All.pipe_left matches_level (FStar_Ident.text_of_id op)  in
      FStar_List.tryFind uu____1432 opinfix34  in
    uu____1425 <> None
  
let handleable_args_length : FStar_Ident.ident -> Prims.int =
  fun op  ->
    let op_s = FStar_Ident.text_of_id op  in
    let uu____1468 =
      (is_general_prefix_op op) || (FStar_List.mem op_s ["-"; "~"])  in
    if uu____1468
    then (Prims.parse_int "1")
    else
      (let uu____1470 =
         ((is_operatorInfix0ad12 op) || (is_operatorInfix34 op)) ||
           (FStar_List.mem op_s
              ["<==>"; "==>"; "\\/"; "/\\"; "="; "|>"; ":="; ".()"; ".[]"])
          in
       if uu____1470
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
  | uu____1492 -> false 
let comment_stack :
  (Prims.string * FStar_Range.range) Prims.list FStar_ST.ref =
  FStar_Util.mk_ref [] 
let with_comment printer tm tmrange =
  let rec comments_before_pos acc print_pos lookahead_pos =
    let uu____1542 = FStar_ST.read comment_stack  in
    match uu____1542 with
    | [] -> (acc, false)
    | (comment,crange)::cs ->
        let uu____1563 = FStar_Range.range_before_pos crange print_pos  in
        if uu____1563
        then
          (FStar_ST.write comment_stack cs;
           (let uu____1572 =
              let uu____1573 =
                let uu____1574 = str comment  in
                FStar_Pprint.op_Hat_Hat uu____1574 FStar_Pprint.hardline  in
              FStar_Pprint.op_Hat_Hat acc uu____1573  in
            comments_before_pos uu____1572 print_pos lookahead_pos))
        else
          (let uu____1576 = FStar_Range.range_before_pos crange lookahead_pos
              in
           (acc, uu____1576))
     in
  let uu____1577 =
    let uu____1580 =
      let uu____1581 = FStar_Range.start_of_range tmrange  in
      FStar_Range.end_of_line uu____1581  in
    let uu____1582 = FStar_Range.end_of_range tmrange  in
    comments_before_pos FStar_Pprint.empty uu____1580 uu____1582  in
  match uu____1577 with
  | (comments,has_lookahead) ->
      let printed_e = printer tm  in
      let comments1 =
        if has_lookahead
        then
          let pos = FStar_Range.end_of_range tmrange  in
          let uu____1588 = comments_before_pos comments pos pos  in
          fst uu____1588
        else comments  in
      let uu____1592 = FStar_Pprint.op_Hat_Hat comments1 printed_e  in
      FStar_Pprint.group uu____1592
  
let rec place_comments_until_pos :
  Prims.int ->
    Prims.int ->
      FStar_Range.pos -> FStar_Pprint.document -> FStar_Pprint.document
  =
  fun k  ->
    fun lbegin  ->
      fun pos_end  ->
        fun doc1  ->
          let uu____1609 = FStar_ST.read comment_stack  in
          match uu____1609 with
          | (comment,crange)::cs when
              FStar_Range.range_before_pos crange pos_end ->
              (FStar_ST.write comment_stack cs;
               (let lnum =
                  let uu____1633 =
                    let uu____1634 =
                      let uu____1635 = FStar_Range.start_of_range crange  in
                      FStar_Range.line_of_pos uu____1635  in
                    uu____1634 - lbegin  in
                  max k uu____1633  in
                let doc2 =
                  let uu____1637 =
                    let uu____1638 =
                      FStar_Pprint.repeat lnum FStar_Pprint.hardline  in
                    let uu____1639 = str comment  in
                    FStar_Pprint.op_Hat_Hat uu____1638 uu____1639  in
                  FStar_Pprint.op_Hat_Hat doc1 uu____1637  in
                let uu____1640 =
                  let uu____1641 = FStar_Range.end_of_range crange  in
                  FStar_Range.line_of_pos uu____1641  in
                place_comments_until_pos (Prims.parse_int "1") uu____1640
                  pos_end doc2))
          | uu____1642 ->
              let lnum =
                let uu____1647 =
                  let uu____1648 = FStar_Range.line_of_pos pos_end  in
                  uu____1648 - lbegin  in
                max (Prims.parse_int "1") uu____1647  in
              let uu____1649 = FStar_Pprint.repeat lnum FStar_Pprint.hardline
                 in
              FStar_Pprint.op_Hat_Hat doc1 uu____1649
  
let separate_map_with_comments prefix1 sep f xs extract_range =
  let fold_fun uu____1704 x =
    match uu____1704 with
    | (last_line,doc1) ->
        let r = extract_range x  in
        let doc2 =
          let uu____1714 = FStar_Range.start_of_range r  in
          place_comments_until_pos (Prims.parse_int "1") last_line uu____1714
            doc1
           in
        let uu____1715 =
          let uu____1716 = FStar_Range.end_of_range r  in
          FStar_Range.line_of_pos uu____1716  in
        let uu____1717 =
          let uu____1718 =
            let uu____1719 = f x  in FStar_Pprint.op_Hat_Hat sep uu____1719
             in
          FStar_Pprint.op_Hat_Hat doc2 uu____1718  in
        (uu____1715, uu____1717)
     in
  let uu____1720 =
    let uu____1724 = FStar_List.hd xs  in
    let uu____1725 = FStar_List.tl xs  in (uu____1724, uu____1725)  in
  match uu____1720 with
  | (x,xs1) ->
      let init1 =
        let uu____1735 =
          let uu____1736 =
            let uu____1737 = extract_range x  in
            FStar_Range.end_of_range uu____1737  in
          FStar_Range.line_of_pos uu____1736  in
        let uu____1738 =
          let uu____1739 = f x  in FStar_Pprint.op_Hat_Hat prefix1 uu____1739
           in
        (uu____1735, uu____1738)  in
      let uu____1740 = FStar_List.fold_left fold_fun init1 xs1  in
      snd uu____1740
  
let rec p_decl : FStar_Parser_AST.decl -> FStar_Pprint.document =
  fun d  ->
    let uu____1986 =
      let uu____1987 = FStar_Pprint.optional p_fsdoc d.FStar_Parser_AST.doc
         in
      let uu____1988 =
        let uu____1989 = p_attributes d.FStar_Parser_AST.attrs  in
        let uu____1990 =
          let uu____1991 = p_qualifiers d.FStar_Parser_AST.quals  in
          let uu____1992 =
            let uu____1993 = p_rawDecl d  in
            FStar_Pprint.op_Hat_Hat
              (if d.FStar_Parser_AST.quals = []
               then FStar_Pprint.empty
               else break1) uu____1993
             in
          FStar_Pprint.op_Hat_Hat uu____1991 uu____1992  in
        FStar_Pprint.op_Hat_Hat uu____1989 uu____1990  in
      FStar_Pprint.op_Hat_Hat uu____1987 uu____1988  in
    FStar_Pprint.group uu____1986

and p_attributes : FStar_Parser_AST.attributes_ -> FStar_Pprint.document =
  fun attrs  ->
    let uu____1996 =
      let uu____1997 = str "@"  in
      FStar_Pprint.op_Hat_Hat FStar_Pprint.lbracket uu____1997  in
    let uu____1998 =
      FStar_Pprint.op_Hat_Hat FStar_Pprint.rbracket FStar_Pprint.hardline  in
    soft_surround_separate_map (Prims.parse_int "0") (Prims.parse_int "2")
      FStar_Pprint.empty uu____1996 FStar_Pprint.space uu____1998
      p_atomicTerm attrs

and p_fsdoc : FStar_Parser_AST.fsdoc -> FStar_Pprint.document =
  fun uu____1999  ->
    match uu____1999 with
    | (doc1,kwd_args) ->
        let kwd_args_doc =
          match kwd_args with
          | [] -> FStar_Pprint.empty
          | kwd_args1 ->
              let process_kwd_arg uu____2020 =
                match uu____2020 with
                | (kwd1,arg) ->
                    let uu____2025 = str "@"  in
                    let uu____2026 =
                      let uu____2027 = str kwd1  in
                      let uu____2028 =
                        let uu____2029 = str arg  in
                        FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____2029
                         in
                      FStar_Pprint.op_Hat_Hat uu____2027 uu____2028  in
                    FStar_Pprint.op_Hat_Hat uu____2025 uu____2026
                 in
              let uu____2030 =
                let uu____2031 =
                  FStar_Pprint.separate_map FStar_Pprint.hardline
                    process_kwd_arg kwd_args1
                   in
                FStar_Pprint.op_Hat_Hat uu____2031 FStar_Pprint.hardline  in
              FStar_Pprint.op_Hat_Hat FStar_Pprint.hardline uu____2030
           in
        let uu____2034 =
          let uu____2035 =
            let uu____2036 =
              let uu____2037 =
                let uu____2038 = str doc1  in
                let uu____2039 =
                  let uu____2040 =
                    let uu____2041 =
                      FStar_Pprint.op_Hat_Hat FStar_Pprint.rparen
                        FStar_Pprint.hardline
                       in
                    FStar_Pprint.op_Hat_Hat FStar_Pprint.star uu____2041  in
                  FStar_Pprint.op_Hat_Hat kwd_args_doc uu____2040  in
                FStar_Pprint.op_Hat_Hat uu____2038 uu____2039  in
              FStar_Pprint.op_Hat_Hat FStar_Pprint.star uu____2037  in
            FStar_Pprint.op_Hat_Hat FStar_Pprint.star uu____2036  in
          FStar_Pprint.op_Hat_Hat FStar_Pprint.lparen uu____2035  in
        FStar_Pprint.op_Hat_Hat FStar_Pprint.hardline uu____2034

and p_rawDecl : FStar_Parser_AST.decl -> FStar_Pprint.document =
  fun d  ->
    match d.FStar_Parser_AST.d with
    | FStar_Parser_AST.Open uid ->
        let uu____2044 =
          let uu____2045 = str "open"  in
          let uu____2046 = p_quident uid  in
          FStar_Pprint.op_Hat_Slash_Hat uu____2045 uu____2046  in
        FStar_Pprint.group uu____2044
    | FStar_Parser_AST.Include uid ->
        let uu____2048 =
          let uu____2049 = str "include"  in
          let uu____2050 = p_quident uid  in
          FStar_Pprint.op_Hat_Slash_Hat uu____2049 uu____2050  in
        FStar_Pprint.group uu____2048
    | FStar_Parser_AST.ModuleAbbrev (uid1,uid2) ->
        let uu____2053 =
          let uu____2054 = str "module"  in
          let uu____2055 =
            let uu____2056 =
              let uu____2057 = p_uident uid1  in
              let uu____2058 =
                FStar_Pprint.op_Hat_Hat FStar_Pprint.space
                  FStar_Pprint.equals
                 in
              FStar_Pprint.op_Hat_Hat uu____2057 uu____2058  in
            FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____2056  in
          FStar_Pprint.op_Hat_Hat uu____2054 uu____2055  in
        let uu____2059 = p_quident uid2  in
        op_Hat_Slash_Plus_Hat uu____2053 uu____2059
    | FStar_Parser_AST.TopLevelModule uid ->
        let uu____2061 =
          let uu____2062 = str "module"  in
          let uu____2063 =
            let uu____2064 = p_quident uid  in
            FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____2064  in
          FStar_Pprint.op_Hat_Hat uu____2062 uu____2063  in
        FStar_Pprint.group uu____2061
    | FStar_Parser_AST.Tycon
        (true ,(FStar_Parser_AST.TyconAbbrev (uid,tpars,None ,t),None )::[])
        ->
        let effect_prefix_doc =
          let uu____2083 = str "effect"  in
          let uu____2084 =
            let uu____2085 = p_uident uid  in
            FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____2085  in
          FStar_Pprint.op_Hat_Hat uu____2083 uu____2084  in
        let uu____2086 =
          let uu____2087 = p_typars tpars  in
          FStar_Pprint.surround (Prims.parse_int "2") (Prims.parse_int "1")
            effect_prefix_doc uu____2087 FStar_Pprint.equals
           in
        let uu____2088 = p_typ t  in
        op_Hat_Slash_Plus_Hat uu____2086 uu____2088
    | FStar_Parser_AST.Tycon (false ,tcdefs) ->
        let uu____2098 = str "type"  in
        let uu____2099 = str "and"  in
        precede_break_separate_map uu____2098 uu____2099 p_fsdocTypeDeclPairs
          tcdefs
    | FStar_Parser_AST.TopLevelLet (q,lbs) ->
        let let_doc =
          let uu____2112 = str "let"  in
          let uu____2113 =
            let uu____2114 = p_letqualifier q  in
            FStar_Pprint.op_Hat_Hat uu____2114 FStar_Pprint.space  in
          FStar_Pprint.op_Hat_Hat uu____2112 uu____2113  in
        let uu____2115 =
          let uu____2116 = str "and"  in
          FStar_Pprint.op_Hat_Hat uu____2116 FStar_Pprint.space  in
        separate_map_with_comments let_doc uu____2115 p_letbinding lbs
          (fun uu____2119  ->
             match uu____2119 with
             | (p,t) ->
                 FStar_Range.union_ranges p.FStar_Parser_AST.prange
                   t.FStar_Parser_AST.range)
    | FStar_Parser_AST.Val (lid,t) ->
        let uu____2126 =
          let uu____2127 = str "val"  in
          let uu____2128 =
            let uu____2129 =
              let uu____2130 = p_lident lid  in
              let uu____2131 =
                FStar_Pprint.op_Hat_Hat FStar_Pprint.space FStar_Pprint.colon
                 in
              FStar_Pprint.op_Hat_Hat uu____2130 uu____2131  in
            FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____2129  in
          FStar_Pprint.op_Hat_Hat uu____2127 uu____2128  in
        let uu____2132 = p_typ t  in
        op_Hat_Slash_Plus_Hat uu____2126 uu____2132
    | FStar_Parser_AST.Assume (id,t) ->
        let decl_keyword =
          let uu____2136 =
            let uu____2137 =
              FStar_Util.char_at id.FStar_Ident.idText (Prims.parse_int "0")
               in
            FStar_All.pipe_right uu____2137 FStar_Util.is_upper  in
          if uu____2136
          then FStar_Pprint.empty
          else
            (let uu____2139 = str "val"  in
             FStar_Pprint.op_Hat_Hat uu____2139 FStar_Pprint.space)
           in
        let uu____2140 =
          let uu____2141 =
            let uu____2142 = p_ident id  in
            let uu____2143 =
              FStar_Pprint.op_Hat_Hat FStar_Pprint.space FStar_Pprint.colon
               in
            FStar_Pprint.op_Hat_Hat uu____2142 uu____2143  in
          FStar_Pprint.op_Hat_Hat decl_keyword uu____2141  in
        let uu____2144 = p_typ t  in
        op_Hat_Slash_Plus_Hat uu____2140 uu____2144
    | FStar_Parser_AST.Exception (uid,t_opt) ->
        let uu____2149 = str "exception"  in
        let uu____2150 =
          let uu____2151 =
            let uu____2152 = p_uident uid  in
            let uu____2153 =
              FStar_Pprint.optional
                (fun t  ->
                   let uu____2155 = str "of"  in
                   let uu____2156 = p_typ t  in
                   op_Hat_Slash_Plus_Hat uu____2155 uu____2156) t_opt
               in
            FStar_Pprint.op_Hat_Hat uu____2152 uu____2153  in
          FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____2151  in
        FStar_Pprint.op_Hat_Hat uu____2149 uu____2150
    | FStar_Parser_AST.NewEffect ne ->
        let uu____2158 = str "new_effect"  in
        let uu____2159 =
          let uu____2160 = p_newEffect ne  in
          FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____2160  in
        FStar_Pprint.op_Hat_Hat uu____2158 uu____2159
    | FStar_Parser_AST.SubEffect se ->
        let uu____2162 = str "sub_effect"  in
        let uu____2163 =
          let uu____2164 = p_subEffect se  in
          FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____2164  in
        FStar_Pprint.op_Hat_Hat uu____2162 uu____2163
    | FStar_Parser_AST.Pragma p -> p_pragma p
    | FStar_Parser_AST.Fsdoc doc1 ->
        let uu____2167 = p_fsdoc doc1  in
        FStar_Pprint.op_Hat_Hat uu____2167 FStar_Pprint.hardline
    | FStar_Parser_AST.Main uu____2168 ->
        failwith "*Main declaration* : Is that really still in use ??"
    | FStar_Parser_AST.Tycon (true ,uu____2169) ->
        failwith
          "Effect abbreviation is expected to be defined by an abbreviation"

and p_pragma : FStar_Parser_AST.pragma -> FStar_Pprint.document =
  fun uu___98_2178  ->
    match uu___98_2178 with
    | FStar_Parser_AST.SetOptions s ->
        let uu____2180 = str "#set-options"  in
        let uu____2181 =
          let uu____2182 =
            let uu____2183 = str s  in FStar_Pprint.dquotes uu____2183  in
          FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____2182  in
        FStar_Pprint.op_Hat_Hat uu____2180 uu____2181
    | FStar_Parser_AST.ResetOptions s_opt ->
        let uu____2186 = str "#reset-options"  in
        let uu____2187 =
          FStar_Pprint.optional
            (fun s  ->
               let uu____2189 =
                 let uu____2190 = str s  in FStar_Pprint.dquotes uu____2190
                  in
               FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____2189) s_opt
           in
        FStar_Pprint.op_Hat_Hat uu____2186 uu____2187
    | FStar_Parser_AST.LightOff  ->
        (FStar_ST.write should_print_fs_typ_app true; str "#light \"off\"")

and p_typars : FStar_Parser_AST.binder Prims.list -> FStar_Pprint.document =
  fun bs  -> p_binders true bs

and p_fsdocTypeDeclPairs :
  (FStar_Parser_AST.tycon * FStar_Parser_AST.fsdoc option) ->
    FStar_Pprint.document
  =
  fun uu____2196  ->
    match uu____2196 with
    | (typedecl,fsdoc_opt) ->
        let uu____2204 = FStar_Pprint.optional p_fsdoc fsdoc_opt  in
        let uu____2205 = p_typeDecl typedecl  in
        FStar_Pprint.op_Hat_Hat uu____2204 uu____2205

and p_typeDecl : FStar_Parser_AST.tycon -> FStar_Pprint.document =
  fun uu___99_2206  ->
    match uu___99_2206 with
    | FStar_Parser_AST.TyconAbstract (lid,bs,typ_opt) ->
        let empty' uu____2217 = FStar_Pprint.empty  in
        p_typeDeclPrefix lid bs typ_opt empty'
    | FStar_Parser_AST.TyconAbbrev (lid,bs,typ_opt,t) ->
        let f uu____2229 =
          let uu____2230 = p_typ t  in prefix2 FStar_Pprint.equals uu____2230
           in
        p_typeDeclPrefix lid bs typ_opt f
    | FStar_Parser_AST.TyconRecord (lid,bs,typ_opt,record_field_decls) ->
        let p_recordFieldAndComments uu____2256 =
          match uu____2256 with
          | (lid1,t,doc_opt) ->
              let uu____2266 =
                FStar_Range.extend_to_end_of_line t.FStar_Parser_AST.range
                 in
              with_comment p_recordFieldDecl (lid1, t, doc_opt) uu____2266
           in
        let p_fields uu____2275 =
          let uu____2276 =
            let uu____2277 =
              let uu____2278 =
                let uu____2279 =
                  FStar_Pprint.op_Hat_Hat FStar_Pprint.semi break1  in
                FStar_Pprint.separate_map uu____2279 p_recordFieldAndComments
                  record_field_decls
                 in
              braces_with_nesting uu____2278  in
            FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____2277  in
          FStar_Pprint.op_Hat_Hat FStar_Pprint.equals uu____2276  in
        p_typeDeclPrefix lid bs typ_opt p_fields
    | FStar_Parser_AST.TyconVariant (lid,bs,typ_opt,ct_decls) ->
        let p_constructorBranchAndComments uu____2315 =
          match uu____2315 with
          | (uid,t_opt,doc_opt,use_of) ->
              let range =
                let uu____2331 =
                  let uu____2332 =
                    FStar_Util.map_opt t_opt
                      (fun t  -> t.FStar_Parser_AST.range)
                     in
                  FStar_Util.dflt uid.FStar_Ident.idRange uu____2332  in
                FStar_Range.extend_to_end_of_line uu____2331  in
              let p_constructorBranch decl =
                let uu____2351 =
                  let uu____2352 =
                    let uu____2353 = p_constructorDecl decl  in
                    FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____2353  in
                  FStar_Pprint.op_Hat_Hat FStar_Pprint.bar uu____2352  in
                FStar_Pprint.group uu____2351  in
              with_comment p_constructorBranch (uid, t_opt, doc_opt, use_of)
                range
           in
        let datacon_doc uu____2365 =
          let uu____2366 =
            FStar_Pprint.separate_map break1 p_constructorBranchAndComments
              ct_decls
             in
          FStar_Pprint.group uu____2366  in
        p_typeDeclPrefix lid bs typ_opt
          (fun uu____2373  ->
             let uu____2374 = datacon_doc ()  in
             prefix2 FStar_Pprint.equals uu____2374)

and p_typeDeclPrefix :
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
            let uu____2385 = p_ident lid  in
            let uu____2386 =
              let uu____2387 = cont ()  in
              FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____2387  in
            FStar_Pprint.op_Hat_Hat uu____2385 uu____2386
          else
            (let binders_doc =
               let uu____2390 = p_typars bs  in
               let uu____2391 =
                 FStar_Pprint.optional
                   (fun t  ->
                      let uu____2393 =
                        let uu____2394 =
                          let uu____2395 = p_typ t  in
                          FStar_Pprint.op_Hat_Hat FStar_Pprint.space
                            uu____2395
                           in
                        FStar_Pprint.op_Hat_Hat FStar_Pprint.colon uu____2394
                         in
                      FStar_Pprint.op_Hat_Hat break1 uu____2393) typ_opt
                  in
               FStar_Pprint.op_Hat_Hat uu____2390 uu____2391  in
             let uu____2396 = p_ident lid  in
             let uu____2397 = cont ()  in
             FStar_Pprint.surround (Prims.parse_int "2")
               (Prims.parse_int "1") uu____2396 binders_doc uu____2397)

and p_recordFieldDecl :
  (FStar_Ident.ident * FStar_Parser_AST.term * FStar_Parser_AST.fsdoc option)
    -> FStar_Pprint.document
  =
  fun uu____2398  ->
    match uu____2398 with
    | (lid,t,doc_opt) ->
        let uu____2408 =
          let uu____2409 = FStar_Pprint.optional p_fsdoc doc_opt  in
          let uu____2410 =
            let uu____2411 = p_lident lid  in
            let uu____2412 =
              let uu____2413 = p_typ t  in
              FStar_Pprint.op_Hat_Hat FStar_Pprint.colon uu____2413  in
            FStar_Pprint.op_Hat_Hat uu____2411 uu____2412  in
          FStar_Pprint.op_Hat_Hat uu____2409 uu____2410  in
        FStar_Pprint.group uu____2408

and p_constructorDecl :
  (FStar_Ident.ident * FStar_Parser_AST.term option * FStar_Parser_AST.fsdoc
    option * Prims.bool) -> FStar_Pprint.document
  =
  fun uu____2414  ->
    match uu____2414 with
    | (uid,t_opt,doc_opt,use_of) ->
        let sep = if use_of then str "of" else FStar_Pprint.colon  in
        let uid_doc = p_uident uid  in
        let uu____2432 = FStar_Pprint.optional p_fsdoc doc_opt  in
        let uu____2433 =
          let uu____2434 = FStar_Pprint.break_ (Prims.parse_int "0")  in
          let uu____2435 =
            default_or_map uid_doc
              (fun t  ->
                 let uu____2437 =
                   let uu____2438 =
                     FStar_Pprint.op_Hat_Hat FStar_Pprint.space sep  in
                   FStar_Pprint.op_Hat_Hat uid_doc uu____2438  in
                 let uu____2439 = p_typ t  in
                 op_Hat_Slash_Plus_Hat uu____2437 uu____2439) t_opt
             in
          FStar_Pprint.op_Hat_Hat uu____2434 uu____2435  in
        FStar_Pprint.op_Hat_Hat uu____2432 uu____2433

and p_letbinding :
  (FStar_Parser_AST.pattern * FStar_Parser_AST.term) -> FStar_Pprint.document
  =
  fun uu____2440  ->
    match uu____2440 with
    | (pat,e) ->
        let pat_doc =
          let uu____2446 =
            match pat.FStar_Parser_AST.pat with
            | FStar_Parser_AST.PatAscribed (pat1,t) ->
                let uu____2453 =
                  let uu____2454 =
                    let uu____2455 =
                      let uu____2456 =
                        let uu____2457 = p_tmArrow p_tmNoEq t  in
                        FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____2457
                         in
                      FStar_Pprint.op_Hat_Hat FStar_Pprint.colon uu____2456
                       in
                    FStar_Pprint.group uu____2455  in
                  FStar_Pprint.op_Hat_Hat break1 uu____2454  in
                (pat1, uu____2453)
            | uu____2458 -> (pat, FStar_Pprint.empty)  in
          match uu____2446 with
          | (pat1,ascr_doc) ->
              (match pat1.FStar_Parser_AST.pat with
               | FStar_Parser_AST.PatApp
                   ({
                      FStar_Parser_AST.pat = FStar_Parser_AST.PatVar
                        (x,uu____2462);
                      FStar_Parser_AST.prange = uu____2463;_},pats)
                   ->
                   let uu____2469 = p_lident x  in
                   let uu____2470 =
                     let uu____2471 =
                       FStar_Pprint.separate_map break1 p_atomicPattern pats
                        in
                     FStar_Pprint.op_Hat_Hat uu____2471 ascr_doc  in
                   FStar_Pprint.surround (Prims.parse_int "2")
                     (Prims.parse_int "1") uu____2469 uu____2470
                     FStar_Pprint.equals
               | uu____2472 ->
                   let uu____2473 =
                     let uu____2474 = p_tuplePattern pat1  in
                     let uu____2475 =
                       FStar_Pprint.op_Hat_Slash_Hat ascr_doc
                         FStar_Pprint.equals
                        in
                     FStar_Pprint.op_Hat_Hat uu____2474 uu____2475  in
                   FStar_Pprint.group uu____2473)
           in
        let uu____2476 = p_term e  in prefix2 pat_doc uu____2476

and p_newEffect : FStar_Parser_AST.effect_decl -> FStar_Pprint.document =
  fun uu___100_2477  ->
    match uu___100_2477 with
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
        let uu____2495 = p_uident uid  in
        let uu____2496 = p_binders true bs  in
        let uu____2497 =
          let uu____2498 = p_simpleTerm t  in
          prefix2 FStar_Pprint.equals uu____2498  in
        FStar_Pprint.surround (Prims.parse_int "2") (Prims.parse_int "1")
          uu____2495 uu____2496 uu____2497

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
          let uu____2505 =
            let uu____2506 =
              let uu____2507 =
                let uu____2508 = p_uident uid  in
                let uu____2509 = p_binders true bs  in
                let uu____2510 =
                  let uu____2511 = p_typ t  in
                  prefix2 FStar_Pprint.colon uu____2511  in
                FStar_Pprint.surround (Prims.parse_int "2")
                  (Prims.parse_int "1") uu____2508 uu____2509 uu____2510
                 in
              FStar_Pprint.group uu____2507  in
            let uu____2512 =
              let uu____2513 = str "with"  in
              let uu____2514 =
                separate_break_map FStar_Pprint.semi p_effectDecl eff_decls
                 in
              prefix2 uu____2513 uu____2514  in
            FStar_Pprint.op_Hat_Slash_Hat uu____2506 uu____2512  in
          braces_with_nesting uu____2505

and p_effectDecl : FStar_Parser_AST.decl -> FStar_Pprint.document =
  fun d  ->
    match d.FStar_Parser_AST.d with
    | FStar_Parser_AST.Tycon
        (false ,(FStar_Parser_AST.TyconAbbrev (lid,[],None ,e),None )::[]) ->
        let uu____2531 =
          let uu____2532 = p_lident lid  in
          let uu____2533 =
            FStar_Pprint.op_Hat_Hat FStar_Pprint.space FStar_Pprint.equals
             in
          FStar_Pprint.op_Hat_Hat uu____2532 uu____2533  in
        let uu____2534 = p_simpleTerm e  in prefix2 uu____2531 uu____2534
    | uu____2535 ->
        let uu____2536 =
          let uu____2537 = FStar_Parser_AST.decl_to_string d  in
          FStar_Util.format1
            "Not a declaration of an effect member... or at least I hope so : %s"
            uu____2537
           in
        failwith uu____2536

and p_subEffect : FStar_Parser_AST.lift -> FStar_Pprint.document =
  fun lift  ->
    let lift_op_doc =
      let lifts =
        match lift.FStar_Parser_AST.lift_op with
        | FStar_Parser_AST.NonReifiableLift t -> [("lift_wp", t)]
        | FStar_Parser_AST.ReifiableLift (t1,t2) ->
            [("lif_wp", t1); ("lift", t2)]
        | FStar_Parser_AST.LiftForFree t -> [("lift", t)]  in
      let p_lift uu____2570 =
        match uu____2570 with
        | (kwd1,t) ->
            let uu____2575 =
              let uu____2576 = str kwd1  in
              let uu____2577 =
                FStar_Pprint.op_Hat_Hat FStar_Pprint.space
                  FStar_Pprint.equals
                 in
              FStar_Pprint.op_Hat_Hat uu____2576 uu____2577  in
            let uu____2578 = p_simpleTerm t  in prefix2 uu____2575 uu____2578
         in
      separate_break_map FStar_Pprint.semi p_lift lifts  in
    let uu____2581 =
      let uu____2582 =
        let uu____2583 = p_quident lift.FStar_Parser_AST.msource  in
        let uu____2584 =
          let uu____2585 = str "~>"  in
          FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____2585  in
        FStar_Pprint.op_Hat_Hat uu____2583 uu____2584  in
      let uu____2586 = p_quident lift.FStar_Parser_AST.mdest  in
      prefix2 uu____2582 uu____2586  in
    let uu____2587 =
      let uu____2588 = braces_with_nesting lift_op_doc  in
      FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____2588  in
    FStar_Pprint.op_Hat_Hat uu____2581 uu____2587

and p_qualifier : FStar_Parser_AST.qualifier -> FStar_Pprint.document =
  fun uu___101_2589  ->
    match uu___101_2589 with
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
    let uu____2591 = FStar_Pprint.separate_map break1 p_qualifier qs  in
    FStar_Pprint.group uu____2591

and p_letqualifier : FStar_Parser_AST.let_qualifier -> FStar_Pprint.document
  =
  fun uu___102_2592  ->
    match uu___102_2592 with
    | FStar_Parser_AST.Rec  ->
        let uu____2593 = str "rec"  in
        FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____2593
    | FStar_Parser_AST.Mutable  ->
        let uu____2594 = str "mutable"  in
        FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____2594
    | FStar_Parser_AST.NoLetQualifier  -> FStar_Pprint.empty

and p_aqual : FStar_Parser_AST.arg_qualifier -> FStar_Pprint.document =
  fun uu___103_2595  ->
    match uu___103_2595 with
    | FStar_Parser_AST.Implicit  -> str "#"
    | FStar_Parser_AST.Equality  -> str "$"

and p_disjunctivePattern : FStar_Parser_AST.pattern -> FStar_Pprint.document
  =
  fun p  ->
    match p.FStar_Parser_AST.pat with
    | FStar_Parser_AST.PatOr pats ->
        let uu____2599 =
          let uu____2600 =
            let uu____2601 =
              FStar_Pprint.op_Hat_Hat FStar_Pprint.bar FStar_Pprint.space  in
            FStar_Pprint.op_Hat_Hat break1 uu____2601  in
          FStar_Pprint.separate_map uu____2600 p_tuplePattern pats  in
        FStar_Pprint.group uu____2599
    | uu____2602 -> p_tuplePattern p

and p_tuplePattern : FStar_Parser_AST.pattern -> FStar_Pprint.document =
  fun p  ->
    match p.FStar_Parser_AST.pat with
    | FStar_Parser_AST.PatTuple (pats,false ) ->
        let uu____2607 =
          let uu____2608 = FStar_Pprint.op_Hat_Hat FStar_Pprint.comma break1
             in
          FStar_Pprint.separate_map uu____2608 p_constructorPattern pats  in
        FStar_Pprint.group uu____2607
    | uu____2609 -> p_constructorPattern p

and p_constructorPattern : FStar_Parser_AST.pattern -> FStar_Pprint.document
  =
  fun p  ->
    match p.FStar_Parser_AST.pat with
    | FStar_Parser_AST.PatApp
        ({ FStar_Parser_AST.pat = FStar_Parser_AST.PatName maybe_cons_lid;
           FStar_Parser_AST.prange = uu____2612;_},hd1::tl1::[])
        when
        FStar_Ident.lid_equals maybe_cons_lid FStar_Parser_Const.cons_lid ->
        let uu____2616 =
          FStar_Pprint.op_Hat_Hat FStar_Pprint.colon FStar_Pprint.colon  in
        let uu____2617 = p_constructorPattern hd1  in
        let uu____2618 = p_constructorPattern tl1  in
        infix0 uu____2616 uu____2617 uu____2618
    | FStar_Parser_AST.PatApp
        ({ FStar_Parser_AST.pat = FStar_Parser_AST.PatName uid;
           FStar_Parser_AST.prange = uu____2620;_},pats)
        ->
        let uu____2624 = p_quident uid  in
        let uu____2625 =
          FStar_Pprint.separate_map break1 p_atomicPattern pats  in
        prefix2 uu____2624 uu____2625
    | uu____2626 -> p_atomicPattern p

and p_atomicPattern : FStar_Parser_AST.pattern -> FStar_Pprint.document =
  fun p  ->
    match p.FStar_Parser_AST.pat with
    | FStar_Parser_AST.PatAscribed (pat,t) ->
        let uu____2630 =
          let uu____2633 =
            let uu____2634 = unparen t  in uu____2634.FStar_Parser_AST.tm  in
          ((pat.FStar_Parser_AST.pat), uu____2633)  in
        (match uu____2630 with
         | (FStar_Parser_AST.PatVar (lid,aqual),FStar_Parser_AST.Refine
            ({ FStar_Parser_AST.b = FStar_Parser_AST.Annotated (lid',t1);
               FStar_Parser_AST.brange = uu____2639;
               FStar_Parser_AST.blevel = uu____2640;
               FStar_Parser_AST.aqual = uu____2641;_},phi))
             when lid.FStar_Ident.idText = lid'.FStar_Ident.idText ->
             let uu____2645 =
               let uu____2646 = p_ident lid  in
               p_refinement aqual uu____2646 t1 phi  in
             soft_parens_with_nesting uu____2645
         | (FStar_Parser_AST.PatWild ,FStar_Parser_AST.Refine
            ({ FStar_Parser_AST.b = FStar_Parser_AST.NoName t1;
               FStar_Parser_AST.brange = uu____2648;
               FStar_Parser_AST.blevel = uu____2649;
               FStar_Parser_AST.aqual = uu____2650;_},phi))
             ->
             let uu____2652 =
               p_refinement None FStar_Pprint.underscore t1 phi  in
             soft_parens_with_nesting uu____2652
         | uu____2653 ->
             let uu____2656 =
               let uu____2657 = p_tuplePattern pat  in
               let uu____2658 =
                 let uu____2659 = FStar_Pprint.break_ (Prims.parse_int "0")
                    in
                 let uu____2660 =
                   let uu____2661 = p_typ t  in
                   FStar_Pprint.op_Hat_Hat FStar_Pprint.colon uu____2661  in
                 FStar_Pprint.op_Hat_Hat uu____2659 uu____2660  in
               FStar_Pprint.op_Hat_Hat uu____2657 uu____2658  in
             soft_parens_with_nesting uu____2656)
    | FStar_Parser_AST.PatList pats ->
        let uu____2664 =
          separate_break_map FStar_Pprint.semi p_tuplePattern pats  in
        FStar_Pprint.surround (Prims.parse_int "2") (Prims.parse_int "0")
          FStar_Pprint.lbracket uu____2664 FStar_Pprint.rbracket
    | FStar_Parser_AST.PatRecord pats ->
        let p_recordFieldPat uu____2674 =
          match uu____2674 with
          | (lid,pat) ->
              let uu____2679 = p_qlident lid  in
              let uu____2680 = p_tuplePattern pat  in
              infix2 FStar_Pprint.equals uu____2679 uu____2680
           in
        let uu____2681 =
          separate_break_map FStar_Pprint.semi p_recordFieldPat pats  in
        soft_braces_with_nesting uu____2681
    | FStar_Parser_AST.PatTuple (pats,true ) ->
        let uu____2687 =
          FStar_Pprint.op_Hat_Hat FStar_Pprint.lparen FStar_Pprint.bar  in
        let uu____2688 =
          separate_break_map FStar_Pprint.comma p_constructorPattern pats  in
        let uu____2689 =
          FStar_Pprint.op_Hat_Hat FStar_Pprint.bar FStar_Pprint.rparen  in
        FStar_Pprint.surround (Prims.parse_int "2") (Prims.parse_int "1")
          uu____2687 uu____2688 uu____2689
    | FStar_Parser_AST.PatTvar (tv,arg_qualifier_opt) -> p_tvar tv
    | FStar_Parser_AST.PatOp op ->
        let uu____2696 =
          let uu____2697 =
            let uu____2698 = str (FStar_Ident.text_of_id op)  in
            let uu____2699 =
              FStar_Pprint.op_Hat_Hat FStar_Pprint.space FStar_Pprint.rparen
               in
            FStar_Pprint.op_Hat_Hat uu____2698 uu____2699  in
          FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____2697  in
        FStar_Pprint.op_Hat_Hat FStar_Pprint.lparen uu____2696
    | FStar_Parser_AST.PatWild  -> FStar_Pprint.underscore
    | FStar_Parser_AST.PatConst c -> p_constant c
    | FStar_Parser_AST.PatVar (lid,aqual) ->
        let uu____2705 = FStar_Pprint.optional p_aqual aqual  in
        let uu____2706 = p_lident lid  in
        FStar_Pprint.op_Hat_Hat uu____2705 uu____2706
    | FStar_Parser_AST.PatName uid -> p_quident uid
    | FStar_Parser_AST.PatOr uu____2708 -> failwith "Inner or pattern !"
    | FStar_Parser_AST.PatApp
        ({ FStar_Parser_AST.pat = FStar_Parser_AST.PatName uu____2710;
           FStar_Parser_AST.prange = uu____2711;_},uu____2712)
        ->
        let uu____2715 = p_tuplePattern p  in
        soft_parens_with_nesting uu____2715
    | FStar_Parser_AST.PatTuple (uu____2716,false ) ->
        let uu____2719 = p_tuplePattern p  in
        soft_parens_with_nesting uu____2719
    | uu____2720 ->
        let uu____2721 =
          let uu____2722 = FStar_Parser_AST.pat_to_string p  in
          FStar_Util.format1 "Invalid pattern %s" uu____2722  in
        failwith uu____2721

and p_binder : Prims.bool -> FStar_Parser_AST.binder -> FStar_Pprint.document
  =
  fun is_atomic  ->
    fun b  ->
      match b.FStar_Parser_AST.b with
      | FStar_Parser_AST.Variable lid ->
          let uu____2726 =
            FStar_Pprint.optional p_aqual b.FStar_Parser_AST.aqual  in
          let uu____2727 = p_lident lid  in
          FStar_Pprint.op_Hat_Hat uu____2726 uu____2727
      | FStar_Parser_AST.TVariable lid -> p_lident lid
      | FStar_Parser_AST.Annotated (lid,t) ->
          let doc1 =
            let uu____2732 =
              let uu____2733 = unparen t  in uu____2733.FStar_Parser_AST.tm
               in
            match uu____2732 with
            | FStar_Parser_AST.Refine
                ({ FStar_Parser_AST.b = FStar_Parser_AST.Annotated (lid',t1);
                   FStar_Parser_AST.brange = uu____2736;
                   FStar_Parser_AST.blevel = uu____2737;
                   FStar_Parser_AST.aqual = uu____2738;_},phi)
                when lid.FStar_Ident.idText = lid'.FStar_Ident.idText ->
                let uu____2740 = p_ident lid  in
                p_refinement b.FStar_Parser_AST.aqual uu____2740 t1 phi
            | uu____2741 ->
                let uu____2742 =
                  FStar_Pprint.optional p_aqual b.FStar_Parser_AST.aqual  in
                let uu____2743 =
                  let uu____2744 = p_lident lid  in
                  let uu____2745 =
                    let uu____2746 =
                      let uu____2747 =
                        FStar_Pprint.break_ (Prims.parse_int "0")  in
                      let uu____2748 = p_tmFormula t  in
                      FStar_Pprint.op_Hat_Hat uu____2747 uu____2748  in
                    FStar_Pprint.op_Hat_Hat FStar_Pprint.colon uu____2746  in
                  FStar_Pprint.op_Hat_Hat uu____2744 uu____2745  in
                FStar_Pprint.op_Hat_Hat uu____2742 uu____2743
             in
          if is_atomic
          then
            let uu____2749 =
              let uu____2750 =
                FStar_Pprint.op_Hat_Hat doc1 FStar_Pprint.rparen  in
              FStar_Pprint.op_Hat_Hat FStar_Pprint.lparen uu____2750  in
            FStar_Pprint.group uu____2749
          else FStar_Pprint.group doc1
      | FStar_Parser_AST.TAnnotated uu____2752 ->
          failwith "Is this still used ?"
      | FStar_Parser_AST.NoName t ->
          let uu____2756 =
            let uu____2757 = unparen t  in uu____2757.FStar_Parser_AST.tm  in
          (match uu____2756 with
           | FStar_Parser_AST.Refine
               ({ FStar_Parser_AST.b = FStar_Parser_AST.NoName t1;
                  FStar_Parser_AST.brange = uu____2759;
                  FStar_Parser_AST.blevel = uu____2760;
                  FStar_Parser_AST.aqual = uu____2761;_},phi)
               ->
               if is_atomic
               then
                 let uu____2763 =
                   let uu____2764 =
                     let uu____2765 =
                       p_refinement b.FStar_Parser_AST.aqual
                         FStar_Pprint.underscore t1 phi
                        in
                     FStar_Pprint.op_Hat_Hat uu____2765 FStar_Pprint.rparen
                      in
                   FStar_Pprint.op_Hat_Hat FStar_Pprint.lparen uu____2764  in
                 FStar_Pprint.group uu____2763
               else
                 (let uu____2767 =
                    p_refinement b.FStar_Parser_AST.aqual
                      FStar_Pprint.underscore t1 phi
                     in
                  FStar_Pprint.group uu____2767)
           | uu____2768 -> if is_atomic then p_atomicTerm t else p_appTerm t)

and p_refinement :
  FStar_Parser_AST.arg_qualifier option ->
    FStar_Pprint.document ->
      FStar_Parser_AST.term -> FStar_Parser_AST.term -> FStar_Pprint.document
  =
  fun aqual_opt  ->
    fun binder  ->
      fun t  ->
        fun phi  ->
          let uu____2775 = FStar_Pprint.optional p_aqual aqual_opt  in
          let uu____2776 =
            let uu____2777 =
              let uu____2778 =
                let uu____2779 = p_appTerm t  in
                let uu____2780 =
                  let uu____2781 = p_noSeqTerm phi  in
                  soft_braces_with_nesting uu____2781  in
                FStar_Pprint.op_Hat_Hat uu____2779 uu____2780  in
              FStar_Pprint.op_Hat_Hat FStar_Pprint.colon uu____2778  in
            FStar_Pprint.op_Hat_Hat binder uu____2777  in
          FStar_Pprint.op_Hat_Hat uu____2775 uu____2776

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
    let uu____2794 =
      let uu____2795 = unparen e  in uu____2795.FStar_Parser_AST.tm  in
    match uu____2794 with
    | FStar_Parser_AST.Seq (e1,e2) ->
        let uu____2798 =
          let uu____2799 =
            let uu____2800 = p_noSeqTerm e1  in
            FStar_Pprint.op_Hat_Hat uu____2800 FStar_Pprint.semi  in
          FStar_Pprint.group uu____2799  in
        let uu____2801 = p_term e2  in
        FStar_Pprint.op_Hat_Slash_Hat uu____2798 uu____2801
    | FStar_Parser_AST.Bind (x,e1,e2) ->
        let uu____2805 =
          let uu____2806 =
            let uu____2807 =
              let uu____2808 = p_lident x  in
              let uu____2809 =
                FStar_Pprint.op_Hat_Hat FStar_Pprint.space
                  FStar_Pprint.long_left_arrow
                 in
              FStar_Pprint.op_Hat_Hat uu____2808 uu____2809  in
            let uu____2810 =
              let uu____2811 = p_noSeqTerm e1  in
              let uu____2812 =
                FStar_Pprint.op_Hat_Hat FStar_Pprint.space FStar_Pprint.semi
                 in
              FStar_Pprint.op_Hat_Hat uu____2811 uu____2812  in
            op_Hat_Slash_Plus_Hat uu____2807 uu____2810  in
          FStar_Pprint.group uu____2806  in
        let uu____2813 = p_term e2  in
        FStar_Pprint.op_Hat_Slash_Hat uu____2805 uu____2813
    | uu____2814 ->
        let uu____2815 = p_noSeqTerm e  in FStar_Pprint.group uu____2815

and p_noSeqTerm : FStar_Parser_AST.term -> FStar_Pprint.document =
  fun e  -> with_comment p_noSeqTerm' e e.FStar_Parser_AST.range

and p_noSeqTerm' : FStar_Parser_AST.term -> FStar_Pprint.document =
  fun e  ->
    let uu____2818 =
      let uu____2819 = unparen e  in uu____2819.FStar_Parser_AST.tm  in
    match uu____2818 with
    | FStar_Parser_AST.Ascribed (e1,t,None ) ->
        let uu____2823 =
          let uu____2824 = p_tmIff e1  in
          let uu____2825 =
            let uu____2826 =
              let uu____2827 = p_typ t  in
              FStar_Pprint.op_Hat_Slash_Hat FStar_Pprint.colon uu____2827  in
            FStar_Pprint.op_Hat_Hat FStar_Pprint.langle uu____2826  in
          FStar_Pprint.op_Hat_Slash_Hat uu____2824 uu____2825  in
        FStar_Pprint.group uu____2823
    | FStar_Parser_AST.Ascribed (e1,t,Some tac) ->
        let uu____2832 =
          let uu____2833 = p_tmIff e1  in
          let uu____2834 =
            let uu____2835 =
              let uu____2836 =
                let uu____2837 = p_typ t  in
                let uu____2838 =
                  let uu____2839 = str "by"  in
                  let uu____2840 = p_typ tac  in
                  FStar_Pprint.op_Hat_Slash_Hat uu____2839 uu____2840  in
                FStar_Pprint.op_Hat_Slash_Hat uu____2837 uu____2838  in
              FStar_Pprint.op_Hat_Slash_Hat FStar_Pprint.colon uu____2836  in
            FStar_Pprint.op_Hat_Hat FStar_Pprint.langle uu____2835  in
          FStar_Pprint.op_Hat_Slash_Hat uu____2833 uu____2834  in
        FStar_Pprint.group uu____2832
    | FStar_Parser_AST.Op
        ({ FStar_Ident.idText = ".()<-"; FStar_Ident.idRange = uu____2841;_},e1::e2::e3::[])
        ->
        let uu____2846 =
          let uu____2847 =
            let uu____2848 =
              let uu____2849 = p_atomicTermNotQUident e1  in
              let uu____2850 =
                let uu____2851 =
                  let uu____2852 =
                    let uu____2853 = p_term e2  in
                    soft_parens_with_nesting uu____2853  in
                  let uu____2854 =
                    FStar_Pprint.op_Hat_Hat FStar_Pprint.space
                      FStar_Pprint.larrow
                     in
                  FStar_Pprint.op_Hat_Hat uu____2852 uu____2854  in
                FStar_Pprint.op_Hat_Hat FStar_Pprint.dot uu____2851  in
              FStar_Pprint.op_Hat_Hat uu____2849 uu____2850  in
            FStar_Pprint.group uu____2848  in
          let uu____2855 =
            let uu____2856 = p_noSeqTerm e3  in jump2 uu____2856  in
          FStar_Pprint.op_Hat_Hat uu____2847 uu____2855  in
        FStar_Pprint.group uu____2846
    | FStar_Parser_AST.Op
        ({ FStar_Ident.idText = ".[]<-"; FStar_Ident.idRange = uu____2857;_},e1::e2::e3::[])
        ->
        let uu____2862 =
          let uu____2863 =
            let uu____2864 =
              let uu____2865 = p_atomicTermNotQUident e1  in
              let uu____2866 =
                let uu____2867 =
                  let uu____2868 =
                    let uu____2869 = p_term e2  in
                    soft_brackets_with_nesting uu____2869  in
                  let uu____2870 =
                    FStar_Pprint.op_Hat_Hat FStar_Pprint.space
                      FStar_Pprint.larrow
                     in
                  FStar_Pprint.op_Hat_Hat uu____2868 uu____2870  in
                FStar_Pprint.op_Hat_Hat FStar_Pprint.dot uu____2867  in
              FStar_Pprint.op_Hat_Hat uu____2865 uu____2866  in
            FStar_Pprint.group uu____2864  in
          let uu____2871 =
            let uu____2872 = p_noSeqTerm e3  in jump2 uu____2872  in
          FStar_Pprint.op_Hat_Hat uu____2863 uu____2871  in
        FStar_Pprint.group uu____2862
    | FStar_Parser_AST.Requires (e1,wtf) ->
        let uu____2878 =
          let uu____2879 = str "requires"  in
          let uu____2880 = p_typ e1  in
          FStar_Pprint.op_Hat_Slash_Hat uu____2879 uu____2880  in
        FStar_Pprint.group uu____2878
    | FStar_Parser_AST.Ensures (e1,wtf) ->
        let uu____2886 =
          let uu____2887 = str "ensures"  in
          let uu____2888 = p_typ e1  in
          FStar_Pprint.op_Hat_Slash_Hat uu____2887 uu____2888  in
        FStar_Pprint.group uu____2886
    | FStar_Parser_AST.Attributes es ->
        let uu____2891 =
          let uu____2892 = str "attributes"  in
          let uu____2893 = FStar_Pprint.separate_map break1 p_atomicTerm es
             in
          FStar_Pprint.op_Hat_Slash_Hat uu____2892 uu____2893  in
        FStar_Pprint.group uu____2891
    | FStar_Parser_AST.If (e1,e2,e3) ->
        let uu____2897 = is_unit e3  in
        if uu____2897
        then
          let uu____2898 =
            let uu____2899 =
              let uu____2900 = str "if"  in
              let uu____2901 = p_noSeqTerm e1  in
              op_Hat_Slash_Plus_Hat uu____2900 uu____2901  in
            let uu____2902 =
              let uu____2903 = str "then"  in
              let uu____2904 = p_noSeqTerm e2  in
              op_Hat_Slash_Plus_Hat uu____2903 uu____2904  in
            FStar_Pprint.op_Hat_Slash_Hat uu____2899 uu____2902  in
          FStar_Pprint.group uu____2898
        else
          (let e2_doc =
             let uu____2907 =
               let uu____2908 = unparen e2  in uu____2908.FStar_Parser_AST.tm
                in
             match uu____2907 with
             | FStar_Parser_AST.If (uu____2909,uu____2910,e31) when
                 is_unit e31 ->
                 let uu____2912 = p_noSeqTerm e2  in
                 soft_parens_with_nesting uu____2912
             | uu____2913 -> p_noSeqTerm e2  in
           let uu____2914 =
             let uu____2915 =
               let uu____2916 = str "if"  in
               let uu____2917 = p_noSeqTerm e1  in
               op_Hat_Slash_Plus_Hat uu____2916 uu____2917  in
             let uu____2918 =
               let uu____2919 =
                 let uu____2920 = str "then"  in
                 op_Hat_Slash_Plus_Hat uu____2920 e2_doc  in
               let uu____2921 =
                 let uu____2922 = str "else"  in
                 let uu____2923 = p_noSeqTerm e3  in
                 op_Hat_Slash_Plus_Hat uu____2922 uu____2923  in
               FStar_Pprint.op_Hat_Slash_Hat uu____2919 uu____2921  in
             FStar_Pprint.op_Hat_Slash_Hat uu____2915 uu____2918  in
           FStar_Pprint.group uu____2914)
    | FStar_Parser_AST.TryWith (e1,branches) ->
        let uu____2936 =
          let uu____2937 =
            let uu____2938 = str "try"  in
            let uu____2939 = p_noSeqTerm e1  in prefix2 uu____2938 uu____2939
             in
          let uu____2940 =
            let uu____2941 = str "with"  in
            let uu____2942 =
              FStar_Pprint.separate_map FStar_Pprint.hardline p_patternBranch
                branches
               in
            FStar_Pprint.op_Hat_Slash_Hat uu____2941 uu____2942  in
          FStar_Pprint.op_Hat_Slash_Hat uu____2937 uu____2940  in
        FStar_Pprint.group uu____2936
    | FStar_Parser_AST.Match (e1,branches) ->
        let uu____2959 =
          let uu____2960 =
            let uu____2961 = str "match"  in
            let uu____2962 = p_noSeqTerm e1  in
            let uu____2963 = str "with"  in
            FStar_Pprint.surround (Prims.parse_int "2") (Prims.parse_int "1")
              uu____2961 uu____2962 uu____2963
             in
          let uu____2964 =
            FStar_Pprint.separate_map FStar_Pprint.hardline p_patternBranch
              branches
             in
          FStar_Pprint.op_Hat_Slash_Hat uu____2960 uu____2964  in
        FStar_Pprint.group uu____2959
    | FStar_Parser_AST.LetOpen (uid,e1) ->
        let uu____2971 =
          let uu____2972 =
            let uu____2973 = str "let open"  in
            let uu____2974 = p_quident uid  in
            let uu____2975 = str "in"  in
            FStar_Pprint.surround (Prims.parse_int "2") (Prims.parse_int "1")
              uu____2973 uu____2974 uu____2975
             in
          let uu____2976 = p_term e1  in
          FStar_Pprint.op_Hat_Slash_Hat uu____2972 uu____2976  in
        FStar_Pprint.group uu____2971
    | FStar_Parser_AST.Let (q,lbs,e1) ->
        let let_doc =
          let uu____2987 = str "let"  in
          let uu____2988 = p_letqualifier q  in
          FStar_Pprint.op_Hat_Hat uu____2987 uu____2988  in
        let uu____2989 =
          let uu____2990 =
            let uu____2991 =
              let uu____2992 = str "and"  in
              precede_break_separate_map let_doc uu____2992 p_letbinding lbs
               in
            let uu____2995 = str "in"  in
            FStar_Pprint.op_Hat_Slash_Hat uu____2991 uu____2995  in
          FStar_Pprint.group uu____2990  in
        let uu____2996 = p_term e1  in
        FStar_Pprint.op_Hat_Slash_Hat uu____2989 uu____2996
    | FStar_Parser_AST.Abs
        ({ FStar_Parser_AST.pat = FStar_Parser_AST.PatVar (x,typ_opt);
           FStar_Parser_AST.prange = uu____2999;_}::[],{
                                                         FStar_Parser_AST.tm
                                                           =
                                                           FStar_Parser_AST.Match
                                                           (maybe_x,branches);
                                                         FStar_Parser_AST.range
                                                           = uu____3002;
                                                         FStar_Parser_AST.level
                                                           = uu____3003;_})
        when matches_var maybe_x x ->
        let uu____3017 =
          let uu____3018 = str "function"  in
          let uu____3019 =
            FStar_Pprint.separate_map FStar_Pprint.hardline p_patternBranch
              branches
             in
          FStar_Pprint.op_Hat_Slash_Hat uu____3018 uu____3019  in
        FStar_Pprint.group uu____3017
    | FStar_Parser_AST.Assign (id,e1) ->
        let uu____3026 =
          let uu____3027 = p_lident id  in
          let uu____3028 =
            let uu____3029 = p_noSeqTerm e1  in
            FStar_Pprint.op_Hat_Slash_Hat FStar_Pprint.larrow uu____3029  in
          FStar_Pprint.op_Hat_Slash_Hat uu____3027 uu____3028  in
        FStar_Pprint.group uu____3026
    | uu____3030 -> p_typ e

and p_typ : FStar_Parser_AST.term -> FStar_Pprint.document =
  fun e  -> with_comment p_typ' e e.FStar_Parser_AST.range

and p_typ' : FStar_Parser_AST.term -> FStar_Pprint.document =
  fun e  ->
    let uu____3033 =
      let uu____3034 = unparen e  in uu____3034.FStar_Parser_AST.tm  in
    match uu____3033 with
    | FStar_Parser_AST.QForall (bs,trigger,e1) ->
        let uu____3044 =
          let uu____3045 =
            let uu____3046 = p_quantifier e  in
            FStar_Pprint.op_Hat_Hat uu____3046 FStar_Pprint.space  in
          let uu____3047 = p_binders true bs  in
          FStar_Pprint.soft_surround (Prims.parse_int "2")
            (Prims.parse_int "0") uu____3045 uu____3047 FStar_Pprint.dot
           in
        let uu____3048 =
          let uu____3049 = p_trigger trigger  in
          let uu____3050 = p_noSeqTerm e1  in
          FStar_Pprint.op_Hat_Hat uu____3049 uu____3050  in
        prefix2 uu____3044 uu____3048
    | FStar_Parser_AST.QExists (bs,trigger,e1) ->
        let uu____3060 =
          let uu____3061 =
            let uu____3062 = p_quantifier e  in
            FStar_Pprint.op_Hat_Hat uu____3062 FStar_Pprint.space  in
          let uu____3063 = p_binders true bs  in
          FStar_Pprint.soft_surround (Prims.parse_int "2")
            (Prims.parse_int "0") uu____3061 uu____3063 FStar_Pprint.dot
           in
        let uu____3064 =
          let uu____3065 = p_trigger trigger  in
          let uu____3066 = p_noSeqTerm e1  in
          FStar_Pprint.op_Hat_Hat uu____3065 uu____3066  in
        prefix2 uu____3060 uu____3064
    | uu____3067 -> p_simpleTerm e

and p_quantifier : FStar_Parser_AST.term -> FStar_Pprint.document =
  fun e  ->
    let uu____3069 =
      let uu____3070 = unparen e  in uu____3070.FStar_Parser_AST.tm  in
    match uu____3069 with
    | FStar_Parser_AST.QForall uu____3071 -> str "forall"
    | FStar_Parser_AST.QExists uu____3078 -> str "exists"
    | uu____3085 ->
        failwith "Imposible : p_quantifier called on a non-quantifier term"

and p_trigger :
  FStar_Parser_AST.term Prims.list Prims.list -> FStar_Pprint.document =
  fun uu___104_3086  ->
    match uu___104_3086 with
    | [] -> FStar_Pprint.empty
    | pats ->
        let uu____3093 =
          let uu____3094 =
            let uu____3095 = str "pattern"  in
            let uu____3096 =
              let uu____3097 =
                let uu____3098 = p_disjunctivePats pats  in jump2 uu____3098
                 in
              let uu____3099 =
                FStar_Pprint.op_Hat_Hat FStar_Pprint.rbrace break1  in
              FStar_Pprint.op_Hat_Slash_Hat uu____3097 uu____3099  in
            FStar_Pprint.op_Hat_Slash_Hat uu____3095 uu____3096  in
          FStar_Pprint.op_Hat_Hat FStar_Pprint.colon uu____3094  in
        FStar_Pprint.op_Hat_Hat FStar_Pprint.lbrace uu____3093

and p_disjunctivePats :
  FStar_Parser_AST.term Prims.list Prims.list -> FStar_Pprint.document =
  fun pats  ->
    let uu____3103 = str "\\/"  in
    FStar_Pprint.separate_map uu____3103 p_conjunctivePats pats

and p_conjunctivePats :
  FStar_Parser_AST.term Prims.list -> FStar_Pprint.document =
  fun pats  ->
    let uu____3107 =
      FStar_Pprint.separate_map FStar_Pprint.semi p_appTerm pats  in
    FStar_Pprint.group uu____3107

and p_simpleTerm : FStar_Parser_AST.term -> FStar_Pprint.document =
  fun e  ->
    let uu____3109 =
      let uu____3110 = unparen e  in uu____3110.FStar_Parser_AST.tm  in
    match uu____3109 with
    | FStar_Parser_AST.Abs (pats,e1) ->
        let uu____3115 =
          let uu____3116 = str "fun"  in
          let uu____3117 =
            let uu____3118 =
              FStar_Pprint.separate_map break1 p_atomicPattern pats  in
            FStar_Pprint.op_Hat_Slash_Hat uu____3118 FStar_Pprint.rarrow  in
          op_Hat_Slash_Plus_Hat uu____3116 uu____3117  in
        let uu____3119 = p_term e1  in
        op_Hat_Slash_Plus_Hat uu____3115 uu____3119
    | uu____3120 -> p_tmIff e

and p_maybeFocusArrow : Prims.bool -> FStar_Pprint.document =
  fun b  -> if b then str "~>" else FStar_Pprint.rarrow

and p_patternBranch :
  (FStar_Parser_AST.pattern * FStar_Parser_AST.term option *
    FStar_Parser_AST.term) -> FStar_Pprint.document
  =
  fun uu____3123  ->
    match uu____3123 with
    | (pat,when_opt,e) ->
        let maybe_paren =
          let uu____3136 =
            let uu____3137 = unparen e  in uu____3137.FStar_Parser_AST.tm  in
          match uu____3136 with
          | FStar_Parser_AST.Match uu____3140 -> soft_begin_end_with_nesting
          | FStar_Parser_AST.TryWith uu____3148 ->
              soft_begin_end_with_nesting
          | FStar_Parser_AST.Abs
              ({
                 FStar_Parser_AST.pat = FStar_Parser_AST.PatVar
                   (x,uu____3157);
                 FStar_Parser_AST.prange = uu____3158;_}::[],{
                                                               FStar_Parser_AST.tm
                                                                 =
                                                                 FStar_Parser_AST.Match
                                                                 (maybe_x,uu____3160);
                                                               FStar_Parser_AST.range
                                                                 = uu____3161;
                                                               FStar_Parser_AST.level
                                                                 = uu____3162;_})
              when matches_var maybe_x x -> soft_begin_end_with_nesting
          | uu____3176 -> (fun x  -> x)  in
        let uu____3178 =
          let uu____3179 =
            let uu____3180 =
              let uu____3181 =
                let uu____3182 =
                  let uu____3183 = p_disjunctivePattern pat  in
                  let uu____3184 =
                    let uu____3185 = p_maybeWhen when_opt  in
                    FStar_Pprint.op_Hat_Hat uu____3185 FStar_Pprint.rarrow
                     in
                  op_Hat_Slash_Plus_Hat uu____3183 uu____3184  in
                FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____3182  in
              FStar_Pprint.op_Hat_Hat FStar_Pprint.bar uu____3181  in
            FStar_Pprint.group uu____3180  in
          let uu____3186 =
            let uu____3187 = p_term e  in maybe_paren uu____3187  in
          op_Hat_Slash_Plus_Hat uu____3179 uu____3186  in
        FStar_Pprint.group uu____3178

and p_maybeWhen : FStar_Parser_AST.term option -> FStar_Pprint.document =
  fun uu___105_3188  ->
    match uu___105_3188 with
    | None  -> FStar_Pprint.empty
    | Some e ->
        let uu____3191 = str "when"  in
        let uu____3192 =
          let uu____3193 = p_tmFormula e  in
          FStar_Pprint.op_Hat_Hat uu____3193 FStar_Pprint.space  in
        op_Hat_Slash_Plus_Hat uu____3191 uu____3192

and p_tmIff : FStar_Parser_AST.term -> FStar_Pprint.document =
  fun e  ->
    let uu____3195 =
      let uu____3196 = unparen e  in uu____3196.FStar_Parser_AST.tm  in
    match uu____3195 with
    | FStar_Parser_AST.Op
        ({ FStar_Ident.idText = "<==>"; FStar_Ident.idRange = uu____3197;_},e1::e2::[])
        ->
        let uu____3201 = str "<==>"  in
        let uu____3202 = p_tmImplies e1  in
        let uu____3203 = p_tmIff e2  in
        infix0 uu____3201 uu____3202 uu____3203
    | uu____3204 -> p_tmImplies e

and p_tmImplies : FStar_Parser_AST.term -> FStar_Pprint.document =
  fun e  ->
    let uu____3206 =
      let uu____3207 = unparen e  in uu____3207.FStar_Parser_AST.tm  in
    match uu____3206 with
    | FStar_Parser_AST.Op
        ({ FStar_Ident.idText = "==>"; FStar_Ident.idRange = uu____3208;_},e1::e2::[])
        ->
        let uu____3212 = str "==>"  in
        let uu____3213 = p_tmArrow p_tmFormula e1  in
        let uu____3214 = p_tmImplies e2  in
        infix0 uu____3212 uu____3213 uu____3214
    | uu____3215 -> p_tmArrow p_tmFormula e

and p_tmArrow :
  (FStar_Parser_AST.term -> FStar_Pprint.document) ->
    FStar_Parser_AST.term -> FStar_Pprint.document
  =
  fun p_Tm  ->
    fun e  ->
      let uu____3220 =
        let uu____3221 = unparen e  in uu____3221.FStar_Parser_AST.tm  in
      match uu____3220 with
      | FStar_Parser_AST.Product (bs,tgt) ->
          let uu____3226 =
            let uu____3227 =
              FStar_Pprint.concat_map
                (fun b  ->
                   let uu____3229 = p_binder false b  in
                   let uu____3230 =
                     let uu____3231 =
                       FStar_Pprint.op_Hat_Hat FStar_Pprint.rarrow break1  in
                     FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____3231
                      in
                   FStar_Pprint.op_Hat_Hat uu____3229 uu____3230) bs
               in
            let uu____3232 = p_tmArrow p_Tm tgt  in
            FStar_Pprint.op_Hat_Hat uu____3227 uu____3232  in
          FStar_Pprint.group uu____3226
      | uu____3233 -> p_Tm e

and p_tmFormula : FStar_Parser_AST.term -> FStar_Pprint.document =
  fun e  ->
    let uu____3235 =
      let uu____3236 = unparen e  in uu____3236.FStar_Parser_AST.tm  in
    match uu____3235 with
    | FStar_Parser_AST.Op
        ({ FStar_Ident.idText = "\\/"; FStar_Ident.idRange = uu____3237;_},e1::e2::[])
        ->
        let uu____3241 = str "\\/"  in
        let uu____3242 = p_tmFormula e1  in
        let uu____3243 = p_tmConjunction e2  in
        infix0 uu____3241 uu____3242 uu____3243
    | uu____3244 -> p_tmConjunction e

and p_tmConjunction : FStar_Parser_AST.term -> FStar_Pprint.document =
  fun e  ->
    let uu____3246 =
      let uu____3247 = unparen e  in uu____3247.FStar_Parser_AST.tm  in
    match uu____3246 with
    | FStar_Parser_AST.Op
        ({ FStar_Ident.idText = "/\\"; FStar_Ident.idRange = uu____3248;_},e1::e2::[])
        ->
        let uu____3252 = str "/\\"  in
        let uu____3253 = p_tmConjunction e1  in
        let uu____3254 = p_tmTuple e2  in
        infix0 uu____3252 uu____3253 uu____3254
    | uu____3255 -> p_tmTuple e

and p_tmTuple : FStar_Parser_AST.term -> FStar_Pprint.document =
  fun e  -> with_comment p_tmTuple' e e.FStar_Parser_AST.range

and p_tmTuple' : FStar_Parser_AST.term -> FStar_Pprint.document =
  fun e  ->
    let uu____3258 =
      let uu____3259 = unparen e  in uu____3259.FStar_Parser_AST.tm  in
    match uu____3258 with
    | FStar_Parser_AST.Construct (lid,args) when is_tuple_constructor lid ->
        let uu____3268 = FStar_Pprint.op_Hat_Hat FStar_Pprint.comma break1
           in
        FStar_Pprint.separate_map uu____3268
          (fun uu____3271  ->
             match uu____3271 with | (e1,uu____3275) -> p_tmEq e1) args
    | uu____3276 -> p_tmEq e

and paren_if :
  Prims.int -> Prims.int -> FStar_Pprint.document -> FStar_Pprint.document =
  fun curr  ->
    fun mine  ->
      fun doc1  ->
        if mine <= curr
        then doc1
        else
          (let uu____3281 =
             let uu____3282 =
               FStar_Pprint.op_Hat_Hat doc1 FStar_Pprint.rparen  in
             FStar_Pprint.op_Hat_Hat FStar_Pprint.lparen uu____3282  in
           FStar_Pprint.group uu____3281)

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
      let uu____3307 =
        let uu____3308 = unparen e  in uu____3308.FStar_Parser_AST.tm  in
      match uu____3307 with
      | FStar_Parser_AST.Op (op,e1::e2::[]) when
          ((is_operatorInfix0ad12 op) || ((FStar_Ident.text_of_id op) = "="))
            || ((FStar_Ident.text_of_id op) = "|>")
          ->
          let op1 = FStar_Ident.text_of_id op  in
          let uu____3314 = levels op1  in
          (match uu____3314 with
           | (left1,mine,right1) ->
               let uu____3321 =
                 let uu____3322 = FStar_All.pipe_left str op1  in
                 let uu____3323 = p_tmEq' left1 e1  in
                 let uu____3324 = p_tmEq' right1 e2  in
                 infix0 uu____3322 uu____3323 uu____3324  in
               paren_if curr mine uu____3321)
      | FStar_Parser_AST.Op
          ({ FStar_Ident.idText = ":="; FStar_Ident.idRange = uu____3325;_},e1::e2::[])
          ->
          let uu____3329 =
            let uu____3330 = p_tmEq e1  in
            let uu____3331 =
              let uu____3332 =
                let uu____3333 =
                  let uu____3334 = p_tmEq e2  in
                  op_Hat_Slash_Plus_Hat FStar_Pprint.equals uu____3334  in
                FStar_Pprint.op_Hat_Hat FStar_Pprint.colon uu____3333  in
              FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____3332  in
            FStar_Pprint.op_Hat_Hat uu____3330 uu____3331  in
          FStar_Pprint.group uu____3329
      | FStar_Parser_AST.Op
          ({ FStar_Ident.idText = "-"; FStar_Ident.idRange = uu____3335;_},e1::[])
          ->
          let uu____3338 = levels "-"  in
          (match uu____3338 with
           | (left1,mine,right1) ->
               let uu____3345 = p_tmEq' mine e1  in
               FStar_Pprint.op_Hat_Slash_Hat FStar_Pprint.minus uu____3345)
      | uu____3346 -> p_tmNoEq e

and p_tmNoEq : FStar_Parser_AST.term -> FStar_Pprint.document =
  fun e  ->
    let n1 = max_level [colon_colon (); amp (); opinfix3 (); opinfix4 ()]  in
    p_tmNoEq' n1 e

and p_tmNoEq' : Prims.int -> FStar_Parser_AST.term -> FStar_Pprint.document =
  fun curr  ->
    fun e  ->
      let uu____3376 =
        let uu____3377 = unparen e  in uu____3377.FStar_Parser_AST.tm  in
      match uu____3376 with
      | FStar_Parser_AST.Construct (lid,(e1,uu____3380)::(e2,uu____3382)::[])
          when
          (FStar_Ident.lid_equals lid FStar_Parser_Const.cons_lid) &&
            (let uu____3392 = is_list e  in Prims.op_Negation uu____3392)
          ->
          let op = "::"  in
          let uu____3394 = levels op  in
          (match uu____3394 with
           | (left1,mine,right1) ->
               let uu____3401 =
                 let uu____3402 = str op  in
                 let uu____3403 = p_tmNoEq' left1 e1  in
                 let uu____3404 = p_tmNoEq' right1 e2  in
                 infix0 uu____3402 uu____3403 uu____3404  in
               paren_if curr mine uu____3401)
      | FStar_Parser_AST.Sum (binders,res) ->
          let op = "&"  in
          let uu____3410 = levels op  in
          (match uu____3410 with
           | (left1,mine,right1) ->
               let p_dsumfst b =
                 let uu____3421 = p_binder false b  in
                 let uu____3422 =
                   let uu____3423 =
                     let uu____3424 = str op  in
                     FStar_Pprint.op_Hat_Hat uu____3424 break1  in
                   FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____3423  in
                 FStar_Pprint.op_Hat_Hat uu____3421 uu____3422  in
               let uu____3425 =
                 let uu____3426 = FStar_Pprint.concat_map p_dsumfst binders
                    in
                 let uu____3427 = p_tmNoEq' right1 res  in
                 FStar_Pprint.op_Hat_Hat uu____3426 uu____3427  in
               paren_if curr mine uu____3425)
      | FStar_Parser_AST.Op (op,e1::e2::[]) when is_operatorInfix34 op ->
          let op1 = FStar_Ident.text_of_id op  in
          let uu____3433 = levels op1  in
          (match uu____3433 with
           | (left1,mine,right1) ->
               let uu____3440 =
                 let uu____3441 = str op1  in
                 let uu____3442 = p_tmNoEq' left1 e1  in
                 let uu____3443 = p_tmNoEq' right1 e2  in
                 infix0 uu____3441 uu____3442 uu____3443  in
               paren_if curr mine uu____3440)
      | FStar_Parser_AST.NamedTyp (lid,e1) ->
          let uu____3446 =
            let uu____3447 = p_lidentOrUnderscore lid  in
            let uu____3448 =
              let uu____3449 = p_appTerm e1  in
              FStar_Pprint.op_Hat_Slash_Hat FStar_Pprint.colon uu____3449  in
            FStar_Pprint.op_Hat_Slash_Hat uu____3447 uu____3448  in
          FStar_Pprint.group uu____3446
      | FStar_Parser_AST.Refine (b,phi) -> p_refinedBinder b phi
      | FStar_Parser_AST.Record (with_opt,record_fields) ->
          let uu____3462 =
            let uu____3463 =
              default_or_map FStar_Pprint.empty p_with_clause with_opt  in
            let uu____3464 =
              let uu____3465 =
                FStar_Pprint.op_Hat_Hat FStar_Pprint.semi break1  in
              FStar_Pprint.separate_map uu____3465 p_simpleDef record_fields
               in
            FStar_Pprint.op_Hat_Hat uu____3463 uu____3464  in
          braces_with_nesting uu____3462
      | FStar_Parser_AST.Op
          ({ FStar_Ident.idText = "~"; FStar_Ident.idRange = uu____3468;_},e1::[])
          ->
          let uu____3471 =
            let uu____3472 = str "~"  in
            let uu____3473 = p_atomicTerm e1  in
            FStar_Pprint.op_Hat_Hat uu____3472 uu____3473  in
          FStar_Pprint.group uu____3471
      | uu____3474 -> p_appTerm e

and p_with_clause : FStar_Parser_AST.term -> FStar_Pprint.document =
  fun e  ->
    let uu____3476 = p_appTerm e  in
    let uu____3477 =
      let uu____3478 =
        let uu____3479 = str "with"  in
        FStar_Pprint.op_Hat_Hat uu____3479 break1  in
      FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____3478  in
    FStar_Pprint.op_Hat_Hat uu____3476 uu____3477

and p_refinedBinder :
  FStar_Parser_AST.binder -> FStar_Parser_AST.term -> FStar_Pprint.document =
  fun b  ->
    fun phi  ->
      match b.FStar_Parser_AST.b with
      | FStar_Parser_AST.Annotated (lid,t) ->
          let uu____3484 =
            let uu____3485 = p_lident lid  in
            p_refinement b.FStar_Parser_AST.aqual uu____3485 t phi  in
          soft_parens_with_nesting uu____3484
      | FStar_Parser_AST.TAnnotated uu____3486 ->
          failwith "Is this still used ?"
      | FStar_Parser_AST.Variable uu____3489 ->
          let uu____3490 =
            let uu____3491 = FStar_Parser_AST.binder_to_string b  in
            FStar_Util.format1
              "Imposible : a refined binder ought to be annotated %s"
              uu____3491
             in
          failwith uu____3490
      | FStar_Parser_AST.TVariable uu____3492 ->
          let uu____3493 =
            let uu____3494 = FStar_Parser_AST.binder_to_string b  in
            FStar_Util.format1
              "Imposible : a refined binder ought to be annotated %s"
              uu____3494
             in
          failwith uu____3493
      | FStar_Parser_AST.NoName uu____3495 ->
          let uu____3496 =
            let uu____3497 = FStar_Parser_AST.binder_to_string b  in
            FStar_Util.format1
              "Imposible : a refined binder ought to be annotated %s"
              uu____3497
             in
          failwith uu____3496

and p_simpleDef :
  (FStar_Ident.lid * FStar_Parser_AST.term) -> FStar_Pprint.document =
  fun uu____3498  ->
    match uu____3498 with
    | (lid,e) ->
        let uu____3503 =
          let uu____3504 = p_qlident lid  in
          let uu____3505 =
            let uu____3506 = p_tmIff e  in
            FStar_Pprint.op_Hat_Slash_Hat FStar_Pprint.equals uu____3506  in
          FStar_Pprint.op_Hat_Slash_Hat uu____3504 uu____3505  in
        FStar_Pprint.group uu____3503

and p_appTerm : FStar_Parser_AST.term -> FStar_Pprint.document =
  fun e  ->
    let uu____3508 =
      let uu____3509 = unparen e  in uu____3509.FStar_Parser_AST.tm  in
    match uu____3508 with
    | FStar_Parser_AST.App uu____3510 when is_general_application e ->
        let uu____3514 = head_and_args e  in
        (match uu____3514 with
         | (head1,args) ->
             let uu____3528 =
               let uu____3534 = FStar_ST.read should_print_fs_typ_app  in
               if uu____3534
               then
                 let uu____3542 =
                   FStar_Util.take
                     (fun uu____3553  ->
                        match uu____3553 with
                        | (uu____3556,aq) -> aq = FStar_Parser_AST.FsTypApp)
                     args
                    in
                 match uu____3542 with
                 | (fs_typ_args,args1) ->
                     let uu____3577 =
                       let uu____3578 = p_indexingTerm head1  in
                       let uu____3579 =
                         let uu____3580 =
                           FStar_Pprint.op_Hat_Hat FStar_Pprint.comma break1
                            in
                         soft_surround_separate_map (Prims.parse_int "2")
                           (Prims.parse_int "0") FStar_Pprint.empty
                           FStar_Pprint.langle uu____3580 FStar_Pprint.rangle
                           p_fsTypArg fs_typ_args
                          in
                       FStar_Pprint.op_Hat_Hat uu____3578 uu____3579  in
                     (uu____3577, args1)
               else
                 (let uu____3587 = p_indexingTerm head1  in
                  (uu____3587, args))
                in
             (match uu____3528 with
              | (head_doc,args1) ->
                  let uu____3599 =
                    let uu____3600 =
                      FStar_Pprint.op_Hat_Hat head_doc FStar_Pprint.space  in
                    soft_surround_separate_map (Prims.parse_int "2")
                      (Prims.parse_int "0") head_doc uu____3600 break1
                      FStar_Pprint.empty p_argTerm args1
                     in
                  FStar_Pprint.group uu____3599))
    | FStar_Parser_AST.Construct (lid,args) when
        (is_general_construction e) &&
          (Prims.op_Negation (is_dtuple_constructor lid))
        ->
        (match args with
         | [] -> p_quident lid
         | arg::[] ->
             let uu____3620 =
               let uu____3621 = p_quident lid  in
               let uu____3622 = p_argTerm arg  in
               FStar_Pprint.op_Hat_Slash_Hat uu____3621 uu____3622  in
             FStar_Pprint.group uu____3620
         | hd1::tl1 ->
             let uu____3632 =
               let uu____3633 =
                 let uu____3634 =
                   let uu____3635 = p_quident lid  in
                   let uu____3636 = p_argTerm hd1  in
                   prefix2 uu____3635 uu____3636  in
                 FStar_Pprint.group uu____3634  in
               let uu____3637 =
                 let uu____3638 =
                   FStar_Pprint.separate_map break1 p_argTerm tl1  in
                 jump2 uu____3638  in
               FStar_Pprint.op_Hat_Hat uu____3633 uu____3637  in
             FStar_Pprint.group uu____3632)
    | uu____3641 -> p_indexingTerm e

and p_argTerm :
  (FStar_Parser_AST.term * FStar_Parser_AST.imp) -> FStar_Pprint.document =
  fun arg_imp  ->
    match arg_imp with
    | ({ FStar_Parser_AST.tm = FStar_Parser_AST.Uvar uu____3645;
         FStar_Parser_AST.range = uu____3646;
         FStar_Parser_AST.level = uu____3647;_},FStar_Parser_AST.UnivApp
       ) -> p_univar (fst arg_imp)
    | (u,FStar_Parser_AST.UnivApp ) -> p_universe u
    | (e,FStar_Parser_AST.FsTypApp ) ->
        (FStar_Util.print_warning
           "Unexpected FsTypApp, output might not be formatted correctly.\n";
         (let uu____3651 = p_indexingTerm e  in
          FStar_Pprint.surround (Prims.parse_int "2") (Prims.parse_int "1")
            FStar_Pprint.langle uu____3651 FStar_Pprint.rangle))
    | (e,FStar_Parser_AST.Hash ) ->
        let uu____3653 = str "#"  in
        let uu____3654 = p_indexingTerm e  in
        FStar_Pprint.op_Hat_Hat uu____3653 uu____3654
    | (e,FStar_Parser_AST.Nothing ) -> p_indexingTerm e

and p_fsTypArg :
  (FStar_Parser_AST.term * FStar_Parser_AST.imp) -> FStar_Pprint.document =
  fun uu____3656  ->
    match uu____3656 with | (e,uu____3660) -> p_indexingTerm e

and p_indexingTerm_aux :
  (FStar_Parser_AST.term -> FStar_Pprint.document) ->
    FStar_Parser_AST.term -> FStar_Pprint.document
  =
  fun exit1  ->
    fun e  ->
      let uu____3665 =
        let uu____3666 = unparen e  in uu____3666.FStar_Parser_AST.tm  in
      match uu____3665 with
      | FStar_Parser_AST.Op
          ({ FStar_Ident.idText = ".()"; FStar_Ident.idRange = uu____3667;_},e1::e2::[])
          ->
          let uu____3671 =
            let uu____3672 = p_indexingTerm_aux p_atomicTermNotQUident e1  in
            let uu____3673 =
              let uu____3674 =
                let uu____3675 = p_term e2  in
                soft_parens_with_nesting uu____3675  in
              FStar_Pprint.op_Hat_Hat FStar_Pprint.dot uu____3674  in
            FStar_Pprint.op_Hat_Hat uu____3672 uu____3673  in
          FStar_Pprint.group uu____3671
      | FStar_Parser_AST.Op
          ({ FStar_Ident.idText = ".[]"; FStar_Ident.idRange = uu____3676;_},e1::e2::[])
          ->
          let uu____3680 =
            let uu____3681 = p_indexingTerm_aux p_atomicTermNotQUident e1  in
            let uu____3682 =
              let uu____3683 =
                let uu____3684 = p_term e2  in
                soft_brackets_with_nesting uu____3684  in
              FStar_Pprint.op_Hat_Hat FStar_Pprint.dot uu____3683  in
            FStar_Pprint.op_Hat_Hat uu____3681 uu____3682  in
          FStar_Pprint.group uu____3680
      | uu____3685 -> exit1 e

and p_indexingTerm : FStar_Parser_AST.term -> FStar_Pprint.document =
  fun e  -> p_indexingTerm_aux p_atomicTerm e

and p_atomicTerm : FStar_Parser_AST.term -> FStar_Pprint.document =
  fun e  ->
    let uu____3688 =
      let uu____3689 = unparen e  in uu____3689.FStar_Parser_AST.tm  in
    match uu____3688 with
    | FStar_Parser_AST.LetOpen (lid,e1) ->
        let uu____3692 = p_quident lid  in
        let uu____3693 =
          let uu____3694 =
            let uu____3695 = p_term e1  in
            soft_parens_with_nesting uu____3695  in
          FStar_Pprint.op_Hat_Hat FStar_Pprint.dot uu____3694  in
        FStar_Pprint.op_Hat_Hat uu____3692 uu____3693
    | FStar_Parser_AST.Name lid -> p_quident lid
    | FStar_Parser_AST.Op (op,e1::[]) when is_general_prefix_op op ->
        let uu____3700 = str (FStar_Ident.text_of_id op)  in
        let uu____3701 = p_atomicTerm e1  in
        FStar_Pprint.op_Hat_Hat uu____3700 uu____3701
    | uu____3702 -> p_atomicTermNotQUident e

and p_atomicTermNotQUident : FStar_Parser_AST.term -> FStar_Pprint.document =
  fun e  ->
    let uu____3704 =
      let uu____3705 = unparen e  in uu____3705.FStar_Parser_AST.tm  in
    match uu____3704 with
    | FStar_Parser_AST.Wild  -> FStar_Pprint.underscore
    | FStar_Parser_AST.Var lid when
        FStar_Ident.lid_equals lid FStar_Parser_Const.assert_lid ->
        str "assert"
    | FStar_Parser_AST.Tvar tv -> p_tvar tv
    | FStar_Parser_AST.Const c ->
        (match c with
         | FStar_Const.Const_char x when x = '\n' -> str "0x0Az"
         | uu____3710 -> p_constant c)
    | FStar_Parser_AST.Name lid when
        FStar_Ident.lid_equals lid FStar_Parser_Const.true_lid -> str "True"
    | FStar_Parser_AST.Name lid when
        FStar_Ident.lid_equals lid FStar_Parser_Const.false_lid ->
        str "False"
    | FStar_Parser_AST.Op (op,e1::[]) when is_general_prefix_op op ->
        let uu____3716 = str (FStar_Ident.text_of_id op)  in
        let uu____3717 = p_atomicTermNotQUident e1  in
        FStar_Pprint.op_Hat_Hat uu____3716 uu____3717
    | FStar_Parser_AST.Op (op,[]) ->
        let uu____3720 =
          let uu____3721 =
            let uu____3722 = str (FStar_Ident.text_of_id op)  in
            let uu____3723 =
              FStar_Pprint.op_Hat_Hat FStar_Pprint.space FStar_Pprint.rparen
               in
            FStar_Pprint.op_Hat_Hat uu____3722 uu____3723  in
          FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____3721  in
        FStar_Pprint.op_Hat_Hat FStar_Pprint.lparen uu____3720
    | FStar_Parser_AST.Construct (lid,args) when is_dtuple_constructor lid ->
        let uu____3732 =
          FStar_Pprint.op_Hat_Hat FStar_Pprint.lparen FStar_Pprint.bar  in
        let uu____3733 =
          let uu____3734 = FStar_Pprint.op_Hat_Hat FStar_Pprint.comma break1
             in
          let uu____3735 = FStar_List.map FStar_Pervasives.fst args  in
          FStar_Pprint.separate_map uu____3734 p_tmEq uu____3735  in
        let uu____3739 =
          FStar_Pprint.op_Hat_Hat FStar_Pprint.bar FStar_Pprint.rparen  in
        FStar_Pprint.surround (Prims.parse_int "2") (Prims.parse_int "1")
          uu____3732 uu____3733 uu____3739
    | FStar_Parser_AST.Project (e1,lid) ->
        let uu____3742 =
          let uu____3743 = p_atomicTermNotQUident e1  in
          let uu____3744 =
            let uu____3745 = p_qlident lid  in
            FStar_Pprint.op_Hat_Hat FStar_Pprint.dot uu____3745  in
          FStar_Pprint.prefix (Prims.parse_int "2") (Prims.parse_int "0")
            uu____3743 uu____3744
           in
        FStar_Pprint.group uu____3742
    | uu____3746 -> p_projectionLHS e

and p_projectionLHS : FStar_Parser_AST.term -> FStar_Pprint.document =
  fun e  ->
    let uu____3748 =
      let uu____3749 = unparen e  in uu____3749.FStar_Parser_AST.tm  in
    match uu____3748 with
    | FStar_Parser_AST.Var lid -> p_qlident lid
    | FStar_Parser_AST.Projector (constr_lid,field_lid) ->
        let uu____3753 = p_quident constr_lid  in
        let uu____3754 =
          let uu____3755 =
            let uu____3756 = p_lident field_lid  in
            FStar_Pprint.op_Hat_Hat FStar_Pprint.dot uu____3756  in
          FStar_Pprint.op_Hat_Hat FStar_Pprint.qmark uu____3755  in
        FStar_Pprint.op_Hat_Hat uu____3753 uu____3754
    | FStar_Parser_AST.Discrim constr_lid ->
        let uu____3758 = p_quident constr_lid  in
        FStar_Pprint.op_Hat_Hat uu____3758 FStar_Pprint.qmark
    | FStar_Parser_AST.Paren e1 ->
        let uu____3760 = p_term e1  in soft_parens_with_nesting uu____3760
    | uu____3761 when is_array e ->
        let es = extract_from_list e  in
        let uu____3764 =
          FStar_Pprint.op_Hat_Hat FStar_Pprint.lbracket FStar_Pprint.bar  in
        let uu____3765 =
          let uu____3766 = FStar_Pprint.op_Hat_Hat FStar_Pprint.semi break1
             in
          separate_map_or_flow uu____3766 p_noSeqTerm es  in
        let uu____3767 =
          FStar_Pprint.op_Hat_Hat FStar_Pprint.bar FStar_Pprint.rbracket  in
        FStar_Pprint.surround (Prims.parse_int "2") (Prims.parse_int "0")
          uu____3764 uu____3765 uu____3767
    | uu____3768 when is_list e ->
        let uu____3769 =
          let uu____3770 = FStar_Pprint.op_Hat_Hat FStar_Pprint.semi break1
             in
          let uu____3771 = extract_from_list e  in
          separate_map_or_flow uu____3770 p_noSeqTerm uu____3771  in
        FStar_Pprint.surround (Prims.parse_int "2") (Prims.parse_int "0")
          FStar_Pprint.lbracket uu____3769 FStar_Pprint.rbracket
    | uu____3773 when is_lex_list e ->
        let uu____3774 =
          FStar_Pprint.op_Hat_Hat FStar_Pprint.percent FStar_Pprint.lbracket
           in
        let uu____3775 =
          let uu____3776 = FStar_Pprint.op_Hat_Hat FStar_Pprint.semi break1
             in
          let uu____3777 = extract_from_list e  in
          separate_map_or_flow uu____3776 p_noSeqTerm uu____3777  in
        FStar_Pprint.surround (Prims.parse_int "2") (Prims.parse_int "1")
          uu____3774 uu____3775 FStar_Pprint.rbracket
    | uu____3779 when is_ref_set e ->
        let es = extract_from_ref_set e  in
        let uu____3782 =
          FStar_Pprint.op_Hat_Hat FStar_Pprint.bang FStar_Pprint.lbrace  in
        let uu____3783 =
          let uu____3784 = FStar_Pprint.op_Hat_Hat FStar_Pprint.comma break1
             in
          separate_map_or_flow uu____3784 p_appTerm es  in
        FStar_Pprint.surround (Prims.parse_int "2") (Prims.parse_int "0")
          uu____3782 uu____3783 FStar_Pprint.rbrace
    | FStar_Parser_AST.Labeled (e1,s,b) ->
        let uu____3788 = FStar_Pprint.break_ (Prims.parse_int "0")  in
        let uu____3789 =
          let uu____3790 = str (Prims.strcat "(*" (Prims.strcat s "*)"))  in
          let uu____3791 = p_term e1  in
          FStar_Pprint.op_Hat_Slash_Hat uu____3790 uu____3791  in
        FStar_Pprint.op_Hat_Hat uu____3788 uu____3789
    | FStar_Parser_AST.Op (op,args) when
        let uu____3796 = handleable_op op args  in
        Prims.op_Negation uu____3796 ->
        let uu____3797 =
          let uu____3798 =
            let uu____3799 =
              let uu____3800 =
                let uu____3801 =
                  FStar_Util.string_of_int (FStar_List.length args)  in
                Prims.strcat uu____3801
                  " arguments couldn't be handled by the pretty printer"
                 in
              Prims.strcat " with " uu____3800  in
            Prims.strcat (FStar_Ident.text_of_id op) uu____3799  in
          Prims.strcat "Operation " uu____3798  in
        failwith uu____3797
    | FStar_Parser_AST.Uvar uu____3808 ->
        failwith "Unexpected universe variable out of universe context"
    | FStar_Parser_AST.Wild  ->
        let uu____3809 = p_term e  in soft_parens_with_nesting uu____3809
    | FStar_Parser_AST.Const uu____3810 ->
        let uu____3811 = p_term e  in soft_parens_with_nesting uu____3811
    | FStar_Parser_AST.Op uu____3812 ->
        let uu____3816 = p_term e  in soft_parens_with_nesting uu____3816
    | FStar_Parser_AST.Tvar uu____3817 ->
        let uu____3818 = p_term e  in soft_parens_with_nesting uu____3818
    | FStar_Parser_AST.Var uu____3819 ->
        let uu____3820 = p_term e  in soft_parens_with_nesting uu____3820
    | FStar_Parser_AST.Name uu____3821 ->
        let uu____3822 = p_term e  in soft_parens_with_nesting uu____3822
    | FStar_Parser_AST.Construct uu____3823 ->
        let uu____3829 = p_term e  in soft_parens_with_nesting uu____3829
    | FStar_Parser_AST.Abs uu____3830 ->
        let uu____3834 = p_term e  in soft_parens_with_nesting uu____3834
    | FStar_Parser_AST.App uu____3835 ->
        let uu____3839 = p_term e  in soft_parens_with_nesting uu____3839
    | FStar_Parser_AST.Let uu____3840 ->
        let uu____3847 = p_term e  in soft_parens_with_nesting uu____3847
    | FStar_Parser_AST.LetOpen uu____3848 ->
        let uu____3851 = p_term e  in soft_parens_with_nesting uu____3851
    | FStar_Parser_AST.Seq uu____3852 ->
        let uu____3855 = p_term e  in soft_parens_with_nesting uu____3855
    | FStar_Parser_AST.Bind uu____3856 ->
        let uu____3860 = p_term e  in soft_parens_with_nesting uu____3860
    | FStar_Parser_AST.If uu____3861 ->
        let uu____3865 = p_term e  in soft_parens_with_nesting uu____3865
    | FStar_Parser_AST.Match uu____3866 ->
        let uu____3874 = p_term e  in soft_parens_with_nesting uu____3874
    | FStar_Parser_AST.TryWith uu____3875 ->
        let uu____3883 = p_term e  in soft_parens_with_nesting uu____3883
    | FStar_Parser_AST.Ascribed uu____3884 ->
        let uu____3889 = p_term e  in soft_parens_with_nesting uu____3889
    | FStar_Parser_AST.Record uu____3890 ->
        let uu____3897 = p_term e  in soft_parens_with_nesting uu____3897
    | FStar_Parser_AST.Project uu____3898 ->
        let uu____3901 = p_term e  in soft_parens_with_nesting uu____3901
    | FStar_Parser_AST.Product uu____3902 ->
        let uu____3906 = p_term e  in soft_parens_with_nesting uu____3906
    | FStar_Parser_AST.Sum uu____3907 ->
        let uu____3911 = p_term e  in soft_parens_with_nesting uu____3911
    | FStar_Parser_AST.QForall uu____3912 ->
        let uu____3919 = p_term e  in soft_parens_with_nesting uu____3919
    | FStar_Parser_AST.QExists uu____3920 ->
        let uu____3927 = p_term e  in soft_parens_with_nesting uu____3927
    | FStar_Parser_AST.Refine uu____3928 ->
        let uu____3931 = p_term e  in soft_parens_with_nesting uu____3931
    | FStar_Parser_AST.NamedTyp uu____3932 ->
        let uu____3935 = p_term e  in soft_parens_with_nesting uu____3935
    | FStar_Parser_AST.Requires uu____3936 ->
        let uu____3940 = p_term e  in soft_parens_with_nesting uu____3940
    | FStar_Parser_AST.Ensures uu____3941 ->
        let uu____3945 = p_term e  in soft_parens_with_nesting uu____3945
    | FStar_Parser_AST.Assign uu____3946 ->
        let uu____3949 = p_term e  in soft_parens_with_nesting uu____3949
    | FStar_Parser_AST.Attributes uu____3950 ->
        let uu____3952 = p_term e  in soft_parens_with_nesting uu____3952

and p_constant : FStar_Const.sconst -> FStar_Pprint.document =
  fun uu___108_3953  ->
    match uu___108_3953 with
    | FStar_Const.Const_effect  -> str "Effect"
    | FStar_Const.Const_unit  -> str "()"
    | FStar_Const.Const_bool b -> FStar_Pprint.doc_of_bool b
    | FStar_Const.Const_float x -> str (FStar_Util.string_of_float x)
    | FStar_Const.Const_char x ->
        let uu____3957 = FStar_Pprint.doc_of_char x  in
        FStar_Pprint.squotes uu____3957
    | FStar_Const.Const_string (bytes,uu____3959) ->
        let uu____3962 = str (FStar_Util.string_of_bytes bytes)  in
        FStar_Pprint.dquotes uu____3962
    | FStar_Const.Const_bytearray (bytes,uu____3964) ->
        let uu____3967 =
          let uu____3968 = str (FStar_Util.string_of_bytes bytes)  in
          FStar_Pprint.dquotes uu____3968  in
        let uu____3969 = str "B"  in
        FStar_Pprint.op_Hat_Hat uu____3967 uu____3969
    | FStar_Const.Const_int (repr,sign_width_opt) ->
        let signedness uu___106_3981 =
          match uu___106_3981 with
          | FStar_Const.Unsigned  -> str "u"
          | FStar_Const.Signed  -> FStar_Pprint.empty  in
        let width uu___107_3985 =
          match uu___107_3985 with
          | FStar_Const.Int8  -> str "y"
          | FStar_Const.Int16  -> str "s"
          | FStar_Const.Int32  -> str "l"
          | FStar_Const.Int64  -> str "L"  in
        let ending =
          default_or_map FStar_Pprint.empty
            (fun uu____3989  ->
               match uu____3989 with
               | (s,w) ->
                   let uu____3994 = signedness s  in
                   let uu____3995 = width w  in
                   FStar_Pprint.op_Hat_Hat uu____3994 uu____3995)
            sign_width_opt
           in
        let uu____3996 = str repr  in
        FStar_Pprint.op_Hat_Hat uu____3996 ending
    | FStar_Const.Const_range r ->
        let uu____3998 = FStar_Range.string_of_range r  in str uu____3998
    | FStar_Const.Const_reify  -> str "reify"
    | FStar_Const.Const_reflect lid ->
        let uu____4000 = p_quident lid  in
        let uu____4001 =
          let uu____4002 =
            let uu____4003 = str "reflect"  in
            FStar_Pprint.op_Hat_Hat FStar_Pprint.dot uu____4003  in
          FStar_Pprint.op_Hat_Hat FStar_Pprint.qmark uu____4002  in
        FStar_Pprint.op_Hat_Hat uu____4000 uu____4001

and p_universe : FStar_Parser_AST.term -> FStar_Pprint.document =
  fun u  ->
    let uu____4005 = str "u#"  in
    let uu____4006 = p_atomicUniverse u  in
    FStar_Pprint.op_Hat_Hat uu____4005 uu____4006

and p_universeFrom : FStar_Parser_AST.term -> FStar_Pprint.document =
  fun u  ->
    let uu____4008 =
      let uu____4009 = unparen u  in uu____4009.FStar_Parser_AST.tm  in
    match uu____4008 with
    | FStar_Parser_AST.Op
        ({ FStar_Ident.idText = "+"; FStar_Ident.idRange = uu____4010;_},u1::u2::[])
        ->
        let uu____4014 =
          let uu____4015 = p_universeFrom u1  in
          let uu____4016 =
            let uu____4017 = p_universeFrom u2  in
            FStar_Pprint.op_Hat_Slash_Hat FStar_Pprint.plus uu____4017  in
          FStar_Pprint.op_Hat_Slash_Hat uu____4015 uu____4016  in
        FStar_Pprint.group uu____4014
    | FStar_Parser_AST.App uu____4018 ->
        let uu____4022 = head_and_args u  in
        (match uu____4022 with
         | (head1,args) ->
             let uu____4036 =
               let uu____4037 = unparen head1  in
               uu____4037.FStar_Parser_AST.tm  in
             (match uu____4036 with
              | FStar_Parser_AST.Var maybe_max_lid when
                  FStar_Ident.lid_equals maybe_max_lid
                    FStar_Parser_Const.max_lid
                  ->
                  let uu____4039 =
                    let uu____4040 = p_qlident FStar_Parser_Const.max_lid  in
                    let uu____4041 =
                      FStar_Pprint.separate_map FStar_Pprint.space
                        (fun uu____4044  ->
                           match uu____4044 with
                           | (u1,uu____4048) -> p_atomicUniverse u1) args
                       in
                    op_Hat_Slash_Plus_Hat uu____4040 uu____4041  in
                  FStar_Pprint.group uu____4039
              | uu____4049 ->
                  let uu____4050 =
                    let uu____4051 = FStar_Parser_AST.term_to_string u  in
                    FStar_Util.format1 "Invalid term in universe context %s"
                      uu____4051
                     in
                  failwith uu____4050))
    | uu____4052 -> p_atomicUniverse u

and p_atomicUniverse : FStar_Parser_AST.term -> FStar_Pprint.document =
  fun u  ->
    let uu____4054 =
      let uu____4055 = unparen u  in uu____4055.FStar_Parser_AST.tm  in
    match uu____4054 with
    | FStar_Parser_AST.Wild  -> FStar_Pprint.underscore
    | FStar_Parser_AST.Const (FStar_Const.Const_int (r,sw)) ->
        p_constant (FStar_Const.Const_int (r, sw))
    | FStar_Parser_AST.Uvar uu____4067 -> p_univar u
    | FStar_Parser_AST.Paren u1 ->
        let uu____4069 = p_universeFrom u1  in
        soft_parens_with_nesting uu____4069
    | FStar_Parser_AST.Op
        ({ FStar_Ident.idText = "+"; FStar_Ident.idRange = uu____4070;_},uu____4071::uu____4072::[])
        ->
        let uu____4074 = p_universeFrom u  in
        soft_parens_with_nesting uu____4074
    | FStar_Parser_AST.App uu____4075 ->
        let uu____4079 = p_universeFrom u  in
        soft_parens_with_nesting uu____4079
    | uu____4080 ->
        let uu____4081 =
          let uu____4082 = FStar_Parser_AST.term_to_string u  in
          FStar_Util.format1 "Invalid term in universe context %s" uu____4082
           in
        failwith uu____4081

and p_univar : FStar_Parser_AST.term -> FStar_Pprint.document =
  fun u  ->
    let uu____4084 =
      let uu____4085 = unparen u  in uu____4085.FStar_Parser_AST.tm  in
    match uu____4084 with
    | FStar_Parser_AST.Uvar id -> str (FStar_Ident.text_of_id id)
    | uu____4087 ->
        let uu____4088 =
          let uu____4089 = FStar_Parser_AST.term_to_string u  in
          FStar_Util.format1 "Not a universe variable %s" uu____4089  in
        failwith uu____4088

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
       | FStar_Parser_AST.Module (uu____4114,decls) ->
           let uu____4118 =
             FStar_All.pipe_right decls (FStar_List.map decl_to_document)  in
           FStar_All.pipe_right uu____4118
             (FStar_Pprint.separate FStar_Pprint.hardline)
       | FStar_Parser_AST.Interface (uu____4123,decls,uu____4125) ->
           let uu____4128 =
             FStar_All.pipe_right decls (FStar_List.map decl_to_document)  in
           FStar_All.pipe_right uu____4128
             (FStar_Pprint.separate FStar_Pprint.hardline)
        in
     FStar_ST.write should_print_fs_typ_app false; res)
  
let comments_to_document :
  (Prims.string * FStar_Range.range) Prims.list -> FStar_Pprint.document =
  fun comments  ->
    FStar_Pprint.separate_map FStar_Pprint.hardline
      (fun uu____4148  ->
         match uu____4148 with | (comment,range) -> str comment) comments
  
let modul_with_comments_to_document :
  FStar_Parser_AST.modul ->
    (Prims.string * FStar_Range.range) Prims.list ->
      (FStar_Pprint.document * (Prims.string * FStar_Range.range) Prims.list)
  =
  fun m  ->
    fun comments  ->
      let decls =
        match m with
        | FStar_Parser_AST.Module (uu____4175,decls) -> decls
        | FStar_Parser_AST.Interface (uu____4179,decls,uu____4181) -> decls
         in
      FStar_ST.write should_print_fs_typ_app false;
      (match decls with
       | [] -> (FStar_Pprint.empty, comments)
       | d::ds ->
           let uu____4198 =
             match ds with
             | {
                 FStar_Parser_AST.d = FStar_Parser_AST.Pragma
                   (FStar_Parser_AST.LightOff );
                 FStar_Parser_AST.drange = uu____4205;
                 FStar_Parser_AST.doc = uu____4206;
                 FStar_Parser_AST.quals = uu____4207;
                 FStar_Parser_AST.attrs = uu____4208;_}::uu____4209 ->
                 let d0 = FStar_List.hd ds  in
                 let uu____4213 =
                   let uu____4215 =
                     let uu____4217 = FStar_List.tl ds  in d :: uu____4217
                      in
                   d0 :: uu____4215  in
                 (uu____4213, (d0.FStar_Parser_AST.drange))
             | uu____4220 -> ((d :: ds), (d.FStar_Parser_AST.drange))  in
           (match uu____4198 with
            | (decls1,first_range) ->
                let extract_decl_range d1 = d1.FStar_Parser_AST.drange  in
                (FStar_ST.write comment_stack comments;
                 (let initial_comment =
                    let uu____4243 = FStar_Range.start_of_range first_range
                       in
                    place_comments_until_pos (Prims.parse_int "0")
                      (Prims.parse_int "1") uu____4243 FStar_Pprint.empty
                     in
                  let doc1 =
                    separate_map_with_comments FStar_Pprint.empty
                      FStar_Pprint.empty decl_to_document decls1
                      extract_decl_range
                     in
                  let comments1 = FStar_ST.read comment_stack  in
                  FStar_ST.write comment_stack [];
                  FStar_ST.write should_print_fs_typ_app false;
                  (let uu____4265 =
                     FStar_Pprint.op_Hat_Hat initial_comment doc1  in
                   (uu____4265, comments1))))))
  