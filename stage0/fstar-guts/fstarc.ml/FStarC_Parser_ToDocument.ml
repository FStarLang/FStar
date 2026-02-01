open Prims
let maybe_unthunk (t : FStarC_Parser_AST.term) : FStarC_Parser_AST.term=
  match t.FStarC_Parser_AST.tm with
  | FStarC_Parser_AST.Abs (uu___::[], body) -> body
  | uu___ -> t
let min (x : Prims.int) (y : Prims.int) : Prims.int= if x > y then y else x
let max (x : Prims.int) (y : Prims.int) : Prims.int= if x > y then x else y
let map_rev (f : 'a -> 'b) (l : 'a Prims.list) : 'b Prims.list=
  let rec aux l1 acc =
    match l1 with
    | [] -> acc
    | x::xs -> let uu___ = let uu___1 = f x in uu___1 :: acc in aux xs uu___ in
  aux l []
let map_if_all (f : 'a -> 'b FStar_Pervasives_Native.option)
  (l : 'a Prims.list) : 'b Prims.list FStar_Pervasives_Native.option=
  let rec aux l1 acc =
    match l1 with
    | [] -> acc
    | x::xs ->
        let uu___ = f x in
        (match uu___ with
         | FStar_Pervasives_Native.Some r -> aux xs (r :: acc)
         | FStar_Pervasives_Native.None -> []) in
  let r = aux l [] in
  if (FStarC_List.length l) = (FStarC_List.length r)
  then FStar_Pervasives_Native.Some r
  else FStar_Pervasives_Native.None
let rec all : 'a . ('a -> Prims.bool) -> 'a Prims.list -> Prims.bool =
  fun f l ->
    match l with
    | [] -> true
    | x::xs -> let uu___ = f x in if uu___ then all f xs else false
let all1_explicit
  (args : (FStarC_Parser_AST.term * FStarC_Parser_AST.imp) Prims.list) :
  Prims.bool=
  (Prims.op_Negation (FStarC_List.isEmpty args)) &&
    (FStarC_Util.for_all
       (fun uu___ ->
          match uu___ with
          | (uu___1, FStarC_Parser_AST.Nothing) -> true
          | uu___1 -> false) args)
let str (s : Prims.string) : FStar_Pprint.document=
  FStar_Pprint.doc_of_string s
let default_or_map (n : 'uuuuu) (f : 'uuuuu1 -> 'uuuuu)
  (x : 'uuuuu1 FStar_Pervasives_Native.option) : 'uuuuu=
  match x with
  | FStar_Pervasives_Native.None -> n
  | FStar_Pervasives_Native.Some x' -> f x'
let prefix2 (prefix_ : FStar_Pprint.document) (body : FStar_Pprint.document)
  : FStar_Pprint.document=
  FStar_Pprint.prefix (Prims.of_int (2)) Prims.int_one prefix_ body
let prefix2_nonempty (prefix_ : FStar_Pprint.document)
  (body : FStar_Pprint.document) : FStar_Pprint.document=
  if body = FStar_Pprint.empty then prefix_ else prefix2 prefix_ body
let op_Hat_Slash_Plus_Hat (prefix_ : FStar_Pprint.document)
  (body : FStar_Pprint.document) : FStar_Pprint.document=
  prefix2 prefix_ body
let jump2 (body : FStar_Pprint.document) : FStar_Pprint.document=
  FStar_Pprint.jump (Prims.of_int (2)) Prims.int_one body
let infix2 :
  FStar_Pprint.document ->
    FStar_Pprint.document -> FStar_Pprint.document -> FStar_Pprint.document=
  FStar_Pprint.infix (Prims.of_int (2)) Prims.int_one
let infix0 :
  FStar_Pprint.document ->
    FStar_Pprint.document -> FStar_Pprint.document -> FStar_Pprint.document=
  FStar_Pprint.infix Prims.int_zero Prims.int_one
let break1 : FStar_Pprint.document= FStar_Pprint.break_ Prims.int_one
let separate_break_map (sep : FStar_Pprint.document)
  (f : 'uuuuu -> FStar_Pprint.document) (l : 'uuuuu Prims.list) :
  FStar_Pprint.document=
  let uu___ =
    FStarC_Pprint.separate_map
      (FStar_Pprint.op_Hat_Hat FStar_Pprint.space
         (FStar_Pprint.op_Hat_Hat sep break1)) f l in
  FStar_Pprint.group uu___
let precede_break_separate_map (prec : FStar_Pprint.document)
  (sep : FStar_Pprint.document) (f : 'uuuuu -> FStar_Pprint.document)
  (l : 'uuuuu Prims.list) : FStar_Pprint.document=
  let uu___ =
    let uu___1 = let uu___2 = FStarC_List.hd l in f uu___2 in
    FStar_Pprint.precede (FStar_Pprint.op_Hat_Hat prec FStar_Pprint.space)
      uu___1 in
  let uu___1 =
    let uu___2 = FStarC_List.tl l in
    FStarC_Pprint.concat_map
      (fun x ->
         let uu___3 =
           let uu___4 =
             let uu___5 = f x in
             FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu___5 in
           FStar_Pprint.op_Hat_Hat sep uu___4 in
         FStar_Pprint.op_Hat_Hat break1 uu___3) uu___2 in
  FStar_Pprint.op_Hat_Hat uu___ uu___1
let concat_break_map (f : 'uuuuu -> FStar_Pprint.document)
  (l : 'uuuuu Prims.list) : FStar_Pprint.document=
  let uu___ =
    FStarC_Pprint.concat_map
      (fun x -> let uu___1 = f x in FStar_Pprint.op_Hat_Hat uu___1 break1) l in
  FStar_Pprint.group uu___
let parens_with_nesting (contents : FStar_Pprint.document) :
  FStar_Pprint.document=
  FStar_Pprint.surround (Prims.of_int (2)) Prims.int_zero FStar_Pprint.lparen
    contents FStar_Pprint.rparen
let soft_parens_with_nesting (contents : FStar_Pprint.document) :
  FStar_Pprint.document=
  FStar_Pprint.soft_surround (Prims.of_int (2)) Prims.int_zero
    FStar_Pprint.lparen contents FStar_Pprint.rparen
let braces_with_nesting (contents : FStar_Pprint.document) :
  FStar_Pprint.document=
  FStar_Pprint.surround (Prims.of_int (2)) Prims.int_one FStar_Pprint.lbrace
    contents FStar_Pprint.rbrace
let soft_braces_with_nesting (contents : FStar_Pprint.document) :
  FStar_Pprint.document=
  FStar_Pprint.soft_surround (Prims.of_int (2)) Prims.int_one
    FStar_Pprint.lbrace contents FStar_Pprint.rbrace
let soft_braces_with_nesting_tight (contents : FStar_Pprint.document) :
  FStar_Pprint.document=
  FStar_Pprint.soft_surround (Prims.of_int (2)) Prims.int_zero
    FStar_Pprint.lbrace contents FStar_Pprint.rbrace
let brackets_with_nesting (contents : FStar_Pprint.document) :
  FStar_Pprint.document=
  FStar_Pprint.surround (Prims.of_int (2)) Prims.int_one
    FStar_Pprint.lbracket contents FStar_Pprint.rbracket
let soft_brackets_with_nesting (contents : FStar_Pprint.document) :
  FStar_Pprint.document=
  FStar_Pprint.soft_surround (Prims.of_int (2)) Prims.int_one
    FStar_Pprint.lbracket contents FStar_Pprint.rbracket
let soft_lens_access_with_nesting (contents : FStar_Pprint.document) :
  FStar_Pprint.document=
  FStar_Pprint.soft_surround (Prims.of_int (2)) Prims.int_one (str "(|")
    contents (str "|)")
let soft_brackets_lens_access_with_nesting (contents : FStar_Pprint.document)
  : FStar_Pprint.document=
  FStar_Pprint.soft_surround (Prims.of_int (2)) Prims.int_one (str "[|")
    contents (str "|]")
let soft_begin_end_with_nesting (contents : FStar_Pprint.document) :
  FStar_Pprint.document=
  FStar_Pprint.soft_surround (Prims.of_int (2)) Prims.int_one (str "begin")
    contents (str "end")
let tc_arg (contents : FStar_Pprint.document) : FStar_Pprint.document=
  FStar_Pprint.soft_surround (Prims.of_int (2)) Prims.int_one (str "{|")
    contents (str "|}")
let is_tc_binder (b : FStarC_Parser_AST.binder) : Prims.bool=
  match b.FStarC_Parser_AST.aqual with
  | FStar_Pervasives_Native.Some (FStarC_Parser_AST.TypeClassArg) -> true
  | uu___ -> false
let is_meta_qualifier
  (aq : FStarC_Parser_AST.arg_qualifier FStar_Pervasives_Native.option) :
  Prims.bool=
  match aq with
  | FStar_Pervasives_Native.Some (FStarC_Parser_AST.Meta uu___) -> true
  | uu___ -> false
let is_joinable_binder (b : FStarC_Parser_AST.binder) : Prims.bool=
  (let uu___ = is_tc_binder b in Prims.op_Negation uu___) &&
    (Prims.op_Negation (is_meta_qualifier b.FStarC_Parser_AST.aqual))
let separate_map_last (sep : FStar_Pprint.document)
  (f : Prims.bool -> 'uuuuu -> FStar_Pprint.document)
  (es : 'uuuuu Prims.list) : FStar_Pprint.document=
  let l = FStarC_List.length es in
  let es1 = FStarC_List.mapi (fun i e -> f (i <> (l - Prims.int_one)) e) es in
  FStar_Pprint.separate sep es1
let separate_break_map_last (sep : FStar_Pprint.document)
  (f : Prims.bool -> 'uuuuu -> FStar_Pprint.document) (l : 'uuuuu Prims.list)
  : FStar_Pprint.document=
  let uu___ =
    separate_map_last
      (FStar_Pprint.op_Hat_Hat FStar_Pprint.space
         (FStar_Pprint.op_Hat_Hat sep break1)) f l in
  FStar_Pprint.group uu___
let separate_map_or_flow (sep : FStar_Pprint.document)
  (f : 'uuuuu -> FStar_Pprint.document) (l : 'uuuuu Prims.list) :
  FStar_Pprint.document=
  if (FStarC_List.length l) < (Prims.of_int (10))
  then FStarC_Pprint.separate_map sep f l
  else FStarC_Pprint.flow_map sep f l
let flow_map_last (sep : FStar_Pprint.document)
  (f : Prims.bool -> 'uuuuu -> FStar_Pprint.document)
  (es : 'uuuuu Prims.list) : FStar_Pprint.document=
  let l = FStarC_List.length es in
  let es1 = FStarC_List.mapi (fun i e -> f (i <> (l - Prims.int_one)) e) es in
  FStar_Pprint.flow sep es1
let separate_map_or_flow_last (sep : FStar_Pprint.document)
  (f : Prims.bool -> 'uuuuu -> FStar_Pprint.document) (l : 'uuuuu Prims.list)
  : FStar_Pprint.document=
  if (FStarC_List.length l) < (Prims.of_int (10))
  then separate_map_last sep f l
  else flow_map_last sep f l
let separate_or_flow (sep : FStar_Pprint.document)
  (l : FStar_Pprint.document Prims.list) : FStar_Pprint.document=
  separate_map_or_flow sep (fun x -> x) l
let surround_maybe_empty (n : Prims.int) (b : Prims.int)
  (doc1 : FStar_Pprint.document) (doc2 : FStar_Pprint.document)
  (doc3 : FStar_Pprint.document) : FStar_Pprint.document=
  if doc2 = FStar_Pprint.empty
  then FStar_Pprint.group (FStar_Pprint.op_Hat_Slash_Hat doc1 doc3)
  else FStar_Pprint.surround n b doc1 doc2 doc3
let soft_surround_separate_map (n : Prims.int) (b : Prims.int)
  (void_ : FStar_Pprint.document) (opening : FStar_Pprint.document)
  (sep : FStar_Pprint.document) (closing : FStar_Pprint.document)
  (f : 'uuuuu -> FStar_Pprint.document) (xs : 'uuuuu Prims.list) :
  FStar_Pprint.document=
  if xs = []
  then void_
  else
    (let uu___1 = FStarC_Pprint.separate_map sep f xs in
     FStar_Pprint.soft_surround n b opening uu___1 closing)
let soft_surround_map_or_flow (n : Prims.int) (b : Prims.int)
  (void_ : FStar_Pprint.document) (opening : FStar_Pprint.document)
  (sep : FStar_Pprint.document) (closing : FStar_Pprint.document)
  (f : 'uuuuu -> FStar_Pprint.document) (xs : 'uuuuu Prims.list) :
  FStar_Pprint.document=
  if xs = []
  then void_
  else
    (let uu___1 = separate_map_or_flow sep f xs in
     FStar_Pprint.soft_surround n b opening uu___1 closing)
let is_unit (e : FStarC_Parser_AST.term) : Prims.bool=
  match e.FStarC_Parser_AST.tm with
  | FStarC_Parser_AST.Const (FStarC_Const.Const_unit) -> true
  | uu___ -> false
let matches_var (t : FStarC_Parser_AST.term) (x : FStarC_Ident.ident) :
  Prims.bool=
  match t.FStarC_Parser_AST.tm with
  | FStarC_Parser_AST.Var y ->
      let uu___ = FStarC_Ident.string_of_id x in
      let uu___1 = FStarC_Ident.string_of_lid y in uu___ = uu___1
  | uu___ -> false
let is_tuple_constructor : FStarC_Ident.lident -> Prims.bool=
  FStarC_Parser_Const_Tuples.is_tuple_datacon_lid
let is_dtuple_constructor : FStarC_Ident.lident -> Prims.bool=
  FStarC_Parser_Const_Tuples.is_dtuple_datacon_lid
let is_array (e : FStarC_Parser_AST.term) : Prims.bool=
  match e.FStarC_Parser_AST.tm with
  | FStarC_Parser_AST.App
      ({ FStarC_Parser_AST.tm = FStarC_Parser_AST.Var lid;
         FStarC_Parser_AST.range = uu___; FStarC_Parser_AST.level = uu___1;_},
       l, FStarC_Parser_AST.Nothing)
      ->
      (FStarC_Ident.lid_equals lid FStarC_Parser_Const.array_of_list_lid) &&
        (FStarC_Parser_AST.uu___is_ListLiteral l.FStarC_Parser_AST.tm)
  | uu___ -> false
let rec is_ref_set (e : FStarC_Parser_AST.term) : Prims.bool=
  match e.FStarC_Parser_AST.tm with
  | FStarC_Parser_AST.Var maybe_empty_lid ->
      FStarC_Ident.lid_equals maybe_empty_lid FStarC_Parser_Const.set_empty
  | FStarC_Parser_AST.App
      ({ FStarC_Parser_AST.tm = FStarC_Parser_AST.Var maybe_singleton_lid;
         FStarC_Parser_AST.range = uu___; FStarC_Parser_AST.level = uu___1;_},
       {
         FStarC_Parser_AST.tm = FStarC_Parser_AST.App
           ({ FStarC_Parser_AST.tm = FStarC_Parser_AST.Var maybe_addr_of_lid;
              FStarC_Parser_AST.range = uu___2;
              FStarC_Parser_AST.level = uu___3;_},
            e1, FStarC_Parser_AST.Nothing);
         FStarC_Parser_AST.range = uu___4;
         FStarC_Parser_AST.level = uu___5;_},
       FStarC_Parser_AST.Nothing)
      ->
      (FStarC_Ident.lid_equals maybe_singleton_lid
         FStarC_Parser_Const.set_singleton)
        &&
        (FStarC_Ident.lid_equals maybe_addr_of_lid
           FStarC_Parser_Const.heap_addr_of_lid)
  | FStarC_Parser_AST.App
      ({
         FStarC_Parser_AST.tm = FStarC_Parser_AST.App
           ({ FStarC_Parser_AST.tm = FStarC_Parser_AST.Var maybe_union_lid;
              FStarC_Parser_AST.range = uu___;
              FStarC_Parser_AST.level = uu___1;_},
            e1, FStarC_Parser_AST.Nothing);
         FStarC_Parser_AST.range = uu___2;
         FStarC_Parser_AST.level = uu___3;_},
       e2, FStarC_Parser_AST.Nothing)
      ->
      ((FStarC_Ident.lid_equals maybe_union_lid FStarC_Parser_Const.set_union)
         && (is_ref_set e1))
        && (is_ref_set e2)
  | uu___ -> false
let rec extract_from_ref_set (e : FStarC_Parser_AST.term) :
  FStarC_Parser_AST.term Prims.list=
  match e.FStarC_Parser_AST.tm with
  | FStarC_Parser_AST.Var uu___ -> []
  | FStarC_Parser_AST.App
      ({ FStarC_Parser_AST.tm = FStarC_Parser_AST.Var uu___;
         FStarC_Parser_AST.range = uu___1;
         FStarC_Parser_AST.level = uu___2;_},
       {
         FStarC_Parser_AST.tm = FStarC_Parser_AST.App
           ({ FStarC_Parser_AST.tm = FStarC_Parser_AST.Var uu___3;
              FStarC_Parser_AST.range = uu___4;
              FStarC_Parser_AST.level = uu___5;_},
            e1, FStarC_Parser_AST.Nothing);
         FStarC_Parser_AST.range = uu___6;
         FStarC_Parser_AST.level = uu___7;_},
       FStarC_Parser_AST.Nothing)
      -> [e1]
  | FStarC_Parser_AST.App
      ({
         FStarC_Parser_AST.tm = FStarC_Parser_AST.App
           ({ FStarC_Parser_AST.tm = FStarC_Parser_AST.Var uu___;
              FStarC_Parser_AST.range = uu___1;
              FStarC_Parser_AST.level = uu___2;_},
            e1, FStarC_Parser_AST.Nothing);
         FStarC_Parser_AST.range = uu___3;
         FStarC_Parser_AST.level = uu___4;_},
       e2, FStarC_Parser_AST.Nothing)
      ->
      let uu___5 = extract_from_ref_set e1 in
      let uu___6 = extract_from_ref_set e2 in FStarC_List.op_At uu___5 uu___6
  | uu___ ->
      let uu___1 =
        let uu___2 = FStarC_Parser_AST.term_to_string e in
        FStarC_Format.fmt1 "Not a ref set %s" uu___2 in
      failwith uu___1
let is_general_application (e : FStarC_Parser_AST.term) : Prims.bool=
  let uu___ = (is_array e) || (is_ref_set e) in Prims.op_Negation uu___
let is_general_construction (e : FStarC_Parser_AST.term) : Prims.bool=
  Prims.op_Negation
    (FStarC_Parser_AST.uu___is_ListLiteral e.FStarC_Parser_AST.tm)
let is_general_prefix_op (op : FStarC_Ident.ident) : Prims.bool=
  let op_starting_char =
    let uu___ = FStarC_Ident.string_of_id op in
    FStarC_Util.char_at uu___ Prims.int_zero in
  ((op_starting_char = 33) || (op_starting_char = 63)) ||
    ((op_starting_char = 126) &&
       (let uu___ = FStarC_Ident.string_of_id op in uu___ <> "~"))
let head_and_args (e : FStarC_Parser_AST.term) :
  (FStarC_Parser_AST.term * (FStarC_Parser_AST.term * FStarC_Parser_AST.imp)
    Prims.list)=
  let rec aux e1 acc =
    match e1.FStarC_Parser_AST.tm with
    | FStarC_Parser_AST.App (head, arg, imp) -> aux head ((arg, imp) :: acc)
    | uu___ -> (e1, acc) in
  aux e []
type associativity =
  | Left 
  | Right 
  | NonAssoc 
let uu___is_Left (projectee : associativity) : Prims.bool=
  match projectee with | Left -> true | uu___ -> false
let uu___is_Right (projectee : associativity) : Prims.bool=
  match projectee with | Right -> true | uu___ -> false
let uu___is_NonAssoc (projectee : associativity) : Prims.bool=
  match projectee with | NonAssoc -> true | uu___ -> false
type token =
  | StartsWith of FStar_Char.char 
  | Exact of Prims.string 
  | UnicodeOperator 
let uu___is_StartsWith (projectee : token) : Prims.bool=
  match projectee with | StartsWith _0 -> true | uu___ -> false
let __proj__StartsWith__item___0 (projectee : token) : FStar_Char.char=
  match projectee with | StartsWith _0 -> _0
let uu___is_Exact (projectee : token) : Prims.bool=
  match projectee with | Exact _0 -> true | uu___ -> false
let __proj__Exact__item___0 (projectee : token) : Prims.string=
  match projectee with | Exact _0 -> _0
let uu___is_UnicodeOperator (projectee : token) : Prims.bool=
  match projectee with | UnicodeOperator -> true | uu___ -> false
type associativity_level = (associativity * token Prims.list)
let token_to_string (uu___ : token) : Prims.string=
  match uu___ with
  | StartsWith c -> Prims.strcat (FStarC_Util.string_of_char c) ".*"
  | Exact s -> s
  | UnicodeOperator -> "<unicode-op>"
let is_non_latin_char (s : FStar_Char.char) : Prims.bool=
  (FStarC_Util.int_of_char s) > (Prims.of_int (0x024f))
let matches_token (s : Prims.string) (uu___ : token) : Prims.bool=
  match uu___ with
  | StartsWith c ->
      let uu___1 = FStarC_String.get s Prims.int_zero in uu___1 = c
  | Exact s' -> s = s'
  | UnicodeOperator ->
      let uu___1 = FStarC_String.get s Prims.int_zero in
      is_non_latin_char uu___1
let matches_level (s : Prims.string) (uu___ : ('uuuuu * token Prims.list)) :
  Prims.bool=
  match uu___ with
  | (assoc_levels, tokens) ->
      let uu___1 = FStarC_List.tryFind (matches_token s) tokens in
      uu___1 <> FStar_Pervasives_Native.None
let opinfix4 : associativity_level= (Right, [Exact "|->"; UnicodeOperator])
let opinfix3l : associativity_level=
  (Left, [StartsWith 42; StartsWith 47; StartsWith 37])
let opinfix3r : associativity_level= (Right, [Exact "**"])
let opinfix2 : associativity_level= (Left, [StartsWith 43; StartsWith 45])
let minus_lvl : associativity_level= (Left, [Exact "-"])
let opinfix1 : associativity_level= (Right, [StartsWith 64; StartsWith 94])
let pipe_right : associativity_level= (Left, [Exact "|>"])
let opinfix0d : associativity_level= (Left, [StartsWith 36])
let opinfix0c : associativity_level=
  (Left, [StartsWith 61; StartsWith 60; StartsWith 62])
let equal : associativity_level= (Left, [Exact "="])
let opinfix0b : associativity_level= (Left, [StartsWith 38])
let opinfix0a : associativity_level= (Left, [StartsWith 124])
let colon_equals : associativity_level= (NonAssoc, [Exact ":="])
let amp : associativity_level= (Right, [Exact "&"])
let colon_colon : associativity_level= (Right, [Exact "::"])
let level_associativity_spec : associativity_level Prims.list=
  [opinfix4;
  opinfix3r;
  opinfix3l;
  opinfix2;
  opinfix1;
  pipe_right;
  opinfix0d;
  opinfix0c;
  opinfix0b;
  opinfix0a;
  colon_equals;
  amp;
  colon_colon]
let level_table :
  ((Prims.int * Prims.int * Prims.int) * token Prims.list) Prims.list=
  let levels_from_associativity l uu___ =
    match uu___ with
    | Left -> (l, l, (l - Prims.int_one))
    | Right -> ((l - Prims.int_one), l, l)
    | NonAssoc -> ((l - Prims.int_one), l, (l - Prims.int_one)) in
  FStarC_List.mapi
    (fun i uu___ ->
       match uu___ with
       | (assoc, tokens) -> ((levels_from_associativity i assoc), tokens))
    level_associativity_spec
let assign_levels (token_associativity_spec : associativity_level Prims.list)
  (s : Prims.string) : (Prims.int * Prims.int * Prims.int)=
  let uu___ = FStarC_List.tryFind (matches_level s) level_table in
  match uu___ with
  | FStar_Pervasives_Native.Some (assoc_levels, uu___1) -> assoc_levels
  | uu___1 -> failwith (Prims.strcat "Unrecognized operator " s)
let max_level (l : ('uuuuu * token Prims.list) Prims.list) : Prims.int=
  let find_level_and_max n level =
    let uu___ =
      FStarC_List.tryFind
        (fun uu___1 ->
           match uu___1 with
           | (uu___2, tokens) -> tokens = (FStar_Pervasives_Native.snd level))
        level_table in
    match uu___ with
    | FStar_Pervasives_Native.Some ((uu___1, l1, uu___2), uu___3) -> max n l1
    | FStar_Pervasives_Native.None ->
        let uu___1 =
          let uu___2 =
            let uu___3 =
              FStarC_List.map token_to_string
                (FStar_Pervasives_Native.snd level) in
            FStarC_String.concat "," uu___3 in
          FStarC_Format.fmt1 "Undefined associativity level %s" uu___2 in
        failwith uu___1 in
  FStarC_List.fold_left find_level_and_max Prims.int_zero l
let levels (op : Prims.string) : (Prims.int * Prims.int * Prims.int)=
  let uu___ = assign_levels level_associativity_spec op in
  match uu___ with
  | (left, mine, right) ->
      if op = "&"
      then ((left - Prims.int_one), mine, right)
      else (left, mine, right)
let operatorInfix0ad12 : associativity_level Prims.list=
  [opinfix0a; opinfix0b; opinfix0c; opinfix0d; opinfix1; opinfix2]
let is_operatorInfix0ad12 (op : FStarC_Ident.ident) : Prims.bool=
  let uu___ =
    let uu___1 =
      let uu___2 = FStarC_Ident.string_of_id op in matches_level uu___2 in
    FStarC_List.tryFind uu___1 operatorInfix0ad12 in
  uu___ <> FStar_Pervasives_Native.None
let is_operatorInfix34 : FStarC_Ident.ident -> Prims.bool=
  let opinfix34 = [opinfix3l; opinfix3r; opinfix4] in
  fun op ->
    let uu___ =
      let uu___1 =
        let uu___2 = FStarC_Ident.string_of_id op in matches_level uu___2 in
      FStarC_List.tryFind uu___1 opinfix34 in
    uu___ <> FStar_Pervasives_Native.None
let handleable_args_length (op : FStarC_Ident.ident) : Prims.int=
  let op_s = FStarC_Ident.string_of_id op in
  let uu___ = (is_general_prefix_op op) || (FStarC_List.mem op_s ["-"; "~"]) in
  if uu___
  then Prims.int_one
  else
    (let uu___2 =
       ((is_operatorInfix0ad12 op) || (is_operatorInfix34 op)) ||
         (FStarC_List.mem op_s
            ["<==>";
            "==>";
            "\\/";
            "/\\";
            "=";
            "|>";
            ":=";
            ".()";
            ".[]";
            ".(||)";
            ".[||]"]) in
     if uu___2
     then (Prims.of_int (2))
     else
       if FStarC_List.mem op_s [".()<-"; ".[]<-"; ".(||)<-"; ".[||]<-"]
       then (Prims.of_int (3))
       else Prims.int_zero)
let handleable_op (op : FStarC_Ident.ident) (args : 'uuuuu Prims.list) :
  Prims.bool=
  match FStarC_List.length args with
  | uu___ when uu___ = Prims.int_zero -> true
  | uu___ when uu___ = Prims.int_one ->
      (is_general_prefix_op op) ||
        (let uu___1 = FStarC_Ident.string_of_id op in
         FStarC_List.mem uu___1 ["-"; "~"])
  | uu___ when uu___ = (Prims.of_int (2)) ->
      ((is_operatorInfix0ad12 op) || (is_operatorInfix34 op)) ||
        (let uu___1 = FStarC_Ident.string_of_id op in
         FStarC_List.mem uu___1
           ["<==>";
           "==>";
           "\\/";
           "/\\";
           "=";
           "|>";
           ":=";
           ".()";
           ".[]";
           ".(||)";
           ".[||]"])
  | uu___ when uu___ = (Prims.of_int (3)) ->
      let uu___1 = FStarC_Ident.string_of_id op in
      FStarC_List.mem uu___1 [".()<-"; ".[]<-"; ".(||)<-"; ".[||]<-"]
  | uu___ -> false
type annotation_style =
  | Binders of (Prims.int * Prims.int * Prims.bool) 
  | Arrows of (Prims.int * Prims.int) 
let uu___is_Binders (projectee : annotation_style) : Prims.bool=
  match projectee with | Binders _0 -> true | uu___ -> false
let __proj__Binders__item___0 (projectee : annotation_style) :
  (Prims.int * Prims.int * Prims.bool)=
  match projectee with | Binders _0 -> _0
let uu___is_Arrows (projectee : annotation_style) : Prims.bool=
  match projectee with | Arrows _0 -> true | uu___ -> false
let __proj__Arrows__item___0 (projectee : annotation_style) :
  (Prims.int * Prims.int)= match projectee with | Arrows _0 -> _0
let all_binders_annot (e : FStarC_Parser_AST.term) : Prims.bool=
  let is_binder_annot b =
    match b.FStarC_Parser_AST.b with
    | FStarC_Parser_AST.Annotated uu___ -> true
    | uu___ -> false in
  let rec all_binders e1 l =
    match e1.FStarC_Parser_AST.tm with
    | FStarC_Parser_AST.Product (bs, tgt) ->
        let uu___ = FStarC_List.for_all is_binder_annot bs in
        if uu___
        then all_binders tgt (l + (FStarC_List.length bs))
        else (false, Prims.int_zero)
    | uu___ -> (true, (l + Prims.int_one)) in
  let uu___ = all_binders e Prims.int_zero in
  match uu___ with
  | (b, l) -> if b && (l > Prims.int_one) then true else false
type catf =
  FStar_Pprint.document -> FStar_Pprint.document -> FStar_Pprint.document
let cat_with_colon (x : FStar_Pprint.document) (y : FStar_Pprint.document) :
  FStar_Pprint.document=
  FStar_Pprint.op_Hat_Hat x
    (FStar_Pprint.op_Hat_Slash_Hat FStar_Pprint.colon y)
let comment_stack :
  (Prims.string * FStarC_Range_Type.range) Prims.list FStarC_Effect.ref=
  FStarC_Effect.mk_ref []
type decl_meta =
  {
  r: FStarC_Range_Type.range ;
  has_qs: Prims.bool ;
  has_attrs: Prims.bool }
let __proj__Mkdecl_meta__item__r (projectee : decl_meta) :
  FStarC_Range_Type.range=
  match projectee with | { r; has_qs; has_attrs;_} -> r
let __proj__Mkdecl_meta__item__has_qs (projectee : decl_meta) : Prims.bool=
  match projectee with | { r; has_qs; has_attrs;_} -> has_qs
let __proj__Mkdecl_meta__item__has_attrs (projectee : decl_meta) :
  Prims.bool= match projectee with | { r; has_qs; has_attrs;_} -> has_attrs
let dummy_meta : decl_meta=
  { r = FStarC_Range_Type.dummyRange; has_qs = false; has_attrs = false }
let with_comment (printer : 'uuuuu -> FStar_Pprint.document) (tm : 'uuuuu)
  (tmrange : FStarC_Range_Type.range) : FStar_Pprint.document=
  let rec comments_before_pos acc print_pos lookahead_pos =
    let uu___ = FStarC_Effect.op_Bang comment_stack in
    match uu___ with
    | [] -> (acc, false)
    | (c, crange)::cs ->
        let comment = FStar_Pprint.op_Hat_Hat (str c) FStar_Pprint.hardline in
        let uu___1 = FStarC_Range_Ops.range_before_pos crange print_pos in
        if uu___1
        then
          (FStarC_Effect.op_Colon_Equals comment_stack cs;
           comments_before_pos (FStar_Pprint.op_Hat_Hat acc comment)
             print_pos lookahead_pos)
        else
          (let uu___3 =
             FStarC_Range_Ops.range_before_pos crange lookahead_pos in
           (acc, uu___3)) in
  let uu___ =
    let uu___1 =
      let uu___2 = FStarC_Range_Ops.start_of_range tmrange in
      FStarC_Range_Ops.end_of_line uu___2 in
    let uu___2 = FStarC_Range_Ops.end_of_range tmrange in
    comments_before_pos FStar_Pprint.empty uu___1 uu___2 in
  match uu___ with
  | (comments, has_lookahead) ->
      let printed_e = printer tm in
      let comments1 =
        if has_lookahead
        then
          let pos = FStarC_Range_Ops.end_of_range tmrange in
          let uu___1 = comments_before_pos comments pos pos in
          FStar_Pervasives_Native.fst uu___1
        else comments in
      if comments1 = FStar_Pprint.empty
      then printed_e
      else FStar_Pprint.group (FStar_Pprint.op_Hat_Hat comments1 printed_e)
let with_comment_sep (printer : 'uuuuu -> 'uuuuu1) (tm : 'uuuuu)
  (tmrange : FStarC_Range_Type.range) : (FStar_Pprint.document * 'uuuuu1)=
  let rec comments_before_pos acc print_pos lookahead_pos =
    let uu___ = FStarC_Effect.op_Bang comment_stack in
    match uu___ with
    | [] -> (acc, false)
    | (c, crange)::cs ->
        let comment = str c in
        let uu___1 = FStarC_Range_Ops.range_before_pos crange print_pos in
        if uu___1
        then
          (FStarC_Effect.op_Colon_Equals comment_stack cs;
           comments_before_pos
             (if acc = FStar_Pprint.empty
              then comment
              else
                FStar_Pprint.op_Hat_Hat acc
                  (FStar_Pprint.op_Hat_Hat FStar_Pprint.hardline comment))
             print_pos lookahead_pos)
        else
          (let uu___3 =
             FStarC_Range_Ops.range_before_pos crange lookahead_pos in
           (acc, uu___3)) in
  let uu___ =
    let uu___1 =
      let uu___2 = FStarC_Range_Ops.start_of_range tmrange in
      FStarC_Range_Ops.end_of_line uu___2 in
    let uu___2 = FStarC_Range_Ops.end_of_range tmrange in
    comments_before_pos FStar_Pprint.empty uu___1 uu___2 in
  match uu___ with
  | (comments, has_lookahead) ->
      let printed_e = printer tm in
      let comments1 =
        if has_lookahead
        then
          let pos = FStarC_Range_Ops.end_of_range tmrange in
          let uu___1 = comments_before_pos comments pos pos in
          FStar_Pervasives_Native.fst uu___1
        else comments in
      (comments1, printed_e)
let rec place_comments_until_pos (k : Prims.int) (lbegin : Prims.int)
  (pos : FStarC_Range_Type.pos) (meta_decl : decl_meta)
  (doc : FStar_Pprint.document) (r : Prims.bool) (init : Prims.bool) :
  FStar_Pprint.document=
  let uu___ = FStarC_Effect.op_Bang comment_stack in
  match uu___ with
  | (comment, crange)::cs when FStarC_Range_Ops.range_before_pos crange pos
      ->
      (FStarC_Effect.op_Colon_Equals comment_stack cs;
       (let lnum =
          let uu___2 =
            let uu___3 =
              let uu___4 = FStarC_Range_Ops.start_of_range crange in
              FStarC_Range_Ops.line_of_pos uu___4 in
            uu___3 - lbegin in
          max k uu___2 in
        let lnum1 = min (Prims.of_int (2)) lnum in
        let doc1 =
          FStar_Pprint.op_Hat_Hat doc
            (FStar_Pprint.op_Hat_Hat
               (FStar_Pprint.repeat lnum1 FStar_Pprint.hardline)
               (str comment)) in
        let uu___2 =
          let uu___3 = FStarC_Range_Ops.end_of_range crange in
          FStarC_Range_Ops.line_of_pos uu___3 in
        place_comments_until_pos Prims.int_one uu___2 pos meta_decl doc1 true
          init))
  | uu___1 ->
      if doc = FStar_Pprint.empty
      then FStar_Pprint.empty
      else
        (let lnum =
           let uu___3 = FStarC_Range_Ops.line_of_pos pos in uu___3 - lbegin in
         let lnum1 = min (Prims.of_int (3)) lnum in
         let lnum2 =
           if meta_decl.has_qs || meta_decl.has_attrs
           then lnum1 - Prims.int_one
           else lnum1 in
         let lnum3 = max k lnum2 in
         let lnum4 =
           if meta_decl.has_qs && meta_decl.has_attrs
           then (Prims.of_int (2))
           else lnum3 in
         let lnum5 = if init then (Prims.of_int (2)) else lnum4 in
         FStar_Pprint.op_Hat_Hat doc
           (FStar_Pprint.repeat lnum5 FStar_Pprint.hardline))
let separate_map_with_comments (prefix : FStar_Pprint.document)
  (sep : FStar_Pprint.document) (f : 'uuuuu -> FStar_Pprint.document)
  (xs : 'uuuuu Prims.list) (extract_meta : 'uuuuu -> decl_meta) :
  FStar_Pprint.document=
  let fold_fun uu___ x =
    match uu___ with
    | (last_line, doc) ->
        let meta_decl = extract_meta x in
        let r = meta_decl.r in
        let doc1 =
          let uu___1 = FStarC_Range_Ops.start_of_range r in
          place_comments_until_pos Prims.int_one last_line uu___1 meta_decl
            doc false false in
        let uu___1 =
          let uu___2 = FStarC_Range_Ops.end_of_range r in
          FStarC_Range_Ops.line_of_pos uu___2 in
        let uu___2 =
          let uu___3 = let uu___4 = f x in FStar_Pprint.op_Hat_Hat sep uu___4 in
          FStar_Pprint.op_Hat_Hat doc1 uu___3 in
        (uu___1, uu___2) in
  let uu___ =
    let uu___1 = FStarC_List.hd xs in
    let uu___2 = FStarC_List.tl xs in (uu___1, uu___2) in
  match uu___ with
  | (x, xs1) ->
      let init =
        let meta_decl = extract_meta x in
        let uu___1 =
          let uu___2 = FStarC_Range_Ops.end_of_range meta_decl.r in
          FStarC_Range_Ops.line_of_pos uu___2 in
        let uu___2 =
          let uu___3 = f x in FStar_Pprint.op_Hat_Hat prefix uu___3 in
        (uu___1, uu___2) in
      let uu___1 = FStarC_List.fold_left fold_fun init xs1 in
      FStar_Pervasives_Native.snd uu___1
let separate_map_with_comments_kw (prefix : 'uuuuu) (sep : 'uuuuu)
  (f : 'uuuuu -> 'uuuuu1 -> FStar_Pprint.document) (xs : 'uuuuu1 Prims.list)
  (extract_meta : 'uuuuu1 -> decl_meta) : FStar_Pprint.document=
  let fold_fun uu___ x =
    match uu___ with
    | (last_line, doc) ->
        let meta_decl = extract_meta x in
        let r = meta_decl.r in
        let doc1 =
          let uu___1 = FStarC_Range_Ops.start_of_range r in
          place_comments_until_pos Prims.int_one last_line uu___1 meta_decl
            doc false false in
        let uu___1 =
          let uu___2 = FStarC_Range_Ops.end_of_range r in
          FStarC_Range_Ops.line_of_pos uu___2 in
        let uu___2 =
          let uu___3 = f sep x in FStar_Pprint.op_Hat_Hat doc1 uu___3 in
        (uu___1, uu___2) in
  let uu___ =
    let uu___1 = FStarC_List.hd xs in
    let uu___2 = FStarC_List.tl xs in (uu___1, uu___2) in
  match uu___ with
  | (x, xs1) ->
      let init =
        let meta_decl = extract_meta x in
        let uu___1 =
          let uu___2 = FStarC_Range_Ops.end_of_range meta_decl.r in
          FStarC_Range_Ops.line_of_pos uu___2 in
        let uu___2 = f prefix x in (uu___1, uu___2) in
      let uu___1 = FStarC_List.fold_left fold_fun init xs1 in
      FStar_Pervasives_Native.snd uu___1
let p_lidentOrOperator' (l : 'uuuuu) (s_l : 'uuuuu -> Prims.string)
  (p_l : 'uuuuu -> FStar_Pprint.document) : FStar_Pprint.document=
  let lstr = s_l l in
  if FStarC_Util.starts_with lstr "op_"
  then
    let uu___ = FStarC_Parser_AST.string_to_op lstr in
    match uu___ with
    | FStar_Pervasives_Native.None ->
        let uu___1 =
          let uu___2 = p_l l in FStar_Pprint.op_Hat_Hat uu___2 (str " )") in
        FStar_Pprint.op_Hat_Hat (str "( ") uu___1
    | FStar_Pervasives_Native.Some (s, uu___1) ->
        FStar_Pprint.op_Hat_Hat (str "( ")
          (FStar_Pprint.op_Hat_Hat (str s) (str " )"))
  else p_l l
let p_char_literal' (quote_char : FStar_Char.char)
  (c : FStarC_BaseTypes.char) : FStar_Pprint.document=
  str
    (match c with
     | 8 -> "\\b"
     | 12 -> "\\f"
     | 10 -> "\\n"
     | 9 -> "\\t"
     | 13 -> "\\r"
     | 11 -> "\\v"
     | 0 -> "\\0"
     | c1 ->
         let s = FStarC_Util.string_of_char c1 in
         if quote_char = c1 then Prims.strcat "\\" s else s)
let p_char_literal (c : FStarC_BaseTypes.char) : FStar_Pprint.document=
  let uu___ = p_char_literal' 39 c in FStar_Pprint.squotes uu___
let p_string_literal (s : Prims.string) : FStar_Pprint.document=
  let quotation_mark = 34 in
  let uu___ =
    FStarC_Pprint.concat_map (p_char_literal' quotation_mark)
      (FStar_String.list_of_string s) in
  FStar_Pprint.dquotes uu___
let string_of_id_or_underscore (lid : FStarC_Ident.ident) :
  FStar_Pprint.document=
  let uu___ =
    (let uu___1 = FStarC_Ident.string_of_id lid in
     FStarC_Util.starts_with uu___1 FStarC_Ident.reserved_prefix) &&
      (let uu___1 = FStarC_Options.print_real_names () in
       Prims.op_Negation uu___1) in
  if uu___
  then FStar_Pprint.underscore
  else (let uu___2 = FStarC_Ident.string_of_id lid in str uu___2)
let text_of_lid_or_underscore (lid : FStarC_Ident.lident) :
  FStar_Pprint.document=
  let uu___ =
    (let uu___1 =
       let uu___2 = FStarC_Ident.ident_of_lid lid in
       FStarC_Ident.string_of_id uu___2 in
     FStarC_Util.starts_with uu___1 FStarC_Ident.reserved_prefix) &&
      (let uu___1 = FStarC_Options.print_real_names () in
       Prims.op_Negation uu___1) in
  if uu___
  then FStar_Pprint.underscore
  else (let uu___2 = FStarC_Ident.string_of_lid lid in str uu___2)
let p_qlident (lid : FStarC_Ident.lident) : FStar_Pprint.document=
  text_of_lid_or_underscore lid
let p_quident (lid : FStarC_Ident.lident) : FStar_Pprint.document=
  text_of_lid_or_underscore lid
let p_ident (lid : FStarC_Ident.ident) : FStar_Pprint.document=
  string_of_id_or_underscore lid
let p_lident (lid : FStarC_Ident.ident) : FStar_Pprint.document=
  string_of_id_or_underscore lid
let p_uident (lid : FStarC_Ident.ident) : FStar_Pprint.document=
  string_of_id_or_underscore lid
let p_tvar (lid : FStarC_Ident.ident) : FStar_Pprint.document=
  string_of_id_or_underscore lid
let p_qlidentOrOperator (lid : FStarC_Ident.lident) : FStar_Pprint.document=
  p_lidentOrOperator' lid FStarC_Ident.string_of_lid p_qlident
let p_lidentOrOperator (lid : FStarC_Ident.ident) : FStar_Pprint.document=
  p_lidentOrOperator' lid FStarC_Ident.string_of_id p_lident
let rec p_decl (d : FStarC_Parser_AST.decl) : FStar_Pprint.document=
  let qualifiers =
    match ((d.FStarC_Parser_AST.quals), (d.FStarC_Parser_AST.d)) with
    | ((FStarC_Parser_AST.Assumption)::[], FStarC_Parser_AST.Assume
       (id, uu___)) ->
        let uu___1 =
          let uu___2 =
            let uu___3 = FStarC_Ident.string_of_id id in
            FStarC_Util.char_at uu___3 Prims.int_zero in
          FStarC_Util.is_upper uu___2 in
        if uu___1
        then
          let uu___2 = p_qualifier FStarC_Parser_AST.Assumption in
          FStar_Pprint.op_Hat_Hat uu___2 FStar_Pprint.space
        else p_qualifiers d.FStarC_Parser_AST.quals
    | uu___ -> p_qualifiers d.FStarC_Parser_AST.quals in
  let uu___ = p_attributes true d.FStarC_Parser_AST.attrs in
  let uu___1 =
    let uu___2 = p_rawDecl d in FStar_Pprint.op_Hat_Hat qualifiers uu___2 in
  FStar_Pprint.op_Hat_Hat uu___ uu___1
and p_attributes (isTopLevel : Prims.bool)
  (attrs : FStarC_Parser_AST.attributes_) : FStar_Pprint.document=
  match attrs with
  | [] -> FStar_Pprint.empty
  | uu___ ->
      let uu___1 =
        let uu___2 =
          let uu___3 =
            let uu___4 =
              let uu___5 =
                let uu___6 =
                  FStarC_List.map (p_noSeqTermAndComment false false) attrs in
                FStar_Pprint.flow (str "; ") uu___6 in
              FStar_Pprint.op_Hat_Hat uu___5 FStar_Pprint.rbracket in
            FStar_Pprint.align uu___4 in
          FStar_Pprint.op_Hat_Hat uu___3
            (if isTopLevel then FStar_Pprint.hardline else FStar_Pprint.empty) in
        FStar_Pprint.op_Hat_Hat (str (if isTopLevel then "@@ " else "@@@ "))
          uu___2 in
      FStar_Pprint.op_Hat_Hat FStar_Pprint.lbracket uu___1
and p_justSig (d : FStarC_Parser_AST.decl) : FStar_Pprint.document=
  match d.FStarC_Parser_AST.d with
  | FStarC_Parser_AST.Val (lid, t) ->
      let uu___ =
        let uu___1 =
          let uu___2 =
            let uu___3 = p_lidentOrOperator lid in
            FStar_Pprint.op_Hat_Hat uu___3
              (FStar_Pprint.op_Hat_Hat FStar_Pprint.space FStar_Pprint.colon) in
          FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu___2 in
        FStar_Pprint.op_Hat_Hat (str "val") uu___1 in
      let uu___1 = p_typ false false t in
      FStar_Pprint.op_Hat_Hat uu___ uu___1
  | FStarC_Parser_AST.TopLevelLet (uu___, lbs) ->
      FStarC_Pprint.separate_map FStar_Pprint.hardline
        (fun lb ->
           let uu___1 = p_letlhs (str "let") lb false in
           FStar_Pprint.group uu___1) lbs
  | uu___ -> FStar_Pprint.empty
and p_list :
  't .
    ('t -> FStar_Pprint.document) ->
      FStar_Pprint.document -> 't Prims.list -> FStar_Pprint.document
  =
  fun f sep l ->
    let rec p_list' uu___ =
      match uu___ with
      | [] -> FStar_Pprint.empty
      | x::[] -> f x
      | x::xs ->
          let uu___1 = f x in
          let uu___2 =
            let uu___3 = p_list' xs in FStar_Pprint.op_Hat_Hat sep uu___3 in
          FStar_Pprint.op_Hat_Hat uu___1 uu___2 in
    let uu___ =
      let uu___1 = p_list' l in FStar_Pprint.op_Hat_Hat uu___1 (str "]") in
    FStar_Pprint.op_Hat_Hat (str "[") uu___
and p_restriction (uu___ : FStarC_Syntax_Syntax.restriction) :
  FStar_Pprint.document=
  match uu___ with
  | FStarC_Syntax_Syntax.Unrestricted -> FStar_Pprint.empty
  | FStarC_Syntax_Syntax.AllowList ids ->
      let uu___1 =
        let uu___2 =
          let uu___3 =
            p_list
              (fun uu___4 ->
                 match uu___4 with
                 | (id, renamed) ->
                     let uu___5 = p_ident id in
                     let uu___6 = FStarC_Pprint.optional p_ident renamed in
                     FStar_Pprint.op_Hat_Slash_Hat uu___5 uu___6) (str ", ")
              ids in
          FStar_Pprint.op_Hat_Hat uu___3 FStar_Pprint.rbrace in
        FStar_Pprint.op_Hat_Hat FStar_Pprint.lbrace uu___2 in
      FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu___1
and p_rawDecl (d : FStarC_Parser_AST.decl) : FStar_Pprint.document=
  match d.FStarC_Parser_AST.d with
  | FStarC_Parser_AST.Open (uid, r) ->
      let uu___ =
        let uu___1 =
          let uu___2 = p_quident uid in
          let uu___3 = p_restriction r in
          FStar_Pprint.op_Hat_Slash_Hat uu___2 uu___3 in
        FStar_Pprint.op_Hat_Slash_Hat (str "open") uu___1 in
      FStar_Pprint.group uu___
  | FStarC_Parser_AST.Include (uid, r) ->
      let uu___ =
        let uu___1 =
          let uu___2 = p_quident uid in
          let uu___3 = p_restriction r in
          FStar_Pprint.op_Hat_Slash_Hat uu___2 uu___3 in
        FStar_Pprint.op_Hat_Slash_Hat (str "include") uu___1 in
      FStar_Pprint.group uu___
  | FStarC_Parser_AST.Friend uid ->
      let uu___ =
        let uu___1 = p_quident uid in
        FStar_Pprint.op_Hat_Slash_Hat (str "friend") uu___1 in
      FStar_Pprint.group uu___
  | FStarC_Parser_AST.ModuleAbbrev (uid1, uid2) ->
      let uu___ =
        let uu___1 =
          let uu___2 =
            let uu___3 = p_uident uid1 in
            FStar_Pprint.op_Hat_Hat uu___3
              (FStar_Pprint.op_Hat_Hat FStar_Pprint.space FStar_Pprint.equals) in
          FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu___2 in
        FStar_Pprint.op_Hat_Hat (str "module") uu___1 in
      let uu___1 = p_quident uid2 in op_Hat_Slash_Plus_Hat uu___ uu___1
  | FStarC_Parser_AST.TopLevelModule uid ->
      let uu___ =
        let uu___1 =
          let uu___2 = p_quident uid in
          FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu___2 in
        FStar_Pprint.op_Hat_Hat (str "module") uu___1 in
      FStar_Pprint.group uu___
  | FStarC_Parser_AST.Tycon
      (true, uu___, (FStarC_Parser_AST.TyconAbbrev
       (uid, tpars, FStar_Pervasives_Native.None, t))::[])
      ->
      let effect_prefix_doc =
        let uu___1 =
          let uu___2 = p_uident uid in
          FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu___2 in
        FStar_Pprint.op_Hat_Hat (str "effect") uu___1 in
      let uu___1 =
        let uu___2 = p_typars tpars in
        FStar_Pprint.surround (Prims.of_int (2)) Prims.int_one
          effect_prefix_doc uu___2 FStar_Pprint.equals in
      let uu___2 = p_typ false false t in op_Hat_Slash_Plus_Hat uu___1 uu___2
  | FStarC_Parser_AST.Tycon (false, tc, tcdefs) ->
      let s = if tc then str "class" else str "type" in
      let uu___ =
        let uu___1 = FStarC_List.hd tcdefs in p_typeDeclWithKw s uu___1 in
      let uu___1 =
        let uu___2 = FStarC_List.tl tcdefs in
        FStarC_Pprint.concat_map
          (fun x ->
             let uu___3 = p_typeDeclWithKw (str "and") x in
             FStar_Pprint.op_Hat_Hat break1 uu___3) uu___2 in
      FStar_Pprint.op_Hat_Hat uu___ uu___1
  | FStarC_Parser_AST.TopLevelLet (q, lbs) ->
      let let_doc =
        let uu___ = p_letqualifier q in
        FStar_Pprint.op_Hat_Hat (str "let") uu___ in
      separate_map_with_comments_kw let_doc (str "and") p_letbinding lbs
        (fun uu___ ->
           match uu___ with
           | (p, t) ->
               let uu___1 =
                 FStarC_Range_Ops.union_ranges p.FStarC_Parser_AST.prange
                   t.FStarC_Parser_AST.range in
               { r = uu___1; has_qs = false; has_attrs = false })
  | FStarC_Parser_AST.Val (lid, t) ->
      let uu___ =
        let uu___1 =
          let uu___2 =
            let uu___3 = p_lidentOrOperator lid in
            let uu___4 = sig_as_binders_if_possible t false in
            FStar_Pprint.op_Hat_Hat uu___3 uu___4 in
          FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu___2 in
        FStar_Pprint.op_Hat_Hat (str "val") uu___1 in
      FStar_Pprint.group uu___
  | FStarC_Parser_AST.Assume (id, t) ->
      let decl_keyword =
        let uu___ =
          let uu___1 =
            let uu___2 = FStarC_Ident.string_of_id id in
            FStarC_Util.char_at uu___2 Prims.int_zero in
          FStarC_Util.is_upper uu___1 in
        if uu___
        then FStar_Pprint.empty
        else FStar_Pprint.op_Hat_Hat (str "val") FStar_Pprint.space in
      let uu___ =
        let uu___1 = p_ident id in
        let uu___2 =
          let uu___3 =
            let uu___4 =
              let uu___5 = p_typ false false t in
              FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu___5 in
            FStar_Pprint.op_Hat_Hat FStar_Pprint.colon uu___4 in
          FStar_Pprint.group uu___3 in
        FStar_Pprint.op_Hat_Hat uu___1 uu___2 in
      FStar_Pprint.op_Hat_Hat decl_keyword uu___
  | FStarC_Parser_AST.Exception (uid, t_opt) ->
      let uu___ =
        let uu___1 =
          let uu___2 = p_uident uid in
          let uu___3 =
            FStarC_Pprint.optional
              (fun t ->
                 let uu___4 =
                   let uu___5 = p_typ false false t in
                   op_Hat_Slash_Plus_Hat (str "of") uu___5 in
                 FStar_Pprint.op_Hat_Hat break1 uu___4) t_opt in
          FStar_Pprint.op_Hat_Hat uu___2 uu___3 in
        FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu___1 in
      FStar_Pprint.op_Hat_Hat (str "exception") uu___
  | FStarC_Parser_AST.NewEffect ne ->
      let uu___ =
        let uu___1 = p_newEffect ne in
        FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu___1 in
      FStar_Pprint.op_Hat_Hat (str "new_effect") uu___
  | FStarC_Parser_AST.SubEffect se ->
      let uu___ =
        let uu___1 = p_subEffect se in
        FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu___1 in
      FStar_Pprint.op_Hat_Hat (str "sub_effect") uu___
  | FStarC_Parser_AST.LayeredEffect ne ->
      let uu___ =
        let uu___1 = p_newEffect ne in
        FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu___1 in
      FStar_Pprint.op_Hat_Hat (str "layered_effect") uu___
  | FStarC_Parser_AST.Polymonadic_bind (l1, l2, l3, t) ->
      let uu___ =
        let uu___1 =
          let uu___2 = p_quident l1 in
          let uu___3 =
            let uu___4 =
              let uu___5 =
                let uu___6 = p_quident l2 in
                let uu___7 =
                  let uu___8 =
                    let uu___9 =
                      let uu___10 = p_quident l3 in
                      let uu___11 =
                        let uu___12 = p_simpleTerm false false t in
                        FStar_Pprint.op_Hat_Hat FStar_Pprint.equals uu___12 in
                      FStar_Pprint.op_Hat_Hat uu___10 uu___11 in
                    FStar_Pprint.op_Hat_Hat (str "|>") uu___9 in
                  FStar_Pprint.op_Hat_Hat FStar_Pprint.rparen uu___8 in
                FStar_Pprint.op_Hat_Hat uu___6 uu___7 in
              FStar_Pprint.op_Hat_Hat break1 uu___5 in
            FStar_Pprint.op_Hat_Hat FStar_Pprint.comma uu___4 in
          FStar_Pprint.op_Hat_Hat uu___2 uu___3 in
        FStar_Pprint.op_Hat_Hat FStar_Pprint.lparen uu___1 in
      FStar_Pprint.op_Hat_Hat (str "polymonadic_bind") uu___
  | FStarC_Parser_AST.Pragma p -> p_pragma p
  | FStarC_Parser_AST.Tycon (true, uu___, uu___1) ->
      failwith
        "Effect abbreviation is expected to be defined by an abbreviation"
  | FStarC_Parser_AST.Splice (is_typed, ids, t) ->
      let uu___ =
        let uu___1 =
          let uu___2 = p_list p_uident (str ";") ids in
          let uu___3 =
            let uu___4 = p_term false false t in
            FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu___4 in
          FStar_Pprint.op_Hat_Hat uu___2 uu___3 in
        FStar_Pprint.op_Hat_Hat
          (if is_typed then str "_t" else FStar_Pprint.empty) uu___1 in
      FStar_Pprint.op_Hat_Hat (str "%splice") uu___
  | FStarC_Parser_AST.DeclSyntaxExtension (tag, blob, blob_rng, start_rng) ->
      FStar_Pprint.op_Hat_Hat
        (FStar_Pprint.doc_of_string (Prims.strcat "```" tag))
        (FStar_Pprint.op_Hat_Hat (FStar_Pprint.arbitrary_string blob)
           (FStar_Pprint.doc_of_string "```"))
  | FStarC_Parser_AST.DeclToBeDesugared tbs ->
      let uu___ = tbs.FStarC_Parser_AST.to_string tbs.FStarC_Parser_AST.blob in
      FStar_Pprint.arbitrary_string uu___
and p_pragma (uu___ : FStarC_Parser_AST.pragma) : FStar_Pprint.document=
  match uu___ with
  | FStarC_Parser_AST.ShowOptions -> str "#show-options"
  | FStarC_Parser_AST.SetOptions s ->
      FStar_Pprint.op_Hat_Hat (str "#set-options")
        (FStar_Pprint.op_Hat_Hat FStar_Pprint.space
           (FStar_Pprint.dquotes (str s)))
  | FStarC_Parser_AST.ResetOptions s_opt ->
      let uu___1 =
        FStarC_Pprint.optional
          (fun s ->
             FStar_Pprint.op_Hat_Hat FStar_Pprint.space
               (FStar_Pprint.dquotes (str s))) s_opt in
      FStar_Pprint.op_Hat_Hat (str "#reset-options") uu___1
  | FStarC_Parser_AST.PushOptions s_opt ->
      let uu___1 =
        FStarC_Pprint.optional
          (fun s ->
             FStar_Pprint.op_Hat_Hat FStar_Pprint.space
               (FStar_Pprint.dquotes (str s))) s_opt in
      FStar_Pprint.op_Hat_Hat (str "#push-options") uu___1
  | FStarC_Parser_AST.PopOptions -> str "#pop-options"
  | FStarC_Parser_AST.RestartSolver -> str "#restart-solver"
  | FStarC_Parser_AST.PrintEffectsGraph -> str "#print-effects-graph"
  | FStarC_Parser_AST.Check t ->
      let uu___1 = p_term false false t in
      FStar_Pprint.op_Hat_Slash_Hat (str "#check") uu___1
and p_typars (bs : FStarC_Parser_AST.binder Prims.list) :
  FStar_Pprint.document= p_binders true bs
and p_typeDeclWithKw (kw : FStar_Pprint.document)
  (typedecl : FStarC_Parser_AST.tycon) : FStar_Pprint.document=
  let uu___ = p_typeDecl kw typedecl in
  match uu___ with
  | (comm, decl, body, pre) ->
      if comm = FStar_Pprint.empty
      then let uu___1 = pre body in FStar_Pprint.op_Hat_Hat decl uu___1
      else
        (let uu___2 =
           let uu___3 =
             let uu___4 =
               let uu___5 = pre body in
               FStar_Pprint.op_Hat_Slash_Hat uu___5 comm in
             FStar_Pprint.op_Hat_Hat decl uu___4 in
           FStar_Pprint.ifflat uu___3
             (FStar_Pprint.op_Hat_Hat decl
                (FStar_Pprint.nest (Prims.of_int (2))
                   (FStar_Pprint.op_Hat_Hat FStar_Pprint.hardline
                      (FStar_Pprint.op_Hat_Hat comm
                         (FStar_Pprint.op_Hat_Hat FStar_Pprint.hardline body))))) in
         FStar_Pprint.group uu___2)
and p_typeDecl (pre : FStar_Pprint.document)
  (uu___ : FStarC_Parser_AST.tycon) :
  (FStar_Pprint.document * FStar_Pprint.document * FStar_Pprint.document *
    (FStar_Pprint.document -> FStar_Pprint.document))=
  match uu___ with
  | FStarC_Parser_AST.TyconAbstract (lid, bs, typ_opt) ->
      let uu___1 = p_typeDeclPrefix pre false lid bs typ_opt in
      (FStar_Pprint.empty, uu___1, FStar_Pprint.empty, ((fun x -> x)))
  | FStarC_Parser_AST.TyconAbbrev (lid, bs, typ_opt, t) ->
      let uu___1 = p_typ_sep false false t in
      (match uu___1 with
       | (comm, doc) ->
           let uu___2 = p_typeDeclPrefix pre true lid bs typ_opt in
           (comm, uu___2, doc, jump2))
  | FStarC_Parser_AST.TyconRecord
      (lid, bs, typ_opt, attrs, record_field_decls) ->
      let uu___1 = p_typeDeclPrefix pre true lid bs typ_opt in
      let uu___2 =
        let uu___3 = p_attributes false attrs in
        let uu___4 = p_typeDeclRecord record_field_decls in
        FStar_Pprint.op_Hat_Hat uu___3 uu___4 in
      (FStar_Pprint.empty, uu___1, uu___2,
        ((fun d -> FStar_Pprint.op_Hat_Hat FStar_Pprint.space d)))
  | FStarC_Parser_AST.TyconVariant (lid, bs, typ_opt, ct_decls) ->
      let p_constructorBranchAndComments uu___1 =
        match uu___1 with
        | (uid, payload, attrs) ->
            let range =
              let uu___2 =
                let uu___3 = FStarC_Ident.range_of_id uid in
                let uu___4 =
                  FStarC_Option.bind payload
                    (fun uu___5 ->
                       match uu___5 with
                       | FStarC_Parser_AST.VpOfNotation t ->
                           FStar_Pervasives_Native.Some
                             (t.FStarC_Parser_AST.range)
                       | FStarC_Parser_AST.VpArbitrary t ->
                           FStar_Pervasives_Native.Some
                             (t.FStarC_Parser_AST.range)
                       | FStarC_Parser_AST.VpRecord (record, uu___6) ->
                           FStar_Pervasives_Native.None) in
                FStarC_Option.dflt uu___3 uu___4 in
              FStarC_Range_Ops.extend_to_end_of_line uu___2 in
            let uu___2 =
              with_comment_sep p_constructorBranch (uid, payload, attrs)
                range in
            (match uu___2 with
             | (comm, ctor) ->
                 inline_comment_or_above comm ctor FStar_Pprint.empty) in
      let datacon_doc =
        FStarC_Pprint.separate_map FStar_Pprint.hardline
          p_constructorBranchAndComments ct_decls in
      let uu___1 = p_typeDeclPrefix pre true lid bs typ_opt in
      (FStar_Pprint.empty, uu___1, datacon_doc, jump2)
and p_typeDeclRecord (fields : FStarC_Parser_AST.tycon_record) :
  FStar_Pprint.document=
  let p_recordField ps uu___ =
    match uu___ with
    | (lid, aq, attrs, t) ->
        let uu___1 =
          let uu___2 =
            FStarC_Range_Ops.extend_to_end_of_line t.FStarC_Parser_AST.range in
          with_comment_sep (p_recordFieldDecl ps) (lid, aq, attrs, t) uu___2 in
        (match uu___1 with
         | (comm, field) ->
             let sep = if ps then FStar_Pprint.semi else FStar_Pprint.empty in
             inline_comment_or_above comm field sep) in
  let uu___ = separate_map_last FStar_Pprint.hardline p_recordField fields in
  braces_with_nesting uu___
and p_typeDeclPrefix (kw : FStar_Pprint.document) (eq : Prims.bool)
  (lid : FStarC_Ident.ident) (bs : FStarC_Parser_AST.binder Prims.list)
  (typ_opt : FStarC_Parser_AST.knd FStar_Pervasives_Native.option) :
  FStar_Pprint.document=
  let with_kw cont =
    let lid_doc = p_ident lid in
    let kw_lid =
      FStar_Pprint.group (FStar_Pprint.op_Hat_Slash_Hat kw lid_doc) in
    cont kw_lid in
  let typ =
    let maybe_eq = if eq then FStar_Pprint.equals else FStar_Pprint.empty in
    match typ_opt with
    | FStar_Pervasives_Native.None -> maybe_eq
    | FStar_Pervasives_Native.Some t ->
        let uu___ =
          let uu___1 =
            let uu___2 = p_typ false false t in
            FStar_Pprint.op_Hat_Slash_Hat uu___2 maybe_eq in
          FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu___1 in
        FStar_Pprint.op_Hat_Hat FStar_Pprint.colon uu___ in
  if bs = []
  then with_kw (fun n -> prefix2 n typ)
  else
    (let binders = p_binders_list true bs in
     with_kw
       (fun n -> prefix2 (prefix2 n (FStar_Pprint.flow break1 binders)) typ))
and p_recordFieldDecl (ps : Prims.bool)
  (uu___ :
    (FStarC_Ident.ident * FStarC_Parser_AST.aqual *
      FStarC_Parser_AST.attributes_ * FStarC_Parser_AST.term))
  : FStar_Pprint.document=
  match uu___ with
  | (lid, aq, attrs, t) ->
      let uu___1 =
        let uu___2 = FStarC_Pprint.optional p_aqual aq in
        let uu___3 =
          let uu___4 = p_attributes false attrs in
          let uu___5 =
            let uu___6 = p_lidentOrOperator lid in
            let uu___7 =
              let uu___8 = p_typ ps false t in
              FStar_Pprint.op_Hat_Hat FStar_Pprint.colon uu___8 in
            FStar_Pprint.op_Hat_Hat uu___6 uu___7 in
          FStar_Pprint.op_Hat_Hat uu___4 uu___5 in
        FStar_Pprint.op_Hat_Hat uu___2 uu___3 in
      FStar_Pprint.group uu___1
and p_constructorBranch
  (uu___ :
    (FStarC_Ident.ident * FStarC_Parser_AST.constructor_payload
      FStar_Pervasives_Native.option * FStarC_Parser_AST.attributes_))
  : FStar_Pprint.document=
  match uu___ with
  | (uid, variant, attrs) ->
      let h isOf t =
        let uu___1 =
          let uu___2 = p_typ false false t in
          FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu___2 in
        FStar_Pprint.op_Hat_Hat
          (if isOf then str "of" else FStar_Pprint.colon) uu___1 in
      let uu___1 =
        let uu___2 =
          let uu___3 =
            let uu___4 =
              let uu___5 = p_attributes false attrs in
              let uu___6 = p_uident uid in
              FStar_Pprint.op_Hat_Hat uu___5 uu___6 in
            FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu___4 in
          FStar_Pprint.op_Hat_Hat FStar_Pprint.bar uu___3 in
        FStar_Pprint.group uu___2 in
      let uu___2 =
        default_or_map FStar_Pprint.empty
          (fun payload ->
             let uu___3 =
               let uu___4 =
                 match payload with
                 | FStarC_Parser_AST.VpOfNotation t -> h true t
                 | FStarC_Parser_AST.VpArbitrary t -> h false t
                 | FStarC_Parser_AST.VpRecord (r, t) ->
                     let uu___5 = p_typeDeclRecord r in
                     let uu___6 =
                       default_or_map FStar_Pprint.empty (h false) t in
                     FStar_Pprint.op_Hat_Hat uu___5 uu___6 in
               FStar_Pprint.group uu___4 in
             FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu___3) variant in
      FStar_Pprint.op_Hat_Hat uu___1 uu___2
and p_letlhs (kw : FStar_Pprint.document)
  (uu___ : (FStarC_Parser_AST.pattern * FStarC_Parser_AST.term))
  (inner_let : Prims.bool) : FStar_Pprint.document=
  match uu___ with
  | (pat, uu___1) ->
      let uu___2 =
        match pat.FStarC_Parser_AST.pat with
        | FStarC_Parser_AST.PatAscribed
            (pat1, (t, FStar_Pervasives_Native.None)) ->
            (pat1, (FStar_Pervasives_Native.Some (t, FStar_Pprint.empty)))
        | FStarC_Parser_AST.PatAscribed
            (pat1, (t, FStar_Pervasives_Native.Some tac)) ->
            let uu___3 =
              let uu___4 =
                let uu___5 =
                  let uu___6 =
                    let uu___7 =
                      let uu___8 =
                        let uu___9 = p_atomicTerm (maybe_unthunk tac) in
                        FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu___9 in
                      FStar_Pprint.op_Hat_Hat (str "by") uu___8 in
                    FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu___7 in
                  FStar_Pprint.group uu___6 in
                (t, uu___5) in
              FStar_Pervasives_Native.Some uu___4 in
            (pat1, uu___3)
        | uu___3 -> (pat, FStar_Pervasives_Native.None) in
      (match uu___2 with
       | (pat1, ascr) ->
           (match pat1.FStarC_Parser_AST.pat with
            | FStarC_Parser_AST.PatApp
                ({
                   FStarC_Parser_AST.pat = FStarC_Parser_AST.PatVar
                     (lid, uu___3, uu___4);
                   FStarC_Parser_AST.prange = uu___5;_},
                 pats)
                ->
                let ascr_doc =
                  match ascr with
                  | FStar_Pervasives_Native.Some (t, tac) ->
                      let uu___6 = sig_as_binders_if_possible t true in
                      FStar_Pprint.op_Hat_Hat uu___6 tac
                  | FStar_Pervasives_Native.None -> FStar_Pprint.empty in
                let uu___6 =
                  if inner_let
                  then
                    let uu___7 = pats_as_binders_if_possible pats in
                    match uu___7 with | (bs, style) -> (bs, style)
                  else
                    (let uu___8 = pats_as_binders_if_possible pats in
                     match uu___8 with | (bs, style) -> (bs, style)) in
                (match uu___6 with
                 | (terms, style) ->
                     let uu___7 =
                       let uu___8 =
                         let uu___9 =
                           let uu___10 = p_lidentOrOperator lid in
                           let uu___11 =
                             format_sig style terms ascr_doc true true in
                           FStar_Pprint.op_Hat_Hat uu___10 uu___11 in
                         FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu___9 in
                       FStar_Pprint.op_Hat_Hat kw uu___8 in
                     FStar_Pprint.group uu___7)
            | uu___3 ->
                let ascr_doc =
                  match ascr with
                  | FStar_Pervasives_Native.Some (t, tac) ->
                      let uu___4 =
                        let uu___5 =
                          let uu___6 =
                            p_typ_top
                              (Arrows
                                 ((Prims.of_int (2)), (Prims.of_int (2))))
                              false false t in
                          FStar_Pprint.op_Hat_Hat FStar_Pprint.colon uu___6 in
                        FStar_Pprint.group uu___5 in
                      FStar_Pprint.op_Hat_Hat uu___4 tac
                  | FStar_Pervasives_Native.None -> FStar_Pprint.empty in
                let uu___4 =
                  let uu___5 =
                    let uu___6 =
                      let uu___7 = p_tuplePattern pat1 in
                      FStar_Pprint.op_Hat_Slash_Hat kw uu___7 in
                    FStar_Pprint.group uu___6 in
                  FStar_Pprint.op_Hat_Hat uu___5 ascr_doc in
                FStar_Pprint.group uu___4))
and p_letbinding (kw : FStar_Pprint.document)
  (uu___ : (FStarC_Parser_AST.pattern * FStarC_Parser_AST.term)) :
  FStar_Pprint.document=
  match uu___ with
  | (pat, e) ->
      let doc_pat = p_letlhs kw (pat, e) false in
      let uu___1 = p_term_sep false false e in
      (match uu___1 with
       | (comm, doc_expr) ->
           let doc_expr1 =
             inline_comment_or_above comm doc_expr FStar_Pprint.empty in
           FStar_Pprint.ifflat
             (FStar_Pprint.op_Hat_Slash_Hat doc_pat
                (FStar_Pprint.op_Hat_Slash_Hat FStar_Pprint.equals doc_expr1))
             (FStar_Pprint.op_Hat_Hat doc_pat
                (FStar_Pprint.op_Hat_Hat FStar_Pprint.space
                   (FStar_Pprint.group
                      (FStar_Pprint.op_Hat_Hat FStar_Pprint.equals
                         (jump2 doc_expr1))))))
and p_term_list (ps : Prims.bool) (pb : Prims.bool)
  (l : FStarC_Parser_AST.term Prims.list) : FStar_Pprint.document=
  let rec aux uu___ =
    match uu___ with
    | [] -> FStar_Pprint.empty
    | x::[] -> p_term ps pb x
    | x::xs ->
        let uu___1 = p_term ps pb x in
        let uu___2 =
          let uu___3 = aux xs in FStar_Pprint.op_Hat_Hat (str ";") uu___3 in
        FStar_Pprint.op_Hat_Hat uu___1 uu___2 in
  let uu___ = let uu___1 = aux l in FStar_Pprint.op_Hat_Hat uu___1 (str "]") in
  FStar_Pprint.op_Hat_Hat (str "[") uu___
and p_newEffect (uu___ : FStarC_Parser_AST.effect_decl) :
  FStar_Pprint.document=
  match uu___ with
  | FStarC_Parser_AST.RedefineEffect (lid, bs, t) ->
      p_effectRedefinition lid bs t
  | FStarC_Parser_AST.DefineEffect (lid, bs, t, eff_decls) ->
      p_effectDefinition lid bs t eff_decls
and p_effectRedefinition (uid : FStarC_Ident.ident)
  (bs : FStarC_Parser_AST.binder Prims.list) (t : FStarC_Parser_AST.term) :
  FStar_Pprint.document=
  let uu___ = p_uident uid in
  let uu___1 = p_binders true bs in
  let uu___2 =
    let uu___3 = p_simpleTerm false false t in
    prefix2 FStar_Pprint.equals uu___3 in
  surround_maybe_empty (Prims.of_int (2)) Prims.int_one uu___ uu___1 uu___2
and p_effectDefinition (uid : FStarC_Ident.ident)
  (bs : FStarC_Parser_AST.binder Prims.list) (t : FStarC_Parser_AST.term)
  (eff_decls : FStarC_Parser_AST.decl Prims.list) : FStar_Pprint.document=
  let binders = p_binders true bs in
  let uu___ =
    let uu___1 =
      let uu___2 =
        let uu___3 = p_uident uid in
        let uu___4 = p_binders true bs in
        let uu___5 =
          let uu___6 = p_typ false false t in
          prefix2 FStar_Pprint.colon uu___6 in
        surround_maybe_empty (Prims.of_int (2)) Prims.int_one uu___3 uu___4
          uu___5 in
      FStar_Pprint.group uu___2 in
    let uu___2 =
      let uu___3 =
        let uu___4 =
          let uu___5 =
            let uu___6 =
              separate_map_last
                (FStar_Pprint.op_Hat_Hat FStar_Pprint.hardline
                   (FStar_Pprint.op_Hat_Hat FStar_Pprint.semi
                      FStar_Pprint.space)) p_effectDecl eff_decls in
            FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu___6 in
          FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu___5 in
        FStar_Pprint.op_Hat_Hat FStar_Pprint.hardline uu___4 in
      FStar_Pprint.op_Hat_Hat (str "with") uu___3 in
    FStar_Pprint.op_Hat_Slash_Hat uu___1 uu___2 in
  braces_with_nesting uu___
and p_effectDecl (ps : Prims.bool) (d : FStarC_Parser_AST.decl) :
  FStar_Pprint.document=
  match d.FStarC_Parser_AST.d with
  | FStarC_Parser_AST.Tycon
      (false, uu___, (FStarC_Parser_AST.TyconAbbrev
       (lid, [], FStar_Pervasives_Native.None, e))::[])
      ->
      let uu___1 =
        let uu___2 = p_lident lid in
        FStar_Pprint.op_Hat_Hat uu___2
          (FStar_Pprint.op_Hat_Hat FStar_Pprint.space FStar_Pprint.equals) in
      let uu___2 = p_simpleTerm ps false e in prefix2 uu___1 uu___2
  | uu___ ->
      let uu___1 =
        let uu___2 = FStarC_Class_Show.show FStarC_Parser_AST.showable_decl d in
        FStarC_Format.fmt1
          "Not a declaration of an effect member... or at least I hope so : %s"
          uu___2 in
      failwith uu___1
and p_subEffect (lift : FStarC_Parser_AST.lift) : FStar_Pprint.document=
  let lift_op_doc =
    let lifts =
      match lift.FStarC_Parser_AST.lift_op with
      | FStarC_Parser_AST.NonReifiableLift t -> [("lift_wp", t)]
      | FStarC_Parser_AST.ReifiableLift (t1, t2) ->
          [("lift_wp", t1); ("lift", t2)]
      | FStarC_Parser_AST.LiftForFree t -> [("lift", t)] in
    let p_lift ps uu___ =
      match uu___ with
      | (kwd, t) ->
          let uu___1 = p_simpleTerm ps false t in
          prefix2
            (FStar_Pprint.op_Hat_Hat (str kwd)
               (FStar_Pprint.op_Hat_Hat FStar_Pprint.space
                  FStar_Pprint.equals)) uu___1 in
    separate_break_map_last FStar_Pprint.semi p_lift lifts in
  let uu___ =
    let uu___1 =
      let uu___2 = p_quident lift.FStarC_Parser_AST.msource in
      FStar_Pprint.op_Hat_Hat uu___2
        (FStar_Pprint.op_Hat_Hat FStar_Pprint.space (str "~>")) in
    let uu___2 = p_quident lift.FStarC_Parser_AST.mdest in
    prefix2 uu___1 uu___2 in
  FStar_Pprint.op_Hat_Hat uu___
    (FStar_Pprint.op_Hat_Hat FStar_Pprint.space
       (braces_with_nesting lift_op_doc))
and p_qualifier (uu___ : FStarC_Parser_AST.qualifier) :
  FStar_Pprint.document=
  match uu___ with
  | FStarC_Parser_AST.Private -> str "private"
  | FStarC_Parser_AST.Noeq -> str "noeq"
  | FStarC_Parser_AST.Unopteq -> str "unopteq"
  | FStarC_Parser_AST.Assumption -> str "assume"
  | FStarC_Parser_AST.TotalEffect -> str "total"
  | FStarC_Parser_AST.Effect_qual -> FStar_Pprint.empty
  | FStarC_Parser_AST.New -> str "new"
  | FStarC_Parser_AST.Inline -> str "inline"
  | FStarC_Parser_AST.Visible -> FStar_Pprint.empty
  | FStarC_Parser_AST.Unfold_for_unification_and_vcgen -> str "unfold"
  | FStarC_Parser_AST.Inline_for_extraction -> str "inline_for_extraction"
  | FStarC_Parser_AST.Irreducible -> str "irreducible"
  | FStarC_Parser_AST.NoExtract -> str "noextract"
  | FStarC_Parser_AST.Reifiable -> str "reifiable"
  | FStarC_Parser_AST.Reflectable -> str "reflectable"
  | FStarC_Parser_AST.Opaque -> str "opaque"
  | FStarC_Parser_AST.Logic -> str "logic"
and p_qualifiers (qs : FStarC_Parser_AST.qualifiers) : FStar_Pprint.document=
  match qs with
  | [] -> FStar_Pprint.empty
  | q::[] ->
      let uu___ = p_qualifier q in
      FStar_Pprint.op_Hat_Hat uu___ FStar_Pprint.hardline
  | uu___ ->
      let uu___1 =
        let uu___2 = FStarC_List.map p_qualifier qs in
        FStar_Pprint.flow break1 uu___2 in
      FStar_Pprint.op_Hat_Hat uu___1 FStar_Pprint.hardline
and p_letqualifier (uu___ : FStarC_Parser_AST.let_qualifier) :
  FStar_Pprint.document=
  match uu___ with
  | FStarC_Parser_AST.Rec ->
      FStar_Pprint.op_Hat_Hat FStar_Pprint.space (str "rec")
  | FStarC_Parser_AST.NoLetQualifier -> FStar_Pprint.empty
and p_aqual (uu___ : FStarC_Parser_AST.arg_qualifier) :
  FStar_Pprint.document=
  match uu___ with
  | FStarC_Parser_AST.Implicit -> str "#"
  | FStarC_Parser_AST.Equality -> str "$"
  | FStarC_Parser_AST.Meta t ->
      let t1 =
        match t.FStarC_Parser_AST.tm with
        | FStarC_Parser_AST.Abs (uu___1, e) -> e
        | uu___1 ->
            let uu___2 =
              let uu___3 =
                let uu___4 =
                  FStarC_Parser_AST.unit_const t.FStarC_Parser_AST.range in
                (t, uu___4, FStarC_Parser_AST.Nothing) in
              FStarC_Parser_AST.App uu___3 in
            FStarC_Parser_AST.mk_term uu___2 t.FStarC_Parser_AST.range
              FStarC_Parser_AST.Expr in
      let uu___1 =
        let uu___2 = p_term false false t1 in
        FStar_Pprint.op_Hat_Hat uu___2
          (FStar_Pprint.op_Hat_Hat (str "]") break1) in
      FStar_Pprint.op_Hat_Hat (str "#[") uu___1
  | FStarC_Parser_AST.TypeClassArg -> FStar_Pprint.empty
and p_disjunctivePattern (p : FStarC_Parser_AST.pattern) :
  FStar_Pprint.document=
  match p.FStarC_Parser_AST.pat with
  | FStarC_Parser_AST.PatOr pats ->
      let uu___ =
        FStarC_Pprint.separate_map
          (FStar_Pprint.op_Hat_Hat break1
             (FStar_Pprint.op_Hat_Hat FStar_Pprint.bar FStar_Pprint.space))
          p_tuplePattern pats in
      FStar_Pprint.group uu___
  | uu___ -> p_tuplePattern p
and p_tuplePattern (p : FStarC_Parser_AST.pattern) : FStar_Pprint.document=
  match p.FStarC_Parser_AST.pat with
  | FStarC_Parser_AST.PatTuple (pats, false) ->
      let uu___ =
        FStarC_Pprint.separate_map
          (FStar_Pprint.op_Hat_Hat FStar_Pprint.comma break1)
          p_constructorPattern pats in
      FStar_Pprint.group uu___
  | uu___ -> p_constructorPattern p
and p_constructorPattern (p : FStarC_Parser_AST.pattern) :
  FStar_Pprint.document=
  match p.FStarC_Parser_AST.pat with
  | FStarC_Parser_AST.PatApp
      ({ FStarC_Parser_AST.pat = FStarC_Parser_AST.PatName maybe_cons_lid;
         FStarC_Parser_AST.prange = uu___;_},
       hd::tl::[])
      when
      FStarC_Ident.lid_equals maybe_cons_lid FStarC_Parser_Const.cons_lid ->
      let uu___1 = p_constructorPattern hd in
      let uu___2 = p_constructorPattern tl in
      infix0 (FStar_Pprint.op_Hat_Hat FStar_Pprint.colon FStar_Pprint.colon)
        uu___1 uu___2
  | FStarC_Parser_AST.PatApp
      ({ FStarC_Parser_AST.pat = FStarC_Parser_AST.PatName uid;
         FStarC_Parser_AST.prange = uu___;_},
       pats)
      ->
      let uu___1 = p_quident uid in
      let uu___2 = FStarC_Pprint.separate_map break1 p_atomicPattern pats in
      prefix2 uu___1 uu___2
  | uu___ -> p_atomicPattern p
and p_atomicPattern (p : FStarC_Parser_AST.pattern) : FStar_Pprint.document=
  match p.FStarC_Parser_AST.pat with
  | FStarC_Parser_AST.PatRest -> str ".."
  | FStarC_Parser_AST.PatAscribed (pat, (t, FStar_Pervasives_Native.None)) ->
      (match ((pat.FStarC_Parser_AST.pat), (t.FStarC_Parser_AST.tm)) with
       | (FStarC_Parser_AST.PatVar (lid, aqual, attrs),
          FStarC_Parser_AST.Refine
          ({ FStarC_Parser_AST.b = FStarC_Parser_AST.Annotated (lid', t1);
             FStarC_Parser_AST.brange = uu___;
             FStarC_Parser_AST.blevel = uu___1;
             FStarC_Parser_AST.aqual = uu___2;
             FStarC_Parser_AST.battributes = uu___3;_},
           phi)) when
           let uu___4 = FStarC_Ident.string_of_id lid in
           let uu___5 = FStarC_Ident.string_of_id lid' in uu___4 = uu___5 ->
           let uu___4 =
             let uu___5 = p_ident lid in
             p_refinement aqual attrs uu___5 t1 phi in
           soft_parens_with_nesting uu___4
       | (FStarC_Parser_AST.PatWild (aqual, attrs), FStarC_Parser_AST.Refine
          ({ FStarC_Parser_AST.b = FStarC_Parser_AST.NoName t1;
             FStarC_Parser_AST.brange = uu___;
             FStarC_Parser_AST.blevel = uu___1;
             FStarC_Parser_AST.aqual = uu___2;
             FStarC_Parser_AST.battributes = uu___3;_},
           phi)) ->
           let uu___4 =
             p_refinement aqual attrs FStar_Pprint.underscore t1 phi in
           soft_parens_with_nesting uu___4
       | (FStarC_Parser_AST.PatVar (uu___, aqual, uu___1), uu___2) ->
           let wrap =
             if
               aqual =
                 (FStar_Pervasives_Native.Some FStarC_Parser_AST.TypeClassArg)
             then tc_arg
             else soft_parens_with_nesting in
           let uu___3 =
             let uu___4 = p_tuplePattern pat in
             let uu___5 =
               let uu___6 = p_tmEqNoRefinement t in
               FStar_Pprint.op_Hat_Slash_Hat FStar_Pprint.colon uu___6 in
             FStar_Pprint.op_Hat_Hat uu___4 uu___5 in
           wrap uu___3
       | (FStarC_Parser_AST.PatWild (aqual, uu___), uu___1) ->
           let wrap =
             if
               aqual =
                 (FStar_Pervasives_Native.Some FStarC_Parser_AST.TypeClassArg)
             then tc_arg
             else soft_parens_with_nesting in
           let uu___2 =
             let uu___3 = p_tuplePattern pat in
             let uu___4 =
               let uu___5 = p_tmEqNoRefinement t in
               FStar_Pprint.op_Hat_Slash_Hat FStar_Pprint.colon uu___5 in
             FStar_Pprint.op_Hat_Hat uu___3 uu___4 in
           wrap uu___2
       | uu___ ->
           let uu___1 =
             let uu___2 = p_tuplePattern pat in
             let uu___3 =
               let uu___4 = p_tmEqNoRefinement t in
               FStar_Pprint.op_Hat_Slash_Hat FStar_Pprint.colon uu___4 in
             FStar_Pprint.op_Hat_Hat uu___2 uu___3 in
           soft_parens_with_nesting uu___1)
  | FStarC_Parser_AST.PatList pats ->
      let uu___ = separate_break_map FStar_Pprint.semi p_tuplePattern pats in
      FStar_Pprint.surround (Prims.of_int (2)) Prims.int_zero
        FStar_Pprint.lbracket uu___ FStar_Pprint.rbracket
  | FStarC_Parser_AST.PatRecord pats ->
      let p_recordFieldPat uu___ =
        match uu___ with
        | (lid, pat) ->
            let uu___1 = p_qlident lid in
            let uu___2 = p_tuplePattern pat in
            infix2 FStar_Pprint.equals uu___1 uu___2 in
      let uu___ = separate_break_map FStar_Pprint.semi p_recordFieldPat pats in
      soft_braces_with_nesting uu___
  | FStarC_Parser_AST.PatTuple (pats, true) ->
      let uu___ =
        separate_break_map FStar_Pprint.comma p_constructorPattern pats in
      FStar_Pprint.surround (Prims.of_int (2)) Prims.int_one
        (FStar_Pprint.op_Hat_Hat FStar_Pprint.lparen FStar_Pprint.bar) uu___
        (FStar_Pprint.op_Hat_Hat FStar_Pprint.bar FStar_Pprint.rparen)
  | FStarC_Parser_AST.PatOp op ->
      let uu___ =
        let uu___1 =
          let uu___2 =
            let uu___3 = FStarC_Ident.string_of_id op in str uu___3 in
          FStar_Pprint.op_Hat_Hat uu___2
            (FStar_Pprint.op_Hat_Hat FStar_Pprint.space FStar_Pprint.rparen) in
        FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu___1 in
      FStar_Pprint.op_Hat_Hat FStar_Pprint.lparen uu___
  | FStarC_Parser_AST.PatWild (aqual, attrs) ->
      let uu___ = FStarC_Pprint.optional p_aqual aqual in
      let uu___1 =
        let uu___2 = p_attributes false attrs in
        FStar_Pprint.op_Hat_Hat uu___2 FStar_Pprint.underscore in
      FStar_Pprint.op_Hat_Hat uu___ uu___1
  | FStarC_Parser_AST.PatConst c -> p_constant c
  | FStarC_Parser_AST.PatVQuote e ->
      let uu___ =
        let uu___1 = p_noSeqTermAndComment false false e in
        FStar_Pprint.op_Hat_Hat (str "`%") uu___1 in
      FStar_Pprint.group uu___
  | FStarC_Parser_AST.PatVar (lid, aqual, attrs) ->
      let uu___ = FStarC_Pprint.optional p_aqual aqual in
      let uu___1 =
        let uu___2 = p_attributes false attrs in
        let uu___3 = p_lident lid in FStar_Pprint.op_Hat_Hat uu___2 uu___3 in
      FStar_Pprint.op_Hat_Hat uu___ uu___1
  | FStarC_Parser_AST.PatName uid -> p_quident uid
  | FStarC_Parser_AST.PatOr uu___ -> failwith "Inner or pattern !"
  | FStarC_Parser_AST.PatApp
      ({ FStarC_Parser_AST.pat = FStarC_Parser_AST.PatName uu___;
         FStarC_Parser_AST.prange = uu___1;_},
       uu___2)
      -> let uu___3 = p_tuplePattern p in soft_parens_with_nesting uu___3
  | FStarC_Parser_AST.PatTuple (uu___, false) ->
      let uu___1 = p_tuplePattern p in soft_parens_with_nesting uu___1
  | uu___ ->
      let uu___1 =
        let uu___2 = FStarC_Parser_AST.pat_to_string p in
        FStarC_Format.fmt1 "Invalid pattern %s" uu___2 in
      failwith uu___1
and is_typ_tuple (e : FStarC_Parser_AST.term) : Prims.bool=
  match e.FStarC_Parser_AST.tm with
  | FStarC_Parser_AST.Op (id, uu___) when
      let uu___1 = FStarC_Ident.string_of_id id in uu___1 = "*" -> true
  | uu___ -> false
and p_binder (is_atomic : Prims.bool) (b : FStarC_Parser_AST.binder) :
  FStar_Pprint.document=
  let is_tc = is_tc_binder b in
  let uu___ = p_binder' false (is_atomic && (Prims.op_Negation is_tc)) b in
  match uu___ with
  | (b', t') ->
      let d =
        match t' with
        | FStar_Pervasives_Native.Some (typ, catf1) -> catf1 b' typ
        | FStar_Pervasives_Native.None -> b' in
      if is_tc then tc_arg d else d
and p_binder' (no_pars : Prims.bool) (is_atomic : Prims.bool)
  (b : FStarC_Parser_AST.binder) :
  (FStar_Pprint.document * (FStar_Pprint.document * catf)
    FStar_Pervasives_Native.option)=
  match b.FStarC_Parser_AST.b with
  | FStarC_Parser_AST.Variable lid ->
      let uu___ =
        let uu___1 = FStarC_Pprint.optional p_aqual b.FStarC_Parser_AST.aqual in
        let uu___2 =
          let uu___3 = p_attributes false b.FStarC_Parser_AST.battributes in
          let uu___4 = p_lident lid in FStar_Pprint.op_Hat_Hat uu___3 uu___4 in
        FStar_Pprint.op_Hat_Hat uu___1 uu___2 in
      (uu___, FStar_Pervasives_Native.None)
  | FStarC_Parser_AST.Annotated (lid, t) ->
      let uu___ =
        match t.FStarC_Parser_AST.tm with
        | FStarC_Parser_AST.Refine
            ({ FStarC_Parser_AST.b = FStarC_Parser_AST.Annotated (lid', t1);
               FStarC_Parser_AST.brange = uu___1;
               FStarC_Parser_AST.blevel = uu___2;
               FStarC_Parser_AST.aqual = uu___3;
               FStarC_Parser_AST.battributes = uu___4;_},
             phi)
            when
            let uu___5 = FStarC_Ident.string_of_id lid in
            let uu___6 = FStarC_Ident.string_of_id lid' in uu___5 = uu___6 ->
            let uu___5 = p_lident lid in
            p_refinement' b.FStarC_Parser_AST.aqual
              b.FStarC_Parser_AST.battributes uu___5 t1 phi
        | uu___1 ->
            let t' =
              let uu___2 = is_typ_tuple t in
              if uu___2
              then
                let uu___3 = p_tmFormula t in soft_parens_with_nesting uu___3
              else p_tmFormula t in
            let uu___2 =
              let uu___3 =
                FStarC_Pprint.optional p_aqual b.FStarC_Parser_AST.aqual in
              let uu___4 =
                let uu___5 =
                  p_attributes false b.FStarC_Parser_AST.battributes in
                let uu___6 = p_lident lid in
                FStar_Pprint.op_Hat_Hat uu___5 uu___6 in
              FStar_Pprint.op_Hat_Hat uu___3 uu___4 in
            (uu___2, t') in
      (match uu___ with
       | (b', t') ->
           let catf1 =
             if
               is_atomic ||
                 ((is_meta_qualifier b.FStarC_Parser_AST.aqual) &&
                    (Prims.op_Negation no_pars))
             then
               fun x y ->
                 FStar_Pprint.group
                   (FStar_Pprint.op_Hat_Hat FStar_Pprint.lparen
                      (FStar_Pprint.op_Hat_Hat (cat_with_colon x y)
                         FStar_Pprint.rparen))
             else (fun x y -> FStar_Pprint.group (cat_with_colon x y)) in
           (b', (FStar_Pervasives_Native.Some (t', catf1))))
  | FStarC_Parser_AST.NoName t ->
      (match t.FStarC_Parser_AST.tm with
       | FStarC_Parser_AST.Refine
           ({ FStarC_Parser_AST.b = FStarC_Parser_AST.NoName t1;
              FStarC_Parser_AST.brange = uu___;
              FStarC_Parser_AST.blevel = uu___1;
              FStarC_Parser_AST.aqual = uu___2;
              FStarC_Parser_AST.battributes = uu___3;_},
            phi)
           ->
           let uu___4 =
             p_refinement' b.FStarC_Parser_AST.aqual
               b.FStarC_Parser_AST.battributes FStar_Pprint.underscore t1 phi in
           (match uu___4 with
            | (b', t') ->
                (b', (FStar_Pervasives_Native.Some (t', cat_with_colon))))
       | uu___ ->
           let pref =
             let uu___1 =
               FStarC_Pprint.optional p_aqual b.FStarC_Parser_AST.aqual in
             let uu___2 = p_attributes false b.FStarC_Parser_AST.battributes in
             FStar_Pprint.op_Hat_Hat uu___1 uu___2 in
           let p_Tm = if is_atomic then p_atomicTerm else p_appTerm in
           let uu___1 =
             let uu___2 = p_Tm t in FStar_Pprint.op_Hat_Hat pref uu___2 in
           (uu___1, FStar_Pervasives_Native.None))
and p_refinement
  (aqual_opt :
    FStarC_Parser_AST.arg_qualifier FStar_Pervasives_Native.option)
  (attrs : FStarC_Parser_AST.term Prims.list)
  (binder : FStar_Pprint.document) (t : FStarC_Parser_AST.term)
  (phi : FStarC_Parser_AST.term) : FStar_Pprint.document=
  let uu___ = p_refinement' aqual_opt attrs binder t phi in
  match uu___ with | (b, typ) -> cat_with_colon b typ
and p_refinement'
  (aqual_opt :
    FStarC_Parser_AST.arg_qualifier FStar_Pervasives_Native.option)
  (attrs : FStarC_Parser_AST.term Prims.list)
  (binder : FStar_Pprint.document) (t : FStarC_Parser_AST.term)
  (phi : FStarC_Parser_AST.term) :
  (FStar_Pprint.document * FStar_Pprint.document)=
  let is_t_atomic =
    match t.FStarC_Parser_AST.tm with
    | FStarC_Parser_AST.Construct uu___ -> false
    | FStarC_Parser_AST.App uu___ -> false
    | FStarC_Parser_AST.Op uu___ -> false
    | uu___ -> true in
  let uu___ = p_noSeqTerm false false phi in
  match uu___ with
  | (comm, phi1) ->
      let phi2 =
        if comm = FStar_Pprint.empty
        then phi1
        else
          FStar_Pprint.op_Hat_Hat comm
            (FStar_Pprint.op_Hat_Hat FStar_Pprint.hardline phi1) in
      let jump_break = if is_t_atomic then Prims.int_zero else Prims.int_one in
      let uu___1 =
        let uu___2 = FStarC_Pprint.optional p_aqual aqual_opt in
        let uu___3 =
          let uu___4 = p_attributes false attrs in
          FStar_Pprint.op_Hat_Hat uu___4 binder in
        FStar_Pprint.op_Hat_Hat uu___2 uu___3 in
      let uu___2 =
        let uu___3 = p_appTerm t in
        FStar_Pprint.op_Hat_Hat uu___3
          (FStar_Pprint.jump (Prims.of_int (2)) jump_break
             (FStar_Pprint.group
                (FStar_Pprint.ifflat (soft_braces_with_nesting_tight phi2)
                   (soft_braces_with_nesting phi2)))) in
      (uu___1, uu___2)
and p_binders_list (is_atomic : Prims.bool)
  (bs : FStarC_Parser_AST.binder Prims.list) :
  FStar_Pprint.document Prims.list= FStarC_List.map (p_binder is_atomic) bs
and p_binders (is_atomic : Prims.bool)
  (bs : FStarC_Parser_AST.binder Prims.list) : FStar_Pprint.document=
  let uu___ = p_binders_list is_atomic bs in separate_or_flow break1 uu___
and p_binders_sep (bs : FStarC_Parser_AST.binder Prims.list) :
  FStar_Pprint.document=
  let uu___ = p_binders_list true bs in
  FStarC_Pprint.separate_map FStar_Pprint.space (fun x -> x) uu___
and paren_if (b : Prims.bool) :
  FStar_Pprint.document -> FStar_Pprint.document=
  if b then soft_parens_with_nesting else (fun x -> x)
and inline_comment_or_above (comm : FStar_Pprint.document)
  (doc : FStar_Pprint.document) (sep : FStar_Pprint.document) :
  FStar_Pprint.document=
  if comm = FStar_Pprint.empty
  then FStar_Pprint.group (FStar_Pprint.op_Hat_Hat doc sep)
  else
    FStar_Pprint.group
      (FStar_Pprint.ifflat
         (FStar_Pprint.group
            (FStar_Pprint.op_Hat_Hat doc
               (FStar_Pprint.op_Hat_Hat sep
                  (FStar_Pprint.op_Hat_Hat break1 comm))))
         (FStar_Pprint.op_Hat_Hat comm
            (FStar_Pprint.op_Hat_Hat FStar_Pprint.hardline
               (FStar_Pprint.op_Hat_Hat doc sep))))
and p_term (ps : Prims.bool) (pb : Prims.bool) (e : FStarC_Parser_AST.term) :
  FStar_Pprint.document=
  match e.FStarC_Parser_AST.tm with
  | FStarC_Parser_AST.Seq (e1, e2) ->
      let uu___ = p_noSeqTerm true false e1 in
      (match uu___ with
       | (comm, t1) ->
           let uu___1 = inline_comment_or_above comm t1 FStar_Pprint.semi in
           let uu___2 =
             let uu___3 = p_term ps pb e2 in
             FStar_Pprint.op_Hat_Hat FStar_Pprint.hardline uu___3 in
           FStar_Pprint.op_Hat_Hat uu___1 uu___2)
  | FStarC_Parser_AST.Bind (x, e1, e2) ->
      let uu___ =
        let uu___1 =
          let uu___2 =
            let uu___3 = p_lident x in
            FStar_Pprint.op_Hat_Hat uu___3
              (FStar_Pprint.op_Hat_Hat FStar_Pprint.space
                 FStar_Pprint.long_left_arrow) in
          let uu___3 =
            let uu___4 = p_noSeqTermAndComment true false e1 in
            FStar_Pprint.op_Hat_Hat uu___4
              (FStar_Pprint.op_Hat_Hat FStar_Pprint.space FStar_Pprint.semi) in
          op_Hat_Slash_Plus_Hat uu___2 uu___3 in
        FStar_Pprint.group uu___1 in
      let uu___1 = p_term ps pb e2 in
      FStar_Pprint.op_Hat_Slash_Hat uu___ uu___1
  | uu___ ->
      let uu___1 = p_noSeqTermAndComment ps pb e in FStar_Pprint.group uu___1
and p_term_sep (ps : Prims.bool) (pb : Prims.bool)
  (e : FStarC_Parser_AST.term) :
  (FStar_Pprint.document * FStar_Pprint.document)=
  match e.FStarC_Parser_AST.tm with
  | FStarC_Parser_AST.Seq (e1, e2) ->
      let uu___ = p_noSeqTerm true false e1 in
      (match uu___ with
       | (comm, t1) ->
           let uu___1 =
             let uu___2 =
               let uu___3 = p_term ps pb e2 in
               FStar_Pprint.op_Hat_Hat FStar_Pprint.hardline uu___3 in
             FStar_Pprint.op_Hat_Hat
               (FStar_Pprint.group
                  (FStar_Pprint.op_Hat_Hat t1 FStar_Pprint.semi)) uu___2 in
           (comm, uu___1))
  | FStarC_Parser_AST.Bind (x, e1, e2) ->
      let uu___ =
        let uu___1 =
          let uu___2 =
            let uu___3 =
              let uu___4 = p_lident x in
              FStar_Pprint.op_Hat_Hat uu___4
                (FStar_Pprint.op_Hat_Hat FStar_Pprint.space
                   FStar_Pprint.long_left_arrow) in
            let uu___4 =
              let uu___5 = p_noSeqTermAndComment true false e1 in
              FStar_Pprint.op_Hat_Hat uu___5
                (FStar_Pprint.op_Hat_Hat FStar_Pprint.space FStar_Pprint.semi) in
            op_Hat_Slash_Plus_Hat uu___3 uu___4 in
          FStar_Pprint.group uu___2 in
        let uu___2 = p_term ps pb e2 in
        FStar_Pprint.op_Hat_Slash_Hat uu___1 uu___2 in
      (FStar_Pprint.empty, uu___)
  | uu___ -> p_noSeqTerm ps pb e
and p_noSeqTerm (ps : Prims.bool) (pb : Prims.bool)
  (e : FStarC_Parser_AST.term) :
  (FStar_Pprint.document * FStar_Pprint.document)=
  with_comment_sep (p_noSeqTerm' ps pb) e e.FStarC_Parser_AST.range
and p_noSeqTermAndComment (ps : Prims.bool) (pb : Prims.bool)
  (e : FStarC_Parser_AST.term) : FStar_Pprint.document=
  with_comment (p_noSeqTerm' ps pb) e e.FStarC_Parser_AST.range
and p_noSeqTerm' (ps : Prims.bool) (pb : Prims.bool)
  (e : FStarC_Parser_AST.term) : FStar_Pprint.document=
  match e.FStarC_Parser_AST.tm with
  | FStarC_Parser_AST.Ascribed (e1, t, FStar_Pervasives_Native.None, use_eq)
      ->
      let uu___ =
        let uu___1 = p_tmIff e1 in
        let uu___2 =
          let uu___3 =
            let uu___4 = p_typ ps pb t in
            FStar_Pprint.op_Hat_Slash_Hat FStar_Pprint.colon uu___4 in
          FStar_Pprint.op_Hat_Hat
            (if use_eq then FStar_Pprint.dollar else FStar_Pprint.langle)
            uu___3 in
        FStar_Pprint.op_Hat_Slash_Hat uu___1 uu___2 in
      FStar_Pprint.group uu___
  | FStarC_Parser_AST.Ascribed
      (e1, t, FStar_Pervasives_Native.Some tac, use_eq) ->
      let uu___ =
        let uu___1 = p_tmIff e1 in
        let uu___2 =
          let uu___3 =
            let uu___4 =
              let uu___5 = p_typ false false t in
              let uu___6 =
                let uu___7 = p_typ ps pb (maybe_unthunk tac) in
                FStar_Pprint.op_Hat_Slash_Hat (str "by") uu___7 in
              FStar_Pprint.op_Hat_Slash_Hat uu___5 uu___6 in
            FStar_Pprint.op_Hat_Slash_Hat FStar_Pprint.colon uu___4 in
          FStar_Pprint.op_Hat_Hat
            (if use_eq then FStar_Pprint.dollar else FStar_Pprint.langle)
            uu___3 in
        FStar_Pprint.op_Hat_Slash_Hat uu___1 uu___2 in
      FStar_Pprint.group uu___
  | FStarC_Parser_AST.Op (id, e1::e2::e3::[]) when
      let uu___ = FStarC_Ident.string_of_id id in uu___ = ".()<-" ->
      let uu___ =
        let uu___1 =
          let uu___2 =
            let uu___3 = p_atomicTermNotQUident e1 in
            let uu___4 =
              let uu___5 =
                let uu___6 =
                  let uu___7 = p_term false false e2 in
                  soft_parens_with_nesting uu___7 in
                FStar_Pprint.op_Hat_Hat uu___6
                  (FStar_Pprint.op_Hat_Hat FStar_Pprint.space
                     FStar_Pprint.larrow) in
              FStar_Pprint.op_Hat_Hat FStar_Pprint.dot uu___5 in
            FStar_Pprint.op_Hat_Hat uu___3 uu___4 in
          FStar_Pprint.group uu___2 in
        let uu___2 =
          let uu___3 = p_noSeqTermAndComment ps pb e3 in jump2 uu___3 in
        FStar_Pprint.op_Hat_Hat uu___1 uu___2 in
      FStar_Pprint.group uu___
  | FStarC_Parser_AST.Op (id, e1::e2::e3::[]) when
      let uu___ = FStarC_Ident.string_of_id id in uu___ = ".[]<-" ->
      let uu___ =
        let uu___1 =
          let uu___2 =
            let uu___3 = p_atomicTermNotQUident e1 in
            let uu___4 =
              let uu___5 =
                let uu___6 =
                  let uu___7 = p_term false false e2 in
                  soft_brackets_with_nesting uu___7 in
                FStar_Pprint.op_Hat_Hat uu___6
                  (FStar_Pprint.op_Hat_Hat FStar_Pprint.space
                     FStar_Pprint.larrow) in
              FStar_Pprint.op_Hat_Hat FStar_Pprint.dot uu___5 in
            FStar_Pprint.op_Hat_Hat uu___3 uu___4 in
          FStar_Pprint.group uu___2 in
        let uu___2 =
          let uu___3 = p_noSeqTermAndComment ps pb e3 in jump2 uu___3 in
        FStar_Pprint.op_Hat_Hat uu___1 uu___2 in
      FStar_Pprint.group uu___
  | FStarC_Parser_AST.Op (id, e1::e2::e3::[]) when
      let uu___ = FStarC_Ident.string_of_id id in uu___ = ".(||)<-" ->
      let uu___ =
        let uu___1 =
          let uu___2 =
            let uu___3 = p_atomicTermNotQUident e1 in
            let uu___4 =
              let uu___5 =
                let uu___6 =
                  let uu___7 = p_term false false e2 in
                  soft_lens_access_with_nesting uu___7 in
                FStar_Pprint.op_Hat_Hat uu___6
                  (FStar_Pprint.op_Hat_Hat FStar_Pprint.space
                     FStar_Pprint.larrow) in
              FStar_Pprint.op_Hat_Hat FStar_Pprint.dot uu___5 in
            FStar_Pprint.op_Hat_Hat uu___3 uu___4 in
          FStar_Pprint.group uu___2 in
        let uu___2 =
          let uu___3 = p_noSeqTermAndComment ps pb e3 in jump2 uu___3 in
        FStar_Pprint.op_Hat_Hat uu___1 uu___2 in
      FStar_Pprint.group uu___
  | FStarC_Parser_AST.Op (id, e1::e2::e3::[]) when
      let uu___ = FStarC_Ident.string_of_id id in uu___ = ".[||]<-" ->
      let uu___ =
        let uu___1 =
          let uu___2 =
            let uu___3 = p_atomicTermNotQUident e1 in
            let uu___4 =
              let uu___5 =
                let uu___6 =
                  let uu___7 = p_term false false e2 in
                  soft_brackets_lens_access_with_nesting uu___7 in
                FStar_Pprint.op_Hat_Hat uu___6
                  (FStar_Pprint.op_Hat_Hat FStar_Pprint.space
                     FStar_Pprint.larrow) in
              FStar_Pprint.op_Hat_Hat FStar_Pprint.dot uu___5 in
            FStar_Pprint.op_Hat_Hat uu___3 uu___4 in
          FStar_Pprint.group uu___2 in
        let uu___2 =
          let uu___3 = p_noSeqTermAndComment ps pb e3 in jump2 uu___3 in
        FStar_Pprint.op_Hat_Hat uu___1 uu___2 in
      FStar_Pprint.group uu___
  | FStarC_Parser_AST.Requires e1 ->
      let uu___ =
        let uu___1 = p_typ ps pb e1 in
        FStar_Pprint.op_Hat_Slash_Hat (str "requires") uu___1 in
      FStar_Pprint.group uu___
  | FStarC_Parser_AST.Ensures e1 ->
      let uu___ =
        let uu___1 = p_typ ps pb e1 in
        FStar_Pprint.op_Hat_Slash_Hat (str "ensures") uu___1 in
      FStar_Pprint.group uu___
  | FStarC_Parser_AST.WFOrder (rel, e1) -> p_dec_wf ps pb rel e1
  | FStarC_Parser_AST.LexList l ->
      let uu___ =
        let uu___1 = p_term_list ps pb l in
        FStar_Pprint.op_Hat_Hat (str "%") uu___1 in
      FStar_Pprint.group uu___
  | FStarC_Parser_AST.Decreases e1 ->
      let uu___ =
        let uu___1 = p_typ ps pb e1 in
        FStar_Pprint.op_Hat_Slash_Hat (str "decreases") uu___1 in
      FStar_Pprint.group uu___
  | FStarC_Parser_AST.Attributes es ->
      let uu___ =
        let uu___1 = FStarC_Pprint.separate_map break1 p_atomicTerm es in
        FStar_Pprint.op_Hat_Slash_Hat (str "attributes") uu___1 in
      FStar_Pprint.group uu___
  | FStarC_Parser_AST.If (e1, op_opt, ret_opt, e2, e3) ->
      if is_unit e3
      then
        let uu___ =
          let uu___1 =
            let uu___2 =
              let uu___3 =
                let uu___4 =
                  let uu___5 =
                    let uu___6 =
                      FStarC_Option.map FStarC_Ident.string_of_id op_opt in
                    FStarC_Option.bind uu___6
                      (FStarC_Parser_AST.strip_prefix "let") in
                  FStarC_Option.dflt "" uu___5 in
                Prims.strcat "if" uu___4 in
              str uu___3 in
            let uu___3 = p_noSeqTermAndComment false false e1 in
            op_Hat_Slash_Plus_Hat uu___2 uu___3 in
          let uu___2 =
            let uu___3 = p_noSeqTermAndComment ps pb e2 in
            op_Hat_Slash_Plus_Hat (str "then") uu___3 in
          FStar_Pprint.op_Hat_Slash_Hat uu___1 uu___2 in
        FStar_Pprint.group uu___
      else
        (let e2_doc =
           match e2.FStarC_Parser_AST.tm with
           | FStarC_Parser_AST.If (uu___1, uu___2, uu___3, uu___4, e31) when
               is_unit e31 ->
               let uu___5 = p_noSeqTermAndComment false false e2 in
               soft_parens_with_nesting uu___5
           | uu___1 -> p_noSeqTermAndComment false false e2 in
         match ret_opt with
         | FStar_Pervasives_Native.None ->
             let uu___1 =
               let uu___2 =
                 let uu___3 = p_noSeqTermAndComment false false e1 in
                 op_Hat_Slash_Plus_Hat (str "if") uu___3 in
               let uu___3 =
                 let uu___4 =
                   let uu___5 = p_noSeqTermAndComment ps pb e3 in
                   op_Hat_Slash_Plus_Hat (str "else") uu___5 in
                 FStar_Pprint.op_Hat_Slash_Hat
                   (op_Hat_Slash_Plus_Hat (str "then") e2_doc) uu___4 in
               FStar_Pprint.op_Hat_Slash_Hat uu___2 uu___3 in
             FStar_Pprint.group uu___1
         | FStar_Pervasives_Native.Some (as_opt, ret, use_eq) ->
             let uu___1 =
               let uu___2 =
                 let uu___3 = p_noSeqTermAndComment false false e1 in
                 op_Hat_Slash_Plus_Hat (str "if") uu___3 in
               let uu___3 =
                 let uu___4 =
                   let uu___5 =
                     match as_opt with
                     | FStar_Pervasives_Native.None -> FStar_Pprint.empty
                     | FStar_Pervasives_Native.Some as_ident ->
                         let uu___6 = p_ident as_ident in
                         FStar_Pprint.op_Hat_Slash_Hat (str "as") uu___6 in
                   let uu___6 =
                     let uu___7 = p_tmIff ret in
                     op_Hat_Slash_Plus_Hat
                       (str (if use_eq then "returns$" else "returns"))
                       uu___7 in
                   FStar_Pprint.op_Hat_Slash_Hat uu___5 uu___6 in
                 let uu___5 =
                   let uu___6 =
                     let uu___7 = p_noSeqTermAndComment ps pb e3 in
                     op_Hat_Slash_Plus_Hat (str "else") uu___7 in
                   FStar_Pprint.op_Hat_Slash_Hat
                     (op_Hat_Slash_Plus_Hat (str "then") e2_doc) uu___6 in
                 FStar_Pprint.op_Hat_Slash_Hat uu___4 uu___5 in
               FStar_Pprint.op_Hat_Slash_Hat uu___2 uu___3 in
             FStar_Pprint.group uu___1)
  | FStarC_Parser_AST.TryWith (e1, branches) ->
      let uu___ =
        let uu___1 =
          let uu___2 =
            let uu___3 = p_noSeqTermAndComment false false e1 in
            prefix2 (str "try") uu___3 in
          let uu___3 =
            let uu___4 =
              separate_map_last FStar_Pprint.hardline p_patternBranch
                branches in
            FStar_Pprint.op_Hat_Slash_Hat (str "with") uu___4 in
          FStar_Pprint.op_Hat_Slash_Hat uu___2 uu___3 in
        FStar_Pprint.group uu___1 in
      let uu___1 = paren_if (ps || pb) in uu___1 uu___
  | FStarC_Parser_AST.Match (e1, op_opt, ret_opt, branches) ->
      let match_doc =
        let uu___ =
          let uu___1 =
            let uu___2 =
              let uu___3 = FStarC_Option.map FStarC_Ident.string_of_id op_opt in
              FStarC_Option.bind uu___3
                (FStarC_Parser_AST.strip_prefix "let") in
            FStarC_Option.dflt "" uu___2 in
          Prims.strcat "match" uu___1 in
        str uu___ in
      let uu___ =
        let uu___1 =
          match ret_opt with
          | FStar_Pervasives_Native.None ->
              let uu___2 =
                let uu___3 = p_noSeqTermAndComment false false e1 in
                FStar_Pprint.surround (Prims.of_int (2)) Prims.int_one
                  match_doc uu___3 (str "with") in
              FStar_Pprint.group uu___2
          | FStar_Pervasives_Native.Some (as_opt, ret, use_eq) ->
              let uu___2 =
                let uu___3 =
                  let uu___4 = p_noSeqTermAndComment false false e1 in
                  let uu___5 =
                    let uu___6 =
                      match as_opt with
                      | FStar_Pervasives_Native.None -> FStar_Pprint.empty
                      | FStar_Pervasives_Native.Some as_ident ->
                          let uu___7 = p_ident as_ident in
                          op_Hat_Slash_Plus_Hat (str "as") uu___7 in
                    let uu___7 =
                      let uu___8 = p_tmIff ret in
                      op_Hat_Slash_Plus_Hat
                        (str (if use_eq then "returns$" else "returns"))
                        uu___8 in
                    op_Hat_Slash_Plus_Hat uu___6 uu___7 in
                  op_Hat_Slash_Plus_Hat uu___4 uu___5 in
                FStar_Pprint.surround (Prims.of_int (2)) Prims.int_one
                  match_doc uu___3 (str "with") in
              FStar_Pprint.group uu___2 in
        let uu___2 =
          separate_map_last FStar_Pprint.hardline p_patternBranch branches in
        FStar_Pprint.op_Hat_Slash_Hat uu___1 uu___2 in
      let uu___1 = paren_if (ps || pb) in uu___1 uu___
  | FStarC_Parser_AST.LetOpen (uid, e1) ->
      let uu___ =
        let uu___1 =
          let uu___2 =
            let uu___3 = p_quident uid in
            FStar_Pprint.surround (Prims.of_int (2)) Prims.int_one
              (str "let open") uu___3 (str "in") in
          let uu___3 = p_term false pb e1 in
          FStar_Pprint.op_Hat_Slash_Hat uu___2 uu___3 in
        FStar_Pprint.group uu___1 in
      let uu___1 = paren_if ps in uu___1 uu___
  | FStarC_Parser_AST.LetOpenRecord (r, rty, e1) ->
      let uu___ =
        let uu___1 =
          let uu___2 =
            let uu___3 = p_term false pb r in
            FStar_Pprint.surround (Prims.of_int (2)) Prims.int_one
              (str "let open") uu___3 (str "as") in
          let uu___3 =
            let uu___4 = p_term false pb rty in
            let uu___5 =
              let uu___6 = p_term false pb e1 in
              FStar_Pprint.op_Hat_Slash_Hat (str "in") uu___6 in
            FStar_Pprint.op_Hat_Slash_Hat uu___4 uu___5 in
          FStar_Pprint.op_Hat_Slash_Hat uu___2 uu___3 in
        FStar_Pprint.group uu___1 in
      let uu___1 = paren_if ps in uu___1 uu___
  | FStarC_Parser_AST.LetOperator (lets, body) ->
      let p_let uu___ is_last =
        match uu___ with
        | (id, pat, e1) ->
            let doc_let_or_and =
              let uu___1 = FStarC_Ident.string_of_id id in str uu___1 in
            let doc_pat = p_letlhs doc_let_or_and (pat, e1) true in
            (match ((pat.FStarC_Parser_AST.pat), (e1.FStarC_Parser_AST.tm))
             with
             | (FStarC_Parser_AST.PatVar (pid, uu___1, uu___2),
                FStarC_Parser_AST.Name tid) when
                 let uu___3 = FStarC_Ident.string_of_id pid in
                 let uu___4 =
                   let uu___5 = FStarC_Ident.path_of_lid tid in
                   FStarC_List.last uu___5 in
                 uu___3 = uu___4 ->
                 FStar_Pprint.op_Hat_Slash_Hat doc_pat
                   (if is_last then str "in" else FStar_Pprint.empty)
             | (FStarC_Parser_AST.PatVar (pid, uu___1, uu___2),
                FStarC_Parser_AST.Var tid) when
                 let uu___3 = FStarC_Ident.string_of_id pid in
                 let uu___4 =
                   let uu___5 = FStarC_Ident.path_of_lid tid in
                   FStarC_List.last uu___5 in
                 uu___3 = uu___4 ->
                 FStar_Pprint.op_Hat_Slash_Hat doc_pat
                   (if is_last then str "in" else FStar_Pprint.empty)
             | uu___1 ->
                 let uu___2 = p_term_sep false false e1 in
                 (match uu___2 with
                  | (comm, doc_expr) ->
                      let doc_expr1 =
                        inline_comment_or_above comm doc_expr
                          FStar_Pprint.empty in
                      if is_last
                      then
                        FStar_Pprint.surround (Prims.of_int (2))
                          Prims.int_one
                          (FStar_Pprint.flow break1
                             [doc_pat; FStar_Pprint.equals]) doc_expr1
                          (str "in")
                      else
                        FStar_Pprint.hang (Prims.of_int (2))
                          (FStar_Pprint.flow break1
                             [doc_pat; FStar_Pprint.equals; doc_expr1]))) in
      let l = FStarC_List.length lets in
      let lets_docs =
        FStarC_List.mapi
          (fun i lb ->
             let uu___ = p_let lb (i = (l - Prims.int_one)) in
             FStar_Pprint.group uu___) lets in
      let lets_doc =
        FStar_Pprint.group (FStar_Pprint.separate break1 lets_docs) in
      let r =
        let uu___ =
          let uu___1 =
            let uu___2 =
              let uu___3 = p_term false pb body in
              FStar_Pprint.op_Hat_Hat FStar_Pprint.hardline uu___3 in
            FStar_Pprint.op_Hat_Hat lets_doc uu___2 in
          FStar_Pprint.group uu___1 in
        let uu___1 = paren_if ps in uu___1 uu___ in
      r
  | FStarC_Parser_AST.Let (q, lbs, e1) ->
      let p_lb q1 uu___ is_last =
        match uu___ with
        | (a, (pat, e2)) ->
            let attrs = p_attrs_opt true a in
            let doc_let_or_and =
              match q1 with
              | FStar_Pervasives_Native.Some (FStarC_Parser_AST.LocalRec) ->
                  FStar_Pprint.group
                    (FStar_Pprint.op_Hat_Slash_Hat (str "let") (str "rec"))
              | FStar_Pervasives_Native.Some
                  (FStarC_Parser_AST.LocalNoLetQualifier) -> str "let"
              | FStar_Pervasives_Native.Some (FStarC_Parser_AST.LocalUnfold)
                  ->
                  FStar_Pprint.group
                    (FStar_Pprint.op_Hat_Slash_Hat (str "let") (str "unfold"))
              | uu___1 -> str "and" in
            let doc_pat = p_letlhs doc_let_or_and (pat, e2) true in
            let uu___1 = p_term_sep false false e2 in
            (match uu___1 with
             | (comm, doc_expr) ->
                 let doc_expr1 =
                   inline_comment_or_above comm doc_expr FStar_Pprint.empty in
                 FStar_Pprint.op_Hat_Hat attrs
                   (if is_last
                    then
                      FStar_Pprint.surround (Prims.of_int (2)) Prims.int_one
                        (FStar_Pprint.flow break1
                           [doc_pat; FStar_Pprint.equals]) doc_expr1
                        (str "in")
                    else
                      FStar_Pprint.hang (Prims.of_int (2))
                        (FStar_Pprint.flow break1
                           [doc_pat; FStar_Pprint.equals; doc_expr1]))) in
      let l = FStarC_List.length lbs in
      let lbs_docs =
        FStarC_List.mapi
          (fun i lb ->
             if i = Prims.int_zero
             then
               let uu___ =
                 p_lb (FStar_Pervasives_Native.Some q) lb
                   (i = (l - Prims.int_one)) in
               FStar_Pprint.group uu___
             else
               (let uu___1 =
                  p_lb FStar_Pervasives_Native.None lb
                    (i = (l - Prims.int_one)) in
                FStar_Pprint.group uu___1)) lbs in
      let lbs_doc =
        FStar_Pprint.group (FStar_Pprint.separate break1 lbs_docs) in
      let uu___ =
        let uu___1 =
          let uu___2 =
            let uu___3 = p_term false pb e1 in
            FStar_Pprint.op_Hat_Hat FStar_Pprint.hardline uu___3 in
          FStar_Pprint.op_Hat_Hat lbs_doc uu___2 in
        FStar_Pprint.group uu___1 in
      let uu___1 = paren_if ps in uu___1 uu___
  | FStarC_Parser_AST.Quote (e1, FStarC_Parser_AST.Dynamic) ->
      let uu___ =
        let uu___1 = p_noSeqTermAndComment ps pb e1 in
        FStar_Pprint.op_Hat_Slash_Hat (str "quote") uu___1 in
      FStar_Pprint.group uu___
  | FStarC_Parser_AST.Quote (e1, FStarC_Parser_AST.Static) ->
      let uu___ =
        let uu___1 = p_noSeqTermAndComment ps pb e1 in
        FStar_Pprint.op_Hat_Hat (str "`") uu___1 in
      FStar_Pprint.group uu___
  | FStarC_Parser_AST.VQuote e1 ->
      let uu___ =
        let uu___1 = p_noSeqTermAndComment ps pb e1 in
        FStar_Pprint.op_Hat_Hat (str "`%") uu___1 in
      FStar_Pprint.group uu___
  | FStarC_Parser_AST.Antiquote
      {
        FStarC_Parser_AST.tm = FStarC_Parser_AST.Quote
          (e1, FStarC_Parser_AST.Dynamic);
        FStarC_Parser_AST.range = uu___; FStarC_Parser_AST.level = uu___1;_}
      ->
      let uu___2 =
        let uu___3 = p_noSeqTermAndComment ps pb e1 in
        FStar_Pprint.op_Hat_Hat (str "`@") uu___3 in
      FStar_Pprint.group uu___2
  | FStarC_Parser_AST.Antiquote e1 ->
      let uu___ =
        let uu___1 = p_noSeqTermAndComment ps pb e1 in
        FStar_Pprint.op_Hat_Hat (str "`#") uu___1 in
      FStar_Pprint.group uu___
  | FStarC_Parser_AST.CalcProof (rel, init, steps) ->
      let head =
        let uu___ =
          let uu___1 =
            let uu___2 = p_noSeqTermAndComment false false rel in
            FStar_Pprint.op_Hat_Hat uu___2
              (FStar_Pprint.op_Hat_Hat FStar_Pprint.space FStar_Pprint.lbrace) in
          FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu___1 in
        FStar_Pprint.op_Hat_Hat (str "calc") uu___ in
      let bot = FStar_Pprint.rbrace in
      let uu___ =
        let uu___1 =
          let uu___2 =
            let uu___3 = p_noSeqTermAndComment false false init in
            let uu___4 =
              let uu___5 =
                let uu___6 =
                  separate_map_last FStar_Pprint.hardline p_calcStep steps in
                FStar_Pprint.op_Hat_Hat FStar_Pprint.hardline uu___6 in
              FStar_Pprint.op_Hat_Hat (str ";") uu___5 in
            FStar_Pprint.op_Hat_Hat uu___3 uu___4 in
          FStar_Pprint.op_Hat_Hat FStar_Pprint.hardline uu___2 in
        FStar_Pprint.nest (Prims.of_int (2)) uu___1 in
      FStar_Pprint.enclose head
        (FStar_Pprint.op_Hat_Hat FStar_Pprint.hardline bot) uu___
  | FStarC_Parser_AST.IntroForall (xs, p, e1) ->
      let p1 = p_noSeqTermAndComment false false p in
      let e2 = p_noSeqTermAndComment false false e1 in
      let xs1 = p_binders_sep xs in
      FStar_Pprint.op_Hat_Hat (str "introduce forall")
        (FStar_Pprint.op_Hat_Hat FStar_Pprint.space
           (FStar_Pprint.op_Hat_Hat xs1
              (FStar_Pprint.op_Hat_Hat FStar_Pprint.space
                 (FStar_Pprint.op_Hat_Hat (str ".")
                    (FStar_Pprint.op_Hat_Hat FStar_Pprint.space
                       (FStar_Pprint.op_Hat_Hat p1
                          (FStar_Pprint.op_Hat_Hat FStar_Pprint.hardline
                             (FStar_Pprint.op_Hat_Hat (str "with")
                                (FStar_Pprint.op_Hat_Hat FStar_Pprint.space
                                   e2)))))))))
  | FStarC_Parser_AST.IntroExists (xs, p, vs, e1) ->
      let p1 = p_noSeqTermAndComment false false p in
      let e2 = p_noSeqTermAndComment false false e1 in
      let xs1 = p_binders_sep xs in
      let uu___ =
        let uu___1 =
          let uu___2 =
            let uu___3 =
              let uu___4 =
                let uu___5 =
                  let uu___6 =
                    let uu___7 =
                      let uu___8 =
                        let uu___9 =
                          let uu___10 =
                            FStarC_Pprint.separate_map FStar_Pprint.space
                              p_atomicTerm vs in
                          FStar_Pprint.op_Hat_Hat uu___10
                            (FStar_Pprint.op_Hat_Hat FStar_Pprint.hardline
                               (FStar_Pprint.op_Hat_Hat (str "and")
                                  (FStar_Pprint.op_Hat_Hat FStar_Pprint.space
                                     e2))) in
                        FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu___9 in
                      FStar_Pprint.op_Hat_Hat (str "with") uu___8 in
                    FStar_Pprint.op_Hat_Hat FStar_Pprint.hardline uu___7 in
                  FStar_Pprint.op_Hat_Hat p1 uu___6 in
                FStar_Pprint.op_Hat_Hat (str ".") uu___5 in
              FStar_Pprint.op_Hat_Hat xs1 uu___4 in
            FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu___3 in
          FStar_Pprint.op_Hat_Hat (str "exists") uu___2 in
        FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu___1 in
      FStar_Pprint.op_Hat_Hat (str "introduce") uu___
  | FStarC_Parser_AST.IntroImplies (p, q, x, e1) ->
      let p1 = p_tmFormula p in
      let q1 = p_tmFormula q in
      let e2 = p_noSeqTermAndComment false false e1 in
      let x1 = p_binders_sep [x] in
      FStar_Pprint.op_Hat_Hat (str "introduce")
        (FStar_Pprint.op_Hat_Hat FStar_Pprint.space
           (FStar_Pprint.op_Hat_Hat p1
              (FStar_Pprint.op_Hat_Hat FStar_Pprint.space
                 (FStar_Pprint.op_Hat_Hat (str "==>")
                    (FStar_Pprint.op_Hat_Hat FStar_Pprint.space
                       (FStar_Pprint.op_Hat_Hat q1
                          (FStar_Pprint.op_Hat_Hat FStar_Pprint.hardline
                             (FStar_Pprint.op_Hat_Hat (str "with")
                                (FStar_Pprint.op_Hat_Hat FStar_Pprint.space
                                   (FStar_Pprint.op_Hat_Hat x1
                                      (FStar_Pprint.op_Hat_Hat (str ".")
                                         (FStar_Pprint.op_Hat_Hat
                                            FStar_Pprint.space e2))))))))))))
  | FStarC_Parser_AST.IntroOr (b, p, q, e1) ->
      let p1 = p_tmFormula p in
      let q1 = p_tmFormula q in
      let e2 = p_noSeqTermAndComment false false e1 in
      FStar_Pprint.op_Hat_Hat (str "introduce")
        (FStar_Pprint.op_Hat_Hat FStar_Pprint.space
           (FStar_Pprint.op_Hat_Hat p1
              (FStar_Pprint.op_Hat_Hat FStar_Pprint.space
                 (FStar_Pprint.op_Hat_Hat (str "\\/")
                    (FStar_Pprint.op_Hat_Hat FStar_Pprint.space
                       (FStar_Pprint.op_Hat_Hat q1
                          (FStar_Pprint.op_Hat_Hat FStar_Pprint.hardline
                             (FStar_Pprint.op_Hat_Hat (str "with")
                                (FStar_Pprint.op_Hat_Hat FStar_Pprint.space
                                   (FStar_Pprint.op_Hat_Hat
                                      (if b then str "Left" else str "Right")
                                      (FStar_Pprint.op_Hat_Hat
                                         FStar_Pprint.space e2)))))))))))
  | FStarC_Parser_AST.IntroAnd (p, q, e1, e2) ->
      let p1 = p_tmFormula p in
      let q1 = p_tmTuple q in
      let e11 = p_noSeqTermAndComment false false e1 in
      let e21 = p_noSeqTermAndComment false false e2 in
      FStar_Pprint.op_Hat_Hat (str "introduce")
        (FStar_Pprint.op_Hat_Hat FStar_Pprint.space
           (FStar_Pprint.op_Hat_Hat p1
              (FStar_Pprint.op_Hat_Hat FStar_Pprint.space
                 (FStar_Pprint.op_Hat_Hat (str "/\\")
                    (FStar_Pprint.op_Hat_Hat FStar_Pprint.space
                       (FStar_Pprint.op_Hat_Hat q1
                          (FStar_Pprint.op_Hat_Hat FStar_Pprint.hardline
                             (FStar_Pprint.op_Hat_Hat (str "with")
                                (FStar_Pprint.op_Hat_Hat FStar_Pprint.space
                                   (FStar_Pprint.op_Hat_Hat e11
                                      (FStar_Pprint.op_Hat_Hat
                                         FStar_Pprint.hardline
                                         (FStar_Pprint.op_Hat_Hat (str "and")
                                            (FStar_Pprint.op_Hat_Hat
                                               FStar_Pprint.space e21)))))))))))))
  | FStarC_Parser_AST.ElimForall (xs, p, vs) ->
      let xs1 = p_binders_sep xs in
      let p1 = p_noSeqTermAndComment false false p in
      let vs1 = FStarC_Pprint.separate_map FStar_Pprint.space p_atomicTerm vs in
      FStar_Pprint.op_Hat_Hat (str "eliminate")
        (FStar_Pprint.op_Hat_Hat FStar_Pprint.space
           (FStar_Pprint.op_Hat_Hat (str "forall")
              (FStar_Pprint.op_Hat_Hat FStar_Pprint.space
                 (FStar_Pprint.op_Hat_Hat xs1
                    (FStar_Pprint.op_Hat_Hat (str ".")
                       (FStar_Pprint.op_Hat_Hat FStar_Pprint.space
                          (FStar_Pprint.op_Hat_Hat p1
                             (FStar_Pprint.op_Hat_Hat FStar_Pprint.hardline
                                (FStar_Pprint.op_Hat_Hat (str "with")
                                   (FStar_Pprint.op_Hat_Hat
                                      FStar_Pprint.space vs1))))))))))
  | FStarC_Parser_AST.ElimExists (bs, p, q, b, e1) ->
      let head =
        let uu___ =
          let uu___1 =
            let uu___2 = p_binders_sep bs in
            FStar_Pprint.op_Hat_Hat uu___2 (str ".") in
          FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu___1 in
        FStar_Pprint.op_Hat_Hat (str "eliminate exists") uu___ in
      let p1 = p_noSeqTermAndComment false false p in
      let q1 = p_noSeqTermAndComment false false q in
      let e2 = p_noSeqTermAndComment false false e1 in
      let uu___ =
        let uu___1 =
          let uu___2 =
            let uu___3 =
              let uu___4 =
                let uu___5 =
                  let uu___6 =
                    let uu___7 =
                      let uu___8 =
                        let uu___9 =
                          let uu___10 = p_binders_sep [b] in
                          FStar_Pprint.op_Hat_Hat uu___10
                            (FStar_Pprint.op_Hat_Hat (str ".")
                               (FStar_Pprint.op_Hat_Hat FStar_Pprint.hardline
                                  e2)) in
                        FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu___9 in
                      FStar_Pprint.op_Hat_Hat (str "with") uu___8 in
                    FStar_Pprint.op_Hat_Hat FStar_Pprint.hardline uu___7 in
                  FStar_Pprint.op_Hat_Hat q1 uu___6 in
                FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu___5 in
              FStar_Pprint.op_Hat_Hat (str "returns") uu___4 in
            FStar_Pprint.op_Hat_Hat FStar_Pprint.hardline uu___3 in
          FStar_Pprint.op_Hat_Hat p1 uu___2 in
        FStar_Pprint.op_Hat_Hat FStar_Pprint.hardline uu___1 in
      FStar_Pprint.op_Hat_Hat head uu___
  | FStarC_Parser_AST.ElimImplies (p, q, e1) ->
      let p1 = p_tmFormula p in
      let q1 = p_tmFormula q in
      let e2 = p_noSeqTermAndComment false false e1 in
      FStar_Pprint.op_Hat_Hat (str "eliminate")
        (FStar_Pprint.op_Hat_Hat FStar_Pprint.space
           (FStar_Pprint.op_Hat_Hat p1
              (FStar_Pprint.op_Hat_Hat FStar_Pprint.space
                 (FStar_Pprint.op_Hat_Hat (str "==>")
                    (FStar_Pprint.op_Hat_Hat FStar_Pprint.space
                       (FStar_Pprint.op_Hat_Hat q1
                          (FStar_Pprint.op_Hat_Hat FStar_Pprint.hardline
                             (FStar_Pprint.op_Hat_Hat (str "with")
                                (FStar_Pprint.op_Hat_Hat FStar_Pprint.space
                                   e2)))))))))
  | FStarC_Parser_AST.ElimOr (p, q, r, x, e1, y, e2) ->
      let p1 = p_tmFormula p in
      let q1 = p_tmFormula q in
      let r1 = p_noSeqTermAndComment false false r in
      let x1 = p_binders_sep [x] in
      let e11 = p_noSeqTermAndComment false false e1 in
      let y1 = p_binders_sep [y] in
      let e21 = p_noSeqTermAndComment false false e2 in
      FStar_Pprint.op_Hat_Hat (str "eliminate")
        (FStar_Pprint.op_Hat_Hat FStar_Pprint.space
           (FStar_Pprint.op_Hat_Hat p1
              (FStar_Pprint.op_Hat_Hat FStar_Pprint.space
                 (FStar_Pprint.op_Hat_Hat (str "\\/")
                    (FStar_Pprint.op_Hat_Hat FStar_Pprint.space
                       (FStar_Pprint.op_Hat_Hat q1
                          (FStar_Pprint.op_Hat_Hat FStar_Pprint.hardline
                             (FStar_Pprint.op_Hat_Hat (str "returns")
                                (FStar_Pprint.op_Hat_Hat FStar_Pprint.space
                                   (FStar_Pprint.op_Hat_Hat r1
                                      (FStar_Pprint.op_Hat_Hat
                                         FStar_Pprint.hardline
                                         (FStar_Pprint.op_Hat_Hat
                                            (str "with")
                                            (FStar_Pprint.op_Hat_Hat
                                               FStar_Pprint.space
                                               (FStar_Pprint.op_Hat_Hat x1
                                                  (FStar_Pprint.op_Hat_Hat
                                                     FStar_Pprint.space
                                                     (FStar_Pprint.op_Hat_Hat
                                                        (str ".")
                                                        (FStar_Pprint.op_Hat_Hat
                                                           FStar_Pprint.space
                                                           (FStar_Pprint.op_Hat_Hat
                                                              e11
                                                              (FStar_Pprint.op_Hat_Hat
                                                                 FStar_Pprint.hardline
                                                                 (FStar_Pprint.op_Hat_Hat
                                                                    (
                                                                    str "and")
                                                                    (
                                                                    FStar_Pprint.op_Hat_Hat
                                                                    FStar_Pprint.space
                                                                    (FStar_Pprint.op_Hat_Hat
                                                                    y1
                                                                    (FStar_Pprint.op_Hat_Hat
                                                                    FStar_Pprint.space
                                                                    (FStar_Pprint.op_Hat_Hat
                                                                    (str ".")
                                                                    (FStar_Pprint.op_Hat_Hat
                                                                    FStar_Pprint.space
                                                                    e21)))))))))))))))))))))))))
  | FStarC_Parser_AST.ElimAnd (p, q, r, x, y, e1) ->
      let p1 = p_tmFormula p in
      let q1 = p_tmTuple q in
      let r1 = p_noSeqTermAndComment false false r in
      let xy = p_binders_sep [x; y] in
      let e2 = p_noSeqTermAndComment false false e1 in
      FStar_Pprint.op_Hat_Hat (str "eliminate")
        (FStar_Pprint.op_Hat_Hat FStar_Pprint.space
           (FStar_Pprint.op_Hat_Hat p1
              (FStar_Pprint.op_Hat_Hat FStar_Pprint.space
                 (FStar_Pprint.op_Hat_Hat (str "/\\")
                    (FStar_Pprint.op_Hat_Hat FStar_Pprint.space
                       (FStar_Pprint.op_Hat_Hat q1
                          (FStar_Pprint.op_Hat_Hat FStar_Pprint.hardline
                             (FStar_Pprint.op_Hat_Hat (str "returns")
                                (FStar_Pprint.op_Hat_Hat FStar_Pprint.space
                                   (FStar_Pprint.op_Hat_Hat r1
                                      (FStar_Pprint.op_Hat_Hat
                                         FStar_Pprint.hardline
                                         (FStar_Pprint.op_Hat_Hat
                                            (str "with")
                                            (FStar_Pprint.op_Hat_Hat
                                               FStar_Pprint.space
                                               (FStar_Pprint.op_Hat_Hat xy
                                                  (FStar_Pprint.op_Hat_Hat
                                                     FStar_Pprint.space
                                                     (FStar_Pprint.op_Hat_Hat
                                                        (str ".")
                                                        (FStar_Pprint.op_Hat_Hat
                                                           FStar_Pprint.space
                                                           e2)))))))))))))))))
  | FStarC_Parser_AST.LitDoc d -> d
  | uu___ -> p_typ ps pb e
and p_dec_wf (ps : Prims.bool) (pb : Prims.bool)
  (rel : FStarC_Parser_AST.term) (e : FStarC_Parser_AST.term) :
  FStar_Pprint.document=
  let uu___ =
    let uu___1 =
      let uu___2 = p_typ ps pb rel in
      let uu___3 =
        let uu___4 = p_typ ps pb e in
        FStar_Pprint.op_Hat_Hat uu___4 (str " }") in
      FStar_Pprint.op_Hat_Slash_Hat uu___2 uu___3 in
    FStar_Pprint.op_Hat_Hat (str "{:well-founded ") uu___1 in
  FStar_Pprint.group uu___
and p_calcStep (uu___ : Prims.bool) (uu___1 : FStarC_Parser_AST.calc_step) :
  FStar_Pprint.document=
  match uu___1 with
  | FStarC_Parser_AST.CalcStep (rel, just, next) ->
      let uu___2 =
        let uu___3 = p_noSeqTermAndComment false false rel in
        let uu___4 =
          let uu___5 =
            let uu___6 =
              let uu___7 =
                let uu___8 = p_noSeqTermAndComment false false just in
                let uu___9 =
                  let uu___10 =
                    let uu___11 =
                      let uu___12 =
                        let uu___13 = p_noSeqTermAndComment false false next in
                        FStar_Pprint.op_Hat_Hat uu___13 (str ";") in
                      FStar_Pprint.op_Hat_Hat FStar_Pprint.hardline uu___12 in
                    FStar_Pprint.op_Hat_Hat FStar_Pprint.rbrace uu___11 in
                  FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu___10 in
                FStar_Pprint.op_Hat_Hat uu___8 uu___9 in
              FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu___7 in
            FStar_Pprint.op_Hat_Hat FStar_Pprint.lbrace uu___6 in
          FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu___5 in
        FStar_Pprint.op_Hat_Hat uu___3 uu___4 in
      FStar_Pprint.group uu___2
and p_attrs_opt (isTopLevel : Prims.bool)
  (uu___ : FStarC_Parser_AST.term Prims.list FStar_Pervasives_Native.option)
  : FStar_Pprint.document=
  match uu___ with
  | FStar_Pervasives_Native.None -> FStar_Pprint.empty
  | FStar_Pervasives_Native.Some terms ->
      let uu___1 =
        let uu___2 =
          let uu___3 =
            FStarC_Pprint.separate_map (str "; ")
              (p_noSeqTermAndComment false false) terms in
          FStar_Pprint.op_Hat_Slash_Hat uu___3 (str "]") in
        FStar_Pprint.op_Hat_Slash_Hat
          (str (if isTopLevel then "[@@" else "[@@@")) uu___2 in
      FStar_Pprint.group uu___1
and p_typ (ps : Prims.bool) (pb : Prims.bool) (e : FStarC_Parser_AST.term) :
  FStar_Pprint.document=
  with_comment (p_typ' ps pb) e e.FStarC_Parser_AST.range
and p_typ_sep (ps : Prims.bool) (pb : Prims.bool)
  (e : FStarC_Parser_AST.term) :
  (FStar_Pprint.document * FStar_Pprint.document)=
  with_comment_sep (p_typ' ps pb) e e.FStarC_Parser_AST.range
and p_typ' (ps : Prims.bool) (pb : Prims.bool) (e : FStarC_Parser_AST.term) :
  FStar_Pprint.document=
  match e.FStarC_Parser_AST.tm with
  | FStarC_Parser_AST.QForall (bs, (uu___, trigger), e1) ->
      let binders_doc = p_binders true bs in
      let term_doc = p_noSeqTermAndComment ps pb e1 in
      (match trigger with
       | [] ->
           let uu___1 =
             let uu___2 =
               let uu___3 = p_quantifier e in
               FStar_Pprint.op_Hat_Hat uu___3 FStar_Pprint.space in
             FStar_Pprint.soft_surround (Prims.of_int (2)) Prims.int_zero
               uu___2 binders_doc FStar_Pprint.dot in
           prefix2 uu___1 term_doc
       | pats ->
           let uu___1 =
             let uu___2 =
               let uu___3 =
                 let uu___4 =
                   let uu___5 = p_quantifier e in
                   FStar_Pprint.op_Hat_Hat uu___5 FStar_Pprint.space in
                 FStar_Pprint.soft_surround (Prims.of_int (2)) Prims.int_zero
                   uu___4 binders_doc FStar_Pprint.dot in
               let uu___4 = p_trigger trigger in prefix2 uu___3 uu___4 in
             FStar_Pprint.group uu___2 in
           prefix2 uu___1 term_doc)
  | FStarC_Parser_AST.QExists (bs, (uu___, trigger), e1) ->
      let binders_doc = p_binders true bs in
      let term_doc = p_noSeqTermAndComment ps pb e1 in
      (match trigger with
       | [] ->
           let uu___1 =
             let uu___2 =
               let uu___3 = p_quantifier e in
               FStar_Pprint.op_Hat_Hat uu___3 FStar_Pprint.space in
             FStar_Pprint.soft_surround (Prims.of_int (2)) Prims.int_zero
               uu___2 binders_doc FStar_Pprint.dot in
           prefix2 uu___1 term_doc
       | pats ->
           let uu___1 =
             let uu___2 =
               let uu___3 =
                 let uu___4 =
                   let uu___5 = p_quantifier e in
                   FStar_Pprint.op_Hat_Hat uu___5 FStar_Pprint.space in
                 FStar_Pprint.soft_surround (Prims.of_int (2)) Prims.int_zero
                   uu___4 binders_doc FStar_Pprint.dot in
               let uu___4 = p_trigger trigger in prefix2 uu___3 uu___4 in
             FStar_Pprint.group uu___2 in
           prefix2 uu___1 term_doc)
  | FStarC_Parser_AST.QuantOp (uu___, bs, (uu___1, trigger), e1) ->
      let binders_doc = p_binders true bs in
      let term_doc = p_noSeqTermAndComment ps pb e1 in
      (match trigger with
       | [] ->
           let uu___2 =
             let uu___3 =
               let uu___4 = p_quantifier e in
               FStar_Pprint.op_Hat_Hat uu___4 FStar_Pprint.space in
             FStar_Pprint.soft_surround (Prims.of_int (2)) Prims.int_zero
               uu___3 binders_doc FStar_Pprint.dot in
           prefix2 uu___2 term_doc
       | pats ->
           let uu___2 =
             let uu___3 =
               let uu___4 =
                 let uu___5 =
                   let uu___6 = p_quantifier e in
                   FStar_Pprint.op_Hat_Hat uu___6 FStar_Pprint.space in
                 FStar_Pprint.soft_surround (Prims.of_int (2)) Prims.int_zero
                   uu___5 binders_doc FStar_Pprint.dot in
               let uu___5 = p_trigger trigger in prefix2 uu___4 uu___5 in
             FStar_Pprint.group uu___3 in
           prefix2 uu___2 term_doc)
  | uu___ -> p_simpleTerm ps pb e
and p_typ_top (style : annotation_style) (ps : Prims.bool) (pb : Prims.bool)
  (e : FStarC_Parser_AST.term) : FStar_Pprint.document=
  with_comment (p_typ_top' style ps pb) e e.FStarC_Parser_AST.range
and p_typ_top' (style : annotation_style) (ps : Prims.bool) (pb : Prims.bool)
  (e : FStarC_Parser_AST.term) : FStar_Pprint.document=
  p_tmArrow style true p_tmFormula e
and sig_as_binders_if_possible (t : FStarC_Parser_AST.term)
  (extra_space : Prims.bool) : FStar_Pprint.document=
  let s = if extra_space then FStar_Pprint.space else FStar_Pprint.empty in
  let uu___ = all_binders_annot t in
  if uu___
  then
    let uu___1 =
      p_typ_top (Binders ((Prims.of_int (4)), Prims.int_zero, true)) false
        false t in
    FStar_Pprint.op_Hat_Hat s uu___1
  else
    (let uu___2 =
       let uu___3 =
         let uu___4 =
           p_typ_top (Arrows ((Prims.of_int (2)), (Prims.of_int (2)))) false
             false t in
         FStar_Pprint.op_Hat_Hat s uu___4 in
       FStar_Pprint.op_Hat_Hat FStar_Pprint.colon uu___3 in
     FStar_Pprint.group uu___2)
and collapse_pats
  (pats :
    (FStar_Pprint.document * FStar_Pprint.document * Prims.bool * Prims.bool)
      Prims.list)
  : FStar_Pprint.document Prims.list=
  let fold_fun bs x =
    let uu___ = x in
    match uu___ with
    | (b1, t1, tc1, j1) ->
        (match bs with
         | [] -> [([b1], t1, tc1, j1)]
         | hd::tl ->
             let uu___1 = hd in
             (match uu___1 with
              | (b2s, t2, tc2, j2) ->
                  if ((t1 = t2) && j1) && j2
                  then ((FStarC_List.op_At b2s [b1]), t1, false, true) :: tl
                  else ([b1], t1, tc1, j1) :: hd :: tl)) in
  let p_collapsed_binder cb =
    let uu___ = cb in
    match uu___ with
    | (bs, typ, istcarg, uu___1) ->
        let body =
          match bs with
          | [] -> failwith "Impossible"
          | hd::tl ->
              let uu___2 =
                FStarC_List.fold_left
                  (fun x y ->
                     FStar_Pprint.op_Hat_Hat x
                       (FStar_Pprint.op_Hat_Hat FStar_Pprint.space y)) hd tl in
              cat_with_colon uu___2 typ in
        if istcarg then tc_arg body else soft_parens_with_nesting body in
  let binders = FStarC_List.fold_left fold_fun [] (FStarC_List.rev pats) in
  map_rev p_collapsed_binder binders
and pats_as_binders_if_possible (pats : FStarC_Parser_AST.pattern Prims.list)
  : (FStar_Pprint.document Prims.list * annotation_style)=
  let all_binders p =
    match p.FStarC_Parser_AST.pat with
    | FStarC_Parser_AST.PatAscribed (pat, (t, FStar_Pervasives_Native.None))
        ->
        (match ((pat.FStarC_Parser_AST.pat), (t.FStarC_Parser_AST.tm)) with
         | (FStarC_Parser_AST.PatVar (lid, aqual, attrs),
            FStarC_Parser_AST.Refine
            ({ FStarC_Parser_AST.b = FStarC_Parser_AST.Annotated (lid', t1);
               FStarC_Parser_AST.brange = uu___;
               FStarC_Parser_AST.blevel = uu___1;
               FStarC_Parser_AST.aqual = uu___2;
               FStarC_Parser_AST.battributes = uu___3;_},
             phi)) when
             let uu___4 = FStarC_Ident.string_of_id lid in
             let uu___5 = FStarC_Ident.string_of_id lid' in uu___4 = uu___5
             ->
             let uu___4 =
               let uu___5 = p_ident lid in
               p_refinement' aqual attrs uu___5 t1 phi in
             (match uu___4 with
              | (x, y) -> FStar_Pervasives_Native.Some (x, y, false, false))
         | (FStarC_Parser_AST.PatVar (lid, aqual, attrs), uu___) ->
             let is_tc =
               aqual =
                 (FStar_Pervasives_Native.Some FStarC_Parser_AST.TypeClassArg) in
             let is_meta =
               match aqual with
               | FStar_Pervasives_Native.Some (FStarC_Parser_AST.Meta uu___1)
                   -> true
               | uu___1 -> false in
             let uu___1 =
               let uu___2 =
                 let uu___3 = FStarC_Pprint.optional p_aqual aqual in
                 let uu___4 =
                   let uu___5 = p_attributes false attrs in
                   let uu___6 = p_ident lid in
                   FStar_Pprint.op_Hat_Hat uu___5 uu___6 in
                 FStar_Pprint.op_Hat_Hat uu___3 uu___4 in
               let uu___3 = p_tmEqNoRefinement t in
               (uu___2, uu___3, is_tc,
                 ((Prims.op_Negation is_tc) && (Prims.op_Negation is_meta))) in
             FStar_Pervasives_Native.Some uu___1
         | uu___ -> FStar_Pervasives_Native.None)
    | uu___ -> FStar_Pervasives_Native.None in
  let uu___ = map_if_all all_binders pats in
  match uu___ with
  | FStar_Pervasives_Native.Some bs ->
      let uu___1 = collapse_pats bs in
      (uu___1, (Binders ((Prims.of_int (4)), Prims.int_zero, true)))
  | FStar_Pervasives_Native.None ->
      let uu___1 = FStarC_List.map p_atomicPattern pats in
      (uu___1, (Binders ((Prims.of_int (4)), Prims.int_zero, false)))
and p_quantifier (e : FStarC_Parser_AST.term) : FStar_Pprint.document=
  match e.FStarC_Parser_AST.tm with
  | FStarC_Parser_AST.QForall uu___ -> str "forall"
  | FStarC_Parser_AST.QExists uu___ -> str "exists"
  | FStarC_Parser_AST.QuantOp (i, uu___, uu___1, uu___2) -> p_ident i
  | uu___ ->
      failwith "Imposible : p_quantifier called on a non-quantifier term"
and p_trigger (uu___ : FStarC_Parser_AST.term Prims.list Prims.list) :
  FStar_Pprint.document=
  match uu___ with
  | [] -> FStar_Pprint.empty
  | pats ->
      let uu___1 =
        let uu___2 =
          let uu___3 =
            let uu___4 =
              let uu___5 =
                let uu___6 = p_disjunctivePats pats in
                FStar_Pprint.jump (Prims.of_int (2)) Prims.int_zero uu___6 in
              FStar_Pprint.op_Hat_Hat uu___5 FStar_Pprint.rbrace in
            FStar_Pprint.op_Hat_Slash_Hat (str "pattern") uu___4 in
          FStar_Pprint.op_Hat_Hat FStar_Pprint.colon uu___3 in
        FStar_Pprint.op_Hat_Hat FStar_Pprint.lbrace uu___2 in
      FStar_Pprint.group uu___1
and p_disjunctivePats (pats : FStarC_Parser_AST.term Prims.list Prims.list) :
  FStar_Pprint.document=
  FStarC_Pprint.separate_map (str "\\/") p_conjunctivePats pats
and p_conjunctivePats (pats : FStarC_Parser_AST.term Prims.list) :
  FStar_Pprint.document=
  let uu___ =
    FStarC_Pprint.separate_map
      (FStar_Pprint.op_Hat_Hat FStar_Pprint.semi break1) p_appTerm pats in
  FStar_Pprint.group uu___
and p_simpleTerm (ps : Prims.bool) (pb : Prims.bool)
  (e : FStarC_Parser_AST.term) : FStar_Pprint.document=
  match e.FStarC_Parser_AST.tm with
  | FStarC_Parser_AST.Function (branches, uu___) ->
      let uu___1 =
        let uu___2 =
          let uu___3 =
            separate_map_last FStar_Pprint.hardline p_patternBranch branches in
          FStar_Pprint.op_Hat_Slash_Hat (str "function") uu___3 in
        FStar_Pprint.group uu___2 in
      let uu___2 = paren_if (ps || pb) in uu___2 uu___1
  | FStarC_Parser_AST.Abs (pats, e1) ->
      let uu___ = p_term_sep false pb e1 in
      (match uu___ with
       | (comm, doc) ->
           let prefix =
             let uu___1 =
               let uu___2 =
                 FStarC_Pprint.separate_map break1 p_atomicPattern pats in
               FStar_Pprint.op_Hat_Slash_Hat uu___2 FStar_Pprint.rarrow in
             op_Hat_Slash_Plus_Hat (str "fun") uu___1 in
           let uu___1 = paren_if ps in
           uu___1
             (if comm <> FStar_Pprint.empty
              then
                FStar_Pprint.op_Hat_Hat prefix
                  (FStar_Pprint.op_Hat_Hat FStar_Pprint.hardline
                     (FStar_Pprint.op_Hat_Hat comm
                        (FStar_Pprint.op_Hat_Hat FStar_Pprint.hardline doc)))
              else FStar_Pprint.group (op_Hat_Slash_Plus_Hat prefix doc)))
  | uu___ -> p_tmIff e
and p_maybeFocusArrow (b : Prims.bool) : FStar_Pprint.document=
  if b then str "~>" else FStar_Pprint.rarrow
and p_patternBranch (pb : Prims.bool)
  (uu___ :
    (FStarC_Parser_AST.pattern * FStarC_Parser_AST.term
      FStar_Pervasives_Native.option * FStarC_Parser_AST.term))
  : FStar_Pprint.document=
  match uu___ with
  | (pat, when_opt, e) ->
      let one_pattern_branch p =
        let branch =
          match when_opt with
          | FStar_Pervasives_Native.None ->
              let uu___1 =
                let uu___2 =
                  let uu___3 =
                    let uu___4 = p_tuplePattern p in
                    FStar_Pprint.op_Hat_Hat uu___4
                      (FStar_Pprint.op_Hat_Hat FStar_Pprint.space
                         FStar_Pprint.rarrow) in
                  FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu___3 in
                FStar_Pprint.op_Hat_Hat FStar_Pprint.bar uu___2 in
              FStar_Pprint.group uu___1
          | FStar_Pervasives_Native.Some f ->
              let uu___1 =
                let uu___2 =
                  let uu___3 =
                    let uu___4 =
                      let uu___5 =
                        let uu___6 = p_tuplePattern p in
                        FStar_Pprint.op_Hat_Slash_Hat uu___6 (str "when") in
                      FStar_Pprint.group uu___5 in
                    let uu___5 =
                      let uu___6 =
                        let uu___7 = p_tmFormula f in
                        [uu___7; FStar_Pprint.rarrow] in
                      FStar_Pprint.flow break1 uu___6 in
                    FStar_Pprint.op_Hat_Slash_Hat uu___4 uu___5 in
                  FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu___3 in
                FStar_Pprint.op_Hat_Hat FStar_Pprint.bar uu___2 in
              FStar_Pprint.hang (Prims.of_int (2)) uu___1 in
        let uu___1 = p_term_sep false pb e in
        match uu___1 with
        | (comm, doc) ->
            if pb
            then
              (if comm = FStar_Pprint.empty
               then FStar_Pprint.group (op_Hat_Slash_Plus_Hat branch doc)
               else
                 (let uu___3 =
                    let uu___4 =
                      let uu___5 =
                        let uu___6 =
                          inline_comment_or_above comm doc FStar_Pprint.empty in
                        jump2 uu___6 in
                      FStar_Pprint.op_Hat_Hat branch uu___5 in
                    FStar_Pprint.ifflat
                      (FStar_Pprint.group
                         (op_Hat_Slash_Plus_Hat branch
                            (FStar_Pprint.op_Hat_Hat doc
                               (FStar_Pprint.op_Hat_Hat break1 comm))))
                      uu___4 in
                  FStar_Pprint.group uu___3))
            else
              if comm <> FStar_Pprint.empty
              then
                op_Hat_Slash_Plus_Hat branch
                  (FStar_Pprint.op_Hat_Hat comm
                     (FStar_Pprint.op_Hat_Hat FStar_Pprint.hardline doc))
              else op_Hat_Slash_Plus_Hat branch doc in
      (match pat.FStarC_Parser_AST.pat with
       | FStarC_Parser_AST.PatOr pats ->
           (match FStarC_List.rev pats with
            | hd::tl ->
                let last_pat_branch = one_pattern_branch hd in
                let uu___1 =
                  let uu___2 =
                    let uu___3 =
                      let uu___4 =
                        FStarC_Pprint.separate_map
                          (FStar_Pprint.op_Hat_Hat break1
                             (FStar_Pprint.op_Hat_Hat FStar_Pprint.bar
                                FStar_Pprint.space)) p_tuplePattern
                          (FStarC_List.rev tl) in
                      FStar_Pprint.op_Hat_Slash_Hat uu___4 last_pat_branch in
                    FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu___3 in
                  FStar_Pprint.op_Hat_Hat FStar_Pprint.bar uu___2 in
                FStar_Pprint.group uu___1
            | [] -> failwith "Impossible: disjunctive pattern can't be empty")
       | uu___1 -> one_pattern_branch pat)
and p_tmIff (e : FStarC_Parser_AST.term) : FStar_Pprint.document=
  match e.FStarC_Parser_AST.tm with
  | FStarC_Parser_AST.Op (id, e1::e2::[]) when
      let uu___ = FStarC_Ident.string_of_id id in uu___ = "<==>" ->
      let uu___ = p_tmImplies e1 in
      let uu___1 = p_tmIff e2 in infix0 (str "<==>") uu___ uu___1
  | uu___ -> p_tmImplies e
and p_tmImplies (e : FStarC_Parser_AST.term) : FStar_Pprint.document=
  match e.FStarC_Parser_AST.tm with
  | FStarC_Parser_AST.Op (id, e1::e2::[]) when
      let uu___ = FStarC_Ident.string_of_id id in uu___ = "==>" ->
      let uu___ =
        p_tmArrow (Arrows ((Prims.of_int (2)), (Prims.of_int (2)))) false
          p_tmFormula e1 in
      let uu___1 = p_tmImplies e2 in infix0 (str "==>") uu___ uu___1
  | uu___ ->
      p_tmArrow (Arrows ((Prims.of_int (2)), (Prims.of_int (2)))) false
        p_tmFormula e
and format_sig (style : annotation_style)
  (terms : FStar_Pprint.document Prims.list) (ret_d : FStar_Pprint.document)
  (no_last_op : Prims.bool) (flat_space : Prims.bool) :
  FStar_Pprint.document=
  let uu___ =
    match style with
    | Arrows (n, ln) ->
        (n, ln,
          (FStar_Pprint.op_Hat_Hat FStar_Pprint.space
             (FStar_Pprint.op_Hat_Hat FStar_Pprint.rarrow break1)),
          (FStar_Pprint.op_Hat_Hat FStar_Pprint.rarrow FStar_Pprint.space))
    | Binders (n, ln, parens) ->
        (n, ln, break1,
          (FStar_Pprint.op_Hat_Hat FStar_Pprint.colon FStar_Pprint.space)) in
  match uu___ with
  | (n, last_n, sep, last_op) ->
      let last_op1 =
        if
          ((FStarC_List.length terms) > Prims.int_zero) &&
            (Prims.op_Negation no_last_op)
        then last_op
        else FStar_Pprint.empty in
      let one_line_space =
        if
          (Prims.op_Negation (ret_d = FStar_Pprint.empty)) ||
            (Prims.op_Negation no_last_op)
        then FStar_Pprint.space
        else FStar_Pprint.empty in
      let single_line_arg_indent = FStar_Pprint.repeat n FStar_Pprint.space in
      let fs = if flat_space then FStar_Pprint.space else FStar_Pprint.empty in
      (match FStarC_List.length terms with
       | uu___1 when uu___1 = Prims.int_zero -> ret_d
       | uu___1 ->
           let uu___2 =
             let uu___3 =
               let uu___4 =
                 let uu___5 =
                   let uu___6 =
                     let uu___7 =
                       let uu___8 =
                         let uu___9 =
                           FStarC_List.map
                             (fun x ->
                                FStar_Pprint.align
                                  (FStar_Pprint.hang (Prims.of_int (2)) x))
                             terms in
                         FStar_Pprint.separate
                           (FStar_Pprint.op_Hat_Hat sep
                              single_line_arg_indent) uu___9 in
                       FStar_Pprint.op_Hat_Hat single_line_arg_indent uu___8 in
                     jump2 uu___7 in
                   FStar_Pprint.ifflat
                     (FStar_Pprint.op_Hat_Hat fs
                        (FStar_Pprint.separate sep terms)) uu___6 in
                 FStar_Pprint.group uu___5 in
               FStar_Pprint.prefix n Prims.int_one uu___4
                 (FStar_Pprint.align
                    (FStar_Pprint.hang last_n
                       (FStar_Pprint.op_Hat_Hat last_op1 ret_d))) in
             FStar_Pprint.ifflat
               (FStar_Pprint.op_Hat_Hat fs
                  (FStar_Pprint.op_Hat_Hat (FStar_Pprint.separate sep terms)
                     (FStar_Pprint.op_Hat_Hat one_line_space
                        (FStar_Pprint.op_Hat_Hat last_op1 ret_d)))) uu___3 in
           FStar_Pprint.group uu___2)
and p_tmArrow (style : annotation_style) (flat_space : Prims.bool)
  (p_Tm : FStarC_Parser_AST.term -> FStar_Pprint.document)
  (e : FStarC_Parser_AST.term) : FStar_Pprint.document=
  let uu___ =
    match style with
    | Arrows uu___1 -> p_tmArrow' p_Tm e
    | Binders uu___1 -> collapse_binders style p_Tm e in
  match uu___ with
  | (terms, ret_d) -> format_sig style terms ret_d false flat_space
and p_tmArrow' (p_Tm : FStarC_Parser_AST.term -> FStar_Pprint.document)
  (e : FStarC_Parser_AST.term) :
  (FStar_Pprint.document Prims.list * FStar_Pprint.document)=
  match e.FStarC_Parser_AST.tm with
  | FStarC_Parser_AST.Product (bs, tgt) ->
      let bs_ds = FStarC_List.map (fun b -> p_binder false b) bs in
      let uu___ = p_tmArrow' p_Tm tgt in
      (match uu___ with
       | (bs_ds', ret) -> ((FStarC_List.op_At bs_ds bs_ds'), ret))
  | uu___ -> let uu___1 = p_Tm e in ([], uu___1)
and collapse_binders (style : annotation_style)
  (p_Tm : FStarC_Parser_AST.term -> FStar_Pprint.document)
  (e : FStarC_Parser_AST.term) :
  (FStar_Pprint.document Prims.list * FStar_Pprint.document)=
  let atomize =
    match style with | Binders (uu___, uu___1, a) -> a | uu___ -> false in
  let wrap is_tc doc =
    if is_tc
    then tc_arg doc
    else if atomize then soft_parens_with_nesting doc else doc in
  let rec accumulate_binders p_Tm1 e1 =
    match e1.FStarC_Parser_AST.tm with
    | FStarC_Parser_AST.Product (bs, tgt) ->
        let bs_ds =
          FStarC_List.map
            (fun b ->
               let uu___ = p_binder' true false b in
               let uu___1 = is_tc_binder b in
               let uu___2 = is_joinable_binder b in (uu___, uu___1, uu___2))
            bs in
        let uu___ = accumulate_binders p_Tm1 tgt in
        (match uu___ with
         | (bs_ds', ret) -> ((FStarC_List.op_At bs_ds bs_ds'), ret))
    | uu___ -> let uu___1 = p_Tm1 e1 in ([], uu___1) in
  let fold_fun bs x =
    let uu___ = x in
    match uu___ with
    | ((b1, t1), tc1, j1) ->
        (match bs with
         | [] -> [([b1], t1, tc1, j1)]
         | hd::tl ->
             let uu___1 = hd in
             (match uu___1 with
              | (b2s, t2, tc2, j2) ->
                  (match (t1, t2) with
                   | (FStar_Pervasives_Native.Some (typ1, catf1),
                      FStar_Pervasives_Native.Some (typ2, uu___2)) when
                       ((typ1 = typ2) && j1) && j2 ->
                       ((FStarC_List.op_At b2s [b1]), t1, false, true) :: tl
                   | uu___2 -> ([b1], t1, tc1, j1) :: bs))) in
  let p_collapsed_binder cb =
    let uu___ = cb in
    match uu___ with
    | (bs, t, is_tc, uu___1) ->
        (match t with
         | FStar_Pervasives_Native.None ->
             (match bs with
              | b::[] -> wrap is_tc b
              | uu___2 -> failwith "Impossible")
         | FStar_Pervasives_Native.Some (typ, f) ->
             (match bs with
              | [] -> failwith "Impossible"
              | hd::tl ->
                  let uu___2 =
                    let uu___3 =
                      FStarC_List.fold_left
                        (fun x y ->
                           FStar_Pprint.op_Hat_Hat x
                             (FStar_Pprint.op_Hat_Hat FStar_Pprint.space y))
                        hd tl in
                    f uu___3 typ in
                  wrap is_tc uu___2)) in
  let uu___ = accumulate_binders p_Tm e in
  match uu___ with
  | (bs_ds, ret_d) ->
      let binders = FStarC_List.fold_left fold_fun [] bs_ds in
      let uu___1 = map_rev p_collapsed_binder binders in (uu___1, ret_d)
and p_tmFormula (e : FStarC_Parser_AST.term) : FStar_Pprint.document=
  let conj =
    FStar_Pprint.op_Hat_Hat FStar_Pprint.space
      (FStar_Pprint.op_Hat_Hat (str "/\\") break1) in
  let disj =
    FStar_Pprint.op_Hat_Hat FStar_Pprint.space
      (FStar_Pprint.op_Hat_Hat (str "\\/") break1) in
  let formula = p_tmDisjunction e in
  FStarC_Pprint.flow_map disj
    (fun d -> FStarC_Pprint.flow_map conj (fun x -> FStar_Pprint.group x) d)
    formula
and p_tmDisjunction (e : FStarC_Parser_AST.term) :
  FStar_Pprint.document Prims.list Prims.list=
  match e.FStarC_Parser_AST.tm with
  | FStarC_Parser_AST.Op (id, e1::e2::[]) when
      let uu___ = FStarC_Ident.string_of_id id in uu___ = "\\/" ->
      let uu___ = p_tmDisjunction e1 in
      let uu___1 = let uu___2 = p_tmConjunction e2 in [uu___2] in
      FStarC_List.op_At uu___ uu___1
  | uu___ -> let uu___1 = p_tmConjunction e in [uu___1]
and p_tmConjunction (e : FStarC_Parser_AST.term) :
  FStar_Pprint.document Prims.list=
  match e.FStarC_Parser_AST.tm with
  | FStarC_Parser_AST.Op (id, e1::e2::[]) when
      let uu___ = FStarC_Ident.string_of_id id in uu___ = "/\\" ->
      let uu___ = p_tmConjunction e1 in
      let uu___1 = let uu___2 = p_tmTuple e2 in [uu___2] in
      FStarC_List.op_At uu___ uu___1
  | uu___ -> let uu___1 = p_tmTuple e in [uu___1]
and p_tmTuple (e : FStarC_Parser_AST.term) : FStar_Pprint.document=
  with_comment p_tmTuple' e e.FStarC_Parser_AST.range
and p_tmTuple' (e : FStarC_Parser_AST.term) : FStar_Pprint.document=
  match e.FStarC_Parser_AST.tm with
  | FStarC_Parser_AST.Construct (lid, args) when
      (is_tuple_constructor lid) && (all1_explicit args) ->
      FStarC_Pprint.separate_map
        (FStar_Pprint.op_Hat_Hat FStar_Pprint.comma break1)
        (fun uu___ -> match uu___ with | (e1, uu___1) -> p_tmEq e1) args
  | uu___ -> p_tmEq e
and paren_if_gt (curr : Prims.int) (mine : Prims.int)
  (doc : FStar_Pprint.document) : FStar_Pprint.document=
  if mine > curr
  then
    FStar_Pprint.group
      (FStar_Pprint.op_Hat_Hat FStar_Pprint.lparen
         (FStar_Pprint.op_Hat_Hat doc FStar_Pprint.rparen))
  else doc
and p_tmEqWith (p_X : FStarC_Parser_AST.term -> FStar_Pprint.document)
  (e : FStarC_Parser_AST.term) : FStar_Pprint.document=
  let n =
    max_level
      (FStarC_List.op_At [colon_equals; pipe_right] operatorInfix0ad12) in
  p_tmEqWith' p_X n e
and p_tmEqWith' (p_X : FStarC_Parser_AST.term -> FStar_Pprint.document)
  (curr : Prims.int) (e : FStarC_Parser_AST.term) : FStar_Pprint.document=
  match e.FStarC_Parser_AST.tm with
  | FStarC_Parser_AST.Op (op, e1::e2::[]) when
      (let uu___ =
         (let uu___1 = FStarC_Ident.string_of_id op in uu___1 = "==>") ||
           (let uu___1 = FStarC_Ident.string_of_id op in uu___1 = "<==>") in
       Prims.op_Negation uu___) &&
        (((is_operatorInfix0ad12 op) ||
            (let uu___ = FStarC_Ident.string_of_id op in uu___ = "="))
           || (let uu___ = FStarC_Ident.string_of_id op in uu___ = "|>"))
      ->
      let op1 = FStarC_Ident.string_of_id op in
      let uu___ = levels op1 in
      (match uu___ with
       | (left, mine, right) ->
           let uu___1 =
             let uu___2 = p_tmEqWith' p_X left e1 in
             let uu___3 = p_tmEqWith' p_X right e2 in
             infix0 (str op1) uu___2 uu___3 in
           paren_if_gt curr mine uu___1)
  | FStarC_Parser_AST.Op (id, e1::e2::[]) when
      let uu___ = FStarC_Ident.string_of_id id in uu___ = ":=" ->
      let uu___ =
        let uu___1 = p_tmEqWith p_X e1 in
        let uu___2 =
          let uu___3 =
            let uu___4 =
              let uu___5 = p_tmEqWith p_X e2 in
              op_Hat_Slash_Plus_Hat FStar_Pprint.equals uu___5 in
            FStar_Pprint.op_Hat_Hat FStar_Pprint.colon uu___4 in
          FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu___3 in
        FStar_Pprint.op_Hat_Hat uu___1 uu___2 in
      FStar_Pprint.group uu___
  | FStarC_Parser_AST.Op (id, e1::[]) when
      let uu___ = FStarC_Ident.string_of_id id in uu___ = "-" ->
      let uu___ = levels "-" in
      (match uu___ with
       | (left, mine, right) ->
           let uu___1 = p_tmEqWith' p_X mine e1 in
           FStar_Pprint.op_Hat_Slash_Hat FStar_Pprint.minus uu___1)
  | uu___ -> p_tmNoEqWith p_X e
and p_tmNoEqWith (p_X : FStarC_Parser_AST.term -> FStar_Pprint.document)
  (e : FStarC_Parser_AST.term) : FStar_Pprint.document=
  let n = max_level [colon_colon; amp; opinfix3l; opinfix3r; opinfix4] in
  p_tmNoEqWith' false p_X n e
and p_tmNoEqWith' (inside_tuple : Prims.bool)
  (p_X : FStarC_Parser_AST.term -> FStar_Pprint.document) (curr : Prims.int)
  (e : FStarC_Parser_AST.term) : FStar_Pprint.document=
  match e.FStarC_Parser_AST.tm with
  | FStarC_Parser_AST.Construct (lid, (e1, uu___)::(e2, uu___1)::[]) when
      FStarC_Ident.lid_equals lid FStarC_Parser_Const.cons_lid ->
      let op = "::" in
      let uu___2 = levels op in
      (match uu___2 with
       | (left, mine, right) ->
           let uu___3 =
             let uu___4 = p_tmNoEqWith' false p_X left e1 in
             let uu___5 = p_tmNoEqWith' false p_X right e2 in
             infix0 (str op) uu___4 uu___5 in
           paren_if_gt curr mine uu___3)
  | FStarC_Parser_AST.Sum (binders, res) ->
      let op = "&" in
      let uu___ = levels op in
      (match uu___ with
       | (left, mine, right) ->
           let p_dsumfst bt =
             match bt with
             | FStar_Pervasives.Inl b ->
                 let uu___1 = p_binder false b in
                 FStar_Pprint.op_Hat_Hat uu___1
                   (FStar_Pprint.op_Hat_Hat FStar_Pprint.space
                      (FStar_Pprint.op_Hat_Hat (str op) break1))
             | FStar_Pervasives.Inr t ->
                 let uu___1 = p_tmNoEqWith' false p_X left t in
                 FStar_Pprint.op_Hat_Hat uu___1
                   (FStar_Pprint.op_Hat_Hat FStar_Pprint.space
                      (FStar_Pprint.op_Hat_Hat (str op) break1)) in
           let uu___1 =
             let uu___2 = FStarC_Pprint.concat_map p_dsumfst binders in
             let uu___3 = p_tmNoEqWith' false p_X right res in
             FStar_Pprint.op_Hat_Hat uu___2 uu___3 in
           paren_if_gt curr mine uu___1)
  | FStarC_Parser_AST.Op (op, e1::e2::[]) when is_operatorInfix34 op ->
      let op1 = FStarC_Ident.string_of_id op in
      let uu___ = levels op1 in
      (match uu___ with
       | (left, mine, right) ->
           let uu___1 =
             let uu___2 = p_tmNoEqWith' false p_X left e1 in
             let uu___3 = p_tmNoEqWith' false p_X right e2 in
             infix0 (str op1) uu___2 uu___3 in
           paren_if_gt curr mine uu___1)
  | FStarC_Parser_AST.Record (with_opt, record_fields) ->
      let uu___ =
        let uu___1 = default_or_map FStar_Pprint.empty p_with_clause with_opt in
        let uu___2 =
          separate_map_last
            (FStar_Pprint.op_Hat_Hat FStar_Pprint.semi break1) p_simpleDef
            record_fields in
        FStar_Pprint.op_Hat_Hat uu___1 uu___2 in
      braces_with_nesting uu___
  | FStarC_Parser_AST.Op (id, e1::[]) when
      let uu___ = FStarC_Ident.string_of_id id in uu___ = "~" ->
      let uu___ =
        let uu___1 = p_atomicTerm e1 in
        FStar_Pprint.op_Hat_Hat (str "~") uu___1 in
      FStar_Pprint.group uu___
  | FStarC_Parser_AST.Paren p when inside_tuple ->
      (match p.FStarC_Parser_AST.tm with
       | FStarC_Parser_AST.Op (id, e1::e2::[]) when
           let uu___ = FStarC_Ident.string_of_id id in uu___ = "*" ->
           let op = "*" in
           let uu___ = levels op in
           (match uu___ with
            | (left, mine, right) ->
                let uu___1 =
                  let uu___2 = p_tmNoEqWith' true p_X left e1 in
                  let uu___3 = p_tmNoEqWith' true p_X right e2 in
                  infix0 (str op) uu___2 uu___3 in
                paren_if_gt curr mine uu___1)
       | uu___ -> p_X e)
  | uu___ -> p_X e
and p_tmEqNoRefinement (e : FStarC_Parser_AST.term) : FStar_Pprint.document=
  p_tmEqWith p_appTerm e
and p_tmEq (e : FStarC_Parser_AST.term) : FStar_Pprint.document=
  p_tmEqWith p_tmRefinement e
and p_tmNoEq (e : FStarC_Parser_AST.term) : FStar_Pprint.document=
  p_tmNoEqWith p_tmRefinement e
and p_tmRefinement (e : FStarC_Parser_AST.term) : FStar_Pprint.document=
  match e.FStarC_Parser_AST.tm with
  | FStarC_Parser_AST.NamedTyp (lid, e1) ->
      let uu___ =
        let uu___1 = p_lident lid in
        let uu___2 =
          let uu___3 = p_appTerm e1 in
          FStar_Pprint.op_Hat_Slash_Hat FStar_Pprint.colon uu___3 in
        FStar_Pprint.op_Hat_Slash_Hat uu___1 uu___2 in
      FStar_Pprint.group uu___
  | FStarC_Parser_AST.Refine (b, phi) -> p_refinedBinder b phi
  | uu___ -> p_appTerm e
and p_with_clause (e : FStarC_Parser_AST.term) : FStar_Pprint.document=
  let uu___ = p_appTerm e in
  FStar_Pprint.op_Hat_Hat uu___
    (FStar_Pprint.op_Hat_Hat FStar_Pprint.space
       (FStar_Pprint.op_Hat_Hat (str "with") break1))
and p_refinedBinder (b : FStarC_Parser_AST.binder)
  (phi : FStarC_Parser_AST.term) : FStar_Pprint.document=
  match b.FStarC_Parser_AST.b with
  | FStarC_Parser_AST.Annotated (lid, t) ->
      let uu___ = p_lident lid in
      p_refinement b.FStarC_Parser_AST.aqual b.FStarC_Parser_AST.battributes
        uu___ t phi
  | FStarC_Parser_AST.Variable lid ->
      let uu___ = p_lident lid in
      let uu___1 =
        let uu___2 = FStarC_Ident.range_of_id lid in
        FStarC_Parser_AST.mk_term FStarC_Parser_AST.Wild uu___2
          FStarC_Parser_AST.Type_level in
      p_refinement b.FStarC_Parser_AST.aqual b.FStarC_Parser_AST.battributes
        uu___ uu___1 phi
  | FStarC_Parser_AST.NoName uu___ ->
      let uu___1 =
        let uu___2 = FStarC_Parser_AST.binder_to_string b in
        FStarC_Format.fmt1
          "Impossible: a refined binder ought to be annotated (%s)" uu___2 in
      failwith uu___1
and p_simpleDef (ps : Prims.bool)
  (uu___ : (FStarC_Ident.lid * FStarC_Parser_AST.term)) :
  FStar_Pprint.document=
  match uu___ with
  | (lid, e) ->
      let uu___1 =
        let uu___2 = p_qlidentOrOperator lid in
        let uu___3 =
          let uu___4 = p_noSeqTermAndComment ps false e in
          FStar_Pprint.op_Hat_Slash_Hat FStar_Pprint.equals uu___4 in
        FStar_Pprint.op_Hat_Slash_Hat uu___2 uu___3 in
      FStar_Pprint.group uu___1
and p_appTerm (e : FStarC_Parser_AST.term) : FStar_Pprint.document=
  match e.FStarC_Parser_AST.tm with
  | FStarC_Parser_AST.App uu___ when is_general_application e ->
      let uu___1 = head_and_args e in
      (match uu___1 with
       | (head, args) ->
           (match args with
            | e1::e2::[] when
                (FStar_Pervasives_Native.snd e1) = FStarC_Parser_AST.Infix ->
                let uu___2 = p_argTerm e1 in
                let uu___3 =
                  let uu___4 =
                    let uu___5 =
                      let uu___6 =
                        let uu___7 = p_indexingTerm head in
                        FStar_Pprint.op_Hat_Hat uu___7 (str "`") in
                      FStar_Pprint.op_Hat_Hat (str "`") uu___6 in
                    FStar_Pprint.group uu___5 in
                  let uu___5 = p_argTerm e2 in
                  FStar_Pprint.op_Hat_Slash_Hat uu___4 uu___5 in
                FStar_Pprint.op_Hat_Slash_Hat uu___2 uu___3
            | uu___2 ->
                let uu___3 =
                  let uu___4 = p_indexingTerm head in (uu___4, args) in
                (match uu___3 with
                 | (head_doc, args1) ->
                     let uu___4 =
                       soft_surround_map_or_flow (Prims.of_int (2))
                         Prims.int_zero head_doc
                         (FStar_Pprint.op_Hat_Hat head_doc FStar_Pprint.space)
                         break1 FStar_Pprint.empty p_argTerm args1 in
                     FStar_Pprint.group uu___4)))
  | FStarC_Parser_AST.Construct (lid, args) when
      ((is_general_construction e) &&
         (let uu___ = (is_dtuple_constructor lid) && (all1_explicit args) in
          Prims.op_Negation uu___))
        &&
        (let uu___ = (is_tuple_constructor lid) && (all1_explicit args) in
         Prims.op_Negation uu___)
      ->
      (match args with
       | [] -> p_quident lid
       | arg::[] ->
           let uu___ =
             let uu___1 = p_quident lid in
             let uu___2 = p_argTerm arg in
             FStar_Pprint.op_Hat_Slash_Hat uu___1 uu___2 in
           FStar_Pprint.group uu___
       | hd::tl ->
           let uu___ =
             let uu___1 =
               let uu___2 =
                 let uu___3 = p_quident lid in
                 let uu___4 = p_argTerm hd in prefix2 uu___3 uu___4 in
               FStar_Pprint.group uu___2 in
             let uu___2 =
               let uu___3 = FStarC_Pprint.separate_map break1 p_argTerm tl in
               jump2 uu___3 in
             FStar_Pprint.op_Hat_Hat uu___1 uu___2 in
           FStar_Pprint.group uu___)
  | uu___ -> p_indexingTerm e
and p_argTerm (arg_imp : (FStarC_Parser_AST.term * FStarC_Parser_AST.imp)) :
  FStar_Pprint.document=
  match arg_imp with
  | (u, FStarC_Parser_AST.UnivApp) -> p_universe u
  | (e, FStarC_Parser_AST.Hash) ->
      let uu___ = p_indexingTerm e in FStar_Pprint.op_Hat_Hat (str "#") uu___
  | (e, FStarC_Parser_AST.HashBrace t) ->
      let uu___ =
        let uu___1 = p_indexingTerm t in
        let uu___2 =
          let uu___3 = p_indexingTerm e in
          FStar_Pprint.op_Hat_Hat (str "]") uu___3 in
        FStar_Pprint.op_Hat_Hat uu___1 uu___2 in
      FStar_Pprint.op_Hat_Hat (str "#[") uu___
  | (e, FStarC_Parser_AST.Infix) -> p_indexingTerm e
  | (e, FStarC_Parser_AST.Nothing) -> p_indexingTerm e
and p_indexingTerm_aux
  (exit : FStarC_Parser_AST.term -> FStar_Pprint.document)
  (e : FStarC_Parser_AST.term) : FStar_Pprint.document=
  match e.FStarC_Parser_AST.tm with
  | FStarC_Parser_AST.Op (id, e1::e2::[]) when
      let uu___ = FStarC_Ident.string_of_id id in uu___ = ".()" ->
      let uu___ =
        let uu___1 = p_indexingTerm_aux p_atomicTermNotQUident e1 in
        let uu___2 =
          let uu___3 =
            let uu___4 = p_term false false e2 in
            soft_parens_with_nesting uu___4 in
          FStar_Pprint.op_Hat_Hat FStar_Pprint.dot uu___3 in
        FStar_Pprint.op_Hat_Hat uu___1 uu___2 in
      FStar_Pprint.group uu___
  | FStarC_Parser_AST.Op (id, e1::e2::[]) when
      let uu___ = FStarC_Ident.string_of_id id in uu___ = ".[]" ->
      let uu___ =
        let uu___1 = p_indexingTerm_aux p_atomicTermNotQUident e1 in
        let uu___2 =
          let uu___3 =
            let uu___4 = p_term false false e2 in
            soft_brackets_with_nesting uu___4 in
          FStar_Pprint.op_Hat_Hat FStar_Pprint.dot uu___3 in
        FStar_Pprint.op_Hat_Hat uu___1 uu___2 in
      FStar_Pprint.group uu___
  | FStarC_Parser_AST.Op (id, e1::e2::[]) when
      let uu___ = FStarC_Ident.string_of_id id in uu___ = ".(||)" ->
      let uu___ =
        let uu___1 = p_indexingTerm_aux p_atomicTermNotQUident e1 in
        let uu___2 =
          let uu___3 =
            let uu___4 = p_term false false e2 in
            soft_lens_access_with_nesting uu___4 in
          FStar_Pprint.op_Hat_Hat FStar_Pprint.dot uu___3 in
        FStar_Pprint.op_Hat_Hat uu___1 uu___2 in
      FStar_Pprint.group uu___
  | FStarC_Parser_AST.Op (id, e1::e2::[]) when
      let uu___ = FStarC_Ident.string_of_id id in uu___ = ".[||]" ->
      let uu___ =
        let uu___1 = p_indexingTerm_aux p_atomicTermNotQUident e1 in
        let uu___2 =
          let uu___3 =
            let uu___4 = p_term false false e2 in
            soft_brackets_lens_access_with_nesting uu___4 in
          FStar_Pprint.op_Hat_Hat FStar_Pprint.dot uu___3 in
        FStar_Pprint.op_Hat_Hat uu___1 uu___2 in
      FStar_Pprint.group uu___
  | uu___ -> exit e
and p_indexingTerm (e : FStarC_Parser_AST.term) : FStar_Pprint.document=
  p_indexingTerm_aux p_atomicTerm e
and p_atomicTerm (e : FStarC_Parser_AST.term) : FStar_Pprint.document=
  match e.FStarC_Parser_AST.tm with
  | FStarC_Parser_AST.LetOpen (lid, e1) ->
      let uu___ = p_quident lid in
      let uu___1 =
        let uu___2 =
          let uu___3 = p_term false false e1 in
          soft_parens_with_nesting uu___3 in
        FStar_Pprint.op_Hat_Hat FStar_Pprint.dot uu___2 in
      FStar_Pprint.op_Hat_Hat uu___ uu___1
  | FStarC_Parser_AST.Name lid -> p_quident lid
  | FStarC_Parser_AST.Construct (lid, []) when is_general_construction e ->
      p_quident lid
  | FStarC_Parser_AST.Op (op, e1::[]) when is_general_prefix_op op ->
      let uu___ = let uu___1 = FStarC_Ident.string_of_id op in str uu___1 in
      let uu___1 = p_atomicTerm e1 in FStar_Pprint.op_Hat_Hat uu___ uu___1
  | FStarC_Parser_AST.ListLiteral ts ->
      let uu___ =
        separate_map_or_flow_last
          (FStar_Pprint.op_Hat_Hat FStar_Pprint.semi break1)
          (fun ps -> p_noSeqTermAndComment ps false) ts in
      FStar_Pprint.surround (Prims.of_int (2)) Prims.int_zero
        FStar_Pprint.lbracket uu___ FStar_Pprint.rbracket
  | FStarC_Parser_AST.SeqLiteral ts ->
      let uu___ =
        separate_map_or_flow_last
          (FStar_Pprint.op_Hat_Hat FStar_Pprint.semi break1)
          (fun ps -> p_noSeqTermAndComment ps false) ts in
      FStar_Pprint.surround (Prims.of_int (2)) Prims.int_zero
        (FStar_Pprint.op_Hat_Hat (FStar_Pprint.doc_of_string "seq!")
           FStar_Pprint.lbracket) uu___ FStar_Pprint.rbracket
  | uu___ -> p_atomicTermNotQUident e
and p_atomicTermNotQUident (e : FStarC_Parser_AST.term) :
  FStar_Pprint.document=
  match e.FStarC_Parser_AST.tm with
  | FStarC_Parser_AST.Wild -> FStar_Pprint.underscore
  | FStarC_Parser_AST.Var lid when
      FStarC_Ident.lid_equals lid FStarC_Parser_Const.assert_lid ->
      str "assert"
  | FStarC_Parser_AST.Var lid when
      FStarC_Ident.lid_equals lid FStarC_Parser_Const.assume_lid ->
      str "assume"
  | FStarC_Parser_AST.Const c -> p_constant c
  | FStarC_Parser_AST.Name lid when
      FStarC_Ident.lid_equals lid FStarC_Parser_Const.true_lid -> str "True"
  | FStarC_Parser_AST.Name lid when
      FStarC_Ident.lid_equals lid FStarC_Parser_Const.false_lid ->
      str "False"
  | FStarC_Parser_AST.Op (op, e1::[]) when is_general_prefix_op op ->
      let uu___ = let uu___1 = FStarC_Ident.string_of_id op in str uu___1 in
      let uu___1 = p_atomicTermNotQUident e1 in
      FStar_Pprint.op_Hat_Hat uu___ uu___1
  | FStarC_Parser_AST.Op (op, []) ->
      let uu___ =
        let uu___1 =
          let uu___2 =
            let uu___3 = FStarC_Ident.string_of_id op in str uu___3 in
          FStar_Pprint.op_Hat_Hat uu___2
            (FStar_Pprint.op_Hat_Hat FStar_Pprint.space FStar_Pprint.rparen) in
        FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu___1 in
      FStar_Pprint.op_Hat_Hat FStar_Pprint.lparen uu___
  | FStarC_Parser_AST.Construct (lid, args) when
      (is_dtuple_constructor lid) && (all1_explicit args) ->
      let uu___ =
        FStarC_Pprint.separate_map
          (FStar_Pprint.op_Hat_Hat FStar_Pprint.comma break1)
          (fun uu___1 -> match uu___1 with | (e1, uu___2) -> p_tmEq e1) args in
      FStar_Pprint.surround (Prims.of_int (2)) Prims.int_one
        (FStar_Pprint.op_Hat_Hat FStar_Pprint.lparen FStar_Pprint.bar) uu___
        (FStar_Pprint.op_Hat_Hat FStar_Pprint.bar FStar_Pprint.rparen)
  | FStarC_Parser_AST.Construct (lid, args) when
      (is_tuple_constructor lid) && (all1_explicit args) ->
      let uu___ = p_tmTuple e in FStar_Pprint.parens uu___
  | FStarC_Parser_AST.Project (e1, lid) ->
      let uu___ =
        let uu___1 = p_atomicTermNotQUident e1 in
        let uu___2 =
          let uu___3 = p_qlident lid in
          FStar_Pprint.op_Hat_Hat FStar_Pprint.dot uu___3 in
        FStar_Pprint.prefix (Prims.of_int (2)) Prims.int_zero uu___1 uu___2 in
      FStar_Pprint.group uu___
  | uu___ -> p_projectionLHS e
and p_projectionLHS (e : FStarC_Parser_AST.term) : FStar_Pprint.document=
  match e.FStarC_Parser_AST.tm with
  | FStarC_Parser_AST.Var lid -> p_qlident lid
  | FStarC_Parser_AST.Projector (constr_lid, field_lid) ->
      let uu___ = p_quident constr_lid in
      let uu___1 =
        let uu___2 =
          let uu___3 = p_lident field_lid in
          FStar_Pprint.op_Hat_Hat FStar_Pprint.dot uu___3 in
        FStar_Pprint.op_Hat_Hat FStar_Pprint.qmark uu___2 in
      FStar_Pprint.op_Hat_Hat uu___ uu___1
  | FStarC_Parser_AST.Discrim constr_lid ->
      let uu___ = p_quident constr_lid in
      FStar_Pprint.op_Hat_Hat uu___ FStar_Pprint.qmark
  | FStarC_Parser_AST.Paren e1 ->
      let uu___ = p_term_sep false false e1 in
      (match uu___ with
       | (comm, t) ->
           let doc = soft_parens_with_nesting t in
           if comm = FStar_Pprint.empty
           then doc
           else
             FStar_Pprint.op_Hat_Hat comm
               (FStar_Pprint.op_Hat_Hat FStar_Pprint.hardline doc))
  | uu___ when is_ref_set e ->
      let es = extract_from_ref_set e in
      let uu___1 =
        separate_map_or_flow
          (FStar_Pprint.op_Hat_Hat FStar_Pprint.comma break1) p_appTerm es in
      FStar_Pprint.surround (Prims.of_int (2)) Prims.int_zero
        (FStar_Pprint.op_Hat_Hat FStar_Pprint.bang FStar_Pprint.lbrace)
        uu___1 FStar_Pprint.rbrace
  | FStarC_Parser_AST.Labeled
      ({ FStarC_Parser_AST.tm = FStarC_Parser_AST.Wild;
         FStarC_Parser_AST.range = uu___; FStarC_Parser_AST.level = uu___1;_},
       s, uu___2)
      ->
      let s1 = FStarC_Util.replace_chars (FStarC_Util.trim_string s) 10 "\\n" in
      str (Prims.strcat "(*" (Prims.strcat s1 "*)_"))
  | FStarC_Parser_AST.Labeled (e1, s, b) ->
      let s1 = FStarC_Util.replace_chars (FStarC_Util.trim_string s) 10 "\\n" in
      let uu___ =
        let uu___1 = p_term false false e1 in
        FStar_Pprint.op_Hat_Slash_Hat
          (str (Prims.strcat "(* " (Prims.strcat s1 " *)"))) uu___1 in
      FStar_Pprint.group uu___
  | FStarC_Parser_AST.Op (op, args) when
      let uu___ = handleable_op op args in Prims.op_Negation uu___ ->
      let uu___ =
        let uu___1 =
          let uu___2 = FStarC_Ident.string_of_id op in
          let uu___3 =
            let uu___4 =
              let uu___5 =
                FStarC_Class_Show.show FStarC_Class_Show.showable_nat
                  (FStarC_List.length args) in
              Prims.strcat uu___5
                " arguments couldn't be handled by the pretty printer" in
            Prims.strcat " with " uu___4 in
          Prims.strcat uu___2 uu___3 in
        Prims.strcat "Operation " uu___1 in
      failwith uu___
  | FStarC_Parser_AST.Uvar id ->
      failwith "Unexpected universe variable out of universe context"
  | FStarC_Parser_AST.LitDoc d -> d
  | FStarC_Parser_AST.Wild ->
      let uu___ = p_term false false e in soft_parens_with_nesting uu___
  | FStarC_Parser_AST.Const uu___ ->
      let uu___1 = p_term false false e in soft_parens_with_nesting uu___1
  | FStarC_Parser_AST.Op uu___ ->
      let uu___1 = p_term false false e in soft_parens_with_nesting uu___1
  | FStarC_Parser_AST.Var uu___ ->
      let uu___1 = p_term false false e in soft_parens_with_nesting uu___1
  | FStarC_Parser_AST.Name uu___ ->
      let uu___1 = p_term false false e in soft_parens_with_nesting uu___1
  | FStarC_Parser_AST.Construct uu___ ->
      let uu___1 = p_term false false e in soft_parens_with_nesting uu___1
  | FStarC_Parser_AST.Abs uu___ ->
      let uu___1 = p_term false false e in soft_parens_with_nesting uu___1
  | FStarC_Parser_AST.App uu___ ->
      let uu___1 = p_term false false e in soft_parens_with_nesting uu___1
  | FStarC_Parser_AST.Let uu___ ->
      let uu___1 = p_term false false e in soft_parens_with_nesting uu___1
  | FStarC_Parser_AST.LetOperator uu___ ->
      let uu___1 = p_term false false e in soft_parens_with_nesting uu___1
  | FStarC_Parser_AST.LetOpen uu___ ->
      let uu___1 = p_term false false e in soft_parens_with_nesting uu___1
  | FStarC_Parser_AST.LetOpenRecord uu___ ->
      let uu___1 = p_term false false e in soft_parens_with_nesting uu___1
  | FStarC_Parser_AST.Seq uu___ ->
      let uu___1 = p_term false false e in soft_parens_with_nesting uu___1
  | FStarC_Parser_AST.Bind uu___ ->
      let uu___1 = p_term false false e in soft_parens_with_nesting uu___1
  | FStarC_Parser_AST.If uu___ ->
      let uu___1 = p_term false false e in soft_parens_with_nesting uu___1
  | FStarC_Parser_AST.Match uu___ ->
      let uu___1 = p_term false false e in soft_parens_with_nesting uu___1
  | FStarC_Parser_AST.TryWith uu___ ->
      let uu___1 = p_term false false e in soft_parens_with_nesting uu___1
  | FStarC_Parser_AST.Ascribed uu___ ->
      let uu___1 = p_term false false e in soft_parens_with_nesting uu___1
  | FStarC_Parser_AST.Record uu___ ->
      let uu___1 = p_term false false e in soft_parens_with_nesting uu___1
  | FStarC_Parser_AST.Project uu___ ->
      let uu___1 = p_term false false e in soft_parens_with_nesting uu___1
  | FStarC_Parser_AST.Product uu___ ->
      let uu___1 = p_term false false e in soft_parens_with_nesting uu___1
  | FStarC_Parser_AST.Sum uu___ ->
      let uu___1 = p_term false false e in soft_parens_with_nesting uu___1
  | FStarC_Parser_AST.QForall uu___ ->
      let uu___1 = p_term false false e in soft_parens_with_nesting uu___1
  | FStarC_Parser_AST.QExists uu___ ->
      let uu___1 = p_term false false e in soft_parens_with_nesting uu___1
  | FStarC_Parser_AST.QuantOp uu___ ->
      let uu___1 = p_term false false e in soft_parens_with_nesting uu___1
  | FStarC_Parser_AST.Refine uu___ ->
      let uu___1 = p_term false false e in soft_parens_with_nesting uu___1
  | FStarC_Parser_AST.NamedTyp uu___ ->
      let uu___1 = p_term false false e in soft_parens_with_nesting uu___1
  | FStarC_Parser_AST.Requires uu___ ->
      let uu___1 = p_term false false e in soft_parens_with_nesting uu___1
  | FStarC_Parser_AST.Ensures uu___ ->
      let uu___1 = p_term false false e in soft_parens_with_nesting uu___1
  | FStarC_Parser_AST.Decreases uu___ ->
      let uu___1 = p_term false false e in soft_parens_with_nesting uu___1
  | FStarC_Parser_AST.Attributes uu___ ->
      let uu___1 = p_term false false e in soft_parens_with_nesting uu___1
  | FStarC_Parser_AST.Quote uu___ ->
      let uu___1 = p_term false false e in soft_parens_with_nesting uu___1
  | FStarC_Parser_AST.VQuote uu___ ->
      let uu___1 = p_term false false e in soft_parens_with_nesting uu___1
  | FStarC_Parser_AST.Antiquote uu___ ->
      let uu___1 = p_term false false e in soft_parens_with_nesting uu___1
  | FStarC_Parser_AST.CalcProof uu___ ->
      let uu___1 = p_term false false e in soft_parens_with_nesting uu___1
  | FStarC_Parser_AST.ListLiteral uu___ ->
      let uu___1 = p_term false false e in soft_parens_with_nesting uu___1
  | FStarC_Parser_AST.SeqLiteral uu___ ->
      let uu___1 = p_term false false e in soft_parens_with_nesting uu___1
  | FStarC_Parser_AST.ElimExists uu___ ->
      let uu___1 = p_term false false e in soft_parens_with_nesting uu___1
  | FStarC_Parser_AST.LexList l ->
      let uu___ =
        let uu___1 = p_term_list false false l in
        FStar_Pprint.op_Hat_Hat (str "%") uu___1 in
      FStar_Pprint.group uu___
  | FStarC_Parser_AST.WFOrder (rel, e1) -> p_dec_wf false false rel e1
and p_constant (uu___ : FStarC_Const.sconst) : FStar_Pprint.document=
  match uu___ with
  | FStarC_Const.Const_effect -> str "Effect"
  | FStarC_Const.Const_unit -> str "()"
  | FStarC_Const.Const_bool b -> FStar_Pprint.doc_of_bool b
  | FStarC_Const.Const_real r -> str (Prims.strcat r "R")
  | FStarC_Const.Const_char x -> p_char_literal x
  | FStarC_Const.Const_string (s, uu___1) -> p_string_literal s
  | FStarC_Const.Const_int (repr, sign_width_opt) ->
      let signedness uu___1 =
        match uu___1 with
        | FStarC_Const.Unsigned -> str "u"
        | FStarC_Const.Signed -> FStar_Pprint.empty in
      let width uu___1 =
        match uu___1 with
        | FStarC_Const.Int8 -> str "y"
        | FStarC_Const.Int16 -> str "s"
        | FStarC_Const.Int32 -> str "l"
        | FStarC_Const.Int64 -> str "L" in
      let suffix uu___1 =
        match uu___1 with
        | (s, w) ->
            (match (s, w) with
             | (uu___2, FStarC_Const.Sizet) -> str "sz"
             | uu___2 -> FStar_Pprint.op_Hat_Hat (signedness s) (width w)) in
      let ending = default_or_map FStar_Pprint.empty suffix sign_width_opt in
      FStar_Pprint.op_Hat_Hat (str repr) ending
  | FStarC_Const.Const_range_of -> str "range_of"
  | FStarC_Const.Const_set_range_of -> str "set_range_of"
  | FStarC_Const.Const_range r ->
      let uu___1 = FStarC_Range_Ops.string_of_range r in str uu___1
  | FStarC_Const.Const_reify uu___1 -> str "reify"
  | FStarC_Const.Const_reflect lid ->
      let uu___1 = p_quident lid in
      FStar_Pprint.op_Hat_Hat uu___1
        (FStar_Pprint.op_Hat_Hat FStar_Pprint.qmark
           (FStar_Pprint.op_Hat_Hat FStar_Pprint.dot (str "reflect")))
and p_universe (u : FStarC_Parser_AST.term) : FStar_Pprint.document=
  let uu___ = p_atomicUniverse u in FStar_Pprint.op_Hat_Hat (str "u#") uu___
and p_universeFrom (u : FStarC_Parser_AST.term) : FStar_Pprint.document=
  match u.FStarC_Parser_AST.tm with
  | FStarC_Parser_AST.Op (id, u1::u2::[]) when
      let uu___ = FStarC_Ident.string_of_id id in uu___ = "+" ->
      let uu___ =
        let uu___1 = p_universeFrom u1 in
        let uu___2 =
          let uu___3 = p_universeFrom u2 in
          FStar_Pprint.op_Hat_Slash_Hat FStar_Pprint.plus uu___3 in
        FStar_Pprint.op_Hat_Slash_Hat uu___1 uu___2 in
      FStar_Pprint.group uu___
  | FStarC_Parser_AST.App uu___ ->
      let uu___1 = head_and_args u in
      (match uu___1 with
       | (head, args) ->
           (match head.FStarC_Parser_AST.tm with
            | FStarC_Parser_AST.Var maybe_max_lid when
                FStarC_Ident.lid_equals maybe_max_lid
                  FStarC_Parser_Const.max_lid
                ->
                let uu___2 =
                  let uu___3 = p_qlident FStarC_Parser_Const.max_lid in
                  let uu___4 =
                    FStarC_Pprint.separate_map FStar_Pprint.space
                      (fun uu___5 ->
                         match uu___5 with
                         | (u1, uu___6) -> p_atomicUniverse u1) args in
                  op_Hat_Slash_Plus_Hat uu___3 uu___4 in
                FStar_Pprint.group uu___2
            | uu___2 ->
                let uu___3 =
                  let uu___4 = FStarC_Parser_AST.term_to_string u in
                  FStarC_Format.fmt1 "Invalid term in universe context %s"
                    uu___4 in
                failwith uu___3))
  | uu___ -> p_atomicUniverse u
and p_atomicUniverse (u : FStarC_Parser_AST.term) : FStar_Pprint.document=
  match u.FStarC_Parser_AST.tm with
  | FStarC_Parser_AST.Wild -> FStar_Pprint.underscore
  | FStarC_Parser_AST.Const (FStarC_Const.Const_int (r, sw)) ->
      p_constant (FStarC_Const.Const_int (r, sw))
  | FStarC_Parser_AST.Uvar id ->
      let uu___ = FStarC_Ident.string_of_id id in str uu___
  | FStarC_Parser_AST.Paren u1 ->
      let uu___ = p_universeFrom u1 in soft_parens_with_nesting uu___
  | FStarC_Parser_AST.App uu___ ->
      let uu___1 = p_universeFrom u in soft_parens_with_nesting uu___1
  | FStarC_Parser_AST.Op (id, uu___::uu___1::[]) when
      let uu___2 = FStarC_Ident.string_of_id id in uu___2 = "+" ->
      let uu___2 = p_universeFrom u in soft_parens_with_nesting uu___2
  | uu___ ->
      let uu___1 =
        let uu___2 = FStarC_Parser_AST.term_to_string u in
        FStarC_Format.fmt1 "Invalid term in universe context %s" uu___2 in
      failwith uu___1
let term_to_document (e : FStarC_Parser_AST.term) : FStar_Pprint.document=
  p_term false false e
let signature_to_document (e : FStarC_Parser_AST.decl) :
  FStar_Pprint.document= p_justSig e
let decl_to_document (e : FStarC_Parser_AST.decl) : FStar_Pprint.document=
  p_decl e
let pat_to_document (p : FStarC_Parser_AST.pattern) : FStar_Pprint.document=
  p_disjunctivePattern p
let binder_to_document (b : FStarC_Parser_AST.binder) :
  FStar_Pprint.document= p_binder true b
let modul_to_document (m : FStarC_Parser_AST.modul) : FStar_Pprint.document=
  match m with
  | FStarC_Parser_AST.Module
      { FStarC_Parser_AST.no_prelude = uu___;
        FStarC_Parser_AST.mname = uu___1; FStarC_Parser_AST.decls = decls;_}
      -> FStarC_Pprint.separate_map FStar_Pprint.hardline p_decl decls
  | FStarC_Parser_AST.Interface
      { FStarC_Parser_AST.no_prelude1 = uu___;
        FStarC_Parser_AST.mname1 = uu___1; FStarC_Parser_AST.decls1 = decls;
        FStarC_Parser_AST.admitted = uu___2;_}
      -> FStarC_Pprint.separate_map FStar_Pprint.hardline p_decl decls
let comments_to_document
  (comments : (Prims.string * FStarC_Range_Type.t) Prims.list) :
  FStar_Pprint.document=
  FStarC_Pprint.separate_map FStar_Pprint.hardline
    (fun uu___ -> match uu___ with | (comment, range) -> str comment)
    comments
let extract_decl_range (d : FStarC_Parser_AST.decl) : decl_meta=
  let has_qs =
    match ((d.FStarC_Parser_AST.quals), (d.FStarC_Parser_AST.d)) with
    | ((FStarC_Parser_AST.Assumption)::[], FStarC_Parser_AST.Assume
       (id, uu___)) -> false
    | ([], uu___) -> false
    | uu___ -> true in
  {
    r = (d.FStarC_Parser_AST.drange);
    has_qs;
    has_attrs =
      (Prims.op_Negation (FStarC_List.isEmpty d.FStarC_Parser_AST.attrs))
  }
let decls_with_comments_to_document
  (decls : FStarC_Parser_AST.decl Prims.list)
  (comments : (Prims.string * FStarC_Range_Type.range) Prims.list) :
  (FStar_Pprint.document * (Prims.string * FStarC_Range_Type.range)
    Prims.list)=
  match decls with
  | [] -> (FStar_Pprint.empty, comments)
  | d::ds ->
      let uu___ = ((d :: ds), (d.FStarC_Parser_AST.drange)) in
      (match uu___ with
       | (decls1, first_range) ->
           (FStarC_Effect.op_Colon_Equals comment_stack comments;
            (let initial_comment =
               let uu___2 = FStarC_Range_Ops.start_of_range first_range in
               place_comments_until_pos Prims.int_zero Prims.int_one uu___2
                 dummy_meta FStar_Pprint.empty false true in
             let doc =
               separate_map_with_comments FStar_Pprint.empty
                 FStar_Pprint.empty p_decl decls1 extract_decl_range in
             let comments1 = FStarC_Effect.op_Bang comment_stack in
             FStarC_Effect.op_Colon_Equals comment_stack [];
             ((FStar_Pprint.op_Hat_Hat initial_comment doc), comments1))))
let modul_with_comments_to_document (m : FStarC_Parser_AST.modul)
  (comments : (Prims.string * FStarC_Range_Type.t) Prims.list) :
  (FStar_Pprint.document * (Prims.string * FStarC_Range_Type.t) Prims.list)=
  let decls =
    match m with
    | FStarC_Parser_AST.Module
        { FStarC_Parser_AST.no_prelude = uu___;
          FStarC_Parser_AST.mname = uu___1;
          FStarC_Parser_AST.decls = decls1;_}
        -> decls1
    | FStarC_Parser_AST.Interface
        { FStarC_Parser_AST.no_prelude1 = uu___;
          FStarC_Parser_AST.mname1 = uu___1;
          FStarC_Parser_AST.decls1 = decls1;
          FStarC_Parser_AST.admitted = uu___2;_}
        -> decls1 in
  decls_with_comments_to_document decls comments
let decl_with_comments_to_document (d : FStarC_Parser_AST.decl)
  (comments : (Prims.string * FStarC_Range_Type.t) Prims.list) :
  (FStar_Pprint.document * (Prims.string * FStarC_Range_Type.t) Prims.list)=
  decls_with_comments_to_document [d] comments
