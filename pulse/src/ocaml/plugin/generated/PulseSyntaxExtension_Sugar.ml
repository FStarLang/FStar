open Prims
type rng = FStar_Compiler_Range_Type.range
let (dummyRange : FStar_Compiler_Range_Type.range) =
  FStar_Compiler_Range_Type.dummyRange
type binder = FStar_Parser_AST.binder
type binders = binder Prims.list
type slprop' =
  | SLPropTerm of FStar_Parser_AST.term 
and slprop = {
  v: slprop' ;
  vrange: rng }
let (uu___is_SLPropTerm : slprop' -> Prims.bool) = fun projectee -> true
let (__proj__SLPropTerm__item___0 : slprop' -> FStar_Parser_AST.term) =
  fun projectee -> match projectee with | SLPropTerm _0 -> _0
let (__proj__Mkslprop__item__v : slprop -> slprop') =
  fun projectee -> match projectee with | { v; vrange;_} -> v
let (__proj__Mkslprop__item__vrange : slprop -> rng) =
  fun projectee -> match projectee with | { v; vrange;_} -> vrange
let (as_slprop : slprop' -> rng -> slprop) =
  fun v -> fun r -> { v; vrange = r }
type st_comp_tag =
  | ST 
  | STAtomic 
  | STGhost 
let (uu___is_ST : st_comp_tag -> Prims.bool) =
  fun projectee -> match projectee with | ST -> true | uu___ -> false
let (uu___is_STAtomic : st_comp_tag -> Prims.bool) =
  fun projectee -> match projectee with | STAtomic -> true | uu___ -> false
let (uu___is_STGhost : st_comp_tag -> Prims.bool) =
  fun projectee -> match projectee with | STGhost -> true | uu___ -> false
type computation_type =
  {
  tag: st_comp_tag ;
  precondition: slprop ;
  return_name: FStar_Ident.ident ;
  return_type: FStar_Parser_AST.term ;
  postcondition: slprop ;
  opens: FStar_Parser_AST.term FStar_Pervasives_Native.option ;
  range: rng }
let (__proj__Mkcomputation_type__item__tag : computation_type -> st_comp_tag)
  =
  fun projectee ->
    match projectee with
    | { tag; precondition; return_name; return_type; postcondition; opens;
        range;_} -> tag
let (__proj__Mkcomputation_type__item__precondition :
  computation_type -> slprop) =
  fun projectee ->
    match projectee with
    | { tag; precondition; return_name; return_type; postcondition; opens;
        range;_} -> precondition
let (__proj__Mkcomputation_type__item__return_name :
  computation_type -> FStar_Ident.ident) =
  fun projectee ->
    match projectee with
    | { tag; precondition; return_name; return_type; postcondition; opens;
        range;_} -> return_name
let (__proj__Mkcomputation_type__item__return_type :
  computation_type -> FStar_Parser_AST.term) =
  fun projectee ->
    match projectee with
    | { tag; precondition; return_name; return_type; postcondition; opens;
        range;_} -> return_type
let (__proj__Mkcomputation_type__item__postcondition :
  computation_type -> slprop) =
  fun projectee ->
    match projectee with
    | { tag; precondition; return_name; return_type; postcondition; opens;
        range;_} -> postcondition
let (__proj__Mkcomputation_type__item__opens :
  computation_type -> FStar_Parser_AST.term FStar_Pervasives_Native.option) =
  fun projectee ->
    match projectee with
    | { tag; precondition; return_name; return_type; postcondition; opens;
        range;_} -> opens
let (__proj__Mkcomputation_type__item__range : computation_type -> rng) =
  fun projectee ->
    match projectee with
    | { tag; precondition; return_name; return_type; postcondition; opens;
        range;_} -> range
type mut_or_ref =
  | MUT 
  | REF 
let (uu___is_MUT : mut_or_ref -> Prims.bool) =
  fun projectee -> match projectee with | MUT -> true | uu___ -> false
let (uu___is_REF : mut_or_ref -> Prims.bool) =
  fun projectee -> match projectee with | REF -> true | uu___ -> false
let (showable_mut_or_ref : mut_or_ref FStar_Class_Show.showable) =
  {
    FStar_Class_Show.show =
      (fun i -> match i with | MUT -> "MUT" | REF -> "REF")
  }
type hint_type =
  | ASSERT of slprop 
  | ASSUME of slprop 
  | UNFOLD of (FStar_Ident.lident Prims.list FStar_Pervasives_Native.option *
  slprop) 
  | FOLD of (FStar_Ident.lident Prims.list FStar_Pervasives_Native.option *
  slprop) 
  | RENAME of ((FStar_Parser_AST.term * FStar_Parser_AST.term) Prims.list *
  slprop FStar_Pervasives_Native.option * FStar_Parser_AST.term
  FStar_Pervasives_Native.option) 
  | REWRITE of (slprop * slprop * FStar_Parser_AST.term
  FStar_Pervasives_Native.option) 
  | WILD 
  | SHOW_PROOF_STATE of rng 
let (uu___is_ASSERT : hint_type -> Prims.bool) =
  fun projectee -> match projectee with | ASSERT _0 -> true | uu___ -> false
let (__proj__ASSERT__item___0 : hint_type -> slprop) =
  fun projectee -> match projectee with | ASSERT _0 -> _0
let (uu___is_ASSUME : hint_type -> Prims.bool) =
  fun projectee -> match projectee with | ASSUME _0 -> true | uu___ -> false
let (__proj__ASSUME__item___0 : hint_type -> slprop) =
  fun projectee -> match projectee with | ASSUME _0 -> _0
let (uu___is_UNFOLD : hint_type -> Prims.bool) =
  fun projectee -> match projectee with | UNFOLD _0 -> true | uu___ -> false
let (__proj__UNFOLD__item___0 :
  hint_type ->
    (FStar_Ident.lident Prims.list FStar_Pervasives_Native.option * slprop))
  = fun projectee -> match projectee with | UNFOLD _0 -> _0
let (uu___is_FOLD : hint_type -> Prims.bool) =
  fun projectee -> match projectee with | FOLD _0 -> true | uu___ -> false
let (__proj__FOLD__item___0 :
  hint_type ->
    (FStar_Ident.lident Prims.list FStar_Pervasives_Native.option * slprop))
  = fun projectee -> match projectee with | FOLD _0 -> _0
let (uu___is_RENAME : hint_type -> Prims.bool) =
  fun projectee -> match projectee with | RENAME _0 -> true | uu___ -> false
let (__proj__RENAME__item___0 :
  hint_type ->
    ((FStar_Parser_AST.term * FStar_Parser_AST.term) Prims.list * slprop
      FStar_Pervasives_Native.option * FStar_Parser_AST.term
      FStar_Pervasives_Native.option))
  = fun projectee -> match projectee with | RENAME _0 -> _0
let (uu___is_REWRITE : hint_type -> Prims.bool) =
  fun projectee -> match projectee with | REWRITE _0 -> true | uu___ -> false
let (__proj__REWRITE__item___0 :
  hint_type ->
    (slprop * slprop * FStar_Parser_AST.term FStar_Pervasives_Native.option))
  = fun projectee -> match projectee with | REWRITE _0 -> _0
let (uu___is_WILD : hint_type -> Prims.bool) =
  fun projectee -> match projectee with | WILD -> true | uu___ -> false
let (uu___is_SHOW_PROOF_STATE : hint_type -> Prims.bool) =
  fun projectee ->
    match projectee with | SHOW_PROOF_STATE _0 -> true | uu___ -> false
let (__proj__SHOW_PROOF_STATE__item___0 : hint_type -> rng) =
  fun projectee -> match projectee with | SHOW_PROOF_STATE _0 -> _0
let (showable_slprop : slprop FStar_Class_Show.showable) =
  {
    FStar_Class_Show.show =
      (fun s ->
         match s.v with
         | SLPropTerm t ->
             FStar_Class_Show.show FStar_Parser_AST.showable_term t)
  }
let (showable_hint_type : hint_type FStar_Class_Show.showable) =
  {
    FStar_Class_Show.show =
      (fun i ->
         match i with
         | ASSERT s ->
             let uu___ = FStar_Class_Show.show showable_slprop s in
             Prims.strcat "ASSERT " uu___
         | ASSUME s ->
             let uu___ = FStar_Class_Show.show showable_slprop s in
             Prims.strcat "ASSUME " uu___
         | UNFOLD (ns, s) ->
             let uu___ =
               let uu___1 =
                 FStar_Class_Show.show
                   (FStar_Class_Show.show_option
                      (FStar_Class_Show.show_list FStar_Ident.showable_lident))
                   ns in
               let uu___2 =
                 let uu___3 = FStar_Class_Show.show showable_slprop s in
                 Prims.strcat " " uu___3 in
               Prims.strcat uu___1 uu___2 in
             Prims.strcat "UNFOLD " uu___
         | FOLD (ns, s) ->
             let uu___ =
               let uu___1 =
                 FStar_Class_Show.show
                   (FStar_Class_Show.show_option
                      (FStar_Class_Show.show_list FStar_Ident.showable_lident))
                   ns in
               let uu___2 =
                 let uu___3 = FStar_Class_Show.show showable_slprop s in
                 Prims.strcat " " uu___3 in
               Prims.strcat uu___1 uu___2 in
             Prims.strcat "FOLD " uu___
         | RENAME (ts, g, t) ->
             let uu___ =
               let uu___1 =
                 FStar_Class_Show.show
                   (FStar_Class_Show.show_list
                      (FStar_Class_Show.show_tuple2
                         FStar_Parser_AST.showable_term
                         FStar_Parser_AST.showable_term)) ts in
               let uu___2 =
                 let uu___3 =
                   let uu___4 =
                     FStar_Class_Show.show
                       (FStar_Class_Show.show_option showable_slprop) g in
                   let uu___5 =
                     let uu___6 =
                       FStar_Class_Show.show
                         (FStar_Class_Show.show_option
                            FStar_Parser_AST.showable_term) t in
                     Prims.strcat " " uu___6 in
                   Prims.strcat uu___4 uu___5 in
                 Prims.strcat " " uu___3 in
               Prims.strcat uu___1 uu___2 in
             Prims.strcat "RENAME " uu___
         | REWRITE (s1, s2, t) ->
             let uu___ =
               let uu___1 = FStar_Class_Show.show showable_slprop s1 in
               let uu___2 =
                 let uu___3 =
                   let uu___4 = FStar_Class_Show.show showable_slprop s2 in
                   let uu___5 =
                     let uu___6 =
                       FStar_Class_Show.show
                         (FStar_Class_Show.show_option
                            FStar_Parser_AST.showable_term) t in
                     Prims.strcat " " uu___6 in
                   Prims.strcat uu___4 uu___5 in
                 Prims.strcat " " uu___3 in
               Prims.strcat uu___1 uu___2 in
             Prims.strcat "REWRITE " uu___
         | WILD -> "WILD"
         | SHOW_PROOF_STATE r -> "SHOW_PROOF_STATE ...")
  }
type array_init = {
  init: FStar_Parser_AST.term ;
  len: FStar_Parser_AST.term }
let (__proj__Mkarray_init__item__init : array_init -> FStar_Parser_AST.term)
  = fun projectee -> match projectee with | { init; len;_} -> init
let (__proj__Mkarray_init__item__len : array_init -> FStar_Parser_AST.term) =
  fun projectee -> match projectee with | { init; len;_} -> len
type ensures_slprop =
  ((FStar_Ident.ident * FStar_Parser_AST.term) FStar_Pervasives_Native.option
    * slprop * FStar_Parser_AST.term FStar_Pervasives_Native.option)
type stmt'__Expr__payload = {
  e: FStar_Parser_AST.term }
and stmt'__Assignment__payload =
  {
  lhs: FStar_Parser_AST.term ;
  value: FStar_Parser_AST.term }
and stmt'__ArrayAssignment__payload =
  {
  arr: FStar_Parser_AST.term ;
  index: FStar_Parser_AST.term ;
  value1: FStar_Parser_AST.term }
and stmt'__LetBinding__payload =
  {
  qualifier: mut_or_ref FStar_Pervasives_Native.option ;
  pat: FStar_Parser_AST.pattern ;
  typ: FStar_Parser_AST.term FStar_Pervasives_Native.option ;
  init1: let_init FStar_Pervasives_Native.option }
and stmt'__Block__payload = {
  stmt: stmt }
and stmt'__If__payload =
  {
  head: FStar_Parser_AST.term ;
  join_slprop: ensures_slprop FStar_Pervasives_Native.option ;
  then_: stmt ;
  else_opt: stmt FStar_Pervasives_Native.option }
and stmt'__Match__payload =
  {
  head1: FStar_Parser_AST.term ;
  returns_annot: ensures_slprop FStar_Pervasives_Native.option ;
  branches: (FStar_Parser_AST.pattern * stmt) Prims.list }
and stmt'__While__payload =
  {
  guard: stmt ;
  id: FStar_Ident.ident ;
  invariant: slprop ;
  body: stmt }
and stmt'__Introduce__payload =
  {
  slprop: slprop ;
  witnesses: FStar_Parser_AST.term Prims.list }
and stmt'__Sequence__payload = {
  s1: stmt ;
  s2: stmt }
and stmt'__Parallel__payload =
  {
  p1: slprop ;
  p2: slprop ;
  q1: slprop ;
  q2: slprop ;
  b1: stmt ;
  b2: stmt }
and stmt'__ProofHintWithBinders__payload =
  {
  hint_type: hint_type ;
  binders: binders }
and stmt'__WithInvariants__payload =
  {
  names: FStar_Parser_AST.term Prims.list ;
  body1: stmt ;
  returns_: ensures_slprop FStar_Pervasives_Native.option }
and stmt' =
  | Open of FStar_Ident.lident 
  | Expr of stmt'__Expr__payload 
  | Assignment of stmt'__Assignment__payload 
  | ArrayAssignment of stmt'__ArrayAssignment__payload 
  | LetBinding of stmt'__LetBinding__payload 
  | Block of stmt'__Block__payload 
  | If of stmt'__If__payload 
  | Match of stmt'__Match__payload 
  | While of stmt'__While__payload 
  | Introduce of stmt'__Introduce__payload 
  | Sequence of stmt'__Sequence__payload 
  | Parallel of stmt'__Parallel__payload 
  | ProofHintWithBinders of stmt'__ProofHintWithBinders__payload 
  | WithInvariants of stmt'__WithInvariants__payload 
and stmt = {
  s: stmt' ;
  range1: rng }
and lambda =
  {
  binders1: binders ;
  ascription: computation_type FStar_Pervasives_Native.option ;
  body2: stmt ;
  range2: rng }
and fn_defn =
  {
  id1: FStar_Ident.ident ;
  is_rec: Prims.bool ;
  binders2: binders ;
  ascription1:
    (computation_type, FStar_Parser_AST.term FStar_Pervasives_Native.option)
      FStar_Pervasives.either
    ;
  measure: FStar_Parser_AST.term FStar_Pervasives_Native.option ;
  body3: (stmt, lambda) FStar_Pervasives.either ;
  decorations: FStar_Parser_AST.decoration Prims.list ;
  range3: rng }
and let_init =
  | Array_initializer of array_init 
  | Default_initializer of FStar_Parser_AST.term 
  | Lambda_initializer of fn_defn 
  | Stmt_initializer of stmt 
let (__proj__Mkstmt'__Expr__payload__item__e :
  stmt'__Expr__payload -> FStar_Parser_AST.term) =
  fun projectee -> match projectee with | { e;_} -> e
let (__proj__Mkstmt'__Assignment__payload__item__lhs :
  stmt'__Assignment__payload -> FStar_Parser_AST.term) =
  fun projectee -> match projectee with | { lhs; value;_} -> lhs
let (__proj__Mkstmt'__Assignment__payload__item__value :
  stmt'__Assignment__payload -> FStar_Parser_AST.term) =
  fun projectee -> match projectee with | { lhs; value;_} -> value
let (__proj__Mkstmt'__ArrayAssignment__payload__item__arr :
  stmt'__ArrayAssignment__payload -> FStar_Parser_AST.term) =
  fun projectee ->
    match projectee with | { arr; index; value1 = value;_} -> arr
let (__proj__Mkstmt'__ArrayAssignment__payload__item__index :
  stmt'__ArrayAssignment__payload -> FStar_Parser_AST.term) =
  fun projectee ->
    match projectee with | { arr; index; value1 = value;_} -> index
let (__proj__Mkstmt'__ArrayAssignment__payload__item__value :
  stmt'__ArrayAssignment__payload -> FStar_Parser_AST.term) =
  fun projectee ->
    match projectee with | { arr; index; value1 = value;_} -> value
let (__proj__Mkstmt'__LetBinding__payload__item__qualifier :
  stmt'__LetBinding__payload -> mut_or_ref FStar_Pervasives_Native.option) =
  fun projectee ->
    match projectee with
    | { qualifier; pat; typ; init1 = init;_} -> qualifier
let (__proj__Mkstmt'__LetBinding__payload__item__pat :
  stmt'__LetBinding__payload -> FStar_Parser_AST.pattern) =
  fun projectee ->
    match projectee with | { qualifier; pat; typ; init1 = init;_} -> pat
let (__proj__Mkstmt'__LetBinding__payload__item__typ :
  stmt'__LetBinding__payload ->
    FStar_Parser_AST.term FStar_Pervasives_Native.option)
  =
  fun projectee ->
    match projectee with | { qualifier; pat; typ; init1 = init;_} -> typ
let (__proj__Mkstmt'__LetBinding__payload__item__init :
  stmt'__LetBinding__payload -> let_init FStar_Pervasives_Native.option) =
  fun projectee ->
    match projectee with | { qualifier; pat; typ; init1 = init;_} -> init
let (__proj__Mkstmt'__Block__payload__item__stmt :
  stmt'__Block__payload -> stmt) =
  fun projectee -> match projectee with | { stmt = stmt1;_} -> stmt1
let (__proj__Mkstmt'__If__payload__item__head :
  stmt'__If__payload -> FStar_Parser_AST.term) =
  fun projectee ->
    match projectee with | { head; join_slprop; then_; else_opt;_} -> head
let (__proj__Mkstmt'__If__payload__item__join_slprop :
  stmt'__If__payload -> ensures_slprop FStar_Pervasives_Native.option) =
  fun projectee ->
    match projectee with
    | { head; join_slprop; then_; else_opt;_} -> join_slprop
let (__proj__Mkstmt'__If__payload__item__then_ : stmt'__If__payload -> stmt)
  =
  fun projectee ->
    match projectee with | { head; join_slprop; then_; else_opt;_} -> then_
let (__proj__Mkstmt'__If__payload__item__else_opt :
  stmt'__If__payload -> stmt FStar_Pervasives_Native.option) =
  fun projectee ->
    match projectee with
    | { head; join_slprop; then_; else_opt;_} -> else_opt
let (__proj__Mkstmt'__Match__payload__item__head :
  stmt'__Match__payload -> FStar_Parser_AST.term) =
  fun projectee ->
    match projectee with | { head1 = head; returns_annot; branches;_} -> head
let (__proj__Mkstmt'__Match__payload__item__returns_annot :
  stmt'__Match__payload -> ensures_slprop FStar_Pervasives_Native.option) =
  fun projectee ->
    match projectee with
    | { head1 = head; returns_annot; branches;_} -> returns_annot
let (__proj__Mkstmt'__Match__payload__item__branches :
  stmt'__Match__payload -> (FStar_Parser_AST.pattern * stmt) Prims.list) =
  fun projectee ->
    match projectee with
    | { head1 = head; returns_annot; branches;_} -> branches
let (__proj__Mkstmt'__While__payload__item__guard :
  stmt'__While__payload -> stmt) =
  fun projectee ->
    match projectee with | { guard; id; invariant; body;_} -> guard
let (__proj__Mkstmt'__While__payload__item__id :
  stmt'__While__payload -> FStar_Ident.ident) =
  fun projectee ->
    match projectee with | { guard; id; invariant; body;_} -> id
let (__proj__Mkstmt'__While__payload__item__invariant :
  stmt'__While__payload -> slprop) =
  fun projectee ->
    match projectee with | { guard; id; invariant; body;_} -> invariant
let (__proj__Mkstmt'__While__payload__item__body :
  stmt'__While__payload -> stmt) =
  fun projectee ->
    match projectee with | { guard; id; invariant; body;_} -> body
let (__proj__Mkstmt'__Introduce__payload__item__slprop :
  stmt'__Introduce__payload -> slprop) =
  fun projectee ->
    match projectee with | { slprop = slprop1; witnesses;_} -> slprop1
let (__proj__Mkstmt'__Introduce__payload__item__witnesses :
  stmt'__Introduce__payload -> FStar_Parser_AST.term Prims.list) =
  fun projectee ->
    match projectee with | { slprop = slprop1; witnesses;_} -> witnesses
let (__proj__Mkstmt'__Sequence__payload__item__s1 :
  stmt'__Sequence__payload -> stmt) =
  fun projectee -> match projectee with | { s1; s2;_} -> s1
let (__proj__Mkstmt'__Sequence__payload__item__s2 :
  stmt'__Sequence__payload -> stmt) =
  fun projectee -> match projectee with | { s1; s2;_} -> s2
let (__proj__Mkstmt'__Parallel__payload__item__p1 :
  stmt'__Parallel__payload -> slprop) =
  fun projectee -> match projectee with | { p1; p2; q1; q2; b1; b2;_} -> p1
let (__proj__Mkstmt'__Parallel__payload__item__p2 :
  stmt'__Parallel__payload -> slprop) =
  fun projectee -> match projectee with | { p1; p2; q1; q2; b1; b2;_} -> p2
let (__proj__Mkstmt'__Parallel__payload__item__q1 :
  stmt'__Parallel__payload -> slprop) =
  fun projectee -> match projectee with | { p1; p2; q1; q2; b1; b2;_} -> q1
let (__proj__Mkstmt'__Parallel__payload__item__q2 :
  stmt'__Parallel__payload -> slprop) =
  fun projectee -> match projectee with | { p1; p2; q1; q2; b1; b2;_} -> q2
let (__proj__Mkstmt'__Parallel__payload__item__b1 :
  stmt'__Parallel__payload -> stmt) =
  fun projectee -> match projectee with | { p1; p2; q1; q2; b1; b2;_} -> b1
let (__proj__Mkstmt'__Parallel__payload__item__b2 :
  stmt'__Parallel__payload -> stmt) =
  fun projectee -> match projectee with | { p1; p2; q1; q2; b1; b2;_} -> b2
let (__proj__Mkstmt'__ProofHintWithBinders__payload__item__hint_type :
  stmt'__ProofHintWithBinders__payload -> hint_type) =
  fun projectee ->
    match projectee with
    | { hint_type = hint_type1; binders = binders1;_} -> hint_type1
let (__proj__Mkstmt'__ProofHintWithBinders__payload__item__binders :
  stmt'__ProofHintWithBinders__payload -> binders) =
  fun projectee ->
    match projectee with
    | { hint_type = hint_type1; binders = binders1;_} -> binders1
let (__proj__Mkstmt'__WithInvariants__payload__item__names :
  stmt'__WithInvariants__payload -> FStar_Parser_AST.term Prims.list) =
  fun projectee ->
    match projectee with | { names; body1 = body; returns_;_} -> names
let (__proj__Mkstmt'__WithInvariants__payload__item__body :
  stmt'__WithInvariants__payload -> stmt) =
  fun projectee ->
    match projectee with | { names; body1 = body; returns_;_} -> body
let (__proj__Mkstmt'__WithInvariants__payload__item__returns_ :
  stmt'__WithInvariants__payload ->
    ensures_slprop FStar_Pervasives_Native.option)
  =
  fun projectee ->
    match projectee with | { names; body1 = body; returns_;_} -> returns_
let (uu___is_Open : stmt' -> Prims.bool) =
  fun projectee -> match projectee with | Open _0 -> true | uu___ -> false
let (__proj__Open__item___0 : stmt' -> FStar_Ident.lident) =
  fun projectee -> match projectee with | Open _0 -> _0
let (uu___is_Expr : stmt' -> Prims.bool) =
  fun projectee -> match projectee with | Expr _0 -> true | uu___ -> false
let (__proj__Expr__item___0 : stmt' -> stmt'__Expr__payload) =
  fun projectee -> match projectee with | Expr _0 -> _0
let (uu___is_Assignment : stmt' -> Prims.bool) =
  fun projectee ->
    match projectee with | Assignment _0 -> true | uu___ -> false
let (__proj__Assignment__item___0 : stmt' -> stmt'__Assignment__payload) =
  fun projectee -> match projectee with | Assignment _0 -> _0
let (uu___is_ArrayAssignment : stmt' -> Prims.bool) =
  fun projectee ->
    match projectee with | ArrayAssignment _0 -> true | uu___ -> false
let (__proj__ArrayAssignment__item___0 :
  stmt' -> stmt'__ArrayAssignment__payload) =
  fun projectee -> match projectee with | ArrayAssignment _0 -> _0
let (uu___is_LetBinding : stmt' -> Prims.bool) =
  fun projectee ->
    match projectee with | LetBinding _0 -> true | uu___ -> false
let (__proj__LetBinding__item___0 : stmt' -> stmt'__LetBinding__payload) =
  fun projectee -> match projectee with | LetBinding _0 -> _0
let (uu___is_Block : stmt' -> Prims.bool) =
  fun projectee -> match projectee with | Block _0 -> true | uu___ -> false
let (__proj__Block__item___0 : stmt' -> stmt'__Block__payload) =
  fun projectee -> match projectee with | Block _0 -> _0
let (uu___is_If : stmt' -> Prims.bool) =
  fun projectee -> match projectee with | If _0 -> true | uu___ -> false
let (__proj__If__item___0 : stmt' -> stmt'__If__payload) =
  fun projectee -> match projectee with | If _0 -> _0
let (uu___is_Match : stmt' -> Prims.bool) =
  fun projectee -> match projectee with | Match _0 -> true | uu___ -> false
let (__proj__Match__item___0 : stmt' -> stmt'__Match__payload) =
  fun projectee -> match projectee with | Match _0 -> _0
let (uu___is_While : stmt' -> Prims.bool) =
  fun projectee -> match projectee with | While _0 -> true | uu___ -> false
let (__proj__While__item___0 : stmt' -> stmt'__While__payload) =
  fun projectee -> match projectee with | While _0 -> _0
let (uu___is_Introduce : stmt' -> Prims.bool) =
  fun projectee ->
    match projectee with | Introduce _0 -> true | uu___ -> false
let (__proj__Introduce__item___0 : stmt' -> stmt'__Introduce__payload) =
  fun projectee -> match projectee with | Introduce _0 -> _0
let (uu___is_Sequence : stmt' -> Prims.bool) =
  fun projectee ->
    match projectee with | Sequence _0 -> true | uu___ -> false
let (__proj__Sequence__item___0 : stmt' -> stmt'__Sequence__payload) =
  fun projectee -> match projectee with | Sequence _0 -> _0
let (uu___is_Parallel : stmt' -> Prims.bool) =
  fun projectee ->
    match projectee with | Parallel _0 -> true | uu___ -> false
let (__proj__Parallel__item___0 : stmt' -> stmt'__Parallel__payload) =
  fun projectee -> match projectee with | Parallel _0 -> _0
let (uu___is_ProofHintWithBinders : stmt' -> Prims.bool) =
  fun projectee ->
    match projectee with | ProofHintWithBinders _0 -> true | uu___ -> false
let (__proj__ProofHintWithBinders__item___0 :
  stmt' -> stmt'__ProofHintWithBinders__payload) =
  fun projectee -> match projectee with | ProofHintWithBinders _0 -> _0
let (uu___is_WithInvariants : stmt' -> Prims.bool) =
  fun projectee ->
    match projectee with | WithInvariants _0 -> true | uu___ -> false
let (__proj__WithInvariants__item___0 :
  stmt' -> stmt'__WithInvariants__payload) =
  fun projectee -> match projectee with | WithInvariants _0 -> _0
let (__proj__Mkstmt__item__s : stmt -> stmt') =
  fun projectee -> match projectee with | { s; range1 = range;_} -> s
let (__proj__Mkstmt__item__range : stmt -> rng) =
  fun projectee -> match projectee with | { s; range1 = range;_} -> range
let (__proj__Mklambda__item__binders : lambda -> binders) =
  fun projectee ->
    match projectee with
    | { binders1; ascription; body2 = body; range2 = range;_} -> binders1
let (__proj__Mklambda__item__ascription :
  lambda -> computation_type FStar_Pervasives_Native.option) =
  fun projectee ->
    match projectee with
    | { binders1; ascription; body2 = body; range2 = range;_} -> ascription
let (__proj__Mklambda__item__body : lambda -> stmt) =
  fun projectee ->
    match projectee with
    | { binders1; ascription; body2 = body; range2 = range;_} -> body
let (__proj__Mklambda__item__range : lambda -> rng) =
  fun projectee ->
    match projectee with
    | { binders1; ascription; body2 = body; range2 = range;_} -> range
let (__proj__Mkfn_defn__item__id : fn_defn -> FStar_Ident.ident) =
  fun projectee ->
    match projectee with
    | { id1 = id; is_rec; binders2 = binders1; ascription1 = ascription;
        measure; body3 = body; decorations; range3 = range;_} -> id
let (__proj__Mkfn_defn__item__is_rec : fn_defn -> Prims.bool) =
  fun projectee ->
    match projectee with
    | { id1 = id; is_rec; binders2 = binders1; ascription1 = ascription;
        measure; body3 = body; decorations; range3 = range;_} -> is_rec
let (__proj__Mkfn_defn__item__binders : fn_defn -> binders) =
  fun projectee ->
    match projectee with
    | { id1 = id; is_rec; binders2 = binders1; ascription1 = ascription;
        measure; body3 = body; decorations; range3 = range;_} -> binders1
let (__proj__Mkfn_defn__item__ascription :
  fn_defn ->
    (computation_type, FStar_Parser_AST.term FStar_Pervasives_Native.option)
      FStar_Pervasives.either)
  =
  fun projectee ->
    match projectee with
    | { id1 = id; is_rec; binders2 = binders1; ascription1 = ascription;
        measure; body3 = body; decorations; range3 = range;_} -> ascription
let (__proj__Mkfn_defn__item__measure :
  fn_defn -> FStar_Parser_AST.term FStar_Pervasives_Native.option) =
  fun projectee ->
    match projectee with
    | { id1 = id; is_rec; binders2 = binders1; ascription1 = ascription;
        measure; body3 = body; decorations; range3 = range;_} -> measure
let (__proj__Mkfn_defn__item__body :
  fn_defn -> (stmt, lambda) FStar_Pervasives.either) =
  fun projectee ->
    match projectee with
    | { id1 = id; is_rec; binders2 = binders1; ascription1 = ascription;
        measure; body3 = body; decorations; range3 = range;_} -> body
let (__proj__Mkfn_defn__item__decorations :
  fn_defn -> FStar_Parser_AST.decoration Prims.list) =
  fun projectee ->
    match projectee with
    | { id1 = id; is_rec; binders2 = binders1; ascription1 = ascription;
        measure; body3 = body; decorations; range3 = range;_} -> decorations
let (__proj__Mkfn_defn__item__range : fn_defn -> rng) =
  fun projectee ->
    match projectee with
    | { id1 = id; is_rec; binders2 = binders1; ascription1 = ascription;
        measure; body3 = body; decorations; range3 = range;_} -> range
let (uu___is_Array_initializer : let_init -> Prims.bool) =
  fun projectee ->
    match projectee with | Array_initializer _0 -> true | uu___ -> false
let (__proj__Array_initializer__item___0 : let_init -> array_init) =
  fun projectee -> match projectee with | Array_initializer _0 -> _0
let (uu___is_Default_initializer : let_init -> Prims.bool) =
  fun projectee ->
    match projectee with | Default_initializer _0 -> true | uu___ -> false
let (__proj__Default_initializer__item___0 :
  let_init -> FStar_Parser_AST.term) =
  fun projectee -> match projectee with | Default_initializer _0 -> _0
let (uu___is_Lambda_initializer : let_init -> Prims.bool) =
  fun projectee ->
    match projectee with | Lambda_initializer _0 -> true | uu___ -> false
let (__proj__Lambda_initializer__item___0 : let_init -> fn_defn) =
  fun projectee -> match projectee with | Lambda_initializer _0 -> _0
let (uu___is_Stmt_initializer : let_init -> Prims.bool) =
  fun projectee ->
    match projectee with | Stmt_initializer _0 -> true | uu___ -> false
let (__proj__Stmt_initializer__item___0 : let_init -> stmt) =
  fun projectee -> match projectee with | Stmt_initializer _0 -> _0
let (showable_let_init : let_init FStar_Class_Show.showable) =
  {
    FStar_Class_Show.show =
      (fun i ->
         match i with
         | Array_initializer a -> "Array_initializer ..."
         | Default_initializer t -> "Default_initializer ..."
         | Lambda_initializer l -> "Lambda_initializer ..."
         | Stmt_initializer s -> "Stmt_initializer ...")
  }
type fn_decl =
  {
  id2: FStar_Ident.ident ;
  binders3: binders ;
  ascription2:
    (computation_type, FStar_Parser_AST.term FStar_Pervasives_Native.option)
      FStar_Pervasives.either
    ;
  decorations1: FStar_Parser_AST.decoration Prims.list ;
  range4: rng }
let (__proj__Mkfn_decl__item__id : fn_decl -> FStar_Ident.ident) =
  fun projectee ->
    match projectee with
    | { id2 = id; binders3 = binders1; ascription2 = ascription;
        decorations1 = decorations; range4 = range;_} -> id
let (__proj__Mkfn_decl__item__binders : fn_decl -> binders) =
  fun projectee ->
    match projectee with
    | { id2 = id; binders3 = binders1; ascription2 = ascription;
        decorations1 = decorations; range4 = range;_} -> binders1
let (__proj__Mkfn_decl__item__ascription :
  fn_decl ->
    (computation_type, FStar_Parser_AST.term FStar_Pervasives_Native.option)
      FStar_Pervasives.either)
  =
  fun projectee ->
    match projectee with
    | { id2 = id; binders3 = binders1; ascription2 = ascription;
        decorations1 = decorations; range4 = range;_} -> ascription
let (__proj__Mkfn_decl__item__decorations :
  fn_decl -> FStar_Parser_AST.decoration Prims.list) =
  fun projectee ->
    match projectee with
    | { id2 = id; binders3 = binders1; ascription2 = ascription;
        decorations1 = decorations; range4 = range;_} -> decorations
let (__proj__Mkfn_decl__item__range : fn_decl -> rng) =
  fun projectee ->
    match projectee with
    | { id2 = id; binders3 = binders1; ascription2 = ascription;
        decorations1 = decorations; range4 = range;_} -> range
let (tag_of_stmt : stmt -> Prims.string) =
  fun s ->
    match s.s with
    | Open uu___ -> "Open"
    | Expr { e = uu___;_} -> "Expr"
    | Assignment { lhs = uu___; value = uu___1;_} -> "Assignment"
    | ArrayAssignment { arr = uu___; index = uu___1; value1 = uu___2;_} ->
        "ArrayAssignment"
    | LetBinding
        { qualifier = uu___; pat = uu___1; typ = uu___2; init1 = uu___3;_} ->
        "LetBinding"
    | Block { stmt = uu___;_} -> "Block"
    | If
        { head = uu___; join_slprop = uu___1; then_ = uu___2;
          else_opt = uu___3;_}
        -> "If"
    | Match { head1 = uu___; returns_annot = uu___1; branches = uu___2;_} ->
        "Match"
    | While
        { guard = uu___; id = uu___1; invariant = uu___2; body = uu___3;_} ->
        "While"
    | Introduce { slprop = uu___; witnesses = uu___1;_} -> "Introduce"
    | Sequence { s1 = uu___; s2 = uu___1;_} -> "Sequence"
    | Parallel
        { p1 = uu___; p2 = uu___1; q1 = uu___2; q2 = uu___3; b1 = uu___4;
          b2 = uu___5;_}
        -> "Parallel"
    | ProofHintWithBinders { hint_type = uu___; binders = uu___1;_} ->
        "ProofHintWithBinders"
    | WithInvariants { names = uu___; body1 = uu___1; returns_ = uu___2;_} ->
        "WithInvariants"
let (tagged_stmt : stmt FStar_Class_Tagged.tagged) =
  { FStar_Class_Tagged.tag_of = tag_of_stmt }
let (record_string :
  (Prims.string * Prims.string) Prims.list -> Prims.string) =
  fun fs ->
    Prims.strcat "{"
      (Prims.strcat
         (FStar_String.concat "; "
            (FStar_List_Tot_Base.map
               (fun uu___ ->
                  match uu___ with
                  | (f, s) -> Prims.strcat f (Prims.strcat " = " s)) fs)) "}")
let (showable_pattern : FStar_Parser_AST.pattern FStar_Class_Show.showable) =
  { FStar_Class_Show.show = FStar_Parser_AST.pat_to_string }
let (showable_a_term : FStar_Parser_AST.term FStar_Class_Show.showable) =
  { FStar_Class_Show.show = FStar_Parser_AST.term_to_string }
let (showable_a_binder : FStar_Parser_AST.binder FStar_Class_Show.showable) =
  { FStar_Class_Show.show = FStar_Parser_AST.binder_to_string }
let rec (stmt_to_string : stmt -> Prims.string) =
  fun s ->
    match s.s with
    | Open l ->
        let uu___ = FStar_Class_Show.show FStar_Ident.showable_lident l in
        Prims.strcat "Open " uu___
    | Expr { e;_} ->
        let uu___ = FStar_Class_Show.show showable_a_term e in
        Prims.strcat "Expr " uu___
    | Assignment { lhs; value;_} ->
        let uu___ =
          let uu___1 =
            let uu___2 =
              let uu___3 = FStar_Class_Show.show showable_a_term lhs in
              ("lhs", uu___3) in
            let uu___3 =
              let uu___4 =
                let uu___5 = FStar_Class_Show.show showable_a_term value in
                ("value", uu___5) in
              [uu___4] in
            uu___2 :: uu___3 in
          record_string uu___1 in
        Prims.strcat "Assignment " uu___
    | ArrayAssignment { arr; index; value1 = value;_} ->
        let uu___ =
          let uu___1 =
            let uu___2 =
              let uu___3 = FStar_Class_Show.show showable_a_term arr in
              ("arr", uu___3) in
            let uu___3 =
              let uu___4 =
                let uu___5 = FStar_Class_Show.show showable_a_term index in
                ("index", uu___5) in
              let uu___5 =
                let uu___6 =
                  let uu___7 = FStar_Class_Show.show showable_a_term value in
                  ("value", uu___7) in
                [uu___6] in
              uu___4 :: uu___5 in
            uu___2 :: uu___3 in
          record_string uu___1 in
        Prims.strcat "ArrayAssignment " uu___
    | LetBinding { qualifier; pat; typ; init1 = init;_} ->
        let uu___ =
          let uu___1 =
            let uu___2 =
              let uu___3 =
                FStar_Class_Show.show
                  (FStar_Class_Show.show_option showable_mut_or_ref)
                  qualifier in
              ("qualifier", uu___3) in
            let uu___3 =
              let uu___4 =
                let uu___5 = FStar_Class_Show.show showable_pattern pat in
                ("pat", uu___5) in
              let uu___5 =
                let uu___6 =
                  let uu___7 =
                    FStar_Class_Show.show
                      (FStar_Class_Show.show_option showable_a_term) typ in
                  ("typ", uu___7) in
                let uu___7 =
                  let uu___8 =
                    let uu___9 =
                      FStar_Class_Show.show
                        (FStar_Class_Show.show_option showable_let_init) init in
                    ("init", uu___9) in
                  [uu___8] in
                uu___6 :: uu___7 in
              uu___4 :: uu___5 in
            uu___2 :: uu___3 in
          record_string uu___1 in
        Prims.strcat "LetBinding " uu___
    | Block { stmt = stmt1;_} ->
        let uu___ =
          let uu___1 = stmt_to_string stmt1 in Prims.strcat uu___1 "}" in
        Prims.strcat "Block {" uu___
    | If { head; join_slprop; then_; else_opt;_} ->
        let uu___ =
          let uu___1 =
            let uu___2 =
              let uu___3 = FStar_Class_Show.show showable_a_term head in
              ("head", uu___3) in
            let uu___3 =
              let uu___4 =
                let uu___5 =
                  FStar_Class_Show.show
                    (FStar_Class_Show.show_option
                       (FStar_Class_Show.show_tuple3
                          (FStar_Class_Show.show_option
                             (FStar_Class_Show.show_tuple2
                                FStar_Ident.showable_ident showable_a_term))
                          showable_slprop
                          (FStar_Class_Show.show_option showable_a_term)))
                    join_slprop in
                ("join_slprop", uu___5) in
              let uu___5 =
                let uu___6 =
                  let uu___7 = stmt_to_string then_ in ("then_", uu___7) in
                let uu___7 =
                  let uu___8 =
                    let uu___9 =
                      FStar_Common.string_of_option stmt_to_string else_opt in
                    ("else_opt", uu___9) in
                  [uu___8] in
                uu___6 :: uu___7 in
              uu___4 :: uu___5 in
            uu___2 :: uu___3 in
          record_string uu___1 in
        Prims.strcat "If " uu___
    | Match { head1 = head; returns_annot; branches;_} ->
        let uu___ =
          let uu___1 =
            let uu___2 =
              let uu___3 = FStar_Class_Show.show showable_a_term head in
              ("head", uu___3) in
            let uu___3 =
              let uu___4 =
                let uu___5 =
                  FStar_Class_Show.show
                    (FStar_Class_Show.show_option
                       (FStar_Class_Show.show_tuple3
                          (FStar_Class_Show.show_option
                             (FStar_Class_Show.show_tuple2
                                FStar_Ident.showable_ident showable_a_term))
                          showable_slprop
                          (FStar_Class_Show.show_option showable_a_term)))
                    returns_annot in
                ("returns_annot", uu___5) in
              let uu___5 =
                let uu___6 =
                  let uu___7 =
                    (FStar_Common.string_of_list ()) branch_to_string
                      branches in
                  ("branches", uu___7) in
                [uu___6] in
              uu___4 :: uu___5 in
            uu___2 :: uu___3 in
          record_string uu___1 in
        Prims.strcat "Match " uu___
    | While { guard; id; invariant; body;_} ->
        let uu___ =
          let uu___1 =
            let uu___2 =
              let uu___3 = stmt_to_string guard in ("guard", uu___3) in
            let uu___3 =
              let uu___4 =
                let uu___5 =
                  FStar_Class_Show.show FStar_Ident.showable_ident id in
                ("id", uu___5) in
              let uu___5 =
                let uu___6 =
                  let uu___7 =
                    FStar_Class_Show.show showable_slprop invariant in
                  ("invariant", uu___7) in
                let uu___7 =
                  let uu___8 =
                    let uu___9 = stmt_to_string body in ("body", uu___9) in
                  [uu___8] in
                uu___6 :: uu___7 in
              uu___4 :: uu___5 in
            uu___2 :: uu___3 in
          record_string uu___1 in
        Prims.strcat "While " uu___
    | Introduce { slprop = slprop1; witnesses;_} ->
        let uu___ =
          let uu___1 =
            let uu___2 =
              let uu___3 = FStar_Class_Show.show showable_slprop slprop1 in
              ("slprop", uu___3) in
            let uu___3 =
              let uu___4 =
                let uu___5 =
                  (FStar_Common.string_of_list ())
                    (FStar_Class_Show.show showable_a_term) witnesses in
                ("witnesses", uu___5) in
              [uu___4] in
            uu___2 :: uu___3 in
          record_string uu___1 in
        Prims.strcat "Introduce " uu___
    | Sequence { s1; s2;_} ->
        let uu___ =
          let uu___1 =
            let uu___2 = let uu___3 = stmt_to_string s1 in ("s1", uu___3) in
            let uu___3 =
              let uu___4 = let uu___5 = stmt_to_string s2 in ("s2", uu___5) in
              [uu___4] in
            uu___2 :: uu___3 in
          record_string uu___1 in
        Prims.strcat "Sequence " uu___
    | Parallel { p1; p2; q1; q2; b1; b2;_} ->
        let uu___ =
          let uu___1 =
            let uu___2 =
              let uu___3 = FStar_Class_Show.show showable_slprop p1 in
              ("p1", uu___3) in
            let uu___3 =
              let uu___4 =
                let uu___5 = FStar_Class_Show.show showable_slprop p2 in
                ("p2", uu___5) in
              let uu___5 =
                let uu___6 =
                  let uu___7 = FStar_Class_Show.show showable_slprop q1 in
                  ("q1", uu___7) in
                let uu___7 =
                  let uu___8 =
                    let uu___9 = FStar_Class_Show.show showable_slprop q2 in
                    ("q2", uu___9) in
                  let uu___9 =
                    let uu___10 =
                      let uu___11 = stmt_to_string b1 in ("b1", uu___11) in
                    let uu___11 =
                      let uu___12 =
                        let uu___13 = stmt_to_string b2 in ("b2", uu___13) in
                      [uu___12] in
                    uu___10 :: uu___11 in
                  uu___8 :: uu___9 in
                uu___6 :: uu___7 in
              uu___4 :: uu___5 in
            uu___2 :: uu___3 in
          record_string uu___1 in
        Prims.strcat "Parallel " uu___
    | ProofHintWithBinders { hint_type = hint_type1; binders = binders1;_} ->
        let uu___ =
          let uu___1 =
            let uu___2 =
              let uu___3 =
                FStar_Class_Show.show showable_hint_type hint_type1 in
              ("hint_type", uu___3) in
            let uu___3 =
              let uu___4 =
                let uu___5 =
                  FStar_Class_Show.show
                    (FStar_Class_Show.show_list showable_a_binder) binders1 in
                ("binders", uu___5) in
              [uu___4] in
            uu___2 :: uu___3 in
          record_string uu___1 in
        Prims.strcat "ProofHintWithBinders " uu___
    | WithInvariants { names; body1 = body; returns_;_} ->
        let uu___ =
          let uu___1 =
            let uu___2 =
              let uu___3 =
                (FStar_Common.string_of_list ())
                  (FStar_Class_Show.show showable_a_term) names in
              ("names", uu___3) in
            let uu___3 =
              let uu___4 =
                let uu___5 = stmt_to_string body in ("body", uu___5) in
              let uu___5 =
                let uu___6 =
                  let uu___7 =
                    FStar_Common.string_of_option
                      (FStar_Class_Show.show
                         (FStar_Class_Show.show_tuple3
                            (FStar_Class_Show.show_option
                               (FStar_Class_Show.show_tuple2
                                  FStar_Ident.showable_ident showable_a_term))
                            showable_slprop
                            (FStar_Class_Show.show_option showable_a_term)))
                      returns_ in
                  ("returns_", uu___7) in
                [uu___6] in
              uu___4 :: uu___5 in
            uu___2 :: uu___3 in
          record_string uu___1 in
        Prims.strcat "WithInvariants " uu___
and (branch_to_string : (FStar_Parser_AST.pattern * stmt) -> Prims.string) =
  fun b ->
    let uu___ = b in
    match uu___ with
    | (p, s) ->
        let uu___1 = FStar_Class_Show.show showable_pattern p in
        let uu___2 =
          let uu___3 = stmt_to_string s in Prims.strcat " -> " uu___3 in
        Prims.strcat uu___1 uu___2
let (showable_stmt : stmt FStar_Class_Show.showable) =
  { FStar_Class_Show.show = stmt_to_string }
type decl =
  | FnDefn of fn_defn 
  | FnDecl of fn_decl 
let (uu___is_FnDefn : decl -> Prims.bool) =
  fun projectee -> match projectee with | FnDefn _0 -> true | uu___ -> false
let (__proj__FnDefn__item___0 : decl -> fn_defn) =
  fun projectee -> match projectee with | FnDefn _0 -> _0
let (uu___is_FnDecl : decl -> Prims.bool) =
  fun projectee -> match projectee with | FnDecl _0 -> true | uu___ -> false
let (__proj__FnDecl__item___0 : decl -> fn_decl) =
  fun projectee -> match projectee with | FnDecl _0 -> _0
let (eq_ident : FStar_Ident.ident -> FStar_Ident.ident -> Prims.bool) =
  fun i1 ->
    fun i2 ->
      FStar_Class_Deq.op_Equals_Question FStar_Syntax_Syntax.deq_univ_name i1
        i2
let (eq_lident : FStar_Ident.lident -> FStar_Ident.lident -> Prims.bool) =
  fun i1 ->
    fun i2 ->
      FStar_Class_Deq.op_Equals_Question FStar_Syntax_Syntax.deq_fv i1 i2
let rec forall2 :
  'a .
    ('a -> 'a -> Prims.bool) -> 'a Prims.list -> 'a Prims.list -> Prims.bool
  =
  fun f ->
    fun l1 ->
      fun l2 ->
        match (l1, l2) with
        | ([], []) -> true
        | (x::xs, y::ys) -> (f x y) && (forall2 f xs ys)
        | (uu___, uu___1) -> false
let eq_opt :
  'a .
    ('a -> 'a -> Prims.bool) ->
      'a FStar_Pervasives_Native.option ->
        'a FStar_Pervasives_Native.option -> Prims.bool
  =
  fun eq ->
    fun o1 ->
      fun o2 ->
        match (o1, o2) with
        | (FStar_Pervasives_Native.Some x, FStar_Pervasives_Native.Some y) ->
            eq x y
        | (FStar_Pervasives_Native.None, FStar_Pervasives_Native.None) ->
            true
        | (uu___, uu___1) -> false
let rec (eq_decl : decl -> decl -> Prims.bool) =
  fun d1 ->
    fun d2 ->
      match (d1, d2) with
      | (FnDefn f1, FnDefn f2) -> eq_fn_defn f1 f2
      | (FnDecl d11, FnDecl d21) -> eq_fn_decl d11 d21
      | uu___ -> false
and (eq_fn_decl : fn_decl -> fn_decl -> Prims.bool) =
  fun f1 ->
    fun f2 ->
      ((eq_ident f1.id2 f2.id2) &&
         (forall2 FStar_Parser_AST_Util.eq_binder f1.binders3 f2.binders3))
        && (eq_ascription f1.ascription2 f2.ascription2)
and (eq_fn_defn : fn_defn -> fn_defn -> Prims.bool) =
  fun f1 ->
    fun f2 ->
      (((((eq_ident f1.id1 f2.id1) && (f1.is_rec = f2.is_rec)) &&
           (forall2 FStar_Parser_AST_Util.eq_binder f1.binders2 f2.binders2))
          && (eq_ascription f1.ascription1 f2.ascription1))
         && (eq_opt FStar_Parser_AST_Util.eq_term f1.measure f2.measure))
        && (eq_body f1.body3 f2.body3)
and (eq_ascription :
  (computation_type, FStar_Parser_AST.term FStar_Pervasives_Native.option)
    FStar_Pervasives.either ->
    (computation_type, FStar_Parser_AST.term FStar_Pervasives_Native.option)
      FStar_Pervasives.either -> Prims.bool)
  =
  fun a1 ->
    fun a2 ->
      match (a1, a2) with
      | (FStar_Pervasives.Inl c1, FStar_Pervasives.Inl c2) ->
          eq_computation_type c1 c2
      | (FStar_Pervasives.Inr t1, FStar_Pervasives.Inr t2) ->
          eq_opt FStar_Parser_AST_Util.eq_term t1 t2
      | (uu___, uu___1) -> false
and (eq_computation_type :
  computation_type -> computation_type -> Prims.bool) =
  fun c1 ->
    fun c2 ->
      (((((c1.tag = c2.tag) && (eq_slprop c1.precondition c2.precondition))
           && (eq_ident c1.return_name c2.return_name))
          && (FStar_Parser_AST_Util.eq_term c1.return_type c2.return_type))
         && (eq_slprop c1.postcondition c2.postcondition))
        && (eq_opt FStar_Parser_AST_Util.eq_term c1.opens c2.opens)
and (eq_slprop : slprop -> slprop -> Prims.bool) =
  fun s1 -> fun s2 -> eq_slprop' s1.v s2.v
and (eq_slprop' : slprop' -> slprop' -> Prims.bool) =
  fun s1 ->
    fun s2 ->
      match (s1, s2) with
      | (SLPropTerm t1, SLPropTerm t2) -> FStar_Parser_AST_Util.eq_term t1 t2
and (eq_body :
  (stmt, lambda) FStar_Pervasives.either ->
    (stmt, lambda) FStar_Pervasives.either -> Prims.bool)
  =
  fun b1 ->
    fun b2 ->
      match (b1, b2) with
      | (FStar_Pervasives.Inl s1, FStar_Pervasives.Inl s2) -> eq_stmt s1 s2
      | (FStar_Pervasives.Inr l1, FStar_Pervasives.Inr l2) -> eq_lambda l1 l2
      | (uu___, uu___1) -> false
and (eq_stmt : stmt -> stmt -> Prims.bool) =
  fun s1 -> fun s2 -> eq_stmt' s1.s s2.s
and (eq_stmt' : stmt' -> stmt' -> Prims.bool) =
  fun s1 ->
    fun s2 ->
      match (s1, s2) with
      | (Open l1, Open l2) -> eq_lident l1 l2
      | (Expr e1, Expr e2) -> FStar_Parser_AST_Util.eq_term e1.e e2.e
      | (Assignment { lhs = l1; value = v1;_}, Assignment
         { lhs = l2; value = v2;_}) ->
          (FStar_Parser_AST_Util.eq_term l1 l2) &&
            (FStar_Parser_AST_Util.eq_term v1 v2)
      | (ArrayAssignment { arr = a1; index = i1; value1 = v1;_},
         ArrayAssignment { arr = a2; index = i2; value1 = v2;_}) ->
          ((FStar_Parser_AST_Util.eq_term a1 a2) &&
             (FStar_Parser_AST_Util.eq_term i1 i2))
            && (FStar_Parser_AST_Util.eq_term v1 v2)
      | (LetBinding { qualifier = q1; pat = pat1; typ = t1; init1;_},
         LetBinding { qualifier = q2; pat = pat2; typ = t2; init1 = init2;_})
          ->
          (((eq_opt eq_mut_or_ref q1 q2) &&
              (FStar_Parser_AST_Util.eq_pattern pat1 pat2))
             && (eq_opt FStar_Parser_AST_Util.eq_term t1 t2))
            && (eq_opt eq_let_init init1 init2)
      | (Block { stmt = s11;_}, Block { stmt = s21;_}) -> eq_stmt s11 s21
      | (If { head = h1; join_slprop = j1; then_ = t1; else_opt = e1;_}, If
         { head = h2; join_slprop = j2; then_ = t2; else_opt = e2;_}) ->
          (((FStar_Parser_AST_Util.eq_term h1 h2) &&
              (eq_opt eq_ensures_slprop j1 j2))
             && (eq_stmt t1 t2))
            && (eq_opt eq_stmt e1 e2)
      | (Match { head1 = h1; returns_annot = r1; branches = b1;_}, Match
         { head1 = h2; returns_annot = r2; branches = b2;_}) ->
          ((FStar_Parser_AST_Util.eq_term h1 h2) &&
             (eq_opt eq_ensures_slprop r1 r2))
            &&
            (forall2
               (fun uu___ ->
                  fun uu___1 ->
                    match (uu___, uu___1) with
                    | ((p1, s11), (p2, s21)) ->
                        (FStar_Parser_AST_Util.eq_pattern p1 p2) &&
                          (eq_stmt s11 s21)) b1 b2)
      | (While { guard = g1; id = id1; invariant = i1; body = b1;_}, While
         { guard = g2; id = id2; invariant = i2; body = b2;_}) ->
          (((eq_stmt g1 g2) && (eq_ident id1 id2)) && (eq_slprop i1 i2)) &&
            (eq_stmt b1 b2)
      | (Introduce { slprop = s11; witnesses = w1;_}, Introduce
         { slprop = s21; witnesses = w2;_}) ->
          (eq_slprop s11 s21) &&
            (forall2 FStar_Parser_AST_Util.eq_term w1 w2)
      | (Sequence { s1 = s11; s2 = s21;_}, Sequence { s1 = s1'; s2 = s2';_})
          -> (eq_stmt s11 s1') && (eq_stmt s21 s2')
      | (Parallel { p1; p2; q1; q2; b1; b2;_}, Parallel
         { p1 = p1'; p2 = p2'; q1 = q1'; q2 = q2'; b1 = b1'; b2 = b2';_}) ->
          (((((eq_slprop p1 p1') && (eq_slprop p2 p2')) && (eq_slprop q1 q1'))
              && (eq_slprop q2 q2'))
             && (eq_stmt b1 b1'))
            && (eq_stmt b2 b2')
      | (ProofHintWithBinders { hint_type = ht1; binders = bs1;_},
         ProofHintWithBinders { hint_type = ht2; binders = bs2;_}) ->
          (eq_hint_type ht1 ht2) &&
            (forall2 FStar_Parser_AST_Util.eq_binder bs1 bs2)
      | (WithInvariants { names = n1; body1 = b1; returns_ = r1;_},
         WithInvariants { names = n2; body1 = b2; returns_ = r2;_}) ->
          ((forall2 FStar_Parser_AST_Util.eq_term n1 n2) && (eq_stmt b1 b2))
            && (eq_opt eq_ensures_slprop r1 r2)
      | uu___ -> false
and (eq_let_init : let_init -> let_init -> Prims.bool) =
  fun i1 ->
    fun i2 ->
      match (i1, i2) with
      | (Array_initializer a1, Array_initializer a2) -> eq_array_init a1 a2
      | (Default_initializer t1, Default_initializer t2) ->
          FStar_Parser_AST_Util.eq_term t1 t2
      | (Lambda_initializer l1, Lambda_initializer l2) -> eq_fn_defn l1 l2
      | (Stmt_initializer s1, Stmt_initializer s2) -> eq_stmt s1 s2
      | (uu___, uu___1) -> false
and (eq_array_init : array_init -> array_init -> Prims.bool) =
  fun a1 ->
    fun a2 ->
      (FStar_Parser_AST_Util.eq_term a1.init a2.init) &&
        (FStar_Parser_AST_Util.eq_term a1.len a2.len)
and (eq_hint_type : hint_type -> hint_type -> Prims.bool) =
  fun h1 ->
    fun h2 ->
      match (h1, h2) with
      | (ASSERT s1, ASSERT s2) -> eq_slprop s1 s2
      | (ASSUME s1, ASSUME s2) -> eq_slprop s1 s2
      | (UNFOLD (ns1, s1), UNFOLD (ns2, s2)) ->
          (eq_opt (forall2 eq_lident) ns1 ns2) && (eq_slprop s1 s2)
      | (FOLD (ns1, s1), FOLD (ns2, s2)) ->
          (eq_opt (forall2 eq_lident) ns1 ns2) && (eq_slprop s1 s2)
      | (RENAME (ts1, g1, t1), RENAME (ts2, g2, t2)) ->
          ((forall2
              (fun uu___ ->
                 fun uu___1 ->
                   match (uu___, uu___1) with
                   | ((t11, t21), (t1', t2')) ->
                       (FStar_Parser_AST_Util.eq_term t11 t1') &&
                         (FStar_Parser_AST_Util.eq_term t21 t2')) ts1 ts2)
             && (eq_opt eq_slprop g1 g2))
            && (eq_opt FStar_Parser_AST_Util.eq_term t1 t2)
      | (REWRITE (s1, s1', t1), REWRITE (s2, s2', t2)) ->
          ((eq_slprop s1 s2) && (eq_slprop s1' s2')) &&
            (eq_opt FStar_Parser_AST_Util.eq_term t1 t2)
      | (WILD, WILD) -> true
      | (SHOW_PROOF_STATE r1, SHOW_PROOF_STATE r2) -> true
      | (uu___, uu___1) -> false
and (eq_ensures_slprop : ensures_slprop -> ensures_slprop -> Prims.bool) =
  fun e1 ->
    fun e2 ->
      let uu___ = e1 in
      match uu___ with
      | (h1, s1, t1) ->
          let uu___1 = e2 in
          (match uu___1 with
           | (h2, s2, t2) ->
               ((eq_opt
                   (fun uu___2 ->
                      fun uu___3 ->
                        match (uu___2, uu___3) with
                        | ((i1, t11), (i2, t21)) ->
                            (eq_ident i1 i2) &&
                              (FStar_Parser_AST_Util.eq_term t11 t21)) h1 h2)
                  && (eq_slprop s1 s2))
                 && (eq_opt FStar_Parser_AST_Util.eq_term t1 t2))
and (eq_lambda : lambda -> lambda -> Prims.bool) =
  fun l1 ->
    fun l2 ->
      ((forall2 FStar_Parser_AST_Util.eq_binder l1.binders1 l2.binders1) &&
         (eq_opt eq_computation_type l1.ascription l2.ascription))
        && (eq_stmt l1.body2 l2.body2)
and (eq_mut_or_ref : mut_or_ref -> mut_or_ref -> Prims.bool) =
  fun m1 ->
    fun m2 ->
      match (m1, m2) with
      | (MUT, MUT) -> true
      | (REF, REF) -> true
      | (uu___, uu___1) -> false
let rec iter : 'a . ('a -> unit) -> 'a Prims.list -> unit =
  fun f -> fun l -> match l with | [] -> () | x::xs -> (f x; iter f xs)
let iopt : 'a . ('a -> unit) -> 'a FStar_Pervasives_Native.option -> unit =
  fun f ->
    fun o ->
      match o with
      | FStar_Pervasives_Native.Some x -> f x
      | FStar_Pervasives_Native.None -> ()
let ieither :
  'a 'b .
    ('a -> unit) -> ('b -> unit) -> ('a, 'b) FStar_Pervasives.either -> unit
  =
  fun f ->
    fun g ->
      fun e ->
        match e with
        | FStar_Pervasives.Inl x -> f x
        | FStar_Pervasives.Inr x -> g x
let rec (scan_decl : FStar_Parser_AST.dep_scan_callbacks -> decl -> unit) =
  fun cbs ->
    fun d ->
      match d with
      | FnDefn f -> scan_fn_defn cbs f
      | FnDecl d1 -> scan_fn_decl cbs d1
and (scan_fn_decl : FStar_Parser_AST.dep_scan_callbacks -> fn_decl -> unit) =
  fun cbs ->
    fun f ->
      iter (scan_binder cbs) f.binders3; scan_ascription cbs f.ascription2
and (scan_fn_defn : FStar_Parser_AST.dep_scan_callbacks -> fn_defn -> unit) =
  fun cbs ->
    fun f ->
      iter (scan_binder cbs) f.binders2;
      ieither (scan_computation_type cbs)
        (iopt cbs.FStar_Parser_AST.scan_term) f.ascription1;
      iopt cbs.FStar_Parser_AST.scan_term f.measure;
      ieither (scan_stmt cbs) (scan_lambda cbs) f.body3
and (scan_binder : FStar_Parser_AST.dep_scan_callbacks -> binder -> unit) =
  fun cbs -> fun b -> cbs.FStar_Parser_AST.scan_binder b
and (scan_ascription :
  FStar_Parser_AST.dep_scan_callbacks ->
    (computation_type, FStar_Parser_AST.term FStar_Pervasives_Native.option)
      FStar_Pervasives.either -> unit)
  =
  fun cbs ->
    fun a ->
      ieither (scan_computation_type cbs)
        (iopt cbs.FStar_Parser_AST.scan_term) a
and (scan_computation_type :
  FStar_Parser_AST.dep_scan_callbacks -> computation_type -> unit) =
  fun cbs ->
    fun c ->
      scan_slprop cbs c.precondition;
      cbs.FStar_Parser_AST.scan_term c.return_type;
      scan_slprop cbs c.postcondition;
      iopt cbs.FStar_Parser_AST.scan_term c.opens
and (scan_slprop : FStar_Parser_AST.dep_scan_callbacks -> slprop -> unit) =
  fun cbs ->
    fun s ->
      let uu___ = s.v in
      match uu___ with | SLPropTerm s1 -> cbs.FStar_Parser_AST.scan_term s1
and (scan_lambda : FStar_Parser_AST.dep_scan_callbacks -> lambda -> unit) =
  fun cbs ->
    fun l ->
      iter (scan_binder cbs) l.binders1;
      iopt (scan_computation_type cbs) l.ascription;
      scan_stmt cbs l.body2
and (scan_stmt : FStar_Parser_AST.dep_scan_callbacks -> stmt -> unit) =
  fun cbs ->
    fun s ->
      match s.s with
      | Open l -> cbs.FStar_Parser_AST.add_open l
      | Expr e -> cbs.FStar_Parser_AST.scan_term e.e
      | Assignment { lhs = l; value = v;_} ->
          (cbs.FStar_Parser_AST.scan_term l; cbs.FStar_Parser_AST.scan_term v)
      | ArrayAssignment { arr = a; index = i; value1 = v;_} ->
          (cbs.FStar_Parser_AST.scan_term a;
           cbs.FStar_Parser_AST.scan_term i;
           cbs.FStar_Parser_AST.scan_term v)
      | LetBinding { qualifier = q; pat = p; typ = t; init1 = init;_} ->
          (iopt (scan_let_init cbs) init;
           cbs.FStar_Parser_AST.scan_pattern p;
           iopt cbs.FStar_Parser_AST.scan_term t)
      | Block { stmt = s1;_} -> scan_stmt cbs s1
      | If { head = h; join_slprop = j; then_ = t; else_opt = e;_} ->
          (cbs.FStar_Parser_AST.scan_term h;
           iopt (scan_ensures_slprop cbs) j;
           scan_stmt cbs t;
           iopt (scan_stmt cbs) e)
      | Match { head1 = h; returns_annot = r; branches = b;_} ->
          (cbs.FStar_Parser_AST.scan_term h;
           iopt (scan_ensures_slprop cbs) r;
           iter
             (fun uu___2 ->
                match uu___2 with
                | (p, s1) ->
                    (cbs.FStar_Parser_AST.scan_pattern p; scan_stmt cbs s1))
             b)
      | While { guard = g; id; invariant = i; body = b;_} ->
          (scan_stmt cbs g; scan_slprop cbs i; scan_stmt cbs b)
      | Introduce { slprop = s1; witnesses = w;_} ->
          (scan_slprop cbs s1; iter cbs.FStar_Parser_AST.scan_term w)
      | Sequence { s1; s2;_} -> (scan_stmt cbs s1; scan_stmt cbs s2)
      | Parallel { p1; p2; q1; q2; b1; b2;_} ->
          (scan_slprop cbs p1;
           scan_slprop cbs p2;
           scan_slprop cbs q1;
           scan_slprop cbs q2;
           scan_stmt cbs b1;
           scan_stmt cbs b2)
      | ProofHintWithBinders { hint_type = ht; binders = bs;_} ->
          (scan_hint_type cbs ht; iter (scan_binder cbs) bs)
      | WithInvariants { names = n; body1 = b; returns_ = r;_} ->
          (iter cbs.FStar_Parser_AST.scan_term n;
           scan_stmt cbs b;
           iopt (scan_ensures_slprop cbs) r)
and (scan_let_init : FStar_Parser_AST.dep_scan_callbacks -> let_init -> unit)
  =
  fun cbs ->
    fun i ->
      match i with
      | Array_initializer a ->
          (cbs.FStar_Parser_AST.scan_term a.init;
           cbs.FStar_Parser_AST.scan_term a.len)
      | Default_initializer t -> cbs.FStar_Parser_AST.scan_term t
      | Lambda_initializer l -> scan_fn_defn cbs l
      | Stmt_initializer s -> scan_stmt cbs s
and (scan_ensures_slprop :
  FStar_Parser_AST.dep_scan_callbacks -> ensures_slprop -> unit) =
  fun cbs ->
    fun e ->
      let uu___ = e in
      match uu___ with
      | (h, s, t) ->
          (iopt
             (fun uu___2 ->
                match uu___2 with
                | (i, t1) -> cbs.FStar_Parser_AST.scan_term t1) h;
           scan_slprop cbs s;
           iopt cbs.FStar_Parser_AST.scan_term t)
and (scan_hint_type :
  FStar_Parser_AST.dep_scan_callbacks -> hint_type -> unit) =
  fun cbs ->
    fun h ->
      match h with
      | ASSERT s -> scan_slprop cbs s
      | ASSUME s -> scan_slprop cbs s
      | UNFOLD (ns, s) -> scan_slprop cbs s
      | FOLD (ns, s) -> scan_slprop cbs s
      | RENAME (ts, g, t) ->
          (iter
             (fun uu___1 ->
                match uu___1 with
                | (t1, t2) ->
                    (cbs.FStar_Parser_AST.scan_term t1;
                     cbs.FStar_Parser_AST.scan_term t2)) ts;
           iopt (scan_slprop cbs) g;
           iopt cbs.FStar_Parser_AST.scan_term t)
      | REWRITE (s1, s2, t) ->
          (scan_slprop cbs s1;
           scan_slprop cbs s2;
           iopt cbs.FStar_Parser_AST.scan_term t)
      | WILD -> ()
      | SHOW_PROOF_STATE uu___ -> ()
let (range_of_decl : decl -> rng) =
  fun d -> match d with | FnDefn f -> f.range3 | FnDecl d1 -> d1.range4
let (mk_comp :
  st_comp_tag ->
    slprop ->
      FStar_Ident.ident ->
        FStar_Parser_AST.term ->
          slprop ->
            FStar_Parser_AST.term FStar_Pervasives_Native.option ->
              rng -> computation_type)
  =
  fun tag ->
    fun precondition ->
      fun return_name ->
        fun return_type ->
          fun postcondition ->
            fun opens ->
              fun range ->
                {
                  tag;
                  precondition;
                  return_name;
                  return_type;
                  postcondition;
                  opens;
                  range
                }
let (add_decorations :
  decl -> FStar_Parser_AST.decoration Prims.list -> decl) =
  fun d ->
    fun ds ->
      match d with
      | FnDefn f ->
          FnDefn
            {
              id1 = (f.id1);
              is_rec = (f.is_rec);
              binders2 = (f.binders2);
              ascription1 = (f.ascription1);
              measure = (f.measure);
              body3 = (f.body3);
              decorations = (FStar_List_Tot_Base.append ds f.decorations);
              range3 = (f.range3)
            }
      | FnDecl f ->
          FnDecl
            {
              id2 = (f.id2);
              binders3 = (f.binders3);
              ascription2 = (f.ascription2);
              decorations1 = (FStar_List_Tot_Base.append ds f.decorations1);
              range4 = (f.range4)
            }
let (mk_expr : FStar_Parser_AST.term -> stmt') = fun e -> Expr { e }
let (mk_assignment : FStar_Parser_AST.term -> FStar_Parser_AST.term -> stmt')
  = fun id -> fun value -> Assignment { lhs = id; value }
let (mk_array_assignment :
  FStar_Parser_AST.term ->
    FStar_Parser_AST.term -> FStar_Parser_AST.term -> stmt')
  =
  fun arr ->
    fun index -> fun value -> ArrayAssignment { arr; index; value1 = value }
let (mk_let_binding :
  mut_or_ref FStar_Pervasives_Native.option ->
    FStar_Parser_AST.pattern ->
      FStar_Parser_AST.term FStar_Pervasives_Native.option ->
        let_init FStar_Pervasives_Native.option -> stmt')
  =
  fun qualifier ->
    fun pat ->
      fun typ -> fun init -> LetBinding { qualifier; pat; typ; init1 = init }
let (mk_block : stmt -> stmt') = fun stmt1 -> Block { stmt = stmt1 }
let (mk_if :
  FStar_Parser_AST.term ->
    ensures_slprop FStar_Pervasives_Native.option ->
      stmt -> stmt FStar_Pervasives_Native.option -> stmt')
  =
  fun head ->
    fun join_slprop ->
      fun then_ -> fun else_opt -> If { head; join_slprop; then_; else_opt }
let (mk_match :
  FStar_Parser_AST.term ->
    ensures_slprop FStar_Pervasives_Native.option ->
      (FStar_Parser_AST.pattern * stmt) Prims.list -> stmt')
  =
  fun head ->
    fun returns_annot ->
      fun branches -> Match { head1 = head; returns_annot; branches }
let (mk_while : stmt -> FStar_Ident.ident -> slprop -> stmt -> stmt') =
  fun guard ->
    fun id ->
      fun invariant -> fun body -> While { guard; id; invariant; body }
let (mk_intro : slprop -> FStar_Parser_AST.term Prims.list -> stmt') =
  fun slprop1 -> fun witnesses -> Introduce { slprop = slprop1; witnesses }
let (mk_sequence : stmt -> stmt -> stmt') =
  fun s1 -> fun s2 -> Sequence { s1; s2 }
let (mk_stmt : stmt' -> rng -> stmt) =
  fun s -> fun range -> { s; range1 = range }
let (mk_fn_defn :
  FStar_Ident.ident ->
    Prims.bool ->
      binders ->
        (computation_type,
          FStar_Parser_AST.term FStar_Pervasives_Native.option)
          FStar_Pervasives.either ->
          FStar_Parser_AST.term FStar_Pervasives_Native.option ->
            (stmt, lambda) FStar_Pervasives.either ->
              FStar_Parser_AST.decoration Prims.list -> rng -> fn_defn)
  =
  fun id ->
    fun is_rec ->
      fun binders1 ->
        fun ascription ->
          fun measure ->
            fun body ->
              fun decorations ->
                fun range ->
                  {
                    id1 = id;
                    is_rec;
                    binders2 = binders1;
                    ascription1 = ascription;
                    measure;
                    body3 = body;
                    decorations;
                    range3 = range
                  }
let (mk_fn_decl :
  FStar_Ident.ident ->
    binders ->
      (computation_type,
        FStar_Parser_AST.term FStar_Pervasives_Native.option)
        FStar_Pervasives.either ->
        FStar_Parser_AST.decoration Prims.list -> rng -> fn_decl)
  =
  fun id ->
    fun binders1 ->
      fun ascription ->
        fun decorations ->
          fun range ->
            {
              id2 = id;
              binders3 = binders1;
              ascription2 = ascription;
              decorations1 = decorations;
              range4 = range
            }
let (mk_open : FStar_Ident.lident -> stmt') = fun lid -> Open lid
let (mk_par : slprop -> slprop -> slprop -> slprop -> stmt -> stmt -> stmt')
  =
  fun p1 ->
    fun p2 ->
      fun q1 ->
        fun q2 -> fun b1 -> fun b2 -> Parallel { p1; p2; q1; q2; b1; b2 }
let (mk_proof_hint_with_binders : hint_type -> binders -> stmt') =
  fun ht -> fun bs -> ProofHintWithBinders { hint_type = ht; binders = bs }
let (mk_lambda :
  binders ->
    computation_type FStar_Pervasives_Native.option -> stmt -> rng -> lambda)
  =
  fun bs ->
    fun ascription ->
      fun body ->
        fun range ->
          { binders1 = bs; ascription; body2 = body; range2 = range }
let (mk_with_invs :
  FStar_Parser_AST.term Prims.list ->
    stmt -> ensures_slprop FStar_Pervasives_Native.option -> stmt')
  =
  fun names ->
    fun body ->
      fun returns_ -> WithInvariants { names; body1 = body; returns_ }