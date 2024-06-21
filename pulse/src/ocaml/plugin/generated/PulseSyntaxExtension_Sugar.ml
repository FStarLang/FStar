open Prims
type rng = FStar_Compiler_Range_Type.range
let (dummyRange : FStar_Compiler_Range_Type.range) =
  FStar_Compiler_Range_Type.dummyRange
type binder = FStar_Parser_AST.binder
type binders = binder Prims.list
type vprop' =
  | VPropTerm of FStar_Parser_AST.term 
and vprop = {
  v: vprop' ;
  vrange: rng }
let (uu___is_VPropTerm : vprop' -> Prims.bool) = fun projectee -> true
let (__proj__VPropTerm__item___0 : vprop' -> FStar_Parser_AST.term) =
  fun projectee -> match projectee with | VPropTerm _0 -> _0
let (__proj__Mkvprop__item__v : vprop -> vprop') =
  fun projectee -> match projectee with | { v; vrange;_} -> v
let (__proj__Mkvprop__item__vrange : vprop -> rng) =
  fun projectee -> match projectee with | { v; vrange;_} -> vrange
let (as_vprop : vprop' -> rng -> vprop) = fun v -> fun r -> { v; vrange = r }
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
  precondition: vprop ;
  return_name: FStar_Ident.ident ;
  return_type: FStar_Parser_AST.term ;
  postcondition: vprop ;
  opens: FStar_Parser_AST.term FStar_Pervasives_Native.option ;
  range: rng }
let (__proj__Mkcomputation_type__item__tag : computation_type -> st_comp_tag)
  =
  fun projectee ->
    match projectee with
    | { tag; precondition; return_name; return_type; postcondition; opens;
        range;_} -> tag
let (__proj__Mkcomputation_type__item__precondition :
  computation_type -> vprop) =
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
  computation_type -> vprop) =
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
type pat__PatConstructor__payload =
  {
  head: FStar_Ident.lident ;
  args: pat Prims.list }
and pat =
  | PatVar of FStar_Ident.ident 
  | PatConstructor of pat__PatConstructor__payload 
let (__proj__Mkpat__PatConstructor__payload__item__head :
  pat__PatConstructor__payload -> FStar_Ident.lident) =
  fun projectee -> match projectee with | { head; args;_} -> head
let (__proj__Mkpat__PatConstructor__payload__item__args :
  pat__PatConstructor__payload -> pat Prims.list) =
  fun projectee -> match projectee with | { head; args;_} -> args
let (uu___is_PatVar : pat -> Prims.bool) =
  fun projectee -> match projectee with | PatVar _0 -> true | uu___ -> false
let (__proj__PatVar__item___0 : pat -> FStar_Ident.ident) =
  fun projectee -> match projectee with | PatVar _0 -> _0
let (uu___is_PatConstructor : pat -> Prims.bool) =
  fun projectee ->
    match projectee with | PatConstructor _0 -> true | uu___ -> false
let (__proj__PatConstructor__item___0 : pat -> pat__PatConstructor__payload)
  = fun projectee -> match projectee with | PatConstructor _0 -> _0
type hint_type =
  | ASSERT of vprop 
  | UNFOLD of (FStar_Ident.lident Prims.list FStar_Pervasives_Native.option *
  vprop) 
  | FOLD of (FStar_Ident.lident Prims.list FStar_Pervasives_Native.option *
  vprop) 
  | RENAME of ((FStar_Parser_AST.term * FStar_Parser_AST.term) Prims.list *
  vprop FStar_Pervasives_Native.option) 
  | REWRITE of (vprop * vprop * FStar_Parser_AST.term
  FStar_Pervasives_Native.option) 
  | WILD 
  | SHOW_PROOF_STATE of rng 
let (uu___is_ASSERT : hint_type -> Prims.bool) =
  fun projectee -> match projectee with | ASSERT _0 -> true | uu___ -> false
let (__proj__ASSERT__item___0 : hint_type -> vprop) =
  fun projectee -> match projectee with | ASSERT _0 -> _0
let (uu___is_UNFOLD : hint_type -> Prims.bool) =
  fun projectee -> match projectee with | UNFOLD _0 -> true | uu___ -> false
let (__proj__UNFOLD__item___0 :
  hint_type ->
    (FStar_Ident.lident Prims.list FStar_Pervasives_Native.option * vprop))
  = fun projectee -> match projectee with | UNFOLD _0 -> _0
let (uu___is_FOLD : hint_type -> Prims.bool) =
  fun projectee -> match projectee with | FOLD _0 -> true | uu___ -> false
let (__proj__FOLD__item___0 :
  hint_type ->
    (FStar_Ident.lident Prims.list FStar_Pervasives_Native.option * vprop))
  = fun projectee -> match projectee with | FOLD _0 -> _0
let (uu___is_RENAME : hint_type -> Prims.bool) =
  fun projectee -> match projectee with | RENAME _0 -> true | uu___ -> false
let (__proj__RENAME__item___0 :
  hint_type ->
    ((FStar_Parser_AST.term * FStar_Parser_AST.term) Prims.list * vprop
      FStar_Pervasives_Native.option))
  = fun projectee -> match projectee with | RENAME _0 -> _0
let (uu___is_REWRITE : hint_type -> Prims.bool) =
  fun projectee -> match projectee with | REWRITE _0 -> true | uu___ -> false
let (__proj__REWRITE__item___0 :
  hint_type ->
    (vprop * vprop * FStar_Parser_AST.term FStar_Pervasives_Native.option))
  = fun projectee -> match projectee with | REWRITE _0 -> _0
let (uu___is_WILD : hint_type -> Prims.bool) =
  fun projectee -> match projectee with | WILD -> true | uu___ -> false
let (uu___is_SHOW_PROOF_STATE : hint_type -> Prims.bool) =
  fun projectee ->
    match projectee with | SHOW_PROOF_STATE _0 -> true | uu___ -> false
let (__proj__SHOW_PROOF_STATE__item___0 : hint_type -> rng) =
  fun projectee -> match projectee with | SHOW_PROOF_STATE _0 -> _0
type array_init = {
  init: FStar_Parser_AST.term ;
  len: FStar_Parser_AST.term }
let (__proj__Mkarray_init__item__init : array_init -> FStar_Parser_AST.term)
  = fun projectee -> match projectee with | { init; len;_} -> init
let (__proj__Mkarray_init__item__len : array_init -> FStar_Parser_AST.term) =
  fun projectee -> match projectee with | { init; len;_} -> len
type ensures_vprop =
  ((FStar_Ident.ident * FStar_Parser_AST.term) FStar_Pervasives_Native.option
    * vprop * FStar_Parser_AST.term FStar_Pervasives_Native.option)
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
  id: FStar_Ident.ident ;
  typ: FStar_Parser_AST.term FStar_Pervasives_Native.option ;
  init1: let_init FStar_Pervasives_Native.option }
and stmt'__Block__payload = {
  stmt: stmt }
and stmt'__If__payload =
  {
  head1: FStar_Parser_AST.term ;
  join_vprop: ensures_vprop FStar_Pervasives_Native.option ;
  then_: stmt ;
  else_opt: stmt FStar_Pervasives_Native.option }
and stmt'__Match__payload =
  {
  head2: FStar_Parser_AST.term ;
  returns_annot: ensures_vprop FStar_Pervasives_Native.option ;
  branches: (FStar_Parser_AST.pattern * stmt) Prims.list }
and stmt'__While__payload =
  {
  guard: stmt ;
  id1: FStar_Ident.ident ;
  invariant: vprop ;
  body: stmt }
and stmt'__Introduce__payload =
  {
  vprop: vprop ;
  witnesses: FStar_Parser_AST.term Prims.list }
and stmt'__Sequence__payload = {
  s1: stmt ;
  s2: stmt }
and stmt'__Parallel__payload =
  {
  p1: vprop ;
  p2: vprop ;
  q1: vprop ;
  q2: vprop ;
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
  returns_: ensures_vprop FStar_Pervasives_Native.option }
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
and fn_decl =
  {
  id2: FStar_Ident.ident ;
  is_rec: Prims.bool ;
  binders2: binders ;
  ascription1:
    (computation_type, FStar_Parser_AST.term FStar_Pervasives_Native.option)
      FStar_Pervasives.either
    ;
  measure: FStar_Parser_AST.term FStar_Pervasives_Native.option ;
  body3: (stmt, lambda) FStar_Pervasives.either ;
  range3: rng }
and let_init =
  | Array_initializer of array_init 
  | Default_initializer of FStar_Parser_AST.term 
  | Lambda_initializer of fn_decl 
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
    match projectee with | { qualifier; id; typ; init1 = init;_} -> qualifier
let (__proj__Mkstmt'__LetBinding__payload__item__id :
  stmt'__LetBinding__payload -> FStar_Ident.ident) =
  fun projectee ->
    match projectee with | { qualifier; id; typ; init1 = init;_} -> id
let (__proj__Mkstmt'__LetBinding__payload__item__typ :
  stmt'__LetBinding__payload ->
    FStar_Parser_AST.term FStar_Pervasives_Native.option)
  =
  fun projectee ->
    match projectee with | { qualifier; id; typ; init1 = init;_} -> typ
let (__proj__Mkstmt'__LetBinding__payload__item__init :
  stmt'__LetBinding__payload -> let_init FStar_Pervasives_Native.option) =
  fun projectee ->
    match projectee with | { qualifier; id; typ; init1 = init;_} -> init
let (__proj__Mkstmt'__Block__payload__item__stmt :
  stmt'__Block__payload -> stmt) =
  fun projectee -> match projectee with | { stmt = stmt1;_} -> stmt1
let (__proj__Mkstmt'__If__payload__item__head :
  stmt'__If__payload -> FStar_Parser_AST.term) =
  fun projectee ->
    match projectee with
    | { head1 = head; join_vprop; then_; else_opt;_} -> head
let (__proj__Mkstmt'__If__payload__item__join_vprop :
  stmt'__If__payload -> ensures_vprop FStar_Pervasives_Native.option) =
  fun projectee ->
    match projectee with
    | { head1 = head; join_vprop; then_; else_opt;_} -> join_vprop
let (__proj__Mkstmt'__If__payload__item__then_ : stmt'__If__payload -> stmt)
  =
  fun projectee ->
    match projectee with
    | { head1 = head; join_vprop; then_; else_opt;_} -> then_
let (__proj__Mkstmt'__If__payload__item__else_opt :
  stmt'__If__payload -> stmt FStar_Pervasives_Native.option) =
  fun projectee ->
    match projectee with
    | { head1 = head; join_vprop; then_; else_opt;_} -> else_opt
let (__proj__Mkstmt'__Match__payload__item__head :
  stmt'__Match__payload -> FStar_Parser_AST.term) =
  fun projectee ->
    match projectee with | { head2 = head; returns_annot; branches;_} -> head
let (__proj__Mkstmt'__Match__payload__item__returns_annot :
  stmt'__Match__payload -> ensures_vprop FStar_Pervasives_Native.option) =
  fun projectee ->
    match projectee with
    | { head2 = head; returns_annot; branches;_} -> returns_annot
let (__proj__Mkstmt'__Match__payload__item__branches :
  stmt'__Match__payload -> (FStar_Parser_AST.pattern * stmt) Prims.list) =
  fun projectee ->
    match projectee with
    | { head2 = head; returns_annot; branches;_} -> branches
let (__proj__Mkstmt'__While__payload__item__guard :
  stmt'__While__payload -> stmt) =
  fun projectee ->
    match projectee with | { guard; id1 = id; invariant; body;_} -> guard
let (__proj__Mkstmt'__While__payload__item__id :
  stmt'__While__payload -> FStar_Ident.ident) =
  fun projectee ->
    match projectee with | { guard; id1 = id; invariant; body;_} -> id
let (__proj__Mkstmt'__While__payload__item__invariant :
  stmt'__While__payload -> vprop) =
  fun projectee ->
    match projectee with | { guard; id1 = id; invariant; body;_} -> invariant
let (__proj__Mkstmt'__While__payload__item__body :
  stmt'__While__payload -> stmt) =
  fun projectee ->
    match projectee with | { guard; id1 = id; invariant; body;_} -> body
let (__proj__Mkstmt'__Introduce__payload__item__vprop :
  stmt'__Introduce__payload -> vprop) =
  fun projectee ->
    match projectee with | { vprop = vprop1; witnesses;_} -> vprop1
let (__proj__Mkstmt'__Introduce__payload__item__witnesses :
  stmt'__Introduce__payload -> FStar_Parser_AST.term Prims.list) =
  fun projectee ->
    match projectee with | { vprop = vprop1; witnesses;_} -> witnesses
let (__proj__Mkstmt'__Sequence__payload__item__s1 :
  stmt'__Sequence__payload -> stmt) =
  fun projectee -> match projectee with | { s1; s2;_} -> s1
let (__proj__Mkstmt'__Sequence__payload__item__s2 :
  stmt'__Sequence__payload -> stmt) =
  fun projectee -> match projectee with | { s1; s2;_} -> s2
let (__proj__Mkstmt'__Parallel__payload__item__p1 :
  stmt'__Parallel__payload -> vprop) =
  fun projectee -> match projectee with | { p1; p2; q1; q2; b1; b2;_} -> p1
let (__proj__Mkstmt'__Parallel__payload__item__p2 :
  stmt'__Parallel__payload -> vprop) =
  fun projectee -> match projectee with | { p1; p2; q1; q2; b1; b2;_} -> p2
let (__proj__Mkstmt'__Parallel__payload__item__q1 :
  stmt'__Parallel__payload -> vprop) =
  fun projectee -> match projectee with | { p1; p2; q1; q2; b1; b2;_} -> q1
let (__proj__Mkstmt'__Parallel__payload__item__q2 :
  stmt'__Parallel__payload -> vprop) =
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
    ensures_vprop FStar_Pervasives_Native.option)
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
let (__proj__Mkfn_decl__item__id : fn_decl -> FStar_Ident.ident) =
  fun projectee ->
    match projectee with
    | { id2 = id; is_rec; binders2 = binders1; ascription1 = ascription;
        measure; body3 = body; range3 = range;_} -> id
let (__proj__Mkfn_decl__item__is_rec : fn_decl -> Prims.bool) =
  fun projectee ->
    match projectee with
    | { id2 = id; is_rec; binders2 = binders1; ascription1 = ascription;
        measure; body3 = body; range3 = range;_} -> is_rec
let (__proj__Mkfn_decl__item__binders : fn_decl -> binders) =
  fun projectee ->
    match projectee with
    | { id2 = id; is_rec; binders2 = binders1; ascription1 = ascription;
        measure; body3 = body; range3 = range;_} -> binders1
let (__proj__Mkfn_decl__item__ascription :
  fn_decl ->
    (computation_type, FStar_Parser_AST.term FStar_Pervasives_Native.option)
      FStar_Pervasives.either)
  =
  fun projectee ->
    match projectee with
    | { id2 = id; is_rec; binders2 = binders1; ascription1 = ascription;
        measure; body3 = body; range3 = range;_} -> ascription
let (__proj__Mkfn_decl__item__measure :
  fn_decl -> FStar_Parser_AST.term FStar_Pervasives_Native.option) =
  fun projectee ->
    match projectee with
    | { id2 = id; is_rec; binders2 = binders1; ascription1 = ascription;
        measure; body3 = body; range3 = range;_} -> measure
let (__proj__Mkfn_decl__item__body :
  fn_decl -> (stmt, lambda) FStar_Pervasives.either) =
  fun projectee ->
    match projectee with
    | { id2 = id; is_rec; binders2 = binders1; ascription1 = ascription;
        measure; body3 = body; range3 = range;_} -> body
let (__proj__Mkfn_decl__item__range : fn_decl -> rng) =
  fun projectee ->
    match projectee with
    | { id2 = id; is_rec; binders2 = binders1; ascription1 = ascription;
        measure; body3 = body; range3 = range;_} -> range
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
let (__proj__Lambda_initializer__item___0 : let_init -> fn_decl) =
  fun projectee -> match projectee with | Lambda_initializer _0 -> _0
let (uu___is_Stmt_initializer : let_init -> Prims.bool) =
  fun projectee ->
    match projectee with | Stmt_initializer _0 -> true | uu___ -> false
let (__proj__Stmt_initializer__item___0 : let_init -> stmt) =
  fun projectee -> match projectee with | Stmt_initializer _0 -> _0
type decl =
  | FnDecl of fn_decl 
let (uu___is_FnDecl : decl -> Prims.bool) = fun projectee -> true
let (__proj__FnDecl__item___0 : decl -> fn_decl) =
  fun projectee -> match projectee with | FnDecl _0 -> _0
let (mk_comp :
  st_comp_tag ->
    vprop ->
      FStar_Ident.ident ->
        FStar_Parser_AST.term ->
          vprop ->
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
    FStar_Ident.ident ->
      FStar_Parser_AST.term FStar_Pervasives_Native.option ->
        let_init FStar_Pervasives_Native.option -> stmt')
  =
  fun qualifier ->
    fun id ->
      fun typ -> fun init -> LetBinding { qualifier; id; typ; init1 = init }
let (mk_block : stmt -> stmt') = fun stmt1 -> Block { stmt = stmt1 }
let (mk_if :
  FStar_Parser_AST.term ->
    ensures_vprop FStar_Pervasives_Native.option ->
      stmt -> stmt FStar_Pervasives_Native.option -> stmt')
  =
  fun head ->
    fun join_vprop ->
      fun then_ ->
        fun else_opt -> If { head1 = head; join_vprop; then_; else_opt }
let (mk_match :
  FStar_Parser_AST.term ->
    ensures_vprop FStar_Pervasives_Native.option ->
      (FStar_Parser_AST.pattern * stmt) Prims.list -> stmt')
  =
  fun head ->
    fun returns_annot ->
      fun branches -> Match { head2 = head; returns_annot; branches }
let (mk_while : stmt -> FStar_Ident.ident -> vprop -> stmt -> stmt') =
  fun guard ->
    fun id ->
      fun invariant -> fun body -> While { guard; id1 = id; invariant; body }
let (mk_intro : vprop -> FStar_Parser_AST.term Prims.list -> stmt') =
  fun vprop1 -> fun witnesses -> Introduce { vprop = vprop1; witnesses }
let (mk_sequence : stmt -> stmt -> stmt') =
  fun s1 -> fun s2 -> Sequence { s1; s2 }
let (mk_stmt : stmt' -> rng -> stmt) =
  fun s -> fun range -> { s; range1 = range }
let (mk_fn_decl :
  FStar_Ident.ident ->
    Prims.bool ->
      binders ->
        (computation_type,
          FStar_Parser_AST.term FStar_Pervasives_Native.option)
          FStar_Pervasives.either ->
          FStar_Parser_AST.term FStar_Pervasives_Native.option ->
            (stmt, lambda) FStar_Pervasives.either -> rng -> fn_decl)
  =
  fun id ->
    fun is_rec ->
      fun binders1 ->
        fun ascription ->
          fun measure ->
            fun body ->
              fun range ->
                {
                  id2 = id;
                  is_rec;
                  binders2 = binders1;
                  ascription1 = ascription;
                  measure;
                  body3 = body;
                  range3 = range
                }
let (mk_open : FStar_Ident.lident -> stmt') = fun lid -> Open lid
let (mk_par : vprop -> vprop -> vprop -> vprop -> stmt -> stmt -> stmt') =
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
    stmt -> ensures_vprop FStar_Pervasives_Native.option -> stmt')
  =
  fun names ->
    fun body ->
      fun returns_ -> WithInvariants { names; body1 = body; returns_ }