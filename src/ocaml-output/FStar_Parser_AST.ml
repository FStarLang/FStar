open Prims
type level =
  | Un 
  | Expr 
  | Type_level 
  | Kind 
  | Formula 
let (uu___is_Un : level -> Prims.bool) =
  fun projectee -> match projectee with | Un -> true | uu___ -> false
let (uu___is_Expr : level -> Prims.bool) =
  fun projectee -> match projectee with | Expr -> true | uu___ -> false
let (uu___is_Type_level : level -> Prims.bool) =
  fun projectee -> match projectee with | Type_level -> true | uu___ -> false
let (uu___is_Kind : level -> Prims.bool) =
  fun projectee -> match projectee with | Kind -> true | uu___ -> false
let (uu___is_Formula : level -> Prims.bool) =
  fun projectee -> match projectee with | Formula -> true | uu___ -> false
type let_qualifier =
  | NoLetQualifier 
  | Rec 
let (uu___is_NoLetQualifier : let_qualifier -> Prims.bool) =
  fun projectee ->
    match projectee with | NoLetQualifier -> true | uu___ -> false
let (uu___is_Rec : let_qualifier -> Prims.bool) =
  fun projectee -> match projectee with | Rec -> true | uu___ -> false
type quote_kind =
  | Static 
  | Dynamic 
let (uu___is_Static : quote_kind -> Prims.bool) =
  fun projectee -> match projectee with | Static -> true | uu___ -> false
let (uu___is_Dynamic : quote_kind -> Prims.bool) =
  fun projectee -> match projectee with | Dynamic -> true | uu___ -> false
type term' =
  | Wild 
  | Const of FStar_Const.sconst 
  | Op of (FStar_Ident.ident * term Prims.list) 
  | Tvar of FStar_Ident.ident 
  | Uvar of FStar_Ident.ident 
  | Var of FStar_Ident.lid 
  | Name of FStar_Ident.lid 
  | Projector of (FStar_Ident.lid * FStar_Ident.ident) 
  | Construct of (FStar_Ident.lid * (term * imp) Prims.list) 
  | Abs of (pattern Prims.list * term) 
  | App of (term * term * imp) 
  | Let of (let_qualifier * (term Prims.list FStar_Pervasives_Native.option *
  (pattern * term)) Prims.list * term) 
  | LetOpen of (FStar_Ident.lid * term) 
  | LetOpenRecord of (term * term * term) 
  | Seq of (term * term) 
  | Bind of (FStar_Ident.ident * term * term) 
  | If of (term * term FStar_Pervasives_Native.option * term * term) 
  | Match of (term * term FStar_Pervasives_Native.option * (pattern * term
  FStar_Pervasives_Native.option * term) Prims.list) 
  | TryWith of (term * (pattern * term FStar_Pervasives_Native.option * term)
  Prims.list) 
  | Ascribed of (term * term * term FStar_Pervasives_Native.option) 
  | Record of (term FStar_Pervasives_Native.option * (FStar_Ident.lid * term)
  Prims.list) 
  | Project of (term * FStar_Ident.lid) 
  | Product of (binder Prims.list * term) 
  | Sum of ((binder, term) FStar_Pervasives.either Prims.list * term) 
  | QForall of (binder Prims.list * (FStar_Ident.ident Prims.list * term
  Prims.list Prims.list) * term) 
  | QExists of (binder Prims.list * (FStar_Ident.ident Prims.list * term
  Prims.list Prims.list) * term) 
  | Refine of (binder * term) 
  | NamedTyp of (FStar_Ident.ident * term) 
  | Paren of term 
  | Requires of (term * Prims.string FStar_Pervasives_Native.option) 
  | Ensures of (term * Prims.string FStar_Pervasives_Native.option) 
  | LexList of term Prims.list 
  | WFOrder of (term * term) 
  | Decreases of (term * Prims.string FStar_Pervasives_Native.option) 
  | Labeled of (term * Prims.string * Prims.bool) 
  | Discrim of FStar_Ident.lid 
  | Attributes of term Prims.list 
  | Antiquote of term 
  | Quote of (term * quote_kind) 
  | VQuote of term 
  | CalcProof of (term * term * calc_step Prims.list) 
and term = {
  tm: term' ;
  range: FStar_Range.range ;
  level: level }
and calc_step =
  | CalcStep of (term * term * term) 
and binder' =
  | Variable of FStar_Ident.ident 
  | TVariable of FStar_Ident.ident 
  | Annotated of (FStar_Ident.ident * term) 
  | TAnnotated of (FStar_Ident.ident * term) 
  | NoName of term 
and binder =
  {
  b: binder' ;
  brange: FStar_Range.range ;
  blevel: level ;
  aqual: arg_qualifier FStar_Pervasives_Native.option ;
  battributes: term Prims.list }
and pattern' =
  | PatWild of (arg_qualifier FStar_Pervasives_Native.option * term
  Prims.list) 
  | PatConst of FStar_Const.sconst 
  | PatApp of (pattern * pattern Prims.list) 
  | PatVar of (FStar_Ident.ident * arg_qualifier
  FStar_Pervasives_Native.option * term Prims.list) 
  | PatName of FStar_Ident.lid 
  | PatTvar of (FStar_Ident.ident * arg_qualifier
  FStar_Pervasives_Native.option * term Prims.list) 
  | PatList of pattern Prims.list 
  | PatTuple of (pattern Prims.list * Prims.bool) 
  | PatRecord of (FStar_Ident.lid * pattern) Prims.list 
  | PatAscribed of (pattern * (term * term FStar_Pervasives_Native.option)) 
  | PatOr of pattern Prims.list 
  | PatOp of FStar_Ident.ident 
and pattern = {
  pat: pattern' ;
  prange: FStar_Range.range }
and arg_qualifier =
  | Implicit 
  | Equality 
  | Meta of term 
and imp =
  | FsTypApp 
  | Hash 
  | UnivApp 
  | HashBrace of term 
  | Infix 
  | Nothing 
let (uu___is_Wild : term' -> Prims.bool) =
  fun projectee -> match projectee with | Wild -> true | uu___ -> false
let (uu___is_Const : term' -> Prims.bool) =
  fun projectee -> match projectee with | Const _0 -> true | uu___ -> false
let (__proj__Const__item___0 : term' -> FStar_Const.sconst) =
  fun projectee -> match projectee with | Const _0 -> _0
let (uu___is_Op : term' -> Prims.bool) =
  fun projectee -> match projectee with | Op _0 -> true | uu___ -> false
let (__proj__Op__item___0 : term' -> (FStar_Ident.ident * term Prims.list)) =
  fun projectee -> match projectee with | Op _0 -> _0
let (uu___is_Tvar : term' -> Prims.bool) =
  fun projectee -> match projectee with | Tvar _0 -> true | uu___ -> false
let (__proj__Tvar__item___0 : term' -> FStar_Ident.ident) =
  fun projectee -> match projectee with | Tvar _0 -> _0
let (uu___is_Uvar : term' -> Prims.bool) =
  fun projectee -> match projectee with | Uvar _0 -> true | uu___ -> false
let (__proj__Uvar__item___0 : term' -> FStar_Ident.ident) =
  fun projectee -> match projectee with | Uvar _0 -> _0
let (uu___is_Var : term' -> Prims.bool) =
  fun projectee -> match projectee with | Var _0 -> true | uu___ -> false
let (__proj__Var__item___0 : term' -> FStar_Ident.lid) =
  fun projectee -> match projectee with | Var _0 -> _0
let (uu___is_Name : term' -> Prims.bool) =
  fun projectee -> match projectee with | Name _0 -> true | uu___ -> false
let (__proj__Name__item___0 : term' -> FStar_Ident.lid) =
  fun projectee -> match projectee with | Name _0 -> _0
let (uu___is_Projector : term' -> Prims.bool) =
  fun projectee ->
    match projectee with | Projector _0 -> true | uu___ -> false
let (__proj__Projector__item___0 :
  term' -> (FStar_Ident.lid * FStar_Ident.ident)) =
  fun projectee -> match projectee with | Projector _0 -> _0
let (uu___is_Construct : term' -> Prims.bool) =
  fun projectee ->
    match projectee with | Construct _0 -> true | uu___ -> false
let (__proj__Construct__item___0 :
  term' -> (FStar_Ident.lid * (term * imp) Prims.list)) =
  fun projectee -> match projectee with | Construct _0 -> _0
let (uu___is_Abs : term' -> Prims.bool) =
  fun projectee -> match projectee with | Abs _0 -> true | uu___ -> false
let (__proj__Abs__item___0 : term' -> (pattern Prims.list * term)) =
  fun projectee -> match projectee with | Abs _0 -> _0
let (uu___is_App : term' -> Prims.bool) =
  fun projectee -> match projectee with | App _0 -> true | uu___ -> false
let (__proj__App__item___0 : term' -> (term * term * imp)) =
  fun projectee -> match projectee with | App _0 -> _0
let (uu___is_Let : term' -> Prims.bool) =
  fun projectee -> match projectee with | Let _0 -> true | uu___ -> false
let (__proj__Let__item___0 :
  term' ->
    (let_qualifier * (term Prims.list FStar_Pervasives_Native.option *
      (pattern * term)) Prims.list * term))
  = fun projectee -> match projectee with | Let _0 -> _0
let (uu___is_LetOpen : term' -> Prims.bool) =
  fun projectee -> match projectee with | LetOpen _0 -> true | uu___ -> false
let (__proj__LetOpen__item___0 : term' -> (FStar_Ident.lid * term)) =
  fun projectee -> match projectee with | LetOpen _0 -> _0
let (uu___is_LetOpenRecord : term' -> Prims.bool) =
  fun projectee ->
    match projectee with | LetOpenRecord _0 -> true | uu___ -> false
let (__proj__LetOpenRecord__item___0 : term' -> (term * term * term)) =
  fun projectee -> match projectee with | LetOpenRecord _0 -> _0
let (uu___is_Seq : term' -> Prims.bool) =
  fun projectee -> match projectee with | Seq _0 -> true | uu___ -> false
let (__proj__Seq__item___0 : term' -> (term * term)) =
  fun projectee -> match projectee with | Seq _0 -> _0
let (uu___is_Bind : term' -> Prims.bool) =
  fun projectee -> match projectee with | Bind _0 -> true | uu___ -> false
let (__proj__Bind__item___0 : term' -> (FStar_Ident.ident * term * term)) =
  fun projectee -> match projectee with | Bind _0 -> _0
let (uu___is_If : term' -> Prims.bool) =
  fun projectee -> match projectee with | If _0 -> true | uu___ -> false
let (__proj__If__item___0 :
  term' -> (term * term FStar_Pervasives_Native.option * term * term)) =
  fun projectee -> match projectee with | If _0 -> _0
let (uu___is_Match : term' -> Prims.bool) =
  fun projectee -> match projectee with | Match _0 -> true | uu___ -> false
let (__proj__Match__item___0 :
  term' ->
    (term * term FStar_Pervasives_Native.option * (pattern * term
      FStar_Pervasives_Native.option * term) Prims.list))
  = fun projectee -> match projectee with | Match _0 -> _0
let (uu___is_TryWith : term' -> Prims.bool) =
  fun projectee -> match projectee with | TryWith _0 -> true | uu___ -> false
let (__proj__TryWith__item___0 :
  term' ->
    (term * (pattern * term FStar_Pervasives_Native.option * term)
      Prims.list))
  = fun projectee -> match projectee with | TryWith _0 -> _0
let (uu___is_Ascribed : term' -> Prims.bool) =
  fun projectee ->
    match projectee with | Ascribed _0 -> true | uu___ -> false
let (__proj__Ascribed__item___0 :
  term' -> (term * term * term FStar_Pervasives_Native.option)) =
  fun projectee -> match projectee with | Ascribed _0 -> _0
let (uu___is_Record : term' -> Prims.bool) =
  fun projectee -> match projectee with | Record _0 -> true | uu___ -> false
let (__proj__Record__item___0 :
  term' ->
    (term FStar_Pervasives_Native.option * (FStar_Ident.lid * term)
      Prims.list))
  = fun projectee -> match projectee with | Record _0 -> _0
let (uu___is_Project : term' -> Prims.bool) =
  fun projectee -> match projectee with | Project _0 -> true | uu___ -> false
let (__proj__Project__item___0 : term' -> (term * FStar_Ident.lid)) =
  fun projectee -> match projectee with | Project _0 -> _0
let (uu___is_Product : term' -> Prims.bool) =
  fun projectee -> match projectee with | Product _0 -> true | uu___ -> false
let (__proj__Product__item___0 : term' -> (binder Prims.list * term)) =
  fun projectee -> match projectee with | Product _0 -> _0
let (uu___is_Sum : term' -> Prims.bool) =
  fun projectee -> match projectee with | Sum _0 -> true | uu___ -> false
let (__proj__Sum__item___0 :
  term' -> ((binder, term) FStar_Pervasives.either Prims.list * term)) =
  fun projectee -> match projectee with | Sum _0 -> _0
let (uu___is_QForall : term' -> Prims.bool) =
  fun projectee -> match projectee with | QForall _0 -> true | uu___ -> false
let (__proj__QForall__item___0 :
  term' ->
    (binder Prims.list * (FStar_Ident.ident Prims.list * term Prims.list
      Prims.list) * term))
  = fun projectee -> match projectee with | QForall _0 -> _0
let (uu___is_QExists : term' -> Prims.bool) =
  fun projectee -> match projectee with | QExists _0 -> true | uu___ -> false
let (__proj__QExists__item___0 :
  term' ->
    (binder Prims.list * (FStar_Ident.ident Prims.list * term Prims.list
      Prims.list) * term))
  = fun projectee -> match projectee with | QExists _0 -> _0
let (uu___is_Refine : term' -> Prims.bool) =
  fun projectee -> match projectee with | Refine _0 -> true | uu___ -> false
let (__proj__Refine__item___0 : term' -> (binder * term)) =
  fun projectee -> match projectee with | Refine _0 -> _0
let (uu___is_NamedTyp : term' -> Prims.bool) =
  fun projectee ->
    match projectee with | NamedTyp _0 -> true | uu___ -> false
let (__proj__NamedTyp__item___0 : term' -> (FStar_Ident.ident * term)) =
  fun projectee -> match projectee with | NamedTyp _0 -> _0
let (uu___is_Paren : term' -> Prims.bool) =
  fun projectee -> match projectee with | Paren _0 -> true | uu___ -> false
let (__proj__Paren__item___0 : term' -> term) =
  fun projectee -> match projectee with | Paren _0 -> _0
let (uu___is_Requires : term' -> Prims.bool) =
  fun projectee ->
    match projectee with | Requires _0 -> true | uu___ -> false
let (__proj__Requires__item___0 :
  term' -> (term * Prims.string FStar_Pervasives_Native.option)) =
  fun projectee -> match projectee with | Requires _0 -> _0
let (uu___is_Ensures : term' -> Prims.bool) =
  fun projectee -> match projectee with | Ensures _0 -> true | uu___ -> false
let (__proj__Ensures__item___0 :
  term' -> (term * Prims.string FStar_Pervasives_Native.option)) =
  fun projectee -> match projectee with | Ensures _0 -> _0
let (uu___is_LexList : term' -> Prims.bool) =
  fun projectee -> match projectee with | LexList _0 -> true | uu___ -> false
let (__proj__LexList__item___0 : term' -> term Prims.list) =
  fun projectee -> match projectee with | LexList _0 -> _0
let (uu___is_WFOrder : term' -> Prims.bool) =
  fun projectee -> match projectee with | WFOrder _0 -> true | uu___ -> false
let (__proj__WFOrder__item___0 : term' -> (term * term)) =
  fun projectee -> match projectee with | WFOrder _0 -> _0
let (uu___is_Decreases : term' -> Prims.bool) =
  fun projectee ->
    match projectee with | Decreases _0 -> true | uu___ -> false
let (__proj__Decreases__item___0 :
  term' -> (term * Prims.string FStar_Pervasives_Native.option)) =
  fun projectee -> match projectee with | Decreases _0 -> _0
let (uu___is_Labeled : term' -> Prims.bool) =
  fun projectee -> match projectee with | Labeled _0 -> true | uu___ -> false
let (__proj__Labeled__item___0 : term' -> (term * Prims.string * Prims.bool))
  = fun projectee -> match projectee with | Labeled _0 -> _0
let (uu___is_Discrim : term' -> Prims.bool) =
  fun projectee -> match projectee with | Discrim _0 -> true | uu___ -> false
let (__proj__Discrim__item___0 : term' -> FStar_Ident.lid) =
  fun projectee -> match projectee with | Discrim _0 -> _0
let (uu___is_Attributes : term' -> Prims.bool) =
  fun projectee ->
    match projectee with | Attributes _0 -> true | uu___ -> false
let (__proj__Attributes__item___0 : term' -> term Prims.list) =
  fun projectee -> match projectee with | Attributes _0 -> _0
let (uu___is_Antiquote : term' -> Prims.bool) =
  fun projectee ->
    match projectee with | Antiquote _0 -> true | uu___ -> false
let (__proj__Antiquote__item___0 : term' -> term) =
  fun projectee -> match projectee with | Antiquote _0 -> _0
let (uu___is_Quote : term' -> Prims.bool) =
  fun projectee -> match projectee with | Quote _0 -> true | uu___ -> false
let (__proj__Quote__item___0 : term' -> (term * quote_kind)) =
  fun projectee -> match projectee with | Quote _0 -> _0
let (uu___is_VQuote : term' -> Prims.bool) =
  fun projectee -> match projectee with | VQuote _0 -> true | uu___ -> false
let (__proj__VQuote__item___0 : term' -> term) =
  fun projectee -> match projectee with | VQuote _0 -> _0
let (uu___is_CalcProof : term' -> Prims.bool) =
  fun projectee ->
    match projectee with | CalcProof _0 -> true | uu___ -> false
let (__proj__CalcProof__item___0 :
  term' -> (term * term * calc_step Prims.list)) =
  fun projectee -> match projectee with | CalcProof _0 -> _0
let (__proj__Mkterm__item__tm : term -> term') =
  fun projectee ->
    match projectee with | { tm; range; level = level1;_} -> tm
let (__proj__Mkterm__item__range : term -> FStar_Range.range) =
  fun projectee ->
    match projectee with | { tm; range; level = level1;_} -> range
let (__proj__Mkterm__item__level : term -> level) =
  fun projectee ->
    match projectee with | { tm; range; level = level1;_} -> level1
let (uu___is_CalcStep : calc_step -> Prims.bool) = fun projectee -> true
let (__proj__CalcStep__item___0 : calc_step -> (term * term * term)) =
  fun projectee -> match projectee with | CalcStep _0 -> _0
let (uu___is_Variable : binder' -> Prims.bool) =
  fun projectee ->
    match projectee with | Variable _0 -> true | uu___ -> false
let (__proj__Variable__item___0 : binder' -> FStar_Ident.ident) =
  fun projectee -> match projectee with | Variable _0 -> _0
let (uu___is_TVariable : binder' -> Prims.bool) =
  fun projectee ->
    match projectee with | TVariable _0 -> true | uu___ -> false
let (__proj__TVariable__item___0 : binder' -> FStar_Ident.ident) =
  fun projectee -> match projectee with | TVariable _0 -> _0
let (uu___is_Annotated : binder' -> Prims.bool) =
  fun projectee ->
    match projectee with | Annotated _0 -> true | uu___ -> false
let (__proj__Annotated__item___0 : binder' -> (FStar_Ident.ident * term)) =
  fun projectee -> match projectee with | Annotated _0 -> _0
let (uu___is_TAnnotated : binder' -> Prims.bool) =
  fun projectee ->
    match projectee with | TAnnotated _0 -> true | uu___ -> false
let (__proj__TAnnotated__item___0 : binder' -> (FStar_Ident.ident * term)) =
  fun projectee -> match projectee with | TAnnotated _0 -> _0
let (uu___is_NoName : binder' -> Prims.bool) =
  fun projectee -> match projectee with | NoName _0 -> true | uu___ -> false
let (__proj__NoName__item___0 : binder' -> term) =
  fun projectee -> match projectee with | NoName _0 -> _0
let (__proj__Mkbinder__item__b : binder -> binder') =
  fun projectee ->
    match projectee with | { b; brange; blevel; aqual; battributes;_} -> b
let (__proj__Mkbinder__item__brange : binder -> FStar_Range.range) =
  fun projectee ->
    match projectee with
    | { b; brange; blevel; aqual; battributes;_} -> brange
let (__proj__Mkbinder__item__blevel : binder -> level) =
  fun projectee ->
    match projectee with
    | { b; brange; blevel; aqual; battributes;_} -> blevel
let (__proj__Mkbinder__item__aqual :
  binder -> arg_qualifier FStar_Pervasives_Native.option) =
  fun projectee ->
    match projectee with
    | { b; brange; blevel; aqual; battributes;_} -> aqual
let (__proj__Mkbinder__item__battributes : binder -> term Prims.list) =
  fun projectee ->
    match projectee with
    | { b; brange; blevel; aqual; battributes;_} -> battributes
let (uu___is_PatWild : pattern' -> Prims.bool) =
  fun projectee -> match projectee with | PatWild _0 -> true | uu___ -> false
let (__proj__PatWild__item___0 :
  pattern' ->
    (arg_qualifier FStar_Pervasives_Native.option * term Prims.list))
  = fun projectee -> match projectee with | PatWild _0 -> _0
let (uu___is_PatConst : pattern' -> Prims.bool) =
  fun projectee ->
    match projectee with | PatConst _0 -> true | uu___ -> false
let (__proj__PatConst__item___0 : pattern' -> FStar_Const.sconst) =
  fun projectee -> match projectee with | PatConst _0 -> _0
let (uu___is_PatApp : pattern' -> Prims.bool) =
  fun projectee -> match projectee with | PatApp _0 -> true | uu___ -> false
let (__proj__PatApp__item___0 : pattern' -> (pattern * pattern Prims.list)) =
  fun projectee -> match projectee with | PatApp _0 -> _0
let (uu___is_PatVar : pattern' -> Prims.bool) =
  fun projectee -> match projectee with | PatVar _0 -> true | uu___ -> false
let (__proj__PatVar__item___0 :
  pattern' ->
    (FStar_Ident.ident * arg_qualifier FStar_Pervasives_Native.option * term
      Prims.list))
  = fun projectee -> match projectee with | PatVar _0 -> _0
let (uu___is_PatName : pattern' -> Prims.bool) =
  fun projectee -> match projectee with | PatName _0 -> true | uu___ -> false
let (__proj__PatName__item___0 : pattern' -> FStar_Ident.lid) =
  fun projectee -> match projectee with | PatName _0 -> _0
let (uu___is_PatTvar : pattern' -> Prims.bool) =
  fun projectee -> match projectee with | PatTvar _0 -> true | uu___ -> false
let (__proj__PatTvar__item___0 :
  pattern' ->
    (FStar_Ident.ident * arg_qualifier FStar_Pervasives_Native.option * term
      Prims.list))
  = fun projectee -> match projectee with | PatTvar _0 -> _0
let (uu___is_PatList : pattern' -> Prims.bool) =
  fun projectee -> match projectee with | PatList _0 -> true | uu___ -> false
let (__proj__PatList__item___0 : pattern' -> pattern Prims.list) =
  fun projectee -> match projectee with | PatList _0 -> _0
let (uu___is_PatTuple : pattern' -> Prims.bool) =
  fun projectee ->
    match projectee with | PatTuple _0 -> true | uu___ -> false
let (__proj__PatTuple__item___0 :
  pattern' -> (pattern Prims.list * Prims.bool)) =
  fun projectee -> match projectee with | PatTuple _0 -> _0
let (uu___is_PatRecord : pattern' -> Prims.bool) =
  fun projectee ->
    match projectee with | PatRecord _0 -> true | uu___ -> false
let (__proj__PatRecord__item___0 :
  pattern' -> (FStar_Ident.lid * pattern) Prims.list) =
  fun projectee -> match projectee with | PatRecord _0 -> _0
let (uu___is_PatAscribed : pattern' -> Prims.bool) =
  fun projectee ->
    match projectee with | PatAscribed _0 -> true | uu___ -> false
let (__proj__PatAscribed__item___0 :
  pattern' -> (pattern * (term * term FStar_Pervasives_Native.option))) =
  fun projectee -> match projectee with | PatAscribed _0 -> _0
let (uu___is_PatOr : pattern' -> Prims.bool) =
  fun projectee -> match projectee with | PatOr _0 -> true | uu___ -> false
let (__proj__PatOr__item___0 : pattern' -> pattern Prims.list) =
  fun projectee -> match projectee with | PatOr _0 -> _0
let (uu___is_PatOp : pattern' -> Prims.bool) =
  fun projectee -> match projectee with | PatOp _0 -> true | uu___ -> false
let (__proj__PatOp__item___0 : pattern' -> FStar_Ident.ident) =
  fun projectee -> match projectee with | PatOp _0 -> _0
let (__proj__Mkpattern__item__pat : pattern -> pattern') =
  fun projectee -> match projectee with | { pat; prange;_} -> pat
let (__proj__Mkpattern__item__prange : pattern -> FStar_Range.range) =
  fun projectee -> match projectee with | { pat; prange;_} -> prange
let (uu___is_Implicit : arg_qualifier -> Prims.bool) =
  fun projectee -> match projectee with | Implicit -> true | uu___ -> false
let (uu___is_Equality : arg_qualifier -> Prims.bool) =
  fun projectee -> match projectee with | Equality -> true | uu___ -> false
let (uu___is_Meta : arg_qualifier -> Prims.bool) =
  fun projectee -> match projectee with | Meta _0 -> true | uu___ -> false
let (__proj__Meta__item___0 : arg_qualifier -> term) =
  fun projectee -> match projectee with | Meta _0 -> _0
let (uu___is_FsTypApp : imp -> Prims.bool) =
  fun projectee -> match projectee with | FsTypApp -> true | uu___ -> false
let (uu___is_Hash : imp -> Prims.bool) =
  fun projectee -> match projectee with | Hash -> true | uu___ -> false
let (uu___is_UnivApp : imp -> Prims.bool) =
  fun projectee -> match projectee with | UnivApp -> true | uu___ -> false
let (uu___is_HashBrace : imp -> Prims.bool) =
  fun projectee ->
    match projectee with | HashBrace _0 -> true | uu___ -> false
let (__proj__HashBrace__item___0 : imp -> term) =
  fun projectee -> match projectee with | HashBrace _0 -> _0
let (uu___is_Infix : imp -> Prims.bool) =
  fun projectee -> match projectee with | Infix -> true | uu___ -> false
let (uu___is_Nothing : imp -> Prims.bool) =
  fun projectee -> match projectee with | Nothing -> true | uu___ -> false
type patterns = (FStar_Ident.ident Prims.list * term Prims.list Prims.list)
type attributes_ = term Prims.list
type branch = (pattern * term FStar_Pervasives_Native.option * term)
type aqual = arg_qualifier FStar_Pervasives_Native.option
type knd = term
type typ = term
type expr = term
type tycon =
  | TyconAbstract of (FStar_Ident.ident * binder Prims.list * knd
  FStar_Pervasives_Native.option) 
  | TyconAbbrev of (FStar_Ident.ident * binder Prims.list * knd
  FStar_Pervasives_Native.option * term) 
  | TyconRecord of (FStar_Ident.ident * binder Prims.list * knd
  FStar_Pervasives_Native.option * (FStar_Ident.ident * aqual * attributes_ *
  term) Prims.list) 
  | TyconVariant of (FStar_Ident.ident * binder Prims.list * knd
  FStar_Pervasives_Native.option * (FStar_Ident.ident * term
  FStar_Pervasives_Native.option * Prims.bool) Prims.list) 
let (uu___is_TyconAbstract : tycon -> Prims.bool) =
  fun projectee ->
    match projectee with | TyconAbstract _0 -> true | uu___ -> false
let (__proj__TyconAbstract__item___0 :
  tycon ->
    (FStar_Ident.ident * binder Prims.list * knd
      FStar_Pervasives_Native.option))
  = fun projectee -> match projectee with | TyconAbstract _0 -> _0
let (uu___is_TyconAbbrev : tycon -> Prims.bool) =
  fun projectee ->
    match projectee with | TyconAbbrev _0 -> true | uu___ -> false
let (__proj__TyconAbbrev__item___0 :
  tycon ->
    (FStar_Ident.ident * binder Prims.list * knd
      FStar_Pervasives_Native.option * term))
  = fun projectee -> match projectee with | TyconAbbrev _0 -> _0
let (uu___is_TyconRecord : tycon -> Prims.bool) =
  fun projectee ->
    match projectee with | TyconRecord _0 -> true | uu___ -> false
let (__proj__TyconRecord__item___0 :
  tycon ->
    (FStar_Ident.ident * binder Prims.list * knd
      FStar_Pervasives_Native.option * (FStar_Ident.ident * aqual *
      attributes_ * term) Prims.list))
  = fun projectee -> match projectee with | TyconRecord _0 -> _0
let (uu___is_TyconVariant : tycon -> Prims.bool) =
  fun projectee ->
    match projectee with | TyconVariant _0 -> true | uu___ -> false
let (__proj__TyconVariant__item___0 :
  tycon ->
    (FStar_Ident.ident * binder Prims.list * knd
      FStar_Pervasives_Native.option * (FStar_Ident.ident * term
      FStar_Pervasives_Native.option * Prims.bool) Prims.list))
  = fun projectee -> match projectee with | TyconVariant _0 -> _0
type qualifier =
  | Private 
  | Noeq 
  | Unopteq 
  | Assumption 
  | DefaultEffect 
  | TotalEffect 
  | Effect_qual 
  | New 
  | Inline 
  | Visible 
  | Unfold_for_unification_and_vcgen 
  | Inline_for_extraction 
  | Irreducible 
  | NoExtract 
  | Reifiable 
  | Reflectable 
  | Opaque 
  | Logic 
let (uu___is_Private : qualifier -> Prims.bool) =
  fun projectee -> match projectee with | Private -> true | uu___ -> false
let (uu___is_Noeq : qualifier -> Prims.bool) =
  fun projectee -> match projectee with | Noeq -> true | uu___ -> false
let (uu___is_Unopteq : qualifier -> Prims.bool) =
  fun projectee -> match projectee with | Unopteq -> true | uu___ -> false
let (uu___is_Assumption : qualifier -> Prims.bool) =
  fun projectee -> match projectee with | Assumption -> true | uu___ -> false
let (uu___is_DefaultEffect : qualifier -> Prims.bool) =
  fun projectee ->
    match projectee with | DefaultEffect -> true | uu___ -> false
let (uu___is_TotalEffect : qualifier -> Prims.bool) =
  fun projectee ->
    match projectee with | TotalEffect -> true | uu___ -> false
let (uu___is_Effect_qual : qualifier -> Prims.bool) =
  fun projectee ->
    match projectee with | Effect_qual -> true | uu___ -> false
let (uu___is_New : qualifier -> Prims.bool) =
  fun projectee -> match projectee with | New -> true | uu___ -> false
let (uu___is_Inline : qualifier -> Prims.bool) =
  fun projectee -> match projectee with | Inline -> true | uu___ -> false
let (uu___is_Visible : qualifier -> Prims.bool) =
  fun projectee -> match projectee with | Visible -> true | uu___ -> false
let (uu___is_Unfold_for_unification_and_vcgen : qualifier -> Prims.bool) =
  fun projectee ->
    match projectee with
    | Unfold_for_unification_and_vcgen -> true
    | uu___ -> false
let (uu___is_Inline_for_extraction : qualifier -> Prims.bool) =
  fun projectee ->
    match projectee with | Inline_for_extraction -> true | uu___ -> false
let (uu___is_Irreducible : qualifier -> Prims.bool) =
  fun projectee ->
    match projectee with | Irreducible -> true | uu___ -> false
let (uu___is_NoExtract : qualifier -> Prims.bool) =
  fun projectee -> match projectee with | NoExtract -> true | uu___ -> false
let (uu___is_Reifiable : qualifier -> Prims.bool) =
  fun projectee -> match projectee with | Reifiable -> true | uu___ -> false
let (uu___is_Reflectable : qualifier -> Prims.bool) =
  fun projectee ->
    match projectee with | Reflectable -> true | uu___ -> false
let (uu___is_Opaque : qualifier -> Prims.bool) =
  fun projectee -> match projectee with | Opaque -> true | uu___ -> false
let (uu___is_Logic : qualifier -> Prims.bool) =
  fun projectee -> match projectee with | Logic -> true | uu___ -> false
type qualifiers = qualifier Prims.list
type decoration =
  | Qualifier of qualifier 
  | DeclAttributes of term Prims.list 
let (uu___is_Qualifier : decoration -> Prims.bool) =
  fun projectee ->
    match projectee with | Qualifier _0 -> true | uu___ -> false
let (__proj__Qualifier__item___0 : decoration -> qualifier) =
  fun projectee -> match projectee with | Qualifier _0 -> _0
let (uu___is_DeclAttributes : decoration -> Prims.bool) =
  fun projectee ->
    match projectee with | DeclAttributes _0 -> true | uu___ -> false
let (__proj__DeclAttributes__item___0 : decoration -> term Prims.list) =
  fun projectee -> match projectee with | DeclAttributes _0 -> _0
type lift_op =
  | NonReifiableLift of term 
  | ReifiableLift of (term * term) 
  | LiftForFree of term 
let (uu___is_NonReifiableLift : lift_op -> Prims.bool) =
  fun projectee ->
    match projectee with | NonReifiableLift _0 -> true | uu___ -> false
let (__proj__NonReifiableLift__item___0 : lift_op -> term) =
  fun projectee -> match projectee with | NonReifiableLift _0 -> _0
let (uu___is_ReifiableLift : lift_op -> Prims.bool) =
  fun projectee ->
    match projectee with | ReifiableLift _0 -> true | uu___ -> false
let (__proj__ReifiableLift__item___0 : lift_op -> (term * term)) =
  fun projectee -> match projectee with | ReifiableLift _0 -> _0
let (uu___is_LiftForFree : lift_op -> Prims.bool) =
  fun projectee ->
    match projectee with | LiftForFree _0 -> true | uu___ -> false
let (__proj__LiftForFree__item___0 : lift_op -> term) =
  fun projectee -> match projectee with | LiftForFree _0 -> _0
type lift =
  {
  msource: FStar_Ident.lid ;
  mdest: FStar_Ident.lid ;
  lift_op: lift_op }
let (__proj__Mklift__item__msource : lift -> FStar_Ident.lid) =
  fun projectee ->
    match projectee with | { msource; mdest; lift_op = lift_op1;_} -> msource
let (__proj__Mklift__item__mdest : lift -> FStar_Ident.lid) =
  fun projectee ->
    match projectee with | { msource; mdest; lift_op = lift_op1;_} -> mdest
let (__proj__Mklift__item__lift_op : lift -> lift_op) =
  fun projectee ->
    match projectee with
    | { msource; mdest; lift_op = lift_op1;_} -> lift_op1
type pragma =
  | SetOptions of Prims.string 
  | ResetOptions of Prims.string FStar_Pervasives_Native.option 
  | PushOptions of Prims.string FStar_Pervasives_Native.option 
  | PopOptions 
  | RestartSolver 
  | LightOff 
let (uu___is_SetOptions : pragma -> Prims.bool) =
  fun projectee ->
    match projectee with | SetOptions _0 -> true | uu___ -> false
let (__proj__SetOptions__item___0 : pragma -> Prims.string) =
  fun projectee -> match projectee with | SetOptions _0 -> _0
let (uu___is_ResetOptions : pragma -> Prims.bool) =
  fun projectee ->
    match projectee with | ResetOptions _0 -> true | uu___ -> false
let (__proj__ResetOptions__item___0 :
  pragma -> Prims.string FStar_Pervasives_Native.option) =
  fun projectee -> match projectee with | ResetOptions _0 -> _0
let (uu___is_PushOptions : pragma -> Prims.bool) =
  fun projectee ->
    match projectee with | PushOptions _0 -> true | uu___ -> false
let (__proj__PushOptions__item___0 :
  pragma -> Prims.string FStar_Pervasives_Native.option) =
  fun projectee -> match projectee with | PushOptions _0 -> _0
let (uu___is_PopOptions : pragma -> Prims.bool) =
  fun projectee -> match projectee with | PopOptions -> true | uu___ -> false
let (uu___is_RestartSolver : pragma -> Prims.bool) =
  fun projectee ->
    match projectee with | RestartSolver -> true | uu___ -> false
let (uu___is_LightOff : pragma -> Prims.bool) =
  fun projectee -> match projectee with | LightOff -> true | uu___ -> false
type decl' =
  | TopLevelModule of FStar_Ident.lid 
  | Open of FStar_Ident.lid 
  | Friend of FStar_Ident.lid 
  | Include of FStar_Ident.lid 
  | ModuleAbbrev of (FStar_Ident.ident * FStar_Ident.lid) 
  | TopLevelLet of (let_qualifier * (pattern * term) Prims.list) 
  | Tycon of (Prims.bool * Prims.bool * tycon Prims.list) 
  | Val of (FStar_Ident.ident * term) 
  | Exception of (FStar_Ident.ident * term FStar_Pervasives_Native.option) 
  | NewEffect of effect_decl 
  | LayeredEffect of effect_decl 
  | SubEffect of lift 
  | Polymonadic_bind of (FStar_Ident.lid * FStar_Ident.lid * FStar_Ident.lid
  * term) 
  | Polymonadic_subcomp of (FStar_Ident.lid * FStar_Ident.lid * term) 
  | Pragma of pragma 
  | Assume of (FStar_Ident.ident * term) 
  | Splice of (FStar_Ident.ident Prims.list * term) 
and decl =
  {
  d: decl' ;
  drange: FStar_Range.range ;
  quals: qualifiers ;
  attrs: attributes_ }
and effect_decl =
  | DefineEffect of (FStar_Ident.ident * binder Prims.list * term * decl
  Prims.list) 
  | RedefineEffect of (FStar_Ident.ident * binder Prims.list * term) 
let (uu___is_TopLevelModule : decl' -> Prims.bool) =
  fun projectee ->
    match projectee with | TopLevelModule _0 -> true | uu___ -> false
let (__proj__TopLevelModule__item___0 : decl' -> FStar_Ident.lid) =
  fun projectee -> match projectee with | TopLevelModule _0 -> _0
let (uu___is_Open : decl' -> Prims.bool) =
  fun projectee -> match projectee with | Open _0 -> true | uu___ -> false
let (__proj__Open__item___0 : decl' -> FStar_Ident.lid) =
  fun projectee -> match projectee with | Open _0 -> _0
let (uu___is_Friend : decl' -> Prims.bool) =
  fun projectee -> match projectee with | Friend _0 -> true | uu___ -> false
let (__proj__Friend__item___0 : decl' -> FStar_Ident.lid) =
  fun projectee -> match projectee with | Friend _0 -> _0
let (uu___is_Include : decl' -> Prims.bool) =
  fun projectee -> match projectee with | Include _0 -> true | uu___ -> false
let (__proj__Include__item___0 : decl' -> FStar_Ident.lid) =
  fun projectee -> match projectee with | Include _0 -> _0
let (uu___is_ModuleAbbrev : decl' -> Prims.bool) =
  fun projectee ->
    match projectee with | ModuleAbbrev _0 -> true | uu___ -> false
let (__proj__ModuleAbbrev__item___0 :
  decl' -> (FStar_Ident.ident * FStar_Ident.lid)) =
  fun projectee -> match projectee with | ModuleAbbrev _0 -> _0
let (uu___is_TopLevelLet : decl' -> Prims.bool) =
  fun projectee ->
    match projectee with | TopLevelLet _0 -> true | uu___ -> false
let (__proj__TopLevelLet__item___0 :
  decl' -> (let_qualifier * (pattern * term) Prims.list)) =
  fun projectee -> match projectee with | TopLevelLet _0 -> _0
let (uu___is_Tycon : decl' -> Prims.bool) =
  fun projectee -> match projectee with | Tycon _0 -> true | uu___ -> false
let (__proj__Tycon__item___0 :
  decl' -> (Prims.bool * Prims.bool * tycon Prims.list)) =
  fun projectee -> match projectee with | Tycon _0 -> _0
let (uu___is_Val : decl' -> Prims.bool) =
  fun projectee -> match projectee with | Val _0 -> true | uu___ -> false
let (__proj__Val__item___0 : decl' -> (FStar_Ident.ident * term)) =
  fun projectee -> match projectee with | Val _0 -> _0
let (uu___is_Exception : decl' -> Prims.bool) =
  fun projectee ->
    match projectee with | Exception _0 -> true | uu___ -> false
let (__proj__Exception__item___0 :
  decl' -> (FStar_Ident.ident * term FStar_Pervasives_Native.option)) =
  fun projectee -> match projectee with | Exception _0 -> _0
let (uu___is_NewEffect : decl' -> Prims.bool) =
  fun projectee ->
    match projectee with | NewEffect _0 -> true | uu___ -> false
let (__proj__NewEffect__item___0 : decl' -> effect_decl) =
  fun projectee -> match projectee with | NewEffect _0 -> _0
let (uu___is_LayeredEffect : decl' -> Prims.bool) =
  fun projectee ->
    match projectee with | LayeredEffect _0 -> true | uu___ -> false
let (__proj__LayeredEffect__item___0 : decl' -> effect_decl) =
  fun projectee -> match projectee with | LayeredEffect _0 -> _0
let (uu___is_SubEffect : decl' -> Prims.bool) =
  fun projectee ->
    match projectee with | SubEffect _0 -> true | uu___ -> false
let (__proj__SubEffect__item___0 : decl' -> lift) =
  fun projectee -> match projectee with | SubEffect _0 -> _0
let (uu___is_Polymonadic_bind : decl' -> Prims.bool) =
  fun projectee ->
    match projectee with | Polymonadic_bind _0 -> true | uu___ -> false
let (__proj__Polymonadic_bind__item___0 :
  decl' -> (FStar_Ident.lid * FStar_Ident.lid * FStar_Ident.lid * term)) =
  fun projectee -> match projectee with | Polymonadic_bind _0 -> _0
let (uu___is_Polymonadic_subcomp : decl' -> Prims.bool) =
  fun projectee ->
    match projectee with | Polymonadic_subcomp _0 -> true | uu___ -> false
let (__proj__Polymonadic_subcomp__item___0 :
  decl' -> (FStar_Ident.lid * FStar_Ident.lid * term)) =
  fun projectee -> match projectee with | Polymonadic_subcomp _0 -> _0
let (uu___is_Pragma : decl' -> Prims.bool) =
  fun projectee -> match projectee with | Pragma _0 -> true | uu___ -> false
let (__proj__Pragma__item___0 : decl' -> pragma) =
  fun projectee -> match projectee with | Pragma _0 -> _0
let (uu___is_Assume : decl' -> Prims.bool) =
  fun projectee -> match projectee with | Assume _0 -> true | uu___ -> false
let (__proj__Assume__item___0 : decl' -> (FStar_Ident.ident * term)) =
  fun projectee -> match projectee with | Assume _0 -> _0
let (uu___is_Splice : decl' -> Prims.bool) =
  fun projectee -> match projectee with | Splice _0 -> true | uu___ -> false
let (__proj__Splice__item___0 :
  decl' -> (FStar_Ident.ident Prims.list * term)) =
  fun projectee -> match projectee with | Splice _0 -> _0
let (__proj__Mkdecl__item__d : decl -> decl') =
  fun projectee -> match projectee with | { d; drange; quals; attrs;_} -> d
let (__proj__Mkdecl__item__drange : decl -> FStar_Range.range) =
  fun projectee ->
    match projectee with | { d; drange; quals; attrs;_} -> drange
let (__proj__Mkdecl__item__quals : decl -> qualifiers) =
  fun projectee ->
    match projectee with | { d; drange; quals; attrs;_} -> quals
let (__proj__Mkdecl__item__attrs : decl -> attributes_) =
  fun projectee ->
    match projectee with | { d; drange; quals; attrs;_} -> attrs
let (uu___is_DefineEffect : effect_decl -> Prims.bool) =
  fun projectee ->
    match projectee with | DefineEffect _0 -> true | uu___ -> false
let (__proj__DefineEffect__item___0 :
  effect_decl ->
    (FStar_Ident.ident * binder Prims.list * term * decl Prims.list))
  = fun projectee -> match projectee with | DefineEffect _0 -> _0
let (uu___is_RedefineEffect : effect_decl -> Prims.bool) =
  fun projectee ->
    match projectee with | RedefineEffect _0 -> true | uu___ -> false
let (__proj__RedefineEffect__item___0 :
  effect_decl -> (FStar_Ident.ident * binder Prims.list * term)) =
  fun projectee -> match projectee with | RedefineEffect _0 -> _0
type modul =
  | Module of (FStar_Ident.lid * decl Prims.list) 
  | Interface of (FStar_Ident.lid * decl Prims.list * Prims.bool) 
let (uu___is_Module : modul -> Prims.bool) =
  fun projectee -> match projectee with | Module _0 -> true | uu___ -> false
let (__proj__Module__item___0 : modul -> (FStar_Ident.lid * decl Prims.list))
  = fun projectee -> match projectee with | Module _0 -> _0
let (uu___is_Interface : modul -> Prims.bool) =
  fun projectee ->
    match projectee with | Interface _0 -> true | uu___ -> false
let (__proj__Interface__item___0 :
  modul -> (FStar_Ident.lid * decl Prims.list * Prims.bool)) =
  fun projectee -> match projectee with | Interface _0 -> _0
type file = modul
type inputFragment = (file, decl Prims.list) FStar_Pervasives.either
let (decl_drange : decl -> FStar_Range.range) = fun decl1 -> decl1.drange
let (check_id : FStar_Ident.ident -> unit) =
  fun id ->
    let first_char =
      let uu___ = FStar_Ident.string_of_id id in
      FStar_String.substring uu___ Prims.int_zero Prims.int_one in
    if (FStar_String.lowercase first_char) = first_char
    then ()
    else
      (let uu___1 =
         let uu___2 =
           let uu___3 = FStar_Ident.string_of_id id in
           FStar_Util.format1
             "Invalid identifer '%s'; expected a symbol that begins with a lower-case character"
             uu___3 in
         (FStar_Errors.Fatal_InvalidIdentifier, uu___2) in
       let uu___2 = FStar_Ident.range_of_id id in
       FStar_Errors.raise_error uu___1 uu___2)
let at_most_one :
  'uuuuu .
    Prims.string ->
      FStar_Range.range ->
        'uuuuu Prims.list -> 'uuuuu FStar_Pervasives_Native.option
  =
  fun s ->
    fun r ->
      fun l ->
        match l with
        | x::[] -> FStar_Pervasives_Native.Some x
        | [] -> FStar_Pervasives_Native.None
        | uu___ ->
            let uu___1 =
              let uu___2 =
                FStar_Util.format1
                  "At most one %s is allowed on declarations" s in
              (FStar_Errors.Fatal_MoreThanOneDeclaration, uu___2) in
            FStar_Errors.raise_error uu___1 r
let (mk_decl : decl' -> FStar_Range.range -> decoration Prims.list -> decl) =
  fun d ->
    fun r ->
      fun decorations ->
        let attributes_1 =
          let uu___ =
            FStar_List.choose
              (fun uu___1 ->
                 match uu___1 with
                 | DeclAttributes a -> FStar_Pervasives_Native.Some a
                 | uu___2 -> FStar_Pervasives_Native.None) decorations in
          at_most_one "attribute set" r uu___ in
        let attributes_2 = FStar_Util.dflt [] attributes_1 in
        let qualifiers1 =
          FStar_List.choose
            (fun uu___ ->
               match uu___ with
               | Qualifier q -> FStar_Pervasives_Native.Some q
               | uu___1 -> FStar_Pervasives_Native.None) decorations in
        { d; drange = r; quals = qualifiers1; attrs = attributes_2 }
let (mk_binder_with_attrs :
  binder' ->
    FStar_Range.range ->
      level ->
        arg_qualifier FStar_Pervasives_Native.option ->
          term Prims.list -> binder)
  =
  fun b ->
    fun r ->
      fun l ->
        fun i ->
          fun attrs ->
            { b; brange = r; blevel = l; aqual = i; battributes = attrs }
let (mk_binder :
  binder' ->
    FStar_Range.range ->
      level -> arg_qualifier FStar_Pervasives_Native.option -> binder)
  = fun b -> fun r -> fun l -> fun i -> mk_binder_with_attrs b r l i []
let (mk_term : term' -> FStar_Range.range -> level -> term) =
  fun t -> fun r -> fun l -> { tm = t; range = r; level = l }
let (mk_uminus :
  term -> FStar_Range.range -> FStar_Range.range -> level -> term) =
  fun t ->
    fun rminus ->
      fun r ->
        fun l ->
          let t1 =
            match t.tm with
            | Const (FStar_Const.Const_int
                (s, FStar_Pervasives_Native.Some (FStar_Const.Signed, width)))
                ->
                Const
                  (FStar_Const.Const_int
                     ((Prims.op_Hat "-" s),
                       (FStar_Pervasives_Native.Some
                          (FStar_Const.Signed, width))))
            | uu___ ->
                let uu___1 =
                  let uu___2 = FStar_Ident.mk_ident ("-", rminus) in
                  (uu___2, [t]) in
                Op uu___1 in
          mk_term t1 r l
let (mk_pattern : pattern' -> FStar_Range.range -> pattern) =
  fun p -> fun r -> { pat = p; prange = r }
let (un_curry_abs : pattern Prims.list -> term -> term') =
  fun ps ->
    fun body ->
      match body.tm with
      | Abs (p', body') -> Abs ((FStar_List.append ps p'), body')
      | uu___ -> Abs (ps, body)
let (mk_function :
  (pattern * term FStar_Pervasives_Native.option * term) Prims.list ->
    FStar_Range.range -> FStar_Range.range -> term)
  =
  fun branches ->
    fun r1 ->
      fun r2 ->
        let x = FStar_Ident.gen r1 in
        let uu___ =
          let uu___1 =
            let uu___2 =
              let uu___3 =
                let uu___4 =
                  let uu___5 =
                    let uu___6 =
                      let uu___7 = FStar_Ident.lid_of_ids [x] in Var uu___7 in
                    mk_term uu___6 r1 Expr in
                  (uu___5, FStar_Pervasives_Native.None, branches) in
                Match uu___4 in
              mk_term uu___3 r2 Expr in
            ([mk_pattern (PatVar (x, FStar_Pervasives_Native.None, [])) r1],
              uu___2) in
          Abs uu___1 in
        mk_term uu___ r2 Expr
let (un_function :
  pattern -> term -> (pattern * term) FStar_Pervasives_Native.option) =
  fun p ->
    fun tm ->
      match ((p.pat), (tm.tm)) with
      | (PatVar uu___, Abs (pats, body)) ->
          FStar_Pervasives_Native.Some
            ((mk_pattern (PatApp (p, pats)) p.prange), body)
      | uu___ -> FStar_Pervasives_Native.None
let (lid_with_range :
  FStar_Ident.lident -> FStar_Range.range -> FStar_Ident.lident) =
  fun lid ->
    fun r ->
      let uu___ = FStar_Ident.path_of_lid lid in
      FStar_Ident.lid_of_path uu___ r
let (consPat : FStar_Range.range -> pattern -> pattern -> pattern') =
  fun r ->
    fun hd ->
      fun tl ->
        PatApp
          ((mk_pattern (PatName FStar_Parser_Const.cons_lid) r), [hd; tl])
let (consTerm : FStar_Range.range -> term -> term -> term) =
  fun r ->
    fun hd ->
      fun tl ->
        mk_term
          (Construct
             (FStar_Parser_Const.cons_lid, [(hd, Nothing); (tl, Nothing)])) r
          Expr
let (mkConsList : FStar_Range.range -> term Prims.list -> term) =
  fun r ->
    fun elts ->
      let nil = mk_term (Construct (FStar_Parser_Const.nil_lid, [])) r Expr in
      FStar_List.fold_right (fun e -> fun tl -> consTerm r e tl) elts nil
let (unit_const : FStar_Range.range -> term) =
  fun r -> mk_term (Const FStar_Const.Const_unit) r Expr
let (ml_comp : term -> term) =
  fun t ->
    let ml = mk_term (Name FStar_Parser_Const.effect_ML_lid) t.range Expr in
    let t1 = mk_term (App (ml, t, Nothing)) t.range Expr in t1
let (tot_comp : term -> term) =
  fun t ->
    let ml = mk_term (Name FStar_Parser_Const.effect_Tot_lid) t.range Expr in
    let t1 = mk_term (App (ml, t, Nothing)) t.range Expr in t1
let (mkApp : term -> (term * imp) Prims.list -> FStar_Range.range -> term) =
  fun t ->
    fun args ->
      fun r ->
        match args with
        | [] -> t
        | uu___ ->
            (match t.tm with
             | Name s -> mk_term (Construct (s, args)) r Un
             | uu___1 ->
                 FStar_List.fold_left
                   (fun t1 ->
                      fun uu___2 ->
                        match uu___2 with
                        | (a, imp1) -> mk_term (App (t1, a, imp1)) r Un) t
                   args)
let (mkRefSet : FStar_Range.range -> term Prims.list -> term) =
  fun r ->
    fun elts ->
      let uu___ =
        (FStar_Parser_Const.set_empty, FStar_Parser_Const.set_singleton,
          FStar_Parser_Const.set_union, FStar_Parser_Const.heap_addr_of_lid) in
      match uu___ with
      | (empty_lid, singleton_lid, union_lid, addr_of_lid) ->
          let empty =
            let uu___1 =
              let uu___2 = FStar_Ident.set_lid_range empty_lid r in
              Var uu___2 in
            mk_term uu___1 r Expr in
          let addr_of =
            let uu___1 =
              let uu___2 = FStar_Ident.set_lid_range addr_of_lid r in
              Var uu___2 in
            mk_term uu___1 r Expr in
          let singleton =
            let uu___1 =
              let uu___2 = FStar_Ident.set_lid_range singleton_lid r in
              Var uu___2 in
            mk_term uu___1 r Expr in
          let union =
            let uu___1 =
              let uu___2 = FStar_Ident.set_lid_range union_lid r in
              Var uu___2 in
            mk_term uu___1 r Expr in
          FStar_List.fold_right
            (fun e ->
               fun tl ->
                 let e1 = mkApp addr_of [(e, Nothing)] r in
                 let single_e = mkApp singleton [(e1, Nothing)] r in
                 mkApp union [(single_e, Nothing); (tl, Nothing)] r) elts
            empty
let (mkExplicitApp : term -> term Prims.list -> FStar_Range.range -> term) =
  fun t ->
    fun args ->
      fun r ->
        match args with
        | [] -> t
        | uu___ ->
            (match t.tm with
             | Name s ->
                 let uu___1 =
                   let uu___2 =
                     let uu___3 = FStar_List.map (fun a -> (a, Nothing)) args in
                     (s, uu___3) in
                   Construct uu___2 in
                 mk_term uu___1 r Un
             | uu___1 ->
                 FStar_List.fold_left
                   (fun t1 -> fun a -> mk_term (App (t1, a, Nothing)) r Un) t
                   args)
let (mkAdmitMagic : FStar_Range.range -> term) =
  fun r ->
    let admit =
      let admit_name =
        let uu___ =
          let uu___1 =
            FStar_Ident.set_lid_range FStar_Parser_Const.admit_lid r in
          Var uu___1 in
        mk_term uu___ r Expr in
      mkExplicitApp admit_name [unit_const r] r in
    let magic =
      let magic_name =
        let uu___ =
          let uu___1 =
            FStar_Ident.set_lid_range FStar_Parser_Const.magic_lid r in
          Var uu___1 in
        mk_term uu___ r Expr in
      mkExplicitApp magic_name [unit_const r] r in
    let admit_magic = mk_term (Seq (admit, magic)) r Expr in admit_magic
let mkWildAdmitMagic :
  'uuuuu .
    FStar_Range.range ->
      (pattern * 'uuuuu FStar_Pervasives_Native.option * term)
  =
  fun r ->
    let uu___ = mkAdmitMagic r in
    ((mk_pattern (PatWild (FStar_Pervasives_Native.None, [])) r),
      FStar_Pervasives_Native.None, uu___)
let focusBranches :
  'uuuuu .
    (Prims.bool * (pattern * 'uuuuu FStar_Pervasives_Native.option * term))
      Prims.list ->
      FStar_Range.range ->
        (pattern * 'uuuuu FStar_Pervasives_Native.option * term) Prims.list
  =
  fun branches ->
    fun r ->
      let should_filter =
        FStar_Util.for_some FStar_Pervasives_Native.fst branches in
      if should_filter
      then
        (FStar_Errors.log_issue r
           (FStar_Errors.Warning_Filtered, "Focusing on only some cases");
         (let focussed =
            let uu___1 =
              FStar_List.filter FStar_Pervasives_Native.fst branches in
            FStar_All.pipe_right uu___1
              (FStar_List.map FStar_Pervasives_Native.snd) in
          let uu___1 = let uu___2 = mkWildAdmitMagic r in [uu___2] in
          FStar_List.append focussed uu___1))
      else
        FStar_All.pipe_right branches
          (FStar_List.map FStar_Pervasives_Native.snd)
let focusLetBindings :
  'uuuuu .
    (Prims.bool * ('uuuuu * term)) Prims.list ->
      FStar_Range.range -> ('uuuuu * term) Prims.list
  =
  fun lbs ->
    fun r ->
      let should_filter = FStar_Util.for_some FStar_Pervasives_Native.fst lbs in
      if should_filter
      then
        (FStar_Errors.log_issue r
           (FStar_Errors.Warning_Filtered,
             "Focusing on only some cases in this (mutually) recursive definition");
         FStar_List.map
           (fun uu___1 ->
              match uu___1 with
              | (f, lb) ->
                  if f
                  then lb
                  else
                    (let uu___3 = mkAdmitMagic r in
                     ((FStar_Pervasives_Native.fst lb), uu___3))) lbs)
      else
        FStar_All.pipe_right lbs (FStar_List.map FStar_Pervasives_Native.snd)
let focusAttrLetBindings :
  'uuuuu 'uuuuu1 .
    ('uuuuu * (Prims.bool * ('uuuuu1 * term))) Prims.list ->
      FStar_Range.range -> ('uuuuu * ('uuuuu1 * term)) Prims.list
  =
  fun lbs ->
    fun r ->
      let should_filter =
        FStar_Util.for_some
          (fun uu___ -> match uu___ with | (attr, (focus, uu___1)) -> focus)
          lbs in
      if should_filter
      then
        (FStar_Errors.log_issue r
           (FStar_Errors.Warning_Filtered,
             "Focusing on only some cases in this (mutually) recursive definition");
         FStar_List.map
           (fun uu___1 ->
              match uu___1 with
              | (attr, (f, lb)) ->
                  if f
                  then (attr, lb)
                  else
                    (let uu___3 =
                       let uu___4 = mkAdmitMagic r in
                       ((FStar_Pervasives_Native.fst lb), uu___4) in
                     (attr, uu___3))) lbs)
      else
        FStar_All.pipe_right lbs
          (FStar_List.map
             (fun uu___1 ->
                match uu___1 with | (attr, (uu___2, lb)) -> (attr, lb)))
let (mkFsTypApp : term -> term Prims.list -> FStar_Range.range -> term) =
  fun t ->
    fun args ->
      fun r ->
        let uu___ = FStar_List.map (fun a -> (a, FsTypApp)) args in
        mkApp t uu___ r
let (mkTuple : term Prims.list -> FStar_Range.range -> term) =
  fun args ->
    fun r ->
      let cons =
        FStar_Parser_Const.mk_tuple_data_lid (FStar_List.length args) r in
      let uu___ = FStar_List.map (fun x -> (x, Nothing)) args in
      mkApp (mk_term (Name cons) r Expr) uu___ r
let (mkDTuple : term Prims.list -> FStar_Range.range -> term) =
  fun args ->
    fun r ->
      let cons =
        FStar_Parser_Const.mk_dtuple_data_lid (FStar_List.length args) r in
      let uu___ = FStar_List.map (fun x -> (x, Nothing)) args in
      mkApp (mk_term (Name cons) r Expr) uu___ r
let (mkRefinedBinder :
  FStar_Ident.ident ->
    term ->
      Prims.bool ->
        term FStar_Pervasives_Native.option ->
          FStar_Range.range ->
            arg_qualifier FStar_Pervasives_Native.option ->
              term Prims.list -> binder)
  =
  fun id ->
    fun t ->
      fun should_bind_var ->
        fun refopt ->
          fun m ->
            fun implicit ->
              fun attrs ->
                let b =
                  mk_binder_with_attrs (Annotated (id, t)) m Type_level
                    implicit attrs in
                match refopt with
                | FStar_Pervasives_Native.None -> b
                | FStar_Pervasives_Native.Some phi ->
                    if should_bind_var
                    then
                      mk_binder_with_attrs
                        (Annotated
                           (id, (mk_term (Refine (b, phi)) m Type_level))) m
                        Type_level implicit attrs
                    else
                      (let x = FStar_Ident.gen t.range in
                       let b1 =
                         mk_binder_with_attrs (Annotated (x, t)) m Type_level
                           implicit attrs in
                       mk_binder_with_attrs
                         (Annotated
                            (id, (mk_term (Refine (b1, phi)) m Type_level)))
                         m Type_level implicit attrs)
let (mkRefinedPattern :
  pattern ->
    term ->
      Prims.bool ->
        term FStar_Pervasives_Native.option ->
          FStar_Range.range -> FStar_Range.range -> pattern)
  =
  fun pat ->
    fun t ->
      fun should_bind_pat ->
        fun phi_opt ->
          fun t_range ->
            fun range ->
              let t1 =
                match phi_opt with
                | FStar_Pervasives_Native.None -> t
                | FStar_Pervasives_Native.Some phi ->
                    if should_bind_pat
                    then
                      (match pat.pat with
                       | PatVar (x, uu___, attrs) ->
                           mk_term
                             (Refine
                                ((mk_binder_with_attrs (Annotated (x, t))
                                    t_range Type_level
                                    FStar_Pervasives_Native.None attrs), phi))
                             range Type_level
                       | uu___ ->
                           let x = FStar_Ident.gen t_range in
                           let phi1 =
                             let x_var =
                               let uu___1 =
                                 let uu___2 = FStar_Ident.lid_of_ids [x] in
                                 Var uu___2 in
                               mk_term uu___1 phi.range Formula in
                             let pat_branch =
                               (pat, FStar_Pervasives_Native.None, phi) in
                             let otherwise_branch =
                               let uu___1 =
                                 let uu___2 =
                                   let uu___3 =
                                     FStar_Ident.lid_of_path ["False"]
                                       phi.range in
                                   Name uu___3 in
                                 mk_term uu___2 phi.range Formula in
                               ((mk_pattern
                                   (PatWild
                                      (FStar_Pervasives_Native.None, []))
                                   phi.range), FStar_Pervasives_Native.None,
                                 uu___1) in
                             mk_term
                               (Match
                                  (x_var, FStar_Pervasives_Native.None,
                                    [pat_branch; otherwise_branch]))
                               phi.range Formula in
                           mk_term
                             (Refine
                                ((mk_binder (Annotated (x, t)) t_range
                                    Type_level FStar_Pervasives_Native.None),
                                  phi1)) range Type_level)
                    else
                      (let x = FStar_Ident.gen t.range in
                       mk_term
                         (Refine
                            ((mk_binder (Annotated (x, t)) t_range Type_level
                                FStar_Pervasives_Native.None), phi)) range
                         Type_level) in
              mk_pattern
                (PatAscribed (pat, (t1, FStar_Pervasives_Native.None))) range
let rec (extract_named_refinement :
  term ->
    (FStar_Ident.ident * term * term FStar_Pervasives_Native.option)
      FStar_Pervasives_Native.option)
  =
  fun t1 ->
    match t1.tm with
    | NamedTyp (x, t) ->
        FStar_Pervasives_Native.Some (x, t, FStar_Pervasives_Native.None)
    | Refine
        ({ b = Annotated (x, t); brange = uu___; blevel = uu___1;
           aqual = uu___2; battributes = uu___3;_},
         t')
        ->
        FStar_Pervasives_Native.Some
          (x, t, (FStar_Pervasives_Native.Some t'))
    | Paren t -> extract_named_refinement t
    | uu___ -> FStar_Pervasives_Native.None
let rec (as_mlist :
  ((FStar_Ident.lid * decl) * decl Prims.list) -> decl Prims.list -> modul) =
  fun cur ->
    fun ds ->
      let uu___ = cur in
      match uu___ with
      | ((m_name, m_decl), cur1) ->
          (match ds with
           | [] -> Module (m_name, (m_decl :: (FStar_List.rev cur1)))
           | d::ds1 ->
               (match d.d with
                | TopLevelModule m' ->
                    FStar_Errors.raise_error
                      (FStar_Errors.Fatal_UnexpectedModuleDeclaration,
                        "Unexpected module declaration") d.drange
                | uu___1 -> as_mlist ((m_name, m_decl), (d :: cur1)) ds1))
let (as_frag :
  Prims.bool -> FStar_Range.range -> decl Prims.list -> inputFragment) =
  fun is_light ->
    fun light_range ->
      fun ds ->
        let uu___ =
          match ds with
          | d::ds1 -> (d, ds1)
          | [] -> FStar_Exn.raise FStar_Errors.Empty_frag in
        match uu___ with
        | (d, ds1) ->
            (match d.d with
             | TopLevelModule m ->
                 let ds2 =
                   if is_light
                   then
                     let uu___1 = mk_decl (Pragma LightOff) light_range [] in
                     uu___1 :: ds1
                   else ds1 in
                 let m1 = as_mlist ((m, d), []) ds2 in
                 FStar_Pervasives.Inl m1
             | uu___1 ->
                 let ds2 = d :: ds1 in
                 (FStar_List.iter
                    (fun uu___3 ->
                       match uu___3 with
                       | { d = TopLevelModule uu___4; drange = r;
                           quals = uu___5; attrs = uu___6;_} ->
                           FStar_Errors.raise_error
                             (FStar_Errors.Fatal_UnexpectedModuleDeclaration,
                               "Unexpected module declaration") r
                       | uu___4 -> ()) ds2;
                  FStar_Pervasives.Inr ds2))
let (compile_op :
  Prims.int -> Prims.string -> FStar_Range.range -> Prims.string) =
  fun arity ->
    fun s ->
      fun r ->
        let name_of_char uu___ =
          match uu___ with
          | 38 -> "Amp"
          | 64 -> "At"
          | 43 -> "Plus"
          | 45 when arity = Prims.int_one -> "Minus"
          | 45 -> "Subtraction"
          | 126 -> "Tilde"
          | 47 -> "Slash"
          | 92 -> "Backslash"
          | 60 -> "Less"
          | 61 -> "Equals"
          | 62 -> "Greater"
          | 95 -> "Underscore"
          | 124 -> "Bar"
          | 33 -> "Bang"
          | 94 -> "Hat"
          | 37 -> "Percent"
          | 42 -> "Star"
          | 63 -> "Question"
          | 58 -> "Colon"
          | 36 -> "Dollar"
          | 46 -> "Dot"
          | c ->
              FStar_Errors.raise_error
                (FStar_Errors.Fatal_UnexpectedOperatorSymbol,
                  (Prims.op_Hat "Unexpected operator symbol: '"
                     (Prims.op_Hat (FStar_Util.string_of_char c) "'"))) r in
        match s with
        | ".[]<-" -> "op_String_Assignment"
        | ".()<-" -> "op_Array_Assignment"
        | ".[||]<-" -> "op_Brack_Lens_Assignment"
        | ".(||)<-" -> "op_Lens_Assignment"
        | ".[]" -> "op_String_Access"
        | ".()" -> "op_Array_Access"
        | ".[||]" -> "op_Brack_Lens_Access"
        | ".(||)" -> "op_Lens_Access"
        | uu___ ->
            let uu___1 =
              let uu___2 =
                let uu___3 = FStar_String.list_of_string s in
                FStar_List.map name_of_char uu___3 in
              FStar_String.concat "_" uu___2 in
            Prims.op_Hat "op_" uu___1
let (compile_op' : Prims.string -> FStar_Range.range -> Prims.string) =
  fun s -> fun r -> compile_op (~- Prims.int_one) s r
let (string_of_fsdoc :
  (Prims.string * (Prims.string * Prims.string) Prims.list) -> Prims.string)
  =
  fun uu___ ->
    match uu___ with
    | (comment, keywords) ->
        let uu___1 =
          let uu___2 =
            FStar_List.map
              (fun uu___3 ->
                 match uu___3 with
                 | (k, v) -> Prims.op_Hat k (Prims.op_Hat "->" v)) keywords in
          FStar_String.concat "," uu___2 in
        Prims.op_Hat comment uu___1
let (string_of_let_qualifier : let_qualifier -> Prims.string) =
  fun uu___ -> match uu___ with | NoLetQualifier -> "" | Rec -> "rec"
let to_string_l :
  'uuuuu .
    Prims.string ->
      ('uuuuu -> Prims.string) -> 'uuuuu Prims.list -> Prims.string
  =
  fun sep ->
    fun f ->
      fun l ->
        let uu___ = FStar_List.map f l in FStar_String.concat sep uu___
let (imp_to_string : imp -> Prims.string) =
  fun uu___ -> match uu___ with | Hash -> "#" | uu___1 -> ""
let rec (term_to_string : term -> Prims.string) =
  fun x ->
    match x.tm with
    | Wild -> "_"
    | LexList l ->
        let uu___ =
          match l with
          | [] -> " "
          | hd::tl ->
              let uu___1 =
                let uu___2 = term_to_string hd in
                FStar_List.fold_left
                  (fun s ->
                     fun t ->
                       let uu___3 =
                         let uu___4 = term_to_string t in
                         Prims.op_Hat "; " uu___4 in
                       Prims.op_Hat s uu___3) uu___2 in
              FStar_All.pipe_right tl uu___1 in
        FStar_Util.format1 "%[%s]" uu___
    | Decreases (t, uu___) ->
        let uu___1 = term_to_string t in
        FStar_Util.format1 "(decreases %s)" uu___1
    | Requires (t, uu___) ->
        let uu___1 = term_to_string t in
        FStar_Util.format1 "(requires %s)" uu___1
    | Ensures (t, uu___) ->
        let uu___1 = term_to_string t in
        FStar_Util.format1 "(ensures %s)" uu___1
    | Labeled (t, l, uu___) ->
        let uu___1 = term_to_string t in
        FStar_Util.format2 "(labeled %s %s)" l uu___1
    | Const c -> FStar_Parser_Const.const_to_string c
    | Op (s, xs) ->
        let uu___ = FStar_Ident.string_of_id s in
        let uu___1 =
          let uu___2 =
            FStar_List.map (fun x1 -> FStar_All.pipe_right x1 term_to_string)
              xs in
          FStar_String.concat ", " uu___2 in
        FStar_Util.format2 "%s(%s)" uu___ uu___1
    | Tvar id -> FStar_Ident.string_of_id id
    | Uvar id -> FStar_Ident.string_of_id id
    | Var l -> FStar_Ident.string_of_lid l
    | Name l -> FStar_Ident.string_of_lid l
    | Projector (rec_lid, field_id) ->
        let uu___ = FStar_Ident.string_of_lid rec_lid in
        let uu___1 = FStar_Ident.string_of_id field_id in
        FStar_Util.format2 "%s?.%s" uu___ uu___1
    | Construct (l, args) ->
        let uu___ = FStar_Ident.string_of_lid l in
        let uu___1 =
          to_string_l " "
            (fun uu___2 ->
               match uu___2 with
               | (a, imp1) ->
                   let uu___3 = term_to_string a in
                   FStar_Util.format2 "%s%s" (imp_to_string imp1) uu___3)
            args in
        FStar_Util.format2 "(%s %s)" uu___ uu___1
    | Abs (pats, t) ->
        let uu___ = to_string_l " " pat_to_string pats in
        let uu___1 = FStar_All.pipe_right t term_to_string in
        FStar_Util.format2 "(fun %s -> %s)" uu___ uu___1
    | App (t1, t2, imp1) ->
        let uu___ = FStar_All.pipe_right t1 term_to_string in
        let uu___1 = FStar_All.pipe_right t2 term_to_string in
        FStar_Util.format3 "%s %s%s" uu___ (imp_to_string imp1) uu___1
    | Let (Rec, (a, (p, b))::lbs, body) ->
        let uu___ = attrs_opt_to_string a in
        let uu___1 =
          let uu___2 = FStar_All.pipe_right p pat_to_string in
          let uu___3 = FStar_All.pipe_right b term_to_string in
          FStar_Util.format2 "%s=%s" uu___2 uu___3 in
        let uu___2 =
          to_string_l " "
            (fun uu___3 ->
               match uu___3 with
               | (a1, (p1, b1)) ->
                   let uu___4 = attrs_opt_to_string a1 in
                   let uu___5 = FStar_All.pipe_right p1 pat_to_string in
                   let uu___6 = FStar_All.pipe_right b1 term_to_string in
                   FStar_Util.format3 "%sand %s=%s" uu___4 uu___5 uu___6) lbs in
        let uu___3 = FStar_All.pipe_right body term_to_string in
        FStar_Util.format4 "%slet rec %s%s in %s" uu___ uu___1 uu___2 uu___3
    | Let (q, (attrs, (pat, tm))::[], body) ->
        let uu___ = attrs_opt_to_string attrs in
        let uu___1 = FStar_All.pipe_right pat pat_to_string in
        let uu___2 = FStar_All.pipe_right tm term_to_string in
        let uu___3 = FStar_All.pipe_right body term_to_string in
        FStar_Util.format5 "%slet %s %s = %s in %s" uu___
          (string_of_let_qualifier q) uu___1 uu___2 uu___3
    | Let (uu___, uu___1, uu___2) ->
        FStar_Errors.raise_error
          (FStar_Errors.Fatal_EmptySurfaceLet,
            "Internal error: found an invalid surface Let") x.range
    | LetOpen (lid, t) ->
        let uu___ = FStar_Ident.string_of_lid lid in
        let uu___1 = term_to_string t in
        FStar_Util.format2 "let open %s in %s" uu___ uu___1
    | Seq (t1, t2) ->
        let uu___ = FStar_All.pipe_right t1 term_to_string in
        let uu___1 = FStar_All.pipe_right t2 term_to_string in
        FStar_Util.format2 "%s; %s" uu___ uu___1
    | Bind (id, t1, t2) ->
        let uu___ = FStar_Ident.string_of_id id in
        let uu___1 = term_to_string t1 in
        let uu___2 = term_to_string t2 in
        FStar_Util.format3 "%s <- %s; %s" uu___ uu___1 uu___2
    | If (t1, ret_opt, t2, t3) ->
        let uu___ = FStar_All.pipe_right t1 term_to_string in
        let uu___1 =
          match ret_opt with
          | FStar_Pervasives_Native.None -> ""
          | FStar_Pervasives_Native.Some ret ->
              let uu___2 = term_to_string ret in
              FStar_Util.format1 "ret %s " uu___2 in
        let uu___2 = FStar_All.pipe_right t2 term_to_string in
        let uu___3 = FStar_All.pipe_right t3 term_to_string in
        FStar_Util.format4 "if %s %sthen %s else %s" uu___ uu___1 uu___2
          uu___3
    | Match (t, ret_opt, branches) ->
        try_or_match_to_string x t branches ret_opt
    | TryWith (t, branches) ->
        try_or_match_to_string x t branches FStar_Pervasives_Native.None
    | Ascribed (t1, t2, FStar_Pervasives_Native.None) ->
        let uu___ = FStar_All.pipe_right t1 term_to_string in
        let uu___1 = FStar_All.pipe_right t2 term_to_string in
        FStar_Util.format2 "(%s : %s)" uu___ uu___1
    | Ascribed (t1, t2, FStar_Pervasives_Native.Some tac) ->
        let uu___ = FStar_All.pipe_right t1 term_to_string in
        let uu___1 = FStar_All.pipe_right t2 term_to_string in
        let uu___2 = FStar_All.pipe_right tac term_to_string in
        FStar_Util.format3 "(%s : %s by %s)" uu___ uu___1 uu___2
    | Record (FStar_Pervasives_Native.Some e, fields) ->
        let uu___ = FStar_All.pipe_right e term_to_string in
        let uu___1 =
          to_string_l " "
            (fun uu___2 ->
               match uu___2 with
               | (l, e1) ->
                   let uu___3 = FStar_Ident.string_of_lid l in
                   let uu___4 = FStar_All.pipe_right e1 term_to_string in
                   FStar_Util.format2 "%s=%s" uu___3 uu___4) fields in
        FStar_Util.format2 "{%s with %s}" uu___ uu___1
    | Record (FStar_Pervasives_Native.None, fields) ->
        let uu___ =
          to_string_l " "
            (fun uu___1 ->
               match uu___1 with
               | (l, e) ->
                   let uu___2 = FStar_Ident.string_of_lid l in
                   let uu___3 = FStar_All.pipe_right e term_to_string in
                   FStar_Util.format2 "%s=%s" uu___2 uu___3) fields in
        FStar_Util.format1 "{%s}" uu___
    | Project (e, l) ->
        let uu___ = FStar_All.pipe_right e term_to_string in
        let uu___1 = FStar_Ident.string_of_lid l in
        FStar_Util.format2 "%s.%s" uu___ uu___1
    | Product ([], t) -> term_to_string t
    | Product (b::hd::tl, t) ->
        term_to_string
          (mk_term
             (Product
                ([b], (mk_term (Product ((hd :: tl), t)) x.range x.level)))
             x.range x.level)
    | Product (b::[], t) when x.level = Type_level ->
        let uu___ = FStar_All.pipe_right b binder_to_string in
        let uu___1 = FStar_All.pipe_right t term_to_string in
        FStar_Util.format2 "%s -> %s" uu___ uu___1
    | Product (b::[], t) when x.level = Kind ->
        let uu___ = FStar_All.pipe_right b binder_to_string in
        let uu___1 = FStar_All.pipe_right t term_to_string in
        FStar_Util.format2 "%s => %s" uu___ uu___1
    | Sum (binders, t) ->
        let uu___ =
          FStar_All.pipe_right
            (FStar_List.append binders [FStar_Pervasives.Inr t])
            (FStar_List.map
               (fun uu___1 ->
                  match uu___1 with
                  | FStar_Pervasives.Inl b -> binder_to_string b
                  | FStar_Pervasives.Inr t1 -> term_to_string t1)) in
        FStar_All.pipe_right uu___ (FStar_String.concat " & ")
    | QForall (bs, (uu___, pats), t) ->
        let uu___1 = to_string_l " " binder_to_string bs in
        let uu___2 =
          to_string_l " \\/ " (to_string_l "; " term_to_string) pats in
        let uu___3 = FStar_All.pipe_right t term_to_string in
        FStar_Util.format3 "forall %s.{:pattern %s} %s" uu___1 uu___2 uu___3
    | QExists (bs, (uu___, pats), t) ->
        let uu___1 = to_string_l " " binder_to_string bs in
        let uu___2 =
          to_string_l " \\/ " (to_string_l "; " term_to_string) pats in
        let uu___3 = FStar_All.pipe_right t term_to_string in
        FStar_Util.format3 "exists %s.{:pattern %s} %s" uu___1 uu___2 uu___3
    | Refine (b, t) ->
        let uu___ = FStar_All.pipe_right b binder_to_string in
        let uu___1 = FStar_All.pipe_right t term_to_string in
        FStar_Util.format2 "%s:{%s}" uu___ uu___1
    | NamedTyp (x1, t) ->
        let uu___ = FStar_Ident.string_of_id x1 in
        let uu___1 = FStar_All.pipe_right t term_to_string in
        FStar_Util.format2 "%s:%s" uu___ uu___1
    | Paren t ->
        let uu___ = FStar_All.pipe_right t term_to_string in
        FStar_Util.format1 "(%s)" uu___
    | Product (bs, t) ->
        let uu___ =
          let uu___1 =
            FStar_All.pipe_right bs (FStar_List.map binder_to_string) in
          FStar_All.pipe_right uu___1 (FStar_String.concat ",") in
        let uu___1 = FStar_All.pipe_right t term_to_string in
        FStar_Util.format2 "Unidentified product: [%s] %s" uu___ uu___1
    | Discrim lid ->
        let uu___ = FStar_Ident.string_of_lid lid in
        FStar_Util.format1 "%s?" uu___
    | Attributes ts ->
        let uu___ =
          let uu___1 = FStar_List.map term_to_string ts in
          FStar_All.pipe_left (FStar_String.concat " ") uu___1 in
        FStar_Util.format1 "(attributes %s)" uu___
    | Antiquote t ->
        let uu___ = term_to_string t in FStar_Util.format1 "(`#%s)" uu___
    | Quote (t, Static) ->
        let uu___ = term_to_string t in FStar_Util.format1 "(`(%s))" uu___
    | Quote (t, Dynamic) ->
        let uu___ = term_to_string t in FStar_Util.format1 "quote (%s)" uu___
    | VQuote t ->
        let uu___ = term_to_string t in FStar_Util.format1 "`%%%s" uu___
    | CalcProof (rel, init, steps) ->
        let uu___ = term_to_string rel in
        let uu___1 = term_to_string init in
        let uu___2 =
          let uu___3 = FStar_List.map calc_step_to_string steps in
          FStar_All.pipe_left (FStar_String.concat " ") uu___3 in
        FStar_Util.format3 "calc (%s) { %s %s }" uu___ uu___1 uu___2
and (try_or_match_to_string :
  term ->
    term ->
      (pattern * term FStar_Pervasives_Native.option * term) Prims.list ->
        term FStar_Pervasives_Native.option -> Prims.string)
  =
  fun x ->
    fun scrutinee ->
      fun branches ->
        fun ret_opt ->
          let s =
            match x.tm with
            | Match uu___ -> "match"
            | TryWith uu___ -> "try"
            | uu___ -> failwith "impossible" in
          let uu___ = FStar_All.pipe_right scrutinee term_to_string in
          let uu___1 =
            match ret_opt with
            | FStar_Pervasives_Native.None -> ""
            | FStar_Pervasives_Native.Some ret ->
                let uu___2 = term_to_string ret in
                FStar_Util.format1 "ret %s " uu___2 in
          let uu___2 =
            to_string_l " | "
              (fun uu___3 ->
                 match uu___3 with
                 | (p, w, e) ->
                     let uu___4 = FStar_All.pipe_right p pat_to_string in
                     let uu___5 =
                       match w with
                       | FStar_Pervasives_Native.None -> ""
                       | FStar_Pervasives_Native.Some e1 ->
                           let uu___6 = term_to_string e1 in
                           FStar_Util.format1 "when %s" uu___6 in
                     let uu___6 = FStar_All.pipe_right e term_to_string in
                     FStar_Util.format3 "%s %s -> %s" uu___4 uu___5 uu___6)
              branches in
          FStar_Util.format4 "%s %s %swith %s" s uu___ uu___1 uu___2
and (calc_step_to_string : calc_step -> Prims.string) =
  fun uu___ ->
    match uu___ with
    | CalcStep (rel, just, next) ->
        let uu___1 = term_to_string rel in
        let uu___2 = term_to_string just in
        let uu___3 = term_to_string next in
        FStar_Util.format3 "%s{ %s } %s" uu___1 uu___2 uu___3
and (binder_to_string : binder -> Prims.string) =
  fun x ->
    let s =
      match x.b with
      | Variable i -> FStar_Ident.string_of_id i
      | TVariable i ->
          let uu___ = FStar_Ident.string_of_id i in
          FStar_Util.format1 "%s:_" uu___
      | TAnnotated (i, t) ->
          let uu___ = FStar_Ident.string_of_id i in
          let uu___1 = FStar_All.pipe_right t term_to_string in
          FStar_Util.format2 "%s:%s" uu___ uu___1
      | Annotated (i, t) ->
          let uu___ = FStar_Ident.string_of_id i in
          let uu___1 = FStar_All.pipe_right t term_to_string in
          FStar_Util.format2 "%s:%s" uu___ uu___1
      | NoName t -> FStar_All.pipe_right t term_to_string in
    let uu___ = aqual_to_string x.aqual in
    let uu___1 = attr_list_to_string x.battributes in
    FStar_Util.format3 "%s%s%s" uu___ uu___1 s
and (aqual_to_string :
  arg_qualifier FStar_Pervasives_Native.option -> Prims.string) =
  fun uu___ ->
    match uu___ with
    | FStar_Pervasives_Native.Some (Equality) -> "$"
    | FStar_Pervasives_Native.Some (Implicit) -> "#"
    | FStar_Pervasives_Native.Some (Meta t) ->
        let uu___1 = let uu___2 = term_to_string t in Prims.op_Hat uu___2 "]" in
        Prims.op_Hat "#[" uu___1
    | FStar_Pervasives_Native.None -> ""
and (attr_list_to_string : term Prims.list -> Prims.string) =
  fun uu___ ->
    match uu___ with
    | [] -> ""
    | l -> attrs_opt_to_string (FStar_Pervasives_Native.Some l)
and (pat_to_string : pattern -> Prims.string) =
  fun x ->
    match x.pat with
    | PatWild (FStar_Pervasives_Native.None, attrs) ->
        let uu___ = attr_list_to_string attrs in Prims.op_Hat uu___ "_"
    | PatWild (uu___, attrs) ->
        let uu___1 =
          let uu___2 = attr_list_to_string attrs in Prims.op_Hat uu___2 "_" in
        Prims.op_Hat "#" uu___1
    | PatConst c -> FStar_Parser_Const.const_to_string c
    | PatApp (p, ps) ->
        let uu___ = FStar_All.pipe_right p pat_to_string in
        let uu___1 = to_string_l " " pat_to_string ps in
        FStar_Util.format2 "(%s %s)" uu___ uu___1
    | PatTvar (i, aq, attrs) ->
        let uu___ = aqual_to_string aq in
        let uu___1 = attr_list_to_string attrs in
        let uu___2 = FStar_Ident.string_of_id i in
        FStar_Util.format3 "%s%s%s" uu___ uu___1 uu___2
    | PatVar (i, aq, attrs) ->
        let uu___ = aqual_to_string aq in
        let uu___1 = attr_list_to_string attrs in
        let uu___2 = FStar_Ident.string_of_id i in
        FStar_Util.format3 "%s%s%s" uu___ uu___1 uu___2
    | PatName l -> FStar_Ident.string_of_lid l
    | PatList l ->
        let uu___ = to_string_l "; " pat_to_string l in
        FStar_Util.format1 "[%s]" uu___
    | PatTuple (l, false) ->
        let uu___ = to_string_l ", " pat_to_string l in
        FStar_Util.format1 "(%s)" uu___
    | PatTuple (l, true) ->
        let uu___ = to_string_l ", " pat_to_string l in
        FStar_Util.format1 "(|%s|)" uu___
    | PatRecord l ->
        let uu___ =
          to_string_l "; "
            (fun uu___1 ->
               match uu___1 with
               | (f, e) ->
                   let uu___2 = FStar_Ident.string_of_lid f in
                   let uu___3 = FStar_All.pipe_right e pat_to_string in
                   FStar_Util.format2 "%s=%s" uu___2 uu___3) l in
        FStar_Util.format1 "{%s}" uu___
    | PatOr l -> to_string_l "|\n " pat_to_string l
    | PatOp op ->
        let uu___ = FStar_Ident.string_of_id op in
        FStar_Util.format1 "(%s)" uu___
    | PatAscribed (p, (t, FStar_Pervasives_Native.None)) ->
        let uu___ = FStar_All.pipe_right p pat_to_string in
        let uu___1 = FStar_All.pipe_right t term_to_string in
        FStar_Util.format2 "(%s:%s)" uu___ uu___1
    | PatAscribed (p, (t, FStar_Pervasives_Native.Some tac)) ->
        let uu___ = FStar_All.pipe_right p pat_to_string in
        let uu___1 = FStar_All.pipe_right t term_to_string in
        let uu___2 = FStar_All.pipe_right tac term_to_string in
        FStar_Util.format3 "(%s:%s by %s)" uu___ uu___1 uu___2
and (attrs_opt_to_string :
  term Prims.list FStar_Pervasives_Native.option -> Prims.string) =
  fun uu___ ->
    match uu___ with
    | FStar_Pervasives_Native.None -> ""
    | FStar_Pervasives_Native.Some attrs ->
        let uu___1 =
          let uu___2 = FStar_List.map term_to_string attrs in
          FStar_All.pipe_right uu___2 (FStar_String.concat "; ") in
        FStar_Util.format1 "[@ %s]" uu___1
let rec (head_id_of_pat : pattern -> FStar_Ident.lident Prims.list) =
  fun p ->
    match p.pat with
    | PatName l -> [l]
    | PatVar (i, uu___, uu___1) ->
        let uu___2 = FStar_Ident.lid_of_ids [i] in [uu___2]
    | PatApp (p1, uu___) -> head_id_of_pat p1
    | PatAscribed (p1, uu___) -> head_id_of_pat p1
    | uu___ -> []
let lids_of_let :
  'uuuuu . (pattern * 'uuuuu) Prims.list -> FStar_Ident.lident Prims.list =
  fun defs ->
    FStar_All.pipe_right defs
      (FStar_List.collect
         (fun uu___ -> match uu___ with | (p, uu___1) -> head_id_of_pat p))
let (id_of_tycon : tycon -> Prims.string) =
  fun uu___ ->
    match uu___ with
    | TyconAbstract (i, uu___1, uu___2) -> FStar_Ident.string_of_id i
    | TyconAbbrev (i, uu___1, uu___2, uu___3) -> FStar_Ident.string_of_id i
    | TyconRecord (i, uu___1, uu___2, uu___3) -> FStar_Ident.string_of_id i
    | TyconVariant (i, uu___1, uu___2, uu___3) -> FStar_Ident.string_of_id i
let (decl_to_string : decl -> Prims.string) =
  fun d ->
    match d.d with
    | TopLevelModule l ->
        let uu___ = FStar_Ident.string_of_lid l in
        Prims.op_Hat "module " uu___
    | Open l ->
        let uu___ = FStar_Ident.string_of_lid l in Prims.op_Hat "open " uu___
    | Friend l ->
        let uu___ = FStar_Ident.string_of_lid l in
        Prims.op_Hat "friend " uu___
    | Include l ->
        let uu___ = FStar_Ident.string_of_lid l in
        Prims.op_Hat "include " uu___
    | ModuleAbbrev (i, l) ->
        let uu___ = FStar_Ident.string_of_id i in
        let uu___1 = FStar_Ident.string_of_lid l in
        FStar_Util.format2 "module %s = %s" uu___ uu___1
    | TopLevelLet (uu___, pats) ->
        let uu___1 =
          let uu___2 =
            let uu___3 = lids_of_let pats in
            FStar_All.pipe_right uu___3
              (FStar_List.map (fun l -> FStar_Ident.string_of_lid l)) in
          FStar_All.pipe_right uu___2 (FStar_String.concat ", ") in
        Prims.op_Hat "let " uu___1
    | Assume (i, uu___) ->
        let uu___1 = FStar_Ident.string_of_id i in
        Prims.op_Hat "assume " uu___1
    | Tycon (uu___, uu___1, tys) ->
        let uu___2 =
          let uu___3 = FStar_All.pipe_right tys (FStar_List.map id_of_tycon) in
          FStar_All.pipe_right uu___3 (FStar_String.concat ", ") in
        Prims.op_Hat "type " uu___2
    | Val (i, uu___) ->
        let uu___1 = FStar_Ident.string_of_id i in Prims.op_Hat "val " uu___1
    | Exception (i, uu___) ->
        let uu___1 = FStar_Ident.string_of_id i in
        Prims.op_Hat "exception " uu___1
    | NewEffect (DefineEffect (i, uu___, uu___1, uu___2)) ->
        let uu___3 = FStar_Ident.string_of_id i in
        Prims.op_Hat "new_effect " uu___3
    | NewEffect (RedefineEffect (i, uu___, uu___1)) ->
        let uu___2 = FStar_Ident.string_of_id i in
        Prims.op_Hat "new_effect " uu___2
    | LayeredEffect (DefineEffect (i, uu___, uu___1, uu___2)) ->
        let uu___3 = FStar_Ident.string_of_id i in
        Prims.op_Hat "layered_effect " uu___3
    | LayeredEffect (RedefineEffect (i, uu___, uu___1)) ->
        let uu___2 = FStar_Ident.string_of_id i in
        Prims.op_Hat "layered_effect " uu___2
    | Polymonadic_bind (l1, l2, l3, uu___) ->
        let uu___1 = FStar_Ident.string_of_lid l1 in
        let uu___2 = FStar_Ident.string_of_lid l2 in
        let uu___3 = FStar_Ident.string_of_lid l3 in
        FStar_Util.format3 "polymonadic_bind (%s, %s) |> %s" uu___1 uu___2
          uu___3
    | Polymonadic_subcomp (l1, l2, uu___) ->
        let uu___1 = FStar_Ident.string_of_lid l1 in
        let uu___2 = FStar_Ident.string_of_lid l2 in
        FStar_Util.format2 "polymonadic_subcomp %s <: %s" uu___1 uu___2
    | Splice (ids, t) ->
        let uu___ =
          let uu___1 =
            let uu___2 =
              FStar_List.map (fun i -> FStar_Ident.string_of_id i) ids in
            FStar_All.pipe_left (FStar_String.concat ";") uu___2 in
          let uu___2 =
            let uu___3 =
              let uu___4 = term_to_string t in Prims.op_Hat uu___4 ")" in
            Prims.op_Hat "] (" uu___3 in
          Prims.op_Hat uu___1 uu___2 in
        Prims.op_Hat "splice[" uu___
    | SubEffect uu___ -> "sub_effect"
    | Pragma uu___ -> "pragma"
let (modul_to_string : modul -> Prims.string) =
  fun m ->
    match m with
    | Module (uu___, decls) ->
        let uu___1 =
          FStar_All.pipe_right decls (FStar_List.map decl_to_string) in
        FStar_All.pipe_right uu___1 (FStar_String.concat "\n")
    | Interface (uu___, decls, uu___1) ->
        let uu___2 =
          FStar_All.pipe_right decls (FStar_List.map decl_to_string) in
        FStar_All.pipe_right uu___2 (FStar_String.concat "\n")
let (decl_is_val : FStar_Ident.ident -> decl -> Prims.bool) =
  fun id ->
    fun decl1 ->
      match decl1.d with
      | Val (id', uu___) -> FStar_Ident.ident_equals id id'
      | uu___ -> false
let (thunk : term -> term) =
  fun ens ->
    let wildpat =
      mk_pattern (PatWild (FStar_Pervasives_Native.None, [])) ens.range in
    mk_term (Abs ([wildpat], ens)) ens.range Expr
let (idents_of_binders :
  binder Prims.list -> FStar_Range.range -> FStar_Ident.ident Prims.list) =
  fun bs ->
    fun r ->
      FStar_All.pipe_right bs
        (FStar_List.map
           (fun b ->
              match b.b with
              | Variable i -> i
              | TVariable i -> i
              | Annotated (i, uu___) -> i
              | TAnnotated (i, uu___) -> i
              | NoName uu___ ->
                  FStar_Errors.raise_error
                    (FStar_Errors.Fatal_MissingQuantifierBinder,
                      "Wildcard binders in quantifiers are not allowed") r))