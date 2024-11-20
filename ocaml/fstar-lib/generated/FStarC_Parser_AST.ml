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
  | Const of FStarC_Const.sconst 
  | Op of (FStarC_Ident.ident * term Prims.list) 
  | Tvar of FStarC_Ident.ident 
  | Uvar of FStarC_Ident.ident 
  | Var of FStarC_Ident.lid 
  | Name of FStarC_Ident.lid 
  | Projector of (FStarC_Ident.lid * FStarC_Ident.ident) 
  | Construct of (FStarC_Ident.lid * (term * imp) Prims.list) 
  | Abs of (pattern Prims.list * term) 
  | Function of ((pattern * term FStar_Pervasives_Native.option * term)
  Prims.list * FStarC_Compiler_Range_Type.range) 
  | App of (term * term * imp) 
  | Let of (let_qualifier * (term Prims.list FStar_Pervasives_Native.option *
  (pattern * term)) Prims.list * term) 
  | LetOperator of ((FStarC_Ident.ident * pattern * term) Prims.list * term)
  
  | LetOpen of (FStarC_Ident.lid * term) 
  | LetOpenRecord of (term * term * term) 
  | Seq of (term * term) 
  | Bind of (FStarC_Ident.ident * term * term) 
  | If of (term * FStarC_Ident.ident FStar_Pervasives_Native.option *
  (FStarC_Ident.ident FStar_Pervasives_Native.option * term * Prims.bool)
  FStar_Pervasives_Native.option * term * term) 
  | Match of (term * FStarC_Ident.ident FStar_Pervasives_Native.option *
  (FStarC_Ident.ident FStar_Pervasives_Native.option * term * Prims.bool)
  FStar_Pervasives_Native.option * (pattern * term
  FStar_Pervasives_Native.option * term) Prims.list) 
  | TryWith of (term * (pattern * term FStar_Pervasives_Native.option * term)
  Prims.list) 
  | Ascribed of (term * term * term FStar_Pervasives_Native.option *
  Prims.bool) 
  | Record of (term FStar_Pervasives_Native.option * (FStarC_Ident.lid *
  term) Prims.list) 
  | Project of (term * FStarC_Ident.lid) 
  | Product of (binder Prims.list * term) 
  | Sum of ((binder, term) FStar_Pervasives.either Prims.list * term) 
  | QForall of (binder Prims.list * (FStarC_Ident.ident Prims.list * term
  Prims.list Prims.list) * term) 
  | QExists of (binder Prims.list * (FStarC_Ident.ident Prims.list * term
  Prims.list Prims.list) * term) 
  | QuantOp of (FStarC_Ident.ident * binder Prims.list * (FStarC_Ident.ident
  Prims.list * term Prims.list Prims.list) * term) 
  | Refine of (binder * term) 
  | NamedTyp of (FStarC_Ident.ident * term) 
  | Paren of term 
  | Requires of (term * Prims.string FStar_Pervasives_Native.option) 
  | Ensures of (term * Prims.string FStar_Pervasives_Native.option) 
  | LexList of term Prims.list 
  | WFOrder of (term * term) 
  | Decreases of (term * Prims.string FStar_Pervasives_Native.option) 
  | Labeled of (term * Prims.string * Prims.bool) 
  | Discrim of FStarC_Ident.lid 
  | Attributes of term Prims.list 
  | Antiquote of term 
  | Quote of (term * quote_kind) 
  | VQuote of term 
  | CalcProof of (term * term * calc_step Prims.list) 
  | IntroForall of (binder Prims.list * term * term) 
  | IntroExists of (binder Prims.list * term * term Prims.list * term) 
  | IntroImplies of (term * term * binder * term) 
  | IntroOr of (Prims.bool * term * term * term) 
  | IntroAnd of (term * term * term * term) 
  | ElimForall of (binder Prims.list * term * term Prims.list) 
  | ElimExists of (binder Prims.list * term * term * binder * term) 
  | ElimImplies of (term * term * term) 
  | ElimOr of (term * term * term * binder * term * binder * term) 
  | ElimAnd of (term * term * term * binder * binder * term) 
  | ListLiteral of term Prims.list 
  | SeqLiteral of term Prims.list 
and term =
  {
  tm: term' ;
  range: FStarC_Compiler_Range_Type.range ;
  level: level }
and calc_step =
  | CalcStep of (term * term * term) 
and binder' =
  | Variable of FStarC_Ident.ident 
  | TVariable of FStarC_Ident.ident 
  | Annotated of (FStarC_Ident.ident * term) 
  | TAnnotated of (FStarC_Ident.ident * term) 
  | NoName of term 
and binder =
  {
  b: binder' ;
  brange: FStarC_Compiler_Range_Type.range ;
  blevel: level ;
  aqual: arg_qualifier FStar_Pervasives_Native.option ;
  battributes: term Prims.list }
and pattern' =
  | PatWild of (arg_qualifier FStar_Pervasives_Native.option * term
  Prims.list) 
  | PatConst of FStarC_Const.sconst 
  | PatApp of (pattern * pattern Prims.list) 
  | PatVar of (FStarC_Ident.ident * arg_qualifier
  FStar_Pervasives_Native.option * term Prims.list) 
  | PatName of FStarC_Ident.lid 
  | PatTvar of (FStarC_Ident.ident * arg_qualifier
  FStar_Pervasives_Native.option * term Prims.list) 
  | PatList of pattern Prims.list 
  | PatTuple of (pattern Prims.list * Prims.bool) 
  | PatRecord of (FStarC_Ident.lid * pattern) Prims.list 
  | PatAscribed of (pattern * (term * term FStar_Pervasives_Native.option)) 
  | PatOr of pattern Prims.list 
  | PatOp of FStarC_Ident.ident 
  | PatVQuote of term 
and pattern = {
  pat: pattern' ;
  prange: FStarC_Compiler_Range_Type.range }
and arg_qualifier =
  | Implicit 
  | Equality 
  | Meta of term 
  | TypeClassArg 
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
let (__proj__Const__item___0 : term' -> FStarC_Const.sconst) =
  fun projectee -> match projectee with | Const _0 -> _0
let (uu___is_Op : term' -> Prims.bool) =
  fun projectee -> match projectee with | Op _0 -> true | uu___ -> false
let (__proj__Op__item___0 : term' -> (FStarC_Ident.ident * term Prims.list))
  = fun projectee -> match projectee with | Op _0 -> _0
let (uu___is_Tvar : term' -> Prims.bool) =
  fun projectee -> match projectee with | Tvar _0 -> true | uu___ -> false
let (__proj__Tvar__item___0 : term' -> FStarC_Ident.ident) =
  fun projectee -> match projectee with | Tvar _0 -> _0
let (uu___is_Uvar : term' -> Prims.bool) =
  fun projectee -> match projectee with | Uvar _0 -> true | uu___ -> false
let (__proj__Uvar__item___0 : term' -> FStarC_Ident.ident) =
  fun projectee -> match projectee with | Uvar _0 -> _0
let (uu___is_Var : term' -> Prims.bool) =
  fun projectee -> match projectee with | Var _0 -> true | uu___ -> false
let (__proj__Var__item___0 : term' -> FStarC_Ident.lid) =
  fun projectee -> match projectee with | Var _0 -> _0
let (uu___is_Name : term' -> Prims.bool) =
  fun projectee -> match projectee with | Name _0 -> true | uu___ -> false
let (__proj__Name__item___0 : term' -> FStarC_Ident.lid) =
  fun projectee -> match projectee with | Name _0 -> _0
let (uu___is_Projector : term' -> Prims.bool) =
  fun projectee ->
    match projectee with | Projector _0 -> true | uu___ -> false
let (__proj__Projector__item___0 :
  term' -> (FStarC_Ident.lid * FStarC_Ident.ident)) =
  fun projectee -> match projectee with | Projector _0 -> _0
let (uu___is_Construct : term' -> Prims.bool) =
  fun projectee ->
    match projectee with | Construct _0 -> true | uu___ -> false
let (__proj__Construct__item___0 :
  term' -> (FStarC_Ident.lid * (term * imp) Prims.list)) =
  fun projectee -> match projectee with | Construct _0 -> _0
let (uu___is_Abs : term' -> Prims.bool) =
  fun projectee -> match projectee with | Abs _0 -> true | uu___ -> false
let (__proj__Abs__item___0 : term' -> (pattern Prims.list * term)) =
  fun projectee -> match projectee with | Abs _0 -> _0
let (uu___is_Function : term' -> Prims.bool) =
  fun projectee ->
    match projectee with | Function _0 -> true | uu___ -> false
let (__proj__Function__item___0 :
  term' ->
    ((pattern * term FStar_Pervasives_Native.option * term) Prims.list *
      FStarC_Compiler_Range_Type.range))
  = fun projectee -> match projectee with | Function _0 -> _0
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
let (uu___is_LetOperator : term' -> Prims.bool) =
  fun projectee ->
    match projectee with | LetOperator _0 -> true | uu___ -> false
let (__proj__LetOperator__item___0 :
  term' -> ((FStarC_Ident.ident * pattern * term) Prims.list * term)) =
  fun projectee -> match projectee with | LetOperator _0 -> _0
let (uu___is_LetOpen : term' -> Prims.bool) =
  fun projectee -> match projectee with | LetOpen _0 -> true | uu___ -> false
let (__proj__LetOpen__item___0 : term' -> (FStarC_Ident.lid * term)) =
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
let (__proj__Bind__item___0 : term' -> (FStarC_Ident.ident * term * term)) =
  fun projectee -> match projectee with | Bind _0 -> _0
let (uu___is_If : term' -> Prims.bool) =
  fun projectee -> match projectee with | If _0 -> true | uu___ -> false
let (__proj__If__item___0 :
  term' ->
    (term * FStarC_Ident.ident FStar_Pervasives_Native.option *
      (FStarC_Ident.ident FStar_Pervasives_Native.option * term * Prims.bool)
      FStar_Pervasives_Native.option * term * term))
  = fun projectee -> match projectee with | If _0 -> _0
let (uu___is_Match : term' -> Prims.bool) =
  fun projectee -> match projectee with | Match _0 -> true | uu___ -> false
let (__proj__Match__item___0 :
  term' ->
    (term * FStarC_Ident.ident FStar_Pervasives_Native.option *
      (FStarC_Ident.ident FStar_Pervasives_Native.option * term * Prims.bool)
      FStar_Pervasives_Native.option * (pattern * term
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
  term' -> (term * term * term FStar_Pervasives_Native.option * Prims.bool))
  = fun projectee -> match projectee with | Ascribed _0 -> _0
let (uu___is_Record : term' -> Prims.bool) =
  fun projectee -> match projectee with | Record _0 -> true | uu___ -> false
let (__proj__Record__item___0 :
  term' ->
    (term FStar_Pervasives_Native.option * (FStarC_Ident.lid * term)
      Prims.list))
  = fun projectee -> match projectee with | Record _0 -> _0
let (uu___is_Project : term' -> Prims.bool) =
  fun projectee -> match projectee with | Project _0 -> true | uu___ -> false
let (__proj__Project__item___0 : term' -> (term * FStarC_Ident.lid)) =
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
    (binder Prims.list * (FStarC_Ident.ident Prims.list * term Prims.list
      Prims.list) * term))
  = fun projectee -> match projectee with | QForall _0 -> _0
let (uu___is_QExists : term' -> Prims.bool) =
  fun projectee -> match projectee with | QExists _0 -> true | uu___ -> false
let (__proj__QExists__item___0 :
  term' ->
    (binder Prims.list * (FStarC_Ident.ident Prims.list * term Prims.list
      Prims.list) * term))
  = fun projectee -> match projectee with | QExists _0 -> _0
let (uu___is_QuantOp : term' -> Prims.bool) =
  fun projectee -> match projectee with | QuantOp _0 -> true | uu___ -> false
let (__proj__QuantOp__item___0 :
  term' ->
    (FStarC_Ident.ident * binder Prims.list * (FStarC_Ident.ident Prims.list
      * term Prims.list Prims.list) * term))
  = fun projectee -> match projectee with | QuantOp _0 -> _0
let (uu___is_Refine : term' -> Prims.bool) =
  fun projectee -> match projectee with | Refine _0 -> true | uu___ -> false
let (__proj__Refine__item___0 : term' -> (binder * term)) =
  fun projectee -> match projectee with | Refine _0 -> _0
let (uu___is_NamedTyp : term' -> Prims.bool) =
  fun projectee ->
    match projectee with | NamedTyp _0 -> true | uu___ -> false
let (__proj__NamedTyp__item___0 : term' -> (FStarC_Ident.ident * term)) =
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
let (__proj__Discrim__item___0 : term' -> FStarC_Ident.lid) =
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
let (uu___is_IntroForall : term' -> Prims.bool) =
  fun projectee ->
    match projectee with | IntroForall _0 -> true | uu___ -> false
let (__proj__IntroForall__item___0 :
  term' -> (binder Prims.list * term * term)) =
  fun projectee -> match projectee with | IntroForall _0 -> _0
let (uu___is_IntroExists : term' -> Prims.bool) =
  fun projectee ->
    match projectee with | IntroExists _0 -> true | uu___ -> false
let (__proj__IntroExists__item___0 :
  term' -> (binder Prims.list * term * term Prims.list * term)) =
  fun projectee -> match projectee with | IntroExists _0 -> _0
let (uu___is_IntroImplies : term' -> Prims.bool) =
  fun projectee ->
    match projectee with | IntroImplies _0 -> true | uu___ -> false
let (__proj__IntroImplies__item___0 : term' -> (term * term * binder * term))
  = fun projectee -> match projectee with | IntroImplies _0 -> _0
let (uu___is_IntroOr : term' -> Prims.bool) =
  fun projectee -> match projectee with | IntroOr _0 -> true | uu___ -> false
let (__proj__IntroOr__item___0 : term' -> (Prims.bool * term * term * term))
  = fun projectee -> match projectee with | IntroOr _0 -> _0
let (uu___is_IntroAnd : term' -> Prims.bool) =
  fun projectee ->
    match projectee with | IntroAnd _0 -> true | uu___ -> false
let (__proj__IntroAnd__item___0 : term' -> (term * term * term * term)) =
  fun projectee -> match projectee with | IntroAnd _0 -> _0
let (uu___is_ElimForall : term' -> Prims.bool) =
  fun projectee ->
    match projectee with | ElimForall _0 -> true | uu___ -> false
let (__proj__ElimForall__item___0 :
  term' -> (binder Prims.list * term * term Prims.list)) =
  fun projectee -> match projectee with | ElimForall _0 -> _0
let (uu___is_ElimExists : term' -> Prims.bool) =
  fun projectee ->
    match projectee with | ElimExists _0 -> true | uu___ -> false
let (__proj__ElimExists__item___0 :
  term' -> (binder Prims.list * term * term * binder * term)) =
  fun projectee -> match projectee with | ElimExists _0 -> _0
let (uu___is_ElimImplies : term' -> Prims.bool) =
  fun projectee ->
    match projectee with | ElimImplies _0 -> true | uu___ -> false
let (__proj__ElimImplies__item___0 : term' -> (term * term * term)) =
  fun projectee -> match projectee with | ElimImplies _0 -> _0
let (uu___is_ElimOr : term' -> Prims.bool) =
  fun projectee -> match projectee with | ElimOr _0 -> true | uu___ -> false
let (__proj__ElimOr__item___0 :
  term' -> (term * term * term * binder * term * binder * term)) =
  fun projectee -> match projectee with | ElimOr _0 -> _0
let (uu___is_ElimAnd : term' -> Prims.bool) =
  fun projectee -> match projectee with | ElimAnd _0 -> true | uu___ -> false
let (__proj__ElimAnd__item___0 :
  term' -> (term * term * term * binder * binder * term)) =
  fun projectee -> match projectee with | ElimAnd _0 -> _0
let (uu___is_ListLiteral : term' -> Prims.bool) =
  fun projectee ->
    match projectee with | ListLiteral _0 -> true | uu___ -> false
let (__proj__ListLiteral__item___0 : term' -> term Prims.list) =
  fun projectee -> match projectee with | ListLiteral _0 -> _0
let (uu___is_SeqLiteral : term' -> Prims.bool) =
  fun projectee ->
    match projectee with | SeqLiteral _0 -> true | uu___ -> false
let (__proj__SeqLiteral__item___0 : term' -> term Prims.list) =
  fun projectee -> match projectee with | SeqLiteral _0 -> _0
let (__proj__Mkterm__item__tm : term -> term') =
  fun projectee ->
    match projectee with | { tm; range; level = level1;_} -> tm
let (__proj__Mkterm__item__range : term -> FStarC_Compiler_Range_Type.range)
  =
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
let (__proj__Variable__item___0 : binder' -> FStarC_Ident.ident) =
  fun projectee -> match projectee with | Variable _0 -> _0
let (uu___is_TVariable : binder' -> Prims.bool) =
  fun projectee ->
    match projectee with | TVariable _0 -> true | uu___ -> false
let (__proj__TVariable__item___0 : binder' -> FStarC_Ident.ident) =
  fun projectee -> match projectee with | TVariable _0 -> _0
let (uu___is_Annotated : binder' -> Prims.bool) =
  fun projectee ->
    match projectee with | Annotated _0 -> true | uu___ -> false
let (__proj__Annotated__item___0 : binder' -> (FStarC_Ident.ident * term)) =
  fun projectee -> match projectee with | Annotated _0 -> _0
let (uu___is_TAnnotated : binder' -> Prims.bool) =
  fun projectee ->
    match projectee with | TAnnotated _0 -> true | uu___ -> false
let (__proj__TAnnotated__item___0 : binder' -> (FStarC_Ident.ident * term)) =
  fun projectee -> match projectee with | TAnnotated _0 -> _0
let (uu___is_NoName : binder' -> Prims.bool) =
  fun projectee -> match projectee with | NoName _0 -> true | uu___ -> false
let (__proj__NoName__item___0 : binder' -> term) =
  fun projectee -> match projectee with | NoName _0 -> _0
let (__proj__Mkbinder__item__b : binder -> binder') =
  fun projectee ->
    match projectee with | { b; brange; blevel; aqual; battributes;_} -> b
let (__proj__Mkbinder__item__brange :
  binder -> FStarC_Compiler_Range_Type.range) =
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
let (__proj__PatConst__item___0 : pattern' -> FStarC_Const.sconst) =
  fun projectee -> match projectee with | PatConst _0 -> _0
let (uu___is_PatApp : pattern' -> Prims.bool) =
  fun projectee -> match projectee with | PatApp _0 -> true | uu___ -> false
let (__proj__PatApp__item___0 : pattern' -> (pattern * pattern Prims.list)) =
  fun projectee -> match projectee with | PatApp _0 -> _0
let (uu___is_PatVar : pattern' -> Prims.bool) =
  fun projectee -> match projectee with | PatVar _0 -> true | uu___ -> false
let (__proj__PatVar__item___0 :
  pattern' ->
    (FStarC_Ident.ident * arg_qualifier FStar_Pervasives_Native.option * term
      Prims.list))
  = fun projectee -> match projectee with | PatVar _0 -> _0
let (uu___is_PatName : pattern' -> Prims.bool) =
  fun projectee -> match projectee with | PatName _0 -> true | uu___ -> false
let (__proj__PatName__item___0 : pattern' -> FStarC_Ident.lid) =
  fun projectee -> match projectee with | PatName _0 -> _0
let (uu___is_PatTvar : pattern' -> Prims.bool) =
  fun projectee -> match projectee with | PatTvar _0 -> true | uu___ -> false
let (__proj__PatTvar__item___0 :
  pattern' ->
    (FStarC_Ident.ident * arg_qualifier FStar_Pervasives_Native.option * term
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
  pattern' -> (FStarC_Ident.lid * pattern) Prims.list) =
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
let (__proj__PatOp__item___0 : pattern' -> FStarC_Ident.ident) =
  fun projectee -> match projectee with | PatOp _0 -> _0
let (uu___is_PatVQuote : pattern' -> Prims.bool) =
  fun projectee ->
    match projectee with | PatVQuote _0 -> true | uu___ -> false
let (__proj__PatVQuote__item___0 : pattern' -> term) =
  fun projectee -> match projectee with | PatVQuote _0 -> _0
let (__proj__Mkpattern__item__pat : pattern -> pattern') =
  fun projectee -> match projectee with | { pat; prange;_} -> pat
let (__proj__Mkpattern__item__prange :
  pattern -> FStarC_Compiler_Range_Type.range) =
  fun projectee -> match projectee with | { pat; prange;_} -> prange
let (uu___is_Implicit : arg_qualifier -> Prims.bool) =
  fun projectee -> match projectee with | Implicit -> true | uu___ -> false
let (uu___is_Equality : arg_qualifier -> Prims.bool) =
  fun projectee -> match projectee with | Equality -> true | uu___ -> false
let (uu___is_Meta : arg_qualifier -> Prims.bool) =
  fun projectee -> match projectee with | Meta _0 -> true | uu___ -> false
let (__proj__Meta__item___0 : arg_qualifier -> term) =
  fun projectee -> match projectee with | Meta _0 -> _0
let (uu___is_TypeClassArg : arg_qualifier -> Prims.bool) =
  fun projectee ->
    match projectee with | TypeClassArg -> true | uu___ -> false
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
type match_returns_annotation =
  (FStarC_Ident.ident FStar_Pervasives_Native.option * term * Prims.bool)
type patterns = (FStarC_Ident.ident Prims.list * term Prims.list Prims.list)
type attributes_ = term Prims.list
type branch = (pattern * term FStar_Pervasives_Native.option * term)
type aqual = arg_qualifier FStar_Pervasives_Native.option
let (hasRange_term : term FStarC_Class_HasRange.hasRange) =
  {
    FStarC_Class_HasRange.pos = (fun t -> t.range);
    FStarC_Class_HasRange.setPos =
      (fun r -> fun t -> { tm = (t.tm); range = r; level = (t.level) })
  }
let (hasRange_pattern : pattern FStarC_Class_HasRange.hasRange) =
  {
    FStarC_Class_HasRange.pos = (fun p -> p.prange);
    FStarC_Class_HasRange.setPos =
      (fun r -> fun p -> { pat = (p.pat); prange = r })
  }
let (hasRange_binder : binder FStarC_Class_HasRange.hasRange) =
  {
    FStarC_Class_HasRange.pos = (fun b -> b.brange);
    FStarC_Class_HasRange.setPos =
      (fun r ->
         fun b ->
           {
             b = (b.b);
             brange = r;
             blevel = (b.blevel);
             aqual = (b.aqual);
             battributes = (b.battributes)
           })
  }
type knd = term
type typ = term
type expr = term
type tycon_record =
  (FStarC_Ident.ident * aqual * attributes_ * term) Prims.list
type constructor_payload =
  | VpOfNotation of typ 
  | VpArbitrary of typ 
  | VpRecord of (tycon_record * typ FStar_Pervasives_Native.option) 
let (uu___is_VpOfNotation : constructor_payload -> Prims.bool) =
  fun projectee ->
    match projectee with | VpOfNotation _0 -> true | uu___ -> false
let (__proj__VpOfNotation__item___0 : constructor_payload -> typ) =
  fun projectee -> match projectee with | VpOfNotation _0 -> _0
let (uu___is_VpArbitrary : constructor_payload -> Prims.bool) =
  fun projectee ->
    match projectee with | VpArbitrary _0 -> true | uu___ -> false
let (__proj__VpArbitrary__item___0 : constructor_payload -> typ) =
  fun projectee -> match projectee with | VpArbitrary _0 -> _0
let (uu___is_VpRecord : constructor_payload -> Prims.bool) =
  fun projectee ->
    match projectee with | VpRecord _0 -> true | uu___ -> false
let (__proj__VpRecord__item___0 :
  constructor_payload -> (tycon_record * typ FStar_Pervasives_Native.option))
  = fun projectee -> match projectee with | VpRecord _0 -> _0
type tycon =
  | TyconAbstract of (FStarC_Ident.ident * binder Prims.list * knd
  FStar_Pervasives_Native.option) 
  | TyconAbbrev of (FStarC_Ident.ident * binder Prims.list * knd
  FStar_Pervasives_Native.option * term) 
  | TyconRecord of (FStarC_Ident.ident * binder Prims.list * knd
  FStar_Pervasives_Native.option * attributes_ * tycon_record) 
  | TyconVariant of (FStarC_Ident.ident * binder Prims.list * knd
  FStar_Pervasives_Native.option * (FStarC_Ident.ident * constructor_payload
  FStar_Pervasives_Native.option * attributes_) Prims.list) 
let (uu___is_TyconAbstract : tycon -> Prims.bool) =
  fun projectee ->
    match projectee with | TyconAbstract _0 -> true | uu___ -> false
let (__proj__TyconAbstract__item___0 :
  tycon ->
    (FStarC_Ident.ident * binder Prims.list * knd
      FStar_Pervasives_Native.option))
  = fun projectee -> match projectee with | TyconAbstract _0 -> _0
let (uu___is_TyconAbbrev : tycon -> Prims.bool) =
  fun projectee ->
    match projectee with | TyconAbbrev _0 -> true | uu___ -> false
let (__proj__TyconAbbrev__item___0 :
  tycon ->
    (FStarC_Ident.ident * binder Prims.list * knd
      FStar_Pervasives_Native.option * term))
  = fun projectee -> match projectee with | TyconAbbrev _0 -> _0
let (uu___is_TyconRecord : tycon -> Prims.bool) =
  fun projectee ->
    match projectee with | TyconRecord _0 -> true | uu___ -> false
let (__proj__TyconRecord__item___0 :
  tycon ->
    (FStarC_Ident.ident * binder Prims.list * knd
      FStar_Pervasives_Native.option * attributes_ * tycon_record))
  = fun projectee -> match projectee with | TyconRecord _0 -> _0
let (uu___is_TyconVariant : tycon -> Prims.bool) =
  fun projectee ->
    match projectee with | TyconVariant _0 -> true | uu___ -> false
let (__proj__TyconVariant__item___0 :
  tycon ->
    (FStarC_Ident.ident * binder Prims.list * knd
      FStar_Pervasives_Native.option * (FStarC_Ident.ident *
      constructor_payload FStar_Pervasives_Native.option * attributes_)
      Prims.list))
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
  msource: FStarC_Ident.lid ;
  mdest: FStarC_Ident.lid ;
  lift_op: lift_op ;
  braced: Prims.bool }
let (__proj__Mklift__item__msource : lift -> FStarC_Ident.lid) =
  fun projectee ->
    match projectee with
    | { msource; mdest; lift_op = lift_op1; braced;_} -> msource
let (__proj__Mklift__item__mdest : lift -> FStarC_Ident.lid) =
  fun projectee ->
    match projectee with
    | { msource; mdest; lift_op = lift_op1; braced;_} -> mdest
let (__proj__Mklift__item__lift_op : lift -> lift_op) =
  fun projectee ->
    match projectee with
    | { msource; mdest; lift_op = lift_op1; braced;_} -> lift_op1
let (__proj__Mklift__item__braced : lift -> Prims.bool) =
  fun projectee ->
    match projectee with
    | { msource; mdest; lift_op = lift_op1; braced;_} -> braced
type pragma =
  | ShowOptions 
  | SetOptions of Prims.string 
  | ResetOptions of Prims.string FStar_Pervasives_Native.option 
  | PushOptions of Prims.string FStar_Pervasives_Native.option 
  | PopOptions 
  | RestartSolver 
  | PrintEffectsGraph 
let (uu___is_ShowOptions : pragma -> Prims.bool) =
  fun projectee ->
    match projectee with | ShowOptions -> true | uu___ -> false
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
let (uu___is_PrintEffectsGraph : pragma -> Prims.bool) =
  fun projectee ->
    match projectee with | PrintEffectsGraph -> true | uu___ -> false
type dep_scan_callbacks =
  {
  scan_term: term -> unit ;
  scan_binder: binder -> unit ;
  scan_pattern: pattern -> unit ;
  add_lident: FStarC_Ident.lident -> unit ;
  add_open: FStarC_Ident.lident -> unit }
let (__proj__Mkdep_scan_callbacks__item__scan_term :
  dep_scan_callbacks -> term -> unit) =
  fun projectee ->
    match projectee with
    | { scan_term; scan_binder; scan_pattern; add_lident; add_open;_} ->
        scan_term
let (__proj__Mkdep_scan_callbacks__item__scan_binder :
  dep_scan_callbacks -> binder -> unit) =
  fun projectee ->
    match projectee with
    | { scan_term; scan_binder; scan_pattern; add_lident; add_open;_} ->
        scan_binder
let (__proj__Mkdep_scan_callbacks__item__scan_pattern :
  dep_scan_callbacks -> pattern -> unit) =
  fun projectee ->
    match projectee with
    | { scan_term; scan_binder; scan_pattern; add_lident; add_open;_} ->
        scan_pattern
let (__proj__Mkdep_scan_callbacks__item__add_lident :
  dep_scan_callbacks -> FStarC_Ident.lident -> unit) =
  fun projectee ->
    match projectee with
    | { scan_term; scan_binder; scan_pattern; add_lident; add_open;_} ->
        add_lident
let (__proj__Mkdep_scan_callbacks__item__add_open :
  dep_scan_callbacks -> FStarC_Ident.lident -> unit) =
  fun projectee ->
    match projectee with
    | { scan_term; scan_binder; scan_pattern; add_lident; add_open;_} ->
        add_open
type to_be_desugared =
  {
  lang_name: Prims.string ;
  blob: FStarC_Dyn.dyn ;
  idents: FStarC_Ident.ident Prims.list ;
  to_string: FStarC_Dyn.dyn -> Prims.string ;
  eq: FStarC_Dyn.dyn -> FStarC_Dyn.dyn -> Prims.bool ;
  dep_scan: dep_scan_callbacks -> FStarC_Dyn.dyn -> unit }
let (__proj__Mkto_be_desugared__item__lang_name :
  to_be_desugared -> Prims.string) =
  fun projectee ->
    match projectee with
    | { lang_name; blob; idents; to_string; eq; dep_scan;_} -> lang_name
let (__proj__Mkto_be_desugared__item__blob :
  to_be_desugared -> FStarC_Dyn.dyn) =
  fun projectee ->
    match projectee with
    | { lang_name; blob; idents; to_string; eq; dep_scan;_} -> blob
let (__proj__Mkto_be_desugared__item__idents :
  to_be_desugared -> FStarC_Ident.ident Prims.list) =
  fun projectee ->
    match projectee with
    | { lang_name; blob; idents; to_string; eq; dep_scan;_} -> idents
let (__proj__Mkto_be_desugared__item__to_string :
  to_be_desugared -> FStarC_Dyn.dyn -> Prims.string) =
  fun projectee ->
    match projectee with
    | { lang_name; blob; idents; to_string; eq; dep_scan;_} -> to_string
let (__proj__Mkto_be_desugared__item__eq :
  to_be_desugared -> FStarC_Dyn.dyn -> FStarC_Dyn.dyn -> Prims.bool) =
  fun projectee ->
    match projectee with
    | { lang_name; blob; idents; to_string; eq; dep_scan;_} -> eq
let (__proj__Mkto_be_desugared__item__dep_scan :
  to_be_desugared -> dep_scan_callbacks -> FStarC_Dyn.dyn -> unit) =
  fun projectee ->
    match projectee with
    | { lang_name; blob; idents; to_string; eq; dep_scan;_} -> dep_scan
type decl' =
  | TopLevelModule of FStarC_Ident.lid 
  | Open of (FStarC_Ident.lid * FStarC_Syntax_Syntax.restriction) 
  | Friend of FStarC_Ident.lid 
  | Include of (FStarC_Ident.lid * FStarC_Syntax_Syntax.restriction) 
  | ModuleAbbrev of (FStarC_Ident.ident * FStarC_Ident.lid) 
  | TopLevelLet of (let_qualifier * (pattern * term) Prims.list) 
  | Tycon of (Prims.bool * Prims.bool * tycon Prims.list) 
  | Val of (FStarC_Ident.ident * term) 
  | Exception of (FStarC_Ident.ident * term FStar_Pervasives_Native.option) 
  | NewEffect of effect_decl 
  | LayeredEffect of effect_decl 
  | SubEffect of lift 
  | Polymonadic_bind of (FStarC_Ident.lid * FStarC_Ident.lid *
  FStarC_Ident.lid * term) 
  | Polymonadic_subcomp of (FStarC_Ident.lid * FStarC_Ident.lid * term) 
  | Pragma of pragma 
  | Assume of (FStarC_Ident.ident * term) 
  | Splice of (Prims.bool * FStarC_Ident.ident Prims.list * term) 
  | DeclSyntaxExtension of (Prims.string * Prims.string *
  FStarC_Compiler_Range_Type.range * FStarC_Compiler_Range_Type.range) 
  | UseLangDecls of Prims.string 
  | DeclToBeDesugared of to_be_desugared 
  | Unparseable 
and decl =
  {
  d: decl' ;
  drange: FStarC_Compiler_Range_Type.range ;
  quals: qualifiers ;
  attrs: attributes_ ;
  interleaved: Prims.bool }
and effect_decl =
  | DefineEffect of (FStarC_Ident.ident * binder Prims.list * term * decl
  Prims.list) 
  | RedefineEffect of (FStarC_Ident.ident * binder Prims.list * term) 
let (uu___is_TopLevelModule : decl' -> Prims.bool) =
  fun projectee ->
    match projectee with | TopLevelModule _0 -> true | uu___ -> false
let (__proj__TopLevelModule__item___0 : decl' -> FStarC_Ident.lid) =
  fun projectee -> match projectee with | TopLevelModule _0 -> _0
let (uu___is_Open : decl' -> Prims.bool) =
  fun projectee -> match projectee with | Open _0 -> true | uu___ -> false
let (__proj__Open__item___0 :
  decl' -> (FStarC_Ident.lid * FStarC_Syntax_Syntax.restriction)) =
  fun projectee -> match projectee with | Open _0 -> _0
let (uu___is_Friend : decl' -> Prims.bool) =
  fun projectee -> match projectee with | Friend _0 -> true | uu___ -> false
let (__proj__Friend__item___0 : decl' -> FStarC_Ident.lid) =
  fun projectee -> match projectee with | Friend _0 -> _0
let (uu___is_Include : decl' -> Prims.bool) =
  fun projectee -> match projectee with | Include _0 -> true | uu___ -> false
let (__proj__Include__item___0 :
  decl' -> (FStarC_Ident.lid * FStarC_Syntax_Syntax.restriction)) =
  fun projectee -> match projectee with | Include _0 -> _0
let (uu___is_ModuleAbbrev : decl' -> Prims.bool) =
  fun projectee ->
    match projectee with | ModuleAbbrev _0 -> true | uu___ -> false
let (__proj__ModuleAbbrev__item___0 :
  decl' -> (FStarC_Ident.ident * FStarC_Ident.lid)) =
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
let (__proj__Val__item___0 : decl' -> (FStarC_Ident.ident * term)) =
  fun projectee -> match projectee with | Val _0 -> _0
let (uu___is_Exception : decl' -> Prims.bool) =
  fun projectee ->
    match projectee with | Exception _0 -> true | uu___ -> false
let (__proj__Exception__item___0 :
  decl' -> (FStarC_Ident.ident * term FStar_Pervasives_Native.option)) =
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
  decl' -> (FStarC_Ident.lid * FStarC_Ident.lid * FStarC_Ident.lid * term)) =
  fun projectee -> match projectee with | Polymonadic_bind _0 -> _0
let (uu___is_Polymonadic_subcomp : decl' -> Prims.bool) =
  fun projectee ->
    match projectee with | Polymonadic_subcomp _0 -> true | uu___ -> false
let (__proj__Polymonadic_subcomp__item___0 :
  decl' -> (FStarC_Ident.lid * FStarC_Ident.lid * term)) =
  fun projectee -> match projectee with | Polymonadic_subcomp _0 -> _0
let (uu___is_Pragma : decl' -> Prims.bool) =
  fun projectee -> match projectee with | Pragma _0 -> true | uu___ -> false
let (__proj__Pragma__item___0 : decl' -> pragma) =
  fun projectee -> match projectee with | Pragma _0 -> _0
let (uu___is_Assume : decl' -> Prims.bool) =
  fun projectee -> match projectee with | Assume _0 -> true | uu___ -> false
let (__proj__Assume__item___0 : decl' -> (FStarC_Ident.ident * term)) =
  fun projectee -> match projectee with | Assume _0 -> _0
let (uu___is_Splice : decl' -> Prims.bool) =
  fun projectee -> match projectee with | Splice _0 -> true | uu___ -> false
let (__proj__Splice__item___0 :
  decl' -> (Prims.bool * FStarC_Ident.ident Prims.list * term)) =
  fun projectee -> match projectee with | Splice _0 -> _0
let (uu___is_DeclSyntaxExtension : decl' -> Prims.bool) =
  fun projectee ->
    match projectee with | DeclSyntaxExtension _0 -> true | uu___ -> false
let (__proj__DeclSyntaxExtension__item___0 :
  decl' ->
    (Prims.string * Prims.string * FStarC_Compiler_Range_Type.range *
      FStarC_Compiler_Range_Type.range))
  = fun projectee -> match projectee with | DeclSyntaxExtension _0 -> _0
let (uu___is_UseLangDecls : decl' -> Prims.bool) =
  fun projectee ->
    match projectee with | UseLangDecls _0 -> true | uu___ -> false
let (__proj__UseLangDecls__item___0 : decl' -> Prims.string) =
  fun projectee -> match projectee with | UseLangDecls _0 -> _0
let (uu___is_DeclToBeDesugared : decl' -> Prims.bool) =
  fun projectee ->
    match projectee with | DeclToBeDesugared _0 -> true | uu___ -> false
let (__proj__DeclToBeDesugared__item___0 : decl' -> to_be_desugared) =
  fun projectee -> match projectee with | DeclToBeDesugared _0 -> _0
let (uu___is_Unparseable : decl' -> Prims.bool) =
  fun projectee ->
    match projectee with | Unparseable -> true | uu___ -> false
let (__proj__Mkdecl__item__d : decl -> decl') =
  fun projectee ->
    match projectee with | { d; drange; quals; attrs; interleaved;_} -> d
let (__proj__Mkdecl__item__drange : decl -> FStarC_Compiler_Range_Type.range)
  =
  fun projectee ->
    match projectee with
    | { d; drange; quals; attrs; interleaved;_} -> drange
let (__proj__Mkdecl__item__quals : decl -> qualifiers) =
  fun projectee ->
    match projectee with | { d; drange; quals; attrs; interleaved;_} -> quals
let (__proj__Mkdecl__item__attrs : decl -> attributes_) =
  fun projectee ->
    match projectee with | { d; drange; quals; attrs; interleaved;_} -> attrs
let (__proj__Mkdecl__item__interleaved : decl -> Prims.bool) =
  fun projectee ->
    match projectee with
    | { d; drange; quals; attrs; interleaved;_} -> interleaved
let (uu___is_DefineEffect : effect_decl -> Prims.bool) =
  fun projectee ->
    match projectee with | DefineEffect _0 -> true | uu___ -> false
let (__proj__DefineEffect__item___0 :
  effect_decl ->
    (FStarC_Ident.ident * binder Prims.list * term * decl Prims.list))
  = fun projectee -> match projectee with | DefineEffect _0 -> _0
let (uu___is_RedefineEffect : effect_decl -> Prims.bool) =
  fun projectee ->
    match projectee with | RedefineEffect _0 -> true | uu___ -> false
let (__proj__RedefineEffect__item___0 :
  effect_decl -> (FStarC_Ident.ident * binder Prims.list * term)) =
  fun projectee -> match projectee with | RedefineEffect _0 -> _0
let (hasRange_decl : decl FStarC_Class_HasRange.hasRange) =
  {
    FStarC_Class_HasRange.pos = (fun d -> d.drange);
    FStarC_Class_HasRange.setPos =
      (fun r ->
         fun d ->
           {
             d = (d.d);
             drange = r;
             quals = (d.quals);
             attrs = (d.attrs);
             interleaved = (d.interleaved)
           })
  }
type modul =
  | Module of (FStarC_Ident.lid * decl Prims.list) 
  | Interface of (FStarC_Ident.lid * decl Prims.list * Prims.bool) 
let (uu___is_Module : modul -> Prims.bool) =
  fun projectee -> match projectee with | Module _0 -> true | uu___ -> false
let (__proj__Module__item___0 :
  modul -> (FStarC_Ident.lid * decl Prims.list)) =
  fun projectee -> match projectee with | Module _0 -> _0
let (uu___is_Interface : modul -> Prims.bool) =
  fun projectee ->
    match projectee with | Interface _0 -> true | uu___ -> false
let (__proj__Interface__item___0 :
  modul -> (FStarC_Ident.lid * decl Prims.list * Prims.bool)) =
  fun projectee -> match projectee with | Interface _0 -> _0
type file = modul
type inputFragment = (file, decl Prims.list) FStar_Pervasives.either
let (lid_of_modul : modul -> FStarC_Ident.lid) =
  fun m ->
    match m with
    | Module (lid, uu___) -> lid
    | Interface (lid, uu___, uu___1) -> lid
let (check_id : FStarC_Ident.ident -> unit) =
  fun id ->
    let first_char =
      let uu___ = FStarC_Ident.string_of_id id in
      FStarC_Compiler_String.substring uu___ Prims.int_zero Prims.int_one in
    if
      Prims.op_Negation
        ((FStarC_Compiler_String.lowercase first_char) = first_char)
    then
      let uu___ =
        let uu___1 = FStarC_Class_Show.show FStarC_Ident.showable_ident id in
        FStarC_Compiler_Util.format1
          "Invalid identifer '%s'; expected a symbol that begins with a lower-case character"
          uu___1 in
      FStarC_Errors.raise_error FStarC_Ident.hasrange_ident id
        FStarC_Errors_Codes.Fatal_InvalidIdentifier ()
        (Obj.magic FStarC_Errors_Msg.is_error_message_string)
        (Obj.magic uu___)
    else ()
let at_most_one :
  'uuuuu .
    Prims.string ->
      FStarC_Compiler_Range_Type.range ->
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
              FStarC_Compiler_Util.format1
                "At most one %s is allowed on declarations" s in
            FStarC_Errors.raise_error FStarC_Class_HasRange.hasRange_range r
              FStarC_Errors_Codes.Fatal_MoreThanOneDeclaration ()
              (Obj.magic FStarC_Errors_Msg.is_error_message_string)
              (Obj.magic uu___1)
let (mk_binder_with_attrs :
  binder' ->
    FStarC_Compiler_Range_Type.range ->
      level -> aqual -> term Prims.list -> binder)
  =
  fun b ->
    fun r ->
      fun l ->
        fun i ->
          fun attrs ->
            { b; brange = r; blevel = l; aqual = i; battributes = attrs }
let (mk_binder :
  binder' -> FStarC_Compiler_Range_Type.range -> level -> aqual -> binder) =
  fun b -> fun r -> fun l -> fun i -> mk_binder_with_attrs b r l i []
let (mk_term : term' -> FStarC_Compiler_Range_Type.range -> level -> term) =
  fun t -> fun r -> fun l -> { tm = t; range = r; level = l }
let (mk_uminus :
  term ->
    FStarC_Compiler_Range_Type.range ->
      FStarC_Compiler_Range_Type.range -> level -> term)
  =
  fun t ->
    fun rminus ->
      fun r ->
        fun l ->
          let t1 =
            match t.tm with
            | Const (FStarC_Const.Const_int
                (s, FStar_Pervasives_Native.Some
                 (FStarC_Const.Signed, width)))
                ->
                Const
                  (FStarC_Const.Const_int
                     ((Prims.strcat "-" s),
                       (FStar_Pervasives_Native.Some
                          (FStarC_Const.Signed, width))))
            | uu___ ->
                let uu___1 =
                  let uu___2 = FStarC_Ident.mk_ident ("-", rminus) in
                  (uu___2, [t]) in
                Op uu___1 in
          mk_term t1 r l
let (mk_pattern : pattern' -> FStarC_Compiler_Range_Type.range -> pattern) =
  fun p -> fun r -> { pat = p; prange = r }
let (un_curry_abs : pattern Prims.list -> term -> term') =
  fun ps ->
    fun body ->
      match body.tm with
      | Abs (p', body') -> Abs ((FStarC_Compiler_List.op_At ps p'), body')
      | uu___ -> Abs (ps, body)
let (mk_function :
  branch Prims.list ->
    FStarC_Compiler_Range_Type.range ->
      FStarC_Compiler_Range_Type.range -> term)
  =
  fun branches ->
    fun r1 -> fun r2 -> mk_term (Function (branches, r1)) r2 Expr
let (un_function :
  pattern -> term -> (pattern * term) FStar_Pervasives_Native.option) =
  fun p ->
    fun tm ->
      match ((p.pat), (tm.tm)) with
      | (PatVar uu___, Abs (pats, body)) ->
          let uu___1 =
            let uu___2 = mk_pattern (PatApp (p, pats)) p.prange in
            (uu___2, body) in
          FStar_Pervasives_Native.Some uu___1
      | uu___ -> FStar_Pervasives_Native.None
let (mkApp :
  term -> (term * imp) Prims.list -> FStarC_Compiler_Range_Type.range -> term)
  =
  fun t ->
    fun args ->
      fun r ->
        match args with
        | [] -> t
        | uu___ ->
            (match t.tm with
             | Name s -> mk_term (Construct (s, args)) r Un
             | uu___1 ->
                 FStarC_Compiler_List.fold_left
                   (fun t1 ->
                      fun uu___2 ->
                        match uu___2 with
                        | (a, imp1) -> mk_term (App (t1, a, imp1)) r Un) t
                   args)
let (consPat :
  FStarC_Compiler_Range_Type.range -> pattern -> pattern -> pattern') =
  fun r ->
    fun hd ->
      fun tl ->
        let uu___ =
          let uu___1 = mk_pattern (PatName FStarC_Parser_Const.cons_lid) r in
          (uu___1, [hd; tl]) in
        PatApp uu___
let (consTerm : FStarC_Compiler_Range_Type.range -> term -> term -> term) =
  fun r ->
    fun hd ->
      fun tl ->
        mk_term
          (Construct
             (FStarC_Parser_Const.cons_lid, [(hd, Nothing); (tl, Nothing)]))
          r Expr
let (mkListLit : FStarC_Compiler_Range_Type.range -> term Prims.list -> term)
  = fun r -> fun elts -> mk_term (ListLiteral elts) r Expr
let (mkSeqLit : FStarC_Compiler_Range_Type.range -> term Prims.list -> term)
  = fun r -> fun elts -> mk_term (SeqLiteral elts) r Expr
let (unit_const : FStarC_Compiler_Range_Type.range -> term) =
  fun r -> mk_term (Const FStarC_Const.Const_unit) r Expr
let (ml_comp : term -> term) =
  fun t ->
    let lid = FStarC_Parser_Const.effect_ML_lid () in
    let ml = mk_term (Name lid) t.range Expr in
    let t1 = mk_term (App (ml, t, Nothing)) t.range Expr in t1
let (tot_comp : term -> term) =
  fun t ->
    let ml = mk_term (Name FStarC_Parser_Const.effect_Tot_lid) t.range Expr in
    let t1 = mk_term (App (ml, t, Nothing)) t.range Expr in t1
let (mkRefSet : FStarC_Compiler_Range_Type.range -> term Prims.list -> term)
  =
  fun r ->
    fun elts ->
      let uu___ =
        (FStarC_Parser_Const.set_empty, FStarC_Parser_Const.set_singleton,
          FStarC_Parser_Const.set_union,
          FStarC_Parser_Const.heap_addr_of_lid) in
      match uu___ with
      | (empty_lid, singleton_lid, union_lid, addr_of_lid) ->
          let empty =
            let uu___1 =
              let uu___2 = FStarC_Ident.set_lid_range empty_lid r in
              Var uu___2 in
            mk_term uu___1 r Expr in
          let addr_of =
            let uu___1 =
              let uu___2 = FStarC_Ident.set_lid_range addr_of_lid r in
              Var uu___2 in
            mk_term uu___1 r Expr in
          let singleton =
            let uu___1 =
              let uu___2 = FStarC_Ident.set_lid_range singleton_lid r in
              Var uu___2 in
            mk_term uu___1 r Expr in
          let union =
            let uu___1 =
              let uu___2 = FStarC_Ident.set_lid_range union_lid r in
              Var uu___2 in
            mk_term uu___1 r Expr in
          FStarC_Compiler_List.fold_right
            (fun e ->
               fun tl ->
                 let e1 = mkApp addr_of [(e, Nothing)] r in
                 let single_e = mkApp singleton [(e1, Nothing)] r in
                 mkApp union [(single_e, Nothing); (tl, Nothing)] r) elts
            empty
let (mkExplicitApp :
  term -> term Prims.list -> FStarC_Compiler_Range_Type.range -> term) =
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
                     let uu___3 =
                       FStarC_Compiler_List.map (fun a -> (a, Nothing)) args in
                     (s, uu___3) in
                   Construct uu___2 in
                 mk_term uu___1 r Un
             | uu___1 ->
                 FStarC_Compiler_List.fold_left
                   (fun t1 -> fun a -> mk_term (App (t1, a, Nothing)) r Un) t
                   args)
let (mkAdmitMagic : FStarC_Compiler_Range_Type.range -> term) =
  fun r ->
    let admit =
      let admit_name =
        let uu___ =
          let uu___1 =
            FStarC_Ident.set_lid_range FStarC_Parser_Const.admit_lid r in
          Var uu___1 in
        mk_term uu___ r Expr in
      let uu___ = let uu___1 = unit_const r in [uu___1] in
      mkExplicitApp admit_name uu___ r in
    let magic =
      let magic_name =
        let uu___ =
          let uu___1 =
            FStarC_Ident.set_lid_range FStarC_Parser_Const.magic_lid r in
          Var uu___1 in
        mk_term uu___ r Expr in
      let uu___ = let uu___1 = unit_const r in [uu___1] in
      mkExplicitApp magic_name uu___ r in
    let admit_magic = mk_term (Seq (admit, magic)) r Expr in admit_magic
let mkWildAdmitMagic :
  'uuuuu .
    FStarC_Compiler_Range_Type.range ->
      (pattern * 'uuuuu FStar_Pervasives_Native.option * term)
  =
  fun r ->
    let uu___ = mk_pattern (PatWild (FStar_Pervasives_Native.None, [])) r in
    let uu___1 = mkAdmitMagic r in
    (uu___, FStar_Pervasives_Native.None, uu___1)
let focusBranches :
  'uuuuu .
    (Prims.bool * (pattern * 'uuuuu FStar_Pervasives_Native.option * term))
      Prims.list ->
      FStarC_Compiler_Range_Type.range ->
        (pattern * 'uuuuu FStar_Pervasives_Native.option * term) Prims.list
  =
  fun branches ->
    fun r ->
      let should_filter =
        FStarC_Compiler_Util.for_some FStar_Pervasives_Native.fst branches in
      if should_filter
      then
        (FStarC_Errors.log_issue FStarC_Class_HasRange.hasRange_range r
           FStarC_Errors_Codes.Warning_Filtered ()
           (Obj.magic FStarC_Errors_Msg.is_error_message_string)
           (Obj.magic "Focusing on only some cases");
         (let focussed =
            let uu___1 =
              FStarC_Compiler_List.filter FStar_Pervasives_Native.fst
                branches in
            FStarC_Compiler_List.map FStar_Pervasives_Native.snd uu___1 in
          let uu___1 = let uu___2 = mkWildAdmitMagic r in [uu___2] in
          FStarC_Compiler_List.op_At focussed uu___1))
      else FStarC_Compiler_List.map FStar_Pervasives_Native.snd branches
let (focusLetBindings :
  (Prims.bool * (pattern * term)) Prims.list ->
    FStarC_Compiler_Range_Type.range -> (pattern * term) Prims.list)
  =
  fun lbs ->
    fun r ->
      let should_filter =
        FStarC_Compiler_Util.for_some FStar_Pervasives_Native.fst lbs in
      if should_filter
      then
        (FStarC_Errors.log_issue FStarC_Class_HasRange.hasRange_range r
           FStarC_Errors_Codes.Warning_Filtered ()
           (Obj.magic FStarC_Errors_Msg.is_error_message_string)
           (Obj.magic
              "Focusing on only some cases in this (mutually) recursive definition");
         FStarC_Compiler_List.map
           (fun uu___1 ->
              match uu___1 with
              | (f, lb) ->
                  if f
                  then lb
                  else
                    (let uu___3 = mkAdmitMagic r in
                     ((FStar_Pervasives_Native.fst lb), uu___3))) lbs)
      else FStarC_Compiler_List.map FStar_Pervasives_Native.snd lbs
let (focusAttrLetBindings :
  (attributes_ FStar_Pervasives_Native.option * (Prims.bool * (pattern *
    term))) Prims.list ->
    FStarC_Compiler_Range_Type.range ->
      (attributes_ FStar_Pervasives_Native.option * (pattern * term))
        Prims.list)
  =
  fun lbs ->
    fun r ->
      let should_filter =
        FStarC_Compiler_Util.for_some
          (fun uu___ -> match uu___ with | (attr, (focus, uu___1)) -> focus)
          lbs in
      if should_filter
      then
        (FStarC_Errors.log_issue FStarC_Class_HasRange.hasRange_range r
           FStarC_Errors_Codes.Warning_Filtered ()
           (Obj.magic FStarC_Errors_Msg.is_error_message_string)
           (Obj.magic
              "Focusing on only some cases in this (mutually) recursive definition");
         FStarC_Compiler_List.map
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
        FStarC_Compiler_List.map
          (fun uu___1 ->
             match uu___1 with | (attr, (uu___2, lb)) -> (attr, lb)) lbs
let (mkFsTypApp :
  term -> term Prims.list -> FStarC_Compiler_Range_Type.range -> term) =
  fun t ->
    fun args ->
      fun r ->
        let uu___ = FStarC_Compiler_List.map (fun a -> (a, FsTypApp)) args in
        mkApp t uu___ r
let (mkTuple : term Prims.list -> FStarC_Compiler_Range_Type.range -> term) =
  fun args ->
    fun r ->
      let cons =
        FStarC_Parser_Const.mk_tuple_data_lid
          (FStarC_Compiler_List.length args) r in
      let uu___ = mk_term (Name cons) r Expr in
      let uu___1 = FStarC_Compiler_List.map (fun x -> (x, Nothing)) args in
      mkApp uu___ uu___1 r
let (mkDTuple : term Prims.list -> FStarC_Compiler_Range_Type.range -> term)
  =
  fun args ->
    fun r ->
      let cons =
        FStarC_Parser_Const.mk_dtuple_data_lid
          (FStarC_Compiler_List.length args) r in
      let uu___ = mk_term (Name cons) r Expr in
      let uu___1 = FStarC_Compiler_List.map (fun x -> (x, Nothing)) args in
      mkApp uu___ uu___1 r
let (mkRefinedBinder :
  FStarC_Ident.ident ->
    term ->
      Prims.bool ->
        term FStar_Pervasives_Native.option ->
          FStarC_Compiler_Range_Type.range ->
            aqual -> term Prims.list -> binder)
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
                      let uu___ =
                        let uu___1 =
                          let uu___2 = mk_term (Refine (b, phi)) m Type_level in
                          (id, uu___2) in
                        Annotated uu___1 in
                      mk_binder_with_attrs uu___ m Type_level implicit attrs
                    else
                      (let x = FStarC_Ident.gen t.range in
                       let b1 =
                         mk_binder_with_attrs (Annotated (x, t)) m Type_level
                           implicit attrs in
                       let uu___1 =
                         let uu___2 =
                           let uu___3 =
                             mk_term (Refine (b1, phi)) m Type_level in
                           (id, uu___3) in
                         Annotated uu___2 in
                       mk_binder_with_attrs uu___1 m Type_level implicit
                         attrs)
let (mkRefinedPattern :
  pattern ->
    term ->
      Prims.bool ->
        term FStar_Pervasives_Native.option ->
          FStarC_Compiler_Range_Type.range ->
            FStarC_Compiler_Range_Type.range -> pattern)
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
                           let uu___1 =
                             let uu___2 =
                               let uu___3 =
                                 mk_binder_with_attrs (Annotated (x, t))
                                   t_range Type_level
                                   FStar_Pervasives_Native.None attrs in
                               (uu___3, phi) in
                             Refine uu___2 in
                           mk_term uu___1 range Type_level
                       | uu___ ->
                           let x = FStarC_Ident.gen t_range in
                           let phi1 =
                             let x_var =
                               let uu___1 =
                                 let uu___2 = FStarC_Ident.lid_of_ids [x] in
                                 Var uu___2 in
                               mk_term uu___1 phi.range Formula in
                             let pat_branch =
                               (pat, FStar_Pervasives_Native.None, phi) in
                             let otherwise_branch =
                               let uu___1 =
                                 mk_pattern
                                   (PatWild
                                      (FStar_Pervasives_Native.None, []))
                                   phi.range in
                               let uu___2 =
                                 let uu___3 =
                                   let uu___4 =
                                     FStarC_Ident.lid_of_path ["False"]
                                       phi.range in
                                   Name uu___4 in
                                 mk_term uu___3 phi.range Formula in
                               (uu___1, FStar_Pervasives_Native.None, uu___2) in
                             mk_term
                               (Match
                                  (x_var, FStar_Pervasives_Native.None,
                                    FStar_Pervasives_Native.None,
                                    [pat_branch; otherwise_branch]))
                               phi.range Formula in
                           let uu___1 =
                             let uu___2 =
                               let uu___3 =
                                 mk_binder (Annotated (x, t)) t_range
                                   Type_level FStar_Pervasives_Native.None in
                               (uu___3, phi1) in
                             Refine uu___2 in
                           mk_term uu___1 range Type_level)
                    else
                      (let x = FStarC_Ident.gen t.range in
                       let uu___1 =
                         let uu___2 =
                           let uu___3 =
                             mk_binder (Annotated (x, t)) t_range Type_level
                               FStar_Pervasives_Native.None in
                           (uu___3, phi) in
                         Refine uu___2 in
                       mk_term uu___1 range Type_level) in
              mk_pattern
                (PatAscribed (pat, (t1, FStar_Pervasives_Native.None))) range
let rec (extract_named_refinement :
  Prims.bool ->
    term ->
      (FStarC_Ident.ident * term * term FStar_Pervasives_Native.option)
        FStar_Pervasives_Native.option)
  =
  fun remove_parens ->
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
      | Paren t when remove_parens ->
          extract_named_refinement remove_parens t
      | uu___ -> FStar_Pervasives_Native.None
let rec (as_mlist :
  ((FStarC_Ident.lid * decl) * decl Prims.list) -> decl Prims.list -> modul)
  =
  fun cur ->
    fun ds ->
      let uu___ = cur in
      match uu___ with
      | ((m_name, m_decl), cur1) ->
          (match ds with
           | [] ->
               Module (m_name, (m_decl :: (FStarC_Compiler_List.rev cur1)))
           | d::ds1 ->
               (match d.d with
                | TopLevelModule m' ->
                    FStarC_Errors.raise_error hasRange_decl d
                      FStarC_Errors_Codes.Fatal_UnexpectedModuleDeclaration
                      ()
                      (Obj.magic FStarC_Errors_Msg.is_error_message_string)
                      (Obj.magic "Unexpected module declaration")
                | uu___1 -> as_mlist ((m_name, m_decl), (d :: cur1)) ds1))
let (as_frag : decl Prims.list -> inputFragment) =
  fun ds ->
    let uu___ =
      match ds with
      | d::ds1 -> (d, ds1)
      | [] -> FStarC_Compiler_Effect.raise FStarC_Errors.Empty_frag in
    match uu___ with
    | (d, ds1) ->
        (match d.d with
         | TopLevelModule m ->
             let m1 = as_mlist ((m, d), []) ds1 in FStar_Pervasives.Inl m1
         | uu___1 ->
             let ds2 = d :: ds1 in
             (FStarC_Compiler_List.iter
                (fun uu___3 ->
                   match uu___3 with
                   | { d = TopLevelModule uu___4; drange = r; quals = uu___5;
                       attrs = uu___6; interleaved = uu___7;_} ->
                       FStarC_Errors.raise_error
                         FStarC_Class_HasRange.hasRange_range r
                         FStarC_Errors_Codes.Fatal_UnexpectedModuleDeclaration
                         ()
                         (Obj.magic FStarC_Errors_Msg.is_error_message_string)
                         (Obj.magic "Unexpected module declaration")
                   | uu___4 -> ()) ds2;
              FStar_Pervasives.Inr ds2))
let (strip_prefix :
  Prims.string -> Prims.string -> Prims.string FStar_Pervasives_Native.option)
  =
  fun prefix ->
    fun s ->
      if FStarC_Compiler_Util.starts_with s prefix
      then
        let uu___ =
          FStarC_Compiler_Util.substring_from s
            (FStarC_Compiler_String.length prefix) in
        FStar_Pervasives_Native.Some uu___
      else FStar_Pervasives_Native.None
let (compile_op :
  Prims.int ->
    Prims.string -> FStarC_Compiler_Range_Type.range -> Prims.string)
  =
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
              let uu___1 =
                FStarC_Compiler_Util.string_of_int
                  (FStarC_Compiler_Util.int_of_char c) in
              Prims.strcat "u" uu___1 in
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
              if
                (FStarC_Compiler_Util.starts_with s "let") ||
                  (FStarC_Compiler_Util.starts_with s "and")
              then
                let uu___2 =
                  let uu___3 =
                    FStarC_Compiler_Util.substring s Prims.int_zero
                      (Prims.of_int (3)) in
                  Prims.strcat uu___3 "_" in
                let uu___3 =
                  FStarC_Compiler_Util.substring_from s (Prims.of_int (3)) in
                (uu___2, uu___3)
              else
                if
                  (FStarC_Compiler_Util.starts_with s "exists") ||
                    (FStarC_Compiler_Util.starts_with s "forall")
                then
                  (let uu___3 =
                     let uu___4 =
                       FStarC_Compiler_Util.substring s Prims.int_zero
                         (Prims.of_int (6)) in
                     Prims.strcat uu___4 "_" in
                   let uu___4 =
                     FStarC_Compiler_Util.substring_from s (Prims.of_int (6)) in
                   (uu___3, uu___4))
                else ("", s) in
            (match uu___1 with
             | (prefix, s1) ->
                 let uu___2 =
                   let uu___3 =
                     let uu___4 =
                       let uu___5 = FStarC_Compiler_String.list_of_string s1 in
                       FStarC_Compiler_List.map name_of_char uu___5 in
                     FStarC_Compiler_String.concat "_" uu___4 in
                   Prims.strcat prefix uu___3 in
                 Prims.strcat "op_" uu___2)
let (compile_op' :
  Prims.string -> FStarC_Compiler_Range_Type.range -> Prims.string) =
  fun s -> fun r -> compile_op (Prims.of_int (-1)) s r
let (string_to_op :
  Prims.string ->
    (Prims.string * Prims.int FStar_Pervasives_Native.option)
      FStar_Pervasives_Native.option)
  =
  fun s ->
    let name_of_op s1 =
      match s1 with
      | "Amp" ->
          FStar_Pervasives_Native.Some ("&", FStar_Pervasives_Native.None)
      | "At" ->
          FStar_Pervasives_Native.Some ("@", FStar_Pervasives_Native.None)
      | "Plus" ->
          FStar_Pervasives_Native.Some
            ("+", (FStar_Pervasives_Native.Some (Prims.of_int (2))))
      | "Minus" ->
          FStar_Pervasives_Native.Some ("-", FStar_Pervasives_Native.None)
      | "Subtraction" ->
          FStar_Pervasives_Native.Some
            ("-", (FStar_Pervasives_Native.Some (Prims.of_int (2))))
      | "Tilde" ->
          FStar_Pervasives_Native.Some ("~", FStar_Pervasives_Native.None)
      | "Slash" ->
          FStar_Pervasives_Native.Some
            ("/", (FStar_Pervasives_Native.Some (Prims.of_int (2))))
      | "Backslash" ->
          FStar_Pervasives_Native.Some ("\\", FStar_Pervasives_Native.None)
      | "Less" ->
          FStar_Pervasives_Native.Some
            ("<", (FStar_Pervasives_Native.Some (Prims.of_int (2))))
      | "Equals" ->
          FStar_Pervasives_Native.Some ("=", FStar_Pervasives_Native.None)
      | "Greater" ->
          FStar_Pervasives_Native.Some
            (">", (FStar_Pervasives_Native.Some (Prims.of_int (2))))
      | "Underscore" ->
          FStar_Pervasives_Native.Some ("_", FStar_Pervasives_Native.None)
      | "Bar" ->
          FStar_Pervasives_Native.Some ("|", FStar_Pervasives_Native.None)
      | "Bang" ->
          FStar_Pervasives_Native.Some ("!", FStar_Pervasives_Native.None)
      | "Hat" ->
          FStar_Pervasives_Native.Some ("^", FStar_Pervasives_Native.None)
      | "Percent" ->
          FStar_Pervasives_Native.Some ("%", FStar_Pervasives_Native.None)
      | "Star" ->
          FStar_Pervasives_Native.Some ("*", FStar_Pervasives_Native.None)
      | "Question" ->
          FStar_Pervasives_Native.Some ("?", FStar_Pervasives_Native.None)
      | "Colon" ->
          FStar_Pervasives_Native.Some (":", FStar_Pervasives_Native.None)
      | "Dollar" ->
          FStar_Pervasives_Native.Some ("$", FStar_Pervasives_Native.None)
      | "Dot" ->
          FStar_Pervasives_Native.Some (".", FStar_Pervasives_Native.None)
      | "let" ->
          FStar_Pervasives_Native.Some (s1, FStar_Pervasives_Native.None)
      | "and" ->
          FStar_Pervasives_Native.Some (s1, FStar_Pervasives_Native.None)
      | "forall" ->
          FStar_Pervasives_Native.Some (s1, FStar_Pervasives_Native.None)
      | "exists" ->
          FStar_Pervasives_Native.Some (s1, FStar_Pervasives_Native.None)
      | uu___ -> FStar_Pervasives_Native.None in
    match s with
    | "op_String_Assignment" ->
        FStar_Pervasives_Native.Some (".[]<-", FStar_Pervasives_Native.None)
    | "op_Array_Assignment" ->
        FStar_Pervasives_Native.Some (".()<-", FStar_Pervasives_Native.None)
    | "op_Brack_Lens_Assignment" ->
        FStar_Pervasives_Native.Some
          (".[||]<-", FStar_Pervasives_Native.None)
    | "op_Lens_Assignment" ->
        FStar_Pervasives_Native.Some
          (".(||)<-", FStar_Pervasives_Native.None)
    | "op_String_Access" ->
        FStar_Pervasives_Native.Some (".[]", FStar_Pervasives_Native.None)
    | "op_Array_Access" ->
        FStar_Pervasives_Native.Some (".()", FStar_Pervasives_Native.None)
    | "op_Brack_Lens_Access" ->
        FStar_Pervasives_Native.Some (".[||]", FStar_Pervasives_Native.None)
    | "op_Lens_Access" ->
        FStar_Pervasives_Native.Some (".(||)", FStar_Pervasives_Native.None)
    | uu___ ->
        if FStarC_Compiler_Util.starts_with s "op_"
        then
          let frags =
            let uu___1 =
              FStarC_Compiler_Util.substring_from s
                (FStarC_Compiler_String.length "op_") in
            FStarC_Compiler_Util.split uu___1 "_" in
          (match frags with
           | op::[] ->
               if FStarC_Compiler_Util.starts_with op "u"
               then
                 let uu___1 =
                   let uu___2 =
                     FStarC_Compiler_Util.substring_from op Prims.int_one in
                   FStarC_Compiler_Util.safe_int_of_string uu___2 in
                 FStarC_Compiler_Util.map_opt uu___1
                   (fun op1 ->
                      ((FStarC_Compiler_Util.string_of_char
                          (FStarC_Compiler_Util.char_of_int op1)),
                        FStar_Pervasives_Native.None))
               else name_of_op op
           | uu___1 ->
               let maybeop =
                 let uu___2 = FStarC_Compiler_List.map name_of_op frags in
                 FStarC_Compiler_List.fold_left
                   (fun acc ->
                      fun x ->
                        match acc with
                        | FStar_Pervasives_Native.None ->
                            FStar_Pervasives_Native.None
                        | FStar_Pervasives_Native.Some acc1 ->
                            (match x with
                             | FStar_Pervasives_Native.Some (op, uu___3) ->
                                 FStar_Pervasives_Native.Some
                                   (Prims.strcat acc1 op)
                             | FStar_Pervasives_Native.None ->
                                 FStar_Pervasives_Native.None))
                   (FStar_Pervasives_Native.Some "") uu___2 in
               FStarC_Compiler_Util.map_opt maybeop
                 (fun o -> (o, FStar_Pervasives_Native.None)))
        else FStar_Pervasives_Native.None
let (string_of_fsdoc :
  (Prims.string * (Prims.string * Prims.string) Prims.list) -> Prims.string)
  =
  fun uu___ ->
    match uu___ with
    | (comment, keywords) ->
        let uu___1 =
          let uu___2 =
            FStarC_Compiler_List.map
              (fun uu___3 ->
                 match uu___3 with
                 | (k, v) -> Prims.strcat k (Prims.strcat "->" v)) keywords in
          FStarC_Compiler_String.concat "," uu___2 in
        Prims.strcat comment uu___1
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
        let uu___ = FStarC_Compiler_List.map f l in
        FStarC_Compiler_String.concat sep uu___
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
              let uu___1 = term_to_string hd in
              FStarC_Compiler_List.fold_left
                (fun s ->
                   fun t ->
                     let uu___2 =
                       let uu___3 = term_to_string t in
                       Prims.strcat "; " uu___3 in
                     Prims.strcat s uu___2) uu___1 tl in
        FStarC_Compiler_Util.format1 "%[%s]" uu___
    | Decreases (t, uu___) ->
        let uu___1 = term_to_string t in
        FStarC_Compiler_Util.format1 "(decreases %s)" uu___1
    | Requires (t, uu___) ->
        let uu___1 = term_to_string t in
        FStarC_Compiler_Util.format1 "(requires %s)" uu___1
    | Ensures (t, uu___) ->
        let uu___1 = term_to_string t in
        FStarC_Compiler_Util.format1 "(ensures %s)" uu___1
    | Labeled (t, l, uu___) ->
        let uu___1 = term_to_string t in
        FStarC_Compiler_Util.format2 "(labeled %s %s)" l uu___1
    | Const c -> FStarC_Parser_Const.const_to_string c
    | Op (s, xs) ->
        let uu___ = FStarC_Ident.string_of_id s in
        let uu___1 =
          let uu___2 =
            FStarC_Compiler_List.map (fun x1 -> term_to_string x1) xs in
          FStarC_Compiler_String.concat ", " uu___2 in
        FStarC_Compiler_Util.format2 "%s(%s)" uu___ uu___1
    | Tvar id -> FStarC_Ident.string_of_id id
    | Uvar id -> FStarC_Ident.string_of_id id
    | Var l -> FStarC_Ident.string_of_lid l
    | Name l -> FStarC_Ident.string_of_lid l
    | Projector (rec_lid, field_id) ->
        let uu___ = FStarC_Ident.string_of_lid rec_lid in
        let uu___1 = FStarC_Ident.string_of_id field_id in
        FStarC_Compiler_Util.format2 "%s?.%s" uu___ uu___1
    | Construct (l, args) ->
        let uu___ = FStarC_Ident.string_of_lid l in
        let uu___1 =
          to_string_l " "
            (fun uu___2 ->
               match uu___2 with
               | (a, imp1) ->
                   let uu___3 = term_to_string a in
                   FStarC_Compiler_Util.format2 "%s%s" (imp_to_string imp1)
                     uu___3) args in
        FStarC_Compiler_Util.format2 "(%s %s)" uu___ uu___1
    | Function (branches, r) ->
        let uu___ =
          to_string_l " | "
            (fun uu___1 ->
               match uu___1 with
               | (p, w, e) ->
                   let uu___2 = pat_to_string p in
                   let uu___3 = term_to_string e in
                   FStarC_Compiler_Util.format2 "%s -> %s" uu___2 uu___3)
            branches in
        FStarC_Compiler_Util.format1 "(function %s)" uu___
    | Abs (pats, t) ->
        let uu___ = to_string_l " " pat_to_string pats in
        let uu___1 = term_to_string t in
        FStarC_Compiler_Util.format2 "(fun %s -> %s)" uu___ uu___1
    | App (t1, t2, imp1) ->
        let uu___ = term_to_string t1 in
        let uu___1 = term_to_string t2 in
        FStarC_Compiler_Util.format3 "%s %s%s" uu___ (imp_to_string imp1)
          uu___1
    | Let (Rec, (a, (p, b))::lbs, body) ->
        let uu___ = attrs_opt_to_string a in
        let uu___1 =
          let uu___2 = pat_to_string p in
          let uu___3 = term_to_string b in
          FStarC_Compiler_Util.format2 "%s=%s" uu___2 uu___3 in
        let uu___2 =
          to_string_l " "
            (fun uu___3 ->
               match uu___3 with
               | (a1, (p1, b1)) ->
                   let uu___4 = attrs_opt_to_string a1 in
                   let uu___5 = pat_to_string p1 in
                   let uu___6 = term_to_string b1 in
                   FStarC_Compiler_Util.format3 "%sand %s=%s" uu___4 uu___5
                     uu___6) lbs in
        let uu___3 = term_to_string body in
        FStarC_Compiler_Util.format4 "%slet rec %s%s in %s" uu___ uu___1
          uu___2 uu___3
    | Let (q, (attrs, (pat, tm))::[], body) ->
        let uu___ = attrs_opt_to_string attrs in
        let uu___1 = string_of_let_qualifier q in
        let uu___2 = pat_to_string pat in
        let uu___3 = term_to_string tm in
        let uu___4 = term_to_string body in
        FStarC_Compiler_Util.format5 "%slet %s %s = %s in %s" uu___ uu___1
          uu___2 uu___3 uu___4
    | Let (uu___, uu___1, uu___2) ->
        FStarC_Errors.raise_error hasRange_term x
          FStarC_Errors_Codes.Fatal_EmptySurfaceLet ()
          (Obj.magic FStarC_Errors_Msg.is_error_message_string)
          (Obj.magic "Internal error: found an invalid surface Let")
    | LetOpen (lid, t) ->
        let uu___ = FStarC_Ident.string_of_lid lid in
        let uu___1 = term_to_string t in
        FStarC_Compiler_Util.format2 "let open %s in %s" uu___ uu___1
    | Seq (t1, t2) ->
        let uu___ = term_to_string t1 in
        let uu___1 = term_to_string t2 in
        FStarC_Compiler_Util.format2 "%s; %s" uu___ uu___1
    | Bind (id, t1, t2) ->
        let uu___ = FStarC_Ident.string_of_id id in
        let uu___1 = term_to_string t1 in
        let uu___2 = term_to_string t2 in
        FStarC_Compiler_Util.format3 "%s <- %s; %s" uu___ uu___1 uu___2
    | If (t1, op_opt, ret_opt, t2, t3) ->
        let uu___ =
          match op_opt with
          | FStar_Pervasives_Native.Some op -> FStarC_Ident.string_of_id op
          | FStar_Pervasives_Native.None -> "" in
        let uu___1 = term_to_string t1 in
        let uu___2 =
          match ret_opt with
          | FStar_Pervasives_Native.None -> ""
          | FStar_Pervasives_Native.Some (as_opt, ret, use_eq) ->
              let s = if use_eq then "returns$" else "returns" in
              let uu___3 =
                match as_opt with
                | FStar_Pervasives_Native.None -> ""
                | FStar_Pervasives_Native.Some as_ident ->
                    let uu___4 = FStarC_Ident.string_of_id as_ident in
                    FStarC_Compiler_Util.format1 " as %s " uu___4 in
              let uu___4 = term_to_string ret in
              FStarC_Compiler_Util.format3 "%s%s %s " uu___3 s uu___4 in
        let uu___3 = term_to_string t2 in
        let uu___4 = term_to_string t3 in
        FStarC_Compiler_Util.format5 "if%s %s %sthen %s else %s" uu___ uu___1
          uu___2 uu___3 uu___4
    | Match (t, op_opt, ret_opt, branches) ->
        try_or_match_to_string x t branches op_opt ret_opt
    | TryWith (t, branches) ->
        try_or_match_to_string x t branches FStar_Pervasives_Native.None
          FStar_Pervasives_Native.None
    | Ascribed (t1, t2, FStar_Pervasives_Native.None, flag) ->
        let s = if flag then "$:" else "<:" in
        let uu___ = term_to_string t1 in
        let uu___1 = term_to_string t2 in
        FStarC_Compiler_Util.format3 "(%s %s %s)" uu___ s uu___1
    | Ascribed (t1, t2, FStar_Pervasives_Native.Some tac, flag) ->
        let s = if flag then "$:" else "<:" in
        let uu___ = term_to_string t1 in
        let uu___1 = term_to_string t2 in
        let uu___2 = term_to_string tac in
        FStarC_Compiler_Util.format4 "(%s %s %s by %s)" uu___ s uu___1 uu___2
    | Record (FStar_Pervasives_Native.Some e, fields) ->
        let uu___ = term_to_string e in
        let uu___1 =
          to_string_l " "
            (fun uu___2 ->
               match uu___2 with
               | (l, e1) ->
                   let uu___3 = FStarC_Ident.string_of_lid l in
                   let uu___4 = term_to_string e1 in
                   FStarC_Compiler_Util.format2 "%s=%s" uu___3 uu___4) fields in
        FStarC_Compiler_Util.format2 "{%s with %s}" uu___ uu___1
    | Record (FStar_Pervasives_Native.None, fields) ->
        let uu___ =
          to_string_l " "
            (fun uu___1 ->
               match uu___1 with
               | (l, e) ->
                   let uu___2 = FStarC_Ident.string_of_lid l in
                   let uu___3 = term_to_string e in
                   FStarC_Compiler_Util.format2 "%s=%s" uu___2 uu___3) fields in
        FStarC_Compiler_Util.format1 "{%s}" uu___
    | Project (e, l) ->
        let uu___ = term_to_string e in
        let uu___1 = FStarC_Ident.string_of_lid l in
        FStarC_Compiler_Util.format2 "%s.%s" uu___ uu___1
    | Product ([], t) -> term_to_string t
    | Product (b::hd::tl, t) ->
        let uu___ =
          let uu___1 =
            let uu___2 =
              let uu___3 = mk_term (Product ((hd :: tl), t)) x.range x.level in
              ([b], uu___3) in
            Product uu___2 in
          mk_term uu___1 x.range x.level in
        term_to_string uu___
    | Product (b::[], t) when x.level = Type_level ->
        let uu___ = binder_to_string b in
        let uu___1 = term_to_string t in
        FStarC_Compiler_Util.format2 "%s -> %s" uu___ uu___1
    | Product (b::[], t) when x.level = Kind ->
        let uu___ = binder_to_string b in
        let uu___1 = term_to_string t in
        FStarC_Compiler_Util.format2 "%s => %s" uu___ uu___1
    | Sum (binders, t) ->
        let uu___ =
          FStarC_Compiler_List.map
            (fun uu___1 ->
               match uu___1 with
               | FStar_Pervasives.Inl b -> binder_to_string b
               | FStar_Pervasives.Inr t1 -> term_to_string t1)
            (FStarC_Compiler_List.op_At binders [FStar_Pervasives.Inr t]) in
        FStarC_Compiler_String.concat " & " uu___
    | QForall (bs, (uu___, pats), t) ->
        let uu___1 = to_string_l " " binder_to_string bs in
        let uu___2 =
          to_string_l " \\/ " (to_string_l "; " term_to_string) pats in
        let uu___3 = term_to_string t in
        FStarC_Compiler_Util.format3 "forall %s.{:pattern %s} %s" uu___1
          uu___2 uu___3
    | QExists (bs, (uu___, pats), t) ->
        let uu___1 = to_string_l " " binder_to_string bs in
        let uu___2 =
          to_string_l " \\/ " (to_string_l "; " term_to_string) pats in
        let uu___3 = term_to_string t in
        FStarC_Compiler_Util.format3 "exists %s.{:pattern %s} %s" uu___1
          uu___2 uu___3
    | QuantOp (i, bs, (uu___, []), t) ->
        let uu___1 = FStarC_Ident.string_of_id i in
        let uu___2 = to_string_l " " binder_to_string bs in
        let uu___3 = term_to_string t in
        FStarC_Compiler_Util.format3 "%s %s. %s" uu___1 uu___2 uu___3
    | QuantOp (i, bs, (uu___, pats), t) ->
        let uu___1 = FStarC_Ident.string_of_id i in
        let uu___2 = to_string_l " " binder_to_string bs in
        let uu___3 =
          to_string_l " \\/ " (to_string_l "; " term_to_string) pats in
        let uu___4 = term_to_string t in
        FStarC_Compiler_Util.format4 "%s %s.{:pattern %s} %s" uu___1 uu___2
          uu___3 uu___4
    | Refine (b, t) ->
        let uu___ = binder_to_string b in
        let uu___1 = term_to_string t in
        FStarC_Compiler_Util.format2 "%s:{%s}" uu___ uu___1
    | NamedTyp (x1, t) ->
        let uu___ = FStarC_Ident.string_of_id x1 in
        let uu___1 = term_to_string t in
        FStarC_Compiler_Util.format2 "%s:%s" uu___ uu___1
    | Paren t ->
        let uu___ = term_to_string t in
        FStarC_Compiler_Util.format1 "(%s)" uu___
    | Product (bs, t) ->
        let uu___ =
          let uu___1 = FStarC_Compiler_List.map binder_to_string bs in
          FStarC_Compiler_String.concat "," uu___1 in
        let uu___1 = term_to_string t in
        FStarC_Compiler_Util.format2 "Unidentified product: [%s] %s" uu___
          uu___1
    | Discrim lid ->
        let uu___ = FStarC_Ident.string_of_lid lid in
        FStarC_Compiler_Util.format1 "%s?" uu___
    | Attributes ts ->
        let uu___ =
          let uu___1 = FStarC_Compiler_List.map term_to_string ts in
          FStarC_Compiler_String.concat " " uu___1 in
        FStarC_Compiler_Util.format1 "(attributes %s)" uu___
    | Antiquote t ->
        let uu___ = term_to_string t in
        FStarC_Compiler_Util.format1 "(`#%s)" uu___
    | Quote (t, Static) ->
        let uu___ = term_to_string t in
        FStarC_Compiler_Util.format1 "(`(%s))" uu___
    | Quote (t, Dynamic) ->
        let uu___ = term_to_string t in
        FStarC_Compiler_Util.format1 "quote (%s)" uu___
    | VQuote t ->
        let uu___ = term_to_string t in
        FStarC_Compiler_Util.format1 "`%%%s" uu___
    | CalcProof (rel, init, steps) ->
        let uu___ = term_to_string rel in
        let uu___1 = term_to_string init in
        let uu___2 =
          let uu___3 = FStarC_Compiler_List.map calc_step_to_string steps in
          FStarC_Compiler_String.concat " " uu___3 in
        FStarC_Compiler_Util.format3 "calc (%s) { %s %s }" uu___ uu___1
          uu___2
    | ElimForall (bs, t, vs) ->
        let uu___ = binders_to_string " " bs in
        let uu___1 = term_to_string t in
        let uu___2 =
          let uu___3 = FStarC_Compiler_List.map term_to_string vs in
          FStarC_Compiler_String.concat " " uu___3 in
        FStarC_Compiler_Util.format3 "_elim_ forall %s. %s using %s" uu___
          uu___1 uu___2
    | ElimExists (bs, p, q, b, e) ->
        let uu___ = binders_to_string " " bs in
        let uu___1 = term_to_string p in
        let uu___2 = term_to_string q in
        let uu___3 = binder_to_string b in
        let uu___4 = term_to_string e in
        FStarC_Compiler_Util.format5
          "_elim_ exists %s. %s _to_ %s\n\\with %s. %s" uu___ uu___1 uu___2
          uu___3 uu___4
    | ElimImplies (p, q, e) ->
        let uu___ = term_to_string p in
        let uu___1 = term_to_string q in
        let uu___2 = term_to_string e in
        FStarC_Compiler_Util.format3 "_elim_ %s ==> %s with %s" uu___ uu___1
          uu___2
    | ElimOr (p, q, r, x1, e, y, e') ->
        let uu___ =
          let uu___1 = term_to_string p in
          let uu___2 =
            let uu___3 = term_to_string q in
            let uu___4 =
              let uu___5 = term_to_string r in
              let uu___6 =
                let uu___7 = binder_to_string x1 in
                let uu___8 =
                  let uu___9 = term_to_string e in
                  let uu___10 =
                    let uu___11 = binder_to_string y in
                    let uu___12 =
                      let uu___13 = term_to_string e' in [uu___13] in
                    uu___11 :: uu___12 in
                  uu___9 :: uu___10 in
                uu___7 :: uu___8 in
              uu___5 :: uu___6 in
            uu___3 :: uu___4 in
          uu___1 :: uu___2 in
        FStarC_Compiler_Util.format
          "_elim_ %s \\/ %s _to_ %s\n\\with %s. %s\n\\and %s.%s" uu___
    | ElimAnd (p, q, r, x1, y, e) ->
        let uu___ =
          let uu___1 = term_to_string p in
          let uu___2 =
            let uu___3 = term_to_string q in
            let uu___4 =
              let uu___5 = term_to_string r in
              let uu___6 =
                let uu___7 = binder_to_string x1 in
                let uu___8 =
                  let uu___9 = binder_to_string y in
                  let uu___10 = let uu___11 = term_to_string e in [uu___11] in
                  uu___9 :: uu___10 in
                uu___7 :: uu___8 in
              uu___5 :: uu___6 in
            uu___3 :: uu___4 in
          uu___1 :: uu___2 in
        FStarC_Compiler_Util.format
          "_elim_ %s /\\ %s _to_ %s\n\\with %s %s. %s" uu___
    | IntroForall (xs, p, e) ->
        let uu___ = binders_to_string " " xs in
        let uu___1 = term_to_string p in
        let uu___2 = term_to_string e in
        FStarC_Compiler_Util.format3 "_intro_ forall %s. %s with %s" uu___
          uu___1 uu___2
    | IntroExists (xs, t, vs, e) ->
        let uu___ = binders_to_string " " xs in
        let uu___1 = term_to_string t in
        let uu___2 =
          let uu___3 = FStarC_Compiler_List.map term_to_string vs in
          FStarC_Compiler_String.concat " " uu___3 in
        let uu___3 = term_to_string e in
        FStarC_Compiler_Util.format4 "_intro_ exists %s. %s using %s with %s"
          uu___ uu___1 uu___2 uu___3
    | IntroImplies (p, q, x1, e) ->
        let uu___ = term_to_string p in
        let uu___1 = term_to_string q in
        let uu___2 = binder_to_string x1 in
        let uu___3 = term_to_string p in
        FStarC_Compiler_Util.format4 "_intro_ %s ==> %s with %s. %s" uu___
          uu___1 uu___2 uu___3
    | IntroOr (b, p, q, r) ->
        let uu___ = term_to_string p in
        let uu___1 = term_to_string q in
        let uu___2 = term_to_string r in
        FStarC_Compiler_Util.format4 "_intro_ %s \\/ %s using %s with %s"
          uu___ uu___1 (if b then "Left" else "Right") uu___2
    | IntroAnd (p, q, e1, e2) ->
        let uu___ = term_to_string p in
        let uu___1 = term_to_string q in
        let uu___2 = term_to_string e1 in
        let uu___3 = term_to_string e2 in
        FStarC_Compiler_Util.format4 "_intro_ %s /\\ %s with %s and %s" uu___
          uu___1 uu___2 uu___3
    | ListLiteral ts ->
        let uu___ = to_string_l "; " term_to_string ts in
        FStarC_Compiler_Util.format1 "[%s]" uu___
    | SeqLiteral ts ->
        let uu___ = to_string_l "; " term_to_string ts in
        FStarC_Compiler_Util.format1 "seq![%s]" uu___
and (binders_to_string : Prims.string -> binder Prims.list -> Prims.string) =
  fun sep ->
    fun bs ->
      let uu___ = FStarC_Compiler_List.map binder_to_string bs in
      FStarC_Compiler_String.concat sep uu___
and (try_or_match_to_string :
  term ->
    term ->
      (pattern * term FStar_Pervasives_Native.option * term) Prims.list ->
        FStarC_Ident.ident FStar_Pervasives_Native.option ->
          (FStarC_Ident.ident FStar_Pervasives_Native.option * term *
            Prims.bool) FStar_Pervasives_Native.option -> Prims.string)
  =
  fun x ->
    fun scrutinee ->
      fun branches ->
        fun op_opt ->
          fun ret_opt ->
            let s =
              match x.tm with
              | Match uu___ -> "match"
              | TryWith uu___ -> "try"
              | uu___ -> failwith "impossible" in
            let uu___ =
              match op_opt with
              | FStar_Pervasives_Native.Some op ->
                  FStarC_Ident.string_of_id op
              | FStar_Pervasives_Native.None -> "" in
            let uu___1 = term_to_string scrutinee in
            let uu___2 =
              match ret_opt with
              | FStar_Pervasives_Native.None -> ""
              | FStar_Pervasives_Native.Some (as_opt, ret, use_eq) ->
                  let s1 = if use_eq then "returns$" else "returns" in
                  let uu___3 =
                    match as_opt with
                    | FStar_Pervasives_Native.None -> ""
                    | FStar_Pervasives_Native.Some as_ident ->
                        let uu___4 = FStarC_Ident.string_of_id as_ident in
                        FStarC_Compiler_Util.format1 "as %s " uu___4 in
                  let uu___4 = term_to_string ret in
                  FStarC_Compiler_Util.format3 "%s%s %s " s1 uu___3 uu___4 in
            let uu___3 =
              to_string_l " | "
                (fun uu___4 ->
                   match uu___4 with
                   | (p, w, e) ->
                       let uu___5 = pat_to_string p in
                       let uu___6 =
                         match w with
                         | FStar_Pervasives_Native.None -> ""
                         | FStar_Pervasives_Native.Some e1 ->
                             let uu___7 = term_to_string e1 in
                             FStarC_Compiler_Util.format1 "when %s" uu___7 in
                       let uu___7 = term_to_string e in
                       FStarC_Compiler_Util.format3 "%s %s -> %s" uu___5
                         uu___6 uu___7) branches in
            FStarC_Compiler_Util.format5 "%s%s %s %swith %s" s uu___ uu___1
              uu___2 uu___3
and (calc_step_to_string : calc_step -> Prims.string) =
  fun uu___ ->
    match uu___ with
    | CalcStep (rel, just, next) ->
        let uu___1 = term_to_string rel in
        let uu___2 = term_to_string just in
        let uu___3 = term_to_string next in
        FStarC_Compiler_Util.format3 "%s{ %s } %s" uu___1 uu___2 uu___3
and (binder_to_string : binder -> Prims.string) =
  fun x ->
    let pr x1 =
      let s =
        match x1.b with
        | Variable i -> FStarC_Ident.string_of_id i
        | TVariable i ->
            let uu___ = FStarC_Ident.string_of_id i in
            FStarC_Compiler_Util.format1 "%s:_" uu___
        | TAnnotated (i, t) ->
            let uu___ = FStarC_Ident.string_of_id i in
            let uu___1 = term_to_string t in
            FStarC_Compiler_Util.format2 "%s:%s" uu___ uu___1
        | Annotated (i, t) ->
            let uu___ = FStarC_Ident.string_of_id i in
            let uu___1 = term_to_string t in
            FStarC_Compiler_Util.format2 "%s:%s" uu___ uu___1
        | NoName t -> term_to_string t in
      let uu___ = aqual_to_string x1.aqual in
      let uu___1 = attr_list_to_string x1.battributes in
      FStarC_Compiler_Util.format3 "%s%s%s" uu___ uu___1 s in
    match x.aqual with
    | FStar_Pervasives_Native.Some (TypeClassArg) ->
        let uu___ = let uu___1 = pr x in Prims.strcat uu___1 " |}" in
        Prims.strcat "{| " uu___
    | uu___ -> pr x
and (aqual_to_string :
  arg_qualifier FStar_Pervasives_Native.option -> Prims.string) =
  fun uu___ ->
    match uu___ with
    | FStar_Pervasives_Native.Some (Equality) -> "$"
    | FStar_Pervasives_Native.Some (Implicit) -> "#"
    | FStar_Pervasives_Native.None -> ""
    | FStar_Pervasives_Native.Some (Meta uu___1) ->
        failwith "aqual_to_strings: meta arg qualifier?"
    | FStar_Pervasives_Native.Some (TypeClassArg) ->
        failwith "aqual_to_strings: meta arg qualifier?"
and (attr_list_to_string : term Prims.list -> Prims.string) =
  fun uu___ ->
    match uu___ with
    | [] -> ""
    | l -> attrs_opt_to_string (FStar_Pervasives_Native.Some l)
and (pat_to_string : pattern -> Prims.string) =
  fun x ->
    match x.pat with
    | PatWild (FStar_Pervasives_Native.None, attrs) ->
        let uu___ = attr_list_to_string attrs in Prims.strcat uu___ "_"
    | PatWild (uu___, attrs) ->
        let uu___1 =
          let uu___2 = attr_list_to_string attrs in Prims.strcat uu___2 "_" in
        Prims.strcat "#" uu___1
    | PatConst c -> FStarC_Parser_Const.const_to_string c
    | PatVQuote t ->
        let uu___ = term_to_string t in
        FStarC_Compiler_Util.format1 "`%%%s" uu___
    | PatApp (p, ps) ->
        let uu___ = pat_to_string p in
        let uu___1 = to_string_l " " pat_to_string ps in
        FStarC_Compiler_Util.format2 "(%s %s)" uu___ uu___1
    | PatTvar (i, aq, attrs) ->
        let uu___ = aqual_to_string aq in
        let uu___1 = attr_list_to_string attrs in
        let uu___2 = FStarC_Ident.string_of_id i in
        FStarC_Compiler_Util.format3 "%s%s%s" uu___ uu___1 uu___2
    | PatVar (i, aq, attrs) ->
        let uu___ = aqual_to_string aq in
        let uu___1 = attr_list_to_string attrs in
        let uu___2 = FStarC_Ident.string_of_id i in
        FStarC_Compiler_Util.format3 "%s%s%s" uu___ uu___1 uu___2
    | PatName l -> FStarC_Ident.string_of_lid l
    | PatList l ->
        let uu___ = to_string_l "; " pat_to_string l in
        FStarC_Compiler_Util.format1 "[%s]" uu___
    | PatTuple (l, false) ->
        let uu___ = to_string_l ", " pat_to_string l in
        FStarC_Compiler_Util.format1 "(%s)" uu___
    | PatTuple (l, true) ->
        let uu___ = to_string_l ", " pat_to_string l in
        FStarC_Compiler_Util.format1 "(|%s|)" uu___
    | PatRecord l ->
        let uu___ =
          to_string_l "; "
            (fun uu___1 ->
               match uu___1 with
               | (f, e) ->
                   let uu___2 = FStarC_Ident.string_of_lid f in
                   let uu___3 = pat_to_string e in
                   FStarC_Compiler_Util.format2 "%s=%s" uu___2 uu___3) l in
        FStarC_Compiler_Util.format1 "{%s}" uu___
    | PatOr l -> to_string_l "|\n " pat_to_string l
    | PatOp op ->
        let uu___ = FStarC_Ident.string_of_id op in
        FStarC_Compiler_Util.format1 "(%s)" uu___
    | PatAscribed (p, (t, FStar_Pervasives_Native.None)) ->
        let uu___ = pat_to_string p in
        let uu___1 = term_to_string t in
        FStarC_Compiler_Util.format2 "(%s:%s)" uu___ uu___1
    | PatAscribed (p, (t, FStar_Pervasives_Native.Some tac)) ->
        let uu___ = pat_to_string p in
        let uu___1 = term_to_string t in
        let uu___2 = term_to_string tac in
        FStarC_Compiler_Util.format3 "(%s:%s by %s)" uu___ uu___1 uu___2
and (attrs_opt_to_string :
  term Prims.list FStar_Pervasives_Native.option -> Prims.string) =
  fun uu___ ->
    match uu___ with
    | FStar_Pervasives_Native.None -> ""
    | FStar_Pervasives_Native.Some attrs ->
        let uu___1 =
          let uu___2 = FStarC_Compiler_List.map term_to_string attrs in
          FStarC_Compiler_String.concat "; " uu___2 in
        FStarC_Compiler_Util.format1 "[@ %s]" uu___1
let rec (head_id_of_pat : pattern -> FStarC_Ident.lident Prims.list) =
  fun p ->
    match p.pat with
    | PatName l -> [l]
    | PatVar (i, uu___, uu___1) ->
        let uu___2 = FStarC_Ident.lid_of_ids [i] in [uu___2]
    | PatApp (p1, uu___) -> head_id_of_pat p1
    | PatAscribed (p1, uu___) -> head_id_of_pat p1
    | uu___ -> []
let (lids_of_let :
  (pattern * term) Prims.list -> FStarC_Ident.lident Prims.list) =
  fun defs ->
    FStarC_Compiler_List.collect
      (fun uu___ -> match uu___ with | (p, uu___1) -> head_id_of_pat p) defs
let (id_of_tycon : tycon -> Prims.string) =
  fun uu___ ->
    match uu___ with
    | TyconAbstract (i, uu___1, uu___2) -> FStarC_Ident.string_of_id i
    | TyconAbbrev (i, uu___1, uu___2, uu___3) -> FStarC_Ident.string_of_id i
    | TyconRecord (i, uu___1, uu___2, uu___3, uu___4) ->
        FStarC_Ident.string_of_id i
    | TyconVariant (i, uu___1, uu___2, uu___3) -> FStarC_Ident.string_of_id i
let (string_of_pragma : pragma -> Prims.string) =
  fun uu___ ->
    match uu___ with
    | ShowOptions -> "show-options"
    | SetOptions s -> FStarC_Compiler_Util.format1 "set-options \"%s\"" s
    | ResetOptions s ->
        FStarC_Compiler_Util.format1 "reset-options \"%s\""
          (FStarC_Compiler_Util.dflt "" s)
    | PushOptions s ->
        FStarC_Compiler_Util.format1 "push-options \"%s\""
          (FStarC_Compiler_Util.dflt "" s)
    | PopOptions -> "pop-options"
    | RestartSolver -> "restart-solver"
    | PrintEffectsGraph -> "print-effects-graph"
let (restriction_to_string :
  FStarC_Syntax_Syntax.restriction -> Prims.string) =
  fun uu___ ->
    match uu___ with
    | FStarC_Syntax_Syntax.Unrestricted -> ""
    | FStarC_Syntax_Syntax.AllowList allow_list ->
        let uu___1 =
          let uu___2 =
            let uu___3 =
              FStarC_Compiler_List.map
                (fun uu___4 ->
                   match uu___4 with
                   | (id, renamed) ->
                       let uu___5 = FStarC_Ident.string_of_id id in
                       let uu___6 =
                         let uu___7 =
                           FStarC_Compiler_Util.map_opt renamed
                             (fun renamed1 ->
                                let uu___8 =
                                  FStarC_Ident.string_of_id renamed1 in
                                Prims.strcat " as " uu___8) in
                         FStarC_Compiler_Util.dflt "" uu___7 in
                       Prims.strcat uu___5 uu___6) allow_list in
            FStarC_Compiler_String.concat ", " uu___3 in
          Prims.strcat uu___2 "}" in
        Prims.strcat " {" uu___1
let rec (decl_to_string : decl -> Prims.string) =
  fun d ->
    match d.d with
    | TopLevelModule l ->
        let uu___ = FStarC_Ident.string_of_lid l in
        Prims.strcat "module " uu___
    | Open (l, r) ->
        let uu___ =
          let uu___1 = FStarC_Ident.string_of_lid l in
          let uu___2 = restriction_to_string r in Prims.strcat uu___1 uu___2 in
        Prims.strcat "open " uu___
    | Friend l ->
        let uu___ = FStarC_Ident.string_of_lid l in
        Prims.strcat "friend " uu___
    | Include (l, r) ->
        let uu___ =
          let uu___1 = FStarC_Ident.string_of_lid l in
          let uu___2 = restriction_to_string r in Prims.strcat uu___1 uu___2 in
        Prims.strcat "include " uu___
    | ModuleAbbrev (i, l) ->
        let uu___ = FStarC_Ident.string_of_id i in
        let uu___1 = FStarC_Ident.string_of_lid l in
        FStarC_Compiler_Util.format2 "module %s = %s" uu___ uu___1
    | TopLevelLet (uu___, pats) ->
        let uu___1 =
          let uu___2 =
            let uu___3 = lids_of_let pats in
            FStarC_Compiler_List.map (fun l -> FStarC_Ident.string_of_lid l)
              uu___3 in
          FStarC_Compiler_String.concat ", " uu___2 in
        Prims.strcat "let " uu___1
    | Assume (i, uu___) ->
        let uu___1 = FStarC_Ident.string_of_id i in
        Prims.strcat "assume " uu___1
    | Tycon (uu___, uu___1, tys) ->
        let uu___2 =
          let uu___3 = FStarC_Compiler_List.map id_of_tycon tys in
          FStarC_Compiler_String.concat ", " uu___3 in
        Prims.strcat "type " uu___2
    | Val (i, uu___) ->
        let uu___1 = FStarC_Ident.string_of_id i in
        Prims.strcat "val " uu___1
    | Exception (i, uu___) ->
        let uu___1 = FStarC_Ident.string_of_id i in
        Prims.strcat "exception " uu___1
    | NewEffect (DefineEffect (i, uu___, uu___1, uu___2)) ->
        let uu___3 = FStarC_Ident.string_of_id i in
        Prims.strcat "new_effect " uu___3
    | NewEffect (RedefineEffect (i, uu___, uu___1)) ->
        let uu___2 = FStarC_Ident.string_of_id i in
        Prims.strcat "new_effect " uu___2
    | LayeredEffect (DefineEffect (i, uu___, uu___1, uu___2)) ->
        let uu___3 = FStarC_Ident.string_of_id i in
        Prims.strcat "layered_effect " uu___3
    | LayeredEffect (RedefineEffect (i, uu___, uu___1)) ->
        let uu___2 = FStarC_Ident.string_of_id i in
        Prims.strcat "layered_effect " uu___2
    | Polymonadic_bind (l1, l2, l3, uu___) ->
        let uu___1 = FStarC_Ident.string_of_lid l1 in
        let uu___2 = FStarC_Ident.string_of_lid l2 in
        let uu___3 = FStarC_Ident.string_of_lid l3 in
        FStarC_Compiler_Util.format3 "polymonadic_bind (%s, %s) |> %s" uu___1
          uu___2 uu___3
    | Polymonadic_subcomp (l1, l2, uu___) ->
        let uu___1 = FStarC_Ident.string_of_lid l1 in
        let uu___2 = FStarC_Ident.string_of_lid l2 in
        FStarC_Compiler_Util.format2 "polymonadic_subcomp %s <: %s" uu___1
          uu___2
    | Splice (is_typed, ids, t) ->
        let uu___ =
          let uu___1 =
            let uu___2 =
              let uu___3 =
                let uu___4 =
                  FStarC_Compiler_List.map
                    (fun i -> FStarC_Ident.string_of_id i) ids in
                FStarC_Compiler_String.concat ";" uu___4 in
              let uu___4 =
                let uu___5 =
                  let uu___6 = term_to_string t in Prims.strcat uu___6 ")" in
                Prims.strcat "] (" uu___5 in
              Prims.strcat uu___3 uu___4 in
            Prims.strcat "[" uu___2 in
          Prims.strcat (if is_typed then "_t" else "") uu___1 in
        Prims.strcat "splice" uu___
    | SubEffect uu___ -> "sub_effect"
    | Pragma p ->
        let uu___ = string_of_pragma p in Prims.strcat "pragma #" uu___
    | DeclSyntaxExtension (id, content, uu___, uu___1) ->
        Prims.strcat "```"
          (Prims.strcat id (Prims.strcat "\n" (Prims.strcat content "\n```")))
    | DeclToBeDesugared tbs ->
        let uu___ =
          let uu___1 = tbs.to_string tbs.blob in Prims.strcat uu___1 ")" in
        Prims.strcat "(to_be_desugared: " uu___
    | UseLangDecls str -> FStarC_Compiler_Util.format1 "#lang-%s" str
    | Unparseable -> "unparseable"
let (modul_to_string : modul -> Prims.string) =
  fun m ->
    match m with
    | Module (uu___, decls) ->
        let uu___1 = FStarC_Compiler_List.map decl_to_string decls in
        FStarC_Compiler_String.concat "\n" uu___1
    | Interface (uu___, decls, uu___1) ->
        let uu___2 = FStarC_Compiler_List.map decl_to_string decls in
        FStarC_Compiler_String.concat "\n" uu___2
let (decl_is_val : FStarC_Ident.ident -> decl -> Prims.bool) =
  fun id ->
    fun decl1 ->
      match decl1.d with
      | Val (id', uu___) -> FStarC_Ident.ident_equals id id'
      | uu___ -> false
let (thunk : term -> term) =
  fun ens ->
    let wildpat =
      mk_pattern (PatWild (FStar_Pervasives_Native.None, [])) ens.range in
    mk_term (Abs ([wildpat], ens)) ens.range Expr
let (ident_of_binder :
  FStarC_Compiler_Range_Type.range -> binder -> FStarC_Ident.ident) =
  fun r ->
    fun b ->
      match b.b with
      | Variable i -> i
      | TVariable i -> i
      | Annotated (i, uu___) -> i
      | TAnnotated (i, uu___) -> i
      | NoName uu___ ->
          FStarC_Errors.raise_error FStarC_Class_HasRange.hasRange_range r
            FStarC_Errors_Codes.Fatal_MissingQuantifierBinder ()
            (Obj.magic FStarC_Errors_Msg.is_error_message_string)
            (Obj.magic "Wildcard binders in quantifiers are not allowed")
let (idents_of_binders :
  binder Prims.list ->
    FStarC_Compiler_Range_Type.range -> FStarC_Ident.ident Prims.list)
  = fun bs -> fun r -> FStarC_Compiler_List.map (ident_of_binder r) bs
let (showable_decl : decl FStarC_Class_Show.showable) =
  { FStarC_Class_Show.show = decl_to_string }
let (showable_term : term FStarC_Class_Show.showable) =
  { FStarC_Class_Show.show = term_to_string }
let (add_decorations : decl -> decoration Prims.list -> decl) =
  fun d ->
    fun decorations ->
      let decorations1 =
        let uu___ =
          FStarC_Compiler_List.partition uu___is_DeclAttributes decorations in
        match uu___ with
        | (attrs, quals) ->
            let attrs1 =
              match (attrs, (d.attrs)) with
              | (attrs2, []) -> attrs2
              | ((DeclAttributes a)::[], attrs2) ->
                  [DeclAttributes (FStarC_Compiler_List.op_At a attrs2)]
              | ([], attrs2) -> [DeclAttributes attrs2]
              | uu___1 ->
                  let uu___2 =
                    let uu___3 =
                      let uu___4 =
                        FStarC_Compiler_List.map
                          (fun uu___5 ->
                             match uu___5 with
                             | DeclAttributes a ->
                                 FStarC_Class_Show.show
                                   (FStarC_Class_Show.show_list showable_term)
                                   a
                             | uu___6 -> "") attrs in
                      FStarC_Compiler_String.concat ", " uu___4 in
                    let uu___4 =
                      let uu___5 =
                        FStarC_Compiler_List.map
                          (FStarC_Class_Show.show showable_term) d.attrs in
                      FStarC_Compiler_String.concat ", " uu___5 in
                    FStarC_Compiler_Util.format2
                      "At most one attribute set is allowed on declarations\n got %s;\n and %s"
                      uu___3 uu___4 in
                  FStarC_Errors.raise_error hasRange_decl d
                    FStarC_Errors_Codes.Fatal_MoreThanOneDeclaration ()
                    (Obj.magic FStarC_Errors_Msg.is_error_message_string)
                    (Obj.magic uu___2) in
            let uu___1 =
              FStarC_Compiler_List.map (fun uu___2 -> Qualifier uu___2)
                d.quals in
            FStarC_Compiler_List.op_At uu___1
              (FStarC_Compiler_List.op_At quals attrs1) in
      let attributes_1 =
        let uu___ =
          FStarC_Compiler_List.choose
            (fun uu___1 ->
               match uu___1 with
               | DeclAttributes a -> FStar_Pervasives_Native.Some a
               | uu___2 -> FStar_Pervasives_Native.None) decorations1 in
        at_most_one "attribute set" d.drange uu___ in
      let attributes_2 = FStarC_Compiler_Util.dflt [] attributes_1 in
      let qualifiers1 =
        FStarC_Compiler_List.choose
          (fun uu___ ->
             match uu___ with
             | Qualifier q -> FStar_Pervasives_Native.Some q
             | uu___1 -> FStar_Pervasives_Native.None) decorations1 in
      {
        d = (d.d);
        drange = (d.drange);
        quals = qualifiers1;
        attrs = attributes_2;
        interleaved = (d.interleaved)
      }
let (mk_decl :
  decl' -> FStarC_Compiler_Range_Type.range -> decoration Prims.list -> decl)
  =
  fun d ->
    fun r ->
      fun decorations ->
        let d1 =
          { d; drange = r; quals = []; attrs = []; interleaved = false } in
        add_decorations d1 decorations