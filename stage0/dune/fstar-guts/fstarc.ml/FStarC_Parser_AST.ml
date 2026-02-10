open Prims
type level =
  | Un 
  | Expr 
  | Type_level 
  | Kind 
  | Formula 
let uu___is_Un (projectee : level) : Prims.bool=
  match projectee with | Un -> true | uu___ -> false
let uu___is_Expr (projectee : level) : Prims.bool=
  match projectee with | Expr -> true | uu___ -> false
let uu___is_Type_level (projectee : level) : Prims.bool=
  match projectee with | Type_level -> true | uu___ -> false
let uu___is_Kind (projectee : level) : Prims.bool=
  match projectee with | Kind -> true | uu___ -> false
let uu___is_Formula (projectee : level) : Prims.bool=
  match projectee with | Formula -> true | uu___ -> false
type let_qualifier =
  | NoLetQualifier 
  | Rec 
let uu___is_NoLetQualifier (projectee : let_qualifier) : Prims.bool=
  match projectee with | NoLetQualifier -> true | uu___ -> false
let uu___is_Rec (projectee : let_qualifier) : Prims.bool=
  match projectee with | Rec -> true | uu___ -> false
type local_let_qualifier =
  | LocalNoLetQualifier 
  | LocalRec 
  | LocalUnfold 
let uu___is_LocalNoLetQualifier (projectee : local_let_qualifier) :
  Prims.bool=
  match projectee with | LocalNoLetQualifier -> true | uu___ -> false
let uu___is_LocalRec (projectee : local_let_qualifier) : Prims.bool=
  match projectee with | LocalRec -> true | uu___ -> false
let uu___is_LocalUnfold (projectee : local_let_qualifier) : Prims.bool=
  match projectee with | LocalUnfold -> true | uu___ -> false
type quote_kind =
  | Static 
  | Dynamic 
let uu___is_Static (projectee : quote_kind) : Prims.bool=
  match projectee with | Static -> true | uu___ -> false
let uu___is_Dynamic (projectee : quote_kind) : Prims.bool=
  match projectee with | Dynamic -> true | uu___ -> false
type term' =
  | Wild 
  | Const of FStarC_Const.sconst 
  | Op of (FStarC_Ident.ident * term Prims.list) 
  | Uvar of FStarC_Ident.ident 
  | Var of FStarC_Ident.lid 
  | Name of FStarC_Ident.lid 
  | Projector of (FStarC_Ident.lid * FStarC_Ident.ident) 
  | Construct of (FStarC_Ident.lid * (term * imp) Prims.list) 
  | Abs of (pattern Prims.list * term) 
  | Function of ((pattern * term FStar_Pervasives_Native.option * term)
  Prims.list * FStarC_Range_Type.range) 
  | App of (term * term * imp) 
  | Let of (local_let_qualifier * (term Prims.list
  FStar_Pervasives_Native.option * (pattern * term)) Prims.list * term) 
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
  | Requires of term 
  | Ensures of term 
  | LexList of term Prims.list 
  | WFOrder of (term * term) 
  | Decreases of term 
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
  | LitDoc of FStar_Pprint.document 
and term = {
  tm: term' ;
  range: FStarC_Range_Type.range ;
  level: level }
and calc_step =
  | CalcStep of (term * term * term) 
and binder' =
  | Variable of FStarC_Ident.ident 
  | Annotated of (FStarC_Ident.ident * term) 
  | NoName of term 
and binder =
  {
  b: binder' ;
  brange: FStarC_Range_Type.range ;
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
  | PatList of pattern Prims.list 
  | PatRest 
  | PatTuple of (pattern Prims.list * Prims.bool) 
  | PatRecord of (FStarC_Ident.lid * pattern) Prims.list 
  | PatAscribed of (pattern * (term * term FStar_Pervasives_Native.option)) 
  | PatOr of pattern Prims.list 
  | PatOp of FStarC_Ident.ident 
  | PatVQuote of term 
and pattern = {
  pat: pattern' ;
  prange: FStarC_Range_Type.range }
and arg_qualifier =
  | Implicit 
  | Equality 
  | Meta of term 
  | TypeClassArg 
and imp =
  | Hash 
  | UnivApp 
  | HashBrace of term 
  | Infix 
  | Nothing 
let uu___is_Wild (projectee : term') : Prims.bool=
  match projectee with | Wild -> true | uu___ -> false
let uu___is_Const (projectee : term') : Prims.bool=
  match projectee with | Const _0 -> true | uu___ -> false
let __proj__Const__item___0 (projectee : term') : FStarC_Const.sconst=
  match projectee with | Const _0 -> _0
let uu___is_Op (projectee : term') : Prims.bool=
  match projectee with | Op _0 -> true | uu___ -> false
let __proj__Op__item___0 (projectee : term') :
  (FStarC_Ident.ident * term Prims.list)= match projectee with | Op _0 -> _0
let uu___is_Uvar (projectee : term') : Prims.bool=
  match projectee with | Uvar _0 -> true | uu___ -> false
let __proj__Uvar__item___0 (projectee : term') : FStarC_Ident.ident=
  match projectee with | Uvar _0 -> _0
let uu___is_Var (projectee : term') : Prims.bool=
  match projectee with | Var _0 -> true | uu___ -> false
let __proj__Var__item___0 (projectee : term') : FStarC_Ident.lid=
  match projectee with | Var _0 -> _0
let uu___is_Name (projectee : term') : Prims.bool=
  match projectee with | Name _0 -> true | uu___ -> false
let __proj__Name__item___0 (projectee : term') : FStarC_Ident.lid=
  match projectee with | Name _0 -> _0
let uu___is_Projector (projectee : term') : Prims.bool=
  match projectee with | Projector _0 -> true | uu___ -> false
let __proj__Projector__item___0 (projectee : term') :
  (FStarC_Ident.lid * FStarC_Ident.ident)=
  match projectee with | Projector _0 -> _0
let uu___is_Construct (projectee : term') : Prims.bool=
  match projectee with | Construct _0 -> true | uu___ -> false
let __proj__Construct__item___0 (projectee : term') :
  (FStarC_Ident.lid * (term * imp) Prims.list)=
  match projectee with | Construct _0 -> _0
let uu___is_Abs (projectee : term') : Prims.bool=
  match projectee with | Abs _0 -> true | uu___ -> false
let __proj__Abs__item___0 (projectee : term') : (pattern Prims.list * term)=
  match projectee with | Abs _0 -> _0
let uu___is_Function (projectee : term') : Prims.bool=
  match projectee with | Function _0 -> true | uu___ -> false
let __proj__Function__item___0 (projectee : term') :
  ((pattern * term FStar_Pervasives_Native.option * term) Prims.list *
    FStarC_Range_Type.range)=
  match projectee with | Function _0 -> _0
let uu___is_App (projectee : term') : Prims.bool=
  match projectee with | App _0 -> true | uu___ -> false
let __proj__App__item___0 (projectee : term') : (term * term * imp)=
  match projectee with | App _0 -> _0
let uu___is_Let (projectee : term') : Prims.bool=
  match projectee with | Let _0 -> true | uu___ -> false
let __proj__Let__item___0 (projectee : term') :
  (local_let_qualifier * (term Prims.list FStar_Pervasives_Native.option *
    (pattern * term)) Prims.list * term)=
  match projectee with | Let _0 -> _0
let uu___is_LetOperator (projectee : term') : Prims.bool=
  match projectee with | LetOperator _0 -> true | uu___ -> false
let __proj__LetOperator__item___0 (projectee : term') :
  ((FStarC_Ident.ident * pattern * term) Prims.list * term)=
  match projectee with | LetOperator _0 -> _0
let uu___is_LetOpen (projectee : term') : Prims.bool=
  match projectee with | LetOpen _0 -> true | uu___ -> false
let __proj__LetOpen__item___0 (projectee : term') :
  (FStarC_Ident.lid * term)= match projectee with | LetOpen _0 -> _0
let uu___is_LetOpenRecord (projectee : term') : Prims.bool=
  match projectee with | LetOpenRecord _0 -> true | uu___ -> false
let __proj__LetOpenRecord__item___0 (projectee : term') :
  (term * term * term)= match projectee with | LetOpenRecord _0 -> _0
let uu___is_Seq (projectee : term') : Prims.bool=
  match projectee with | Seq _0 -> true | uu___ -> false
let __proj__Seq__item___0 (projectee : term') : (term * term)=
  match projectee with | Seq _0 -> _0
let uu___is_Bind (projectee : term') : Prims.bool=
  match projectee with | Bind _0 -> true | uu___ -> false
let __proj__Bind__item___0 (projectee : term') :
  (FStarC_Ident.ident * term * term)= match projectee with | Bind _0 -> _0
let uu___is_If (projectee : term') : Prims.bool=
  match projectee with | If _0 -> true | uu___ -> false
let __proj__If__item___0 (projectee : term') :
  (term * FStarC_Ident.ident FStar_Pervasives_Native.option *
    (FStarC_Ident.ident FStar_Pervasives_Native.option * term * Prims.bool)
    FStar_Pervasives_Native.option * term * term)=
  match projectee with | If _0 -> _0
let uu___is_Match (projectee : term') : Prims.bool=
  match projectee with | Match _0 -> true | uu___ -> false
let __proj__Match__item___0 (projectee : term') :
  (term * FStarC_Ident.ident FStar_Pervasives_Native.option *
    (FStarC_Ident.ident FStar_Pervasives_Native.option * term * Prims.bool)
    FStar_Pervasives_Native.option * (pattern * term
    FStar_Pervasives_Native.option * term) Prims.list)=
  match projectee with | Match _0 -> _0
let uu___is_TryWith (projectee : term') : Prims.bool=
  match projectee with | TryWith _0 -> true | uu___ -> false
let __proj__TryWith__item___0 (projectee : term') :
  (term * (pattern * term FStar_Pervasives_Native.option * term) Prims.list)=
  match projectee with | TryWith _0 -> _0
let uu___is_Ascribed (projectee : term') : Prims.bool=
  match projectee with | Ascribed _0 -> true | uu___ -> false
let __proj__Ascribed__item___0 (projectee : term') :
  (term * term * term FStar_Pervasives_Native.option * Prims.bool)=
  match projectee with | Ascribed _0 -> _0
let uu___is_Record (projectee : term') : Prims.bool=
  match projectee with | Record _0 -> true | uu___ -> false
let __proj__Record__item___0 (projectee : term') :
  (term FStar_Pervasives_Native.option * (FStarC_Ident.lid * term)
    Prims.list)=
  match projectee with | Record _0 -> _0
let uu___is_Project (projectee : term') : Prims.bool=
  match projectee with | Project _0 -> true | uu___ -> false
let __proj__Project__item___0 (projectee : term') :
  (term * FStarC_Ident.lid)= match projectee with | Project _0 -> _0
let uu___is_Product (projectee : term') : Prims.bool=
  match projectee with | Product _0 -> true | uu___ -> false
let __proj__Product__item___0 (projectee : term') :
  (binder Prims.list * term)= match projectee with | Product _0 -> _0
let uu___is_Sum (projectee : term') : Prims.bool=
  match projectee with | Sum _0 -> true | uu___ -> false
let __proj__Sum__item___0 (projectee : term') :
  ((binder, term) FStar_Pervasives.either Prims.list * term)=
  match projectee with | Sum _0 -> _0
let uu___is_QForall (projectee : term') : Prims.bool=
  match projectee with | QForall _0 -> true | uu___ -> false
let __proj__QForall__item___0 (projectee : term') :
  (binder Prims.list * (FStarC_Ident.ident Prims.list * term Prims.list
    Prims.list) * term)=
  match projectee with | QForall _0 -> _0
let uu___is_QExists (projectee : term') : Prims.bool=
  match projectee with | QExists _0 -> true | uu___ -> false
let __proj__QExists__item___0 (projectee : term') :
  (binder Prims.list * (FStarC_Ident.ident Prims.list * term Prims.list
    Prims.list) * term)=
  match projectee with | QExists _0 -> _0
let uu___is_QuantOp (projectee : term') : Prims.bool=
  match projectee with | QuantOp _0 -> true | uu___ -> false
let __proj__QuantOp__item___0 (projectee : term') :
  (FStarC_Ident.ident * binder Prims.list * (FStarC_Ident.ident Prims.list *
    term Prims.list Prims.list) * term)=
  match projectee with | QuantOp _0 -> _0
let uu___is_Refine (projectee : term') : Prims.bool=
  match projectee with | Refine _0 -> true | uu___ -> false
let __proj__Refine__item___0 (projectee : term') : (binder * term)=
  match projectee with | Refine _0 -> _0
let uu___is_NamedTyp (projectee : term') : Prims.bool=
  match projectee with | NamedTyp _0 -> true | uu___ -> false
let __proj__NamedTyp__item___0 (projectee : term') :
  (FStarC_Ident.ident * term)= match projectee with | NamedTyp _0 -> _0
let uu___is_Paren (projectee : term') : Prims.bool=
  match projectee with | Paren _0 -> true | uu___ -> false
let __proj__Paren__item___0 (projectee : term') : term=
  match projectee with | Paren _0 -> _0
let uu___is_Requires (projectee : term') : Prims.bool=
  match projectee with | Requires _0 -> true | uu___ -> false
let __proj__Requires__item___0 (projectee : term') : term=
  match projectee with | Requires _0 -> _0
let uu___is_Ensures (projectee : term') : Prims.bool=
  match projectee with | Ensures _0 -> true | uu___ -> false
let __proj__Ensures__item___0 (projectee : term') : term=
  match projectee with | Ensures _0 -> _0
let uu___is_LexList (projectee : term') : Prims.bool=
  match projectee with | LexList _0 -> true | uu___ -> false
let __proj__LexList__item___0 (projectee : term') : term Prims.list=
  match projectee with | LexList _0 -> _0
let uu___is_WFOrder (projectee : term') : Prims.bool=
  match projectee with | WFOrder _0 -> true | uu___ -> false
let __proj__WFOrder__item___0 (projectee : term') : (term * term)=
  match projectee with | WFOrder _0 -> _0
let uu___is_Decreases (projectee : term') : Prims.bool=
  match projectee with | Decreases _0 -> true | uu___ -> false
let __proj__Decreases__item___0 (projectee : term') : term=
  match projectee with | Decreases _0 -> _0
let uu___is_Labeled (projectee : term') : Prims.bool=
  match projectee with | Labeled _0 -> true | uu___ -> false
let __proj__Labeled__item___0 (projectee : term') :
  (term * Prims.string * Prims.bool)= match projectee with | Labeled _0 -> _0
let uu___is_Discrim (projectee : term') : Prims.bool=
  match projectee with | Discrim _0 -> true | uu___ -> false
let __proj__Discrim__item___0 (projectee : term') : FStarC_Ident.lid=
  match projectee with | Discrim _0 -> _0
let uu___is_Attributes (projectee : term') : Prims.bool=
  match projectee with | Attributes _0 -> true | uu___ -> false
let __proj__Attributes__item___0 (projectee : term') : term Prims.list=
  match projectee with | Attributes _0 -> _0
let uu___is_Antiquote (projectee : term') : Prims.bool=
  match projectee with | Antiquote _0 -> true | uu___ -> false
let __proj__Antiquote__item___0 (projectee : term') : term=
  match projectee with | Antiquote _0 -> _0
let uu___is_Quote (projectee : term') : Prims.bool=
  match projectee with | Quote _0 -> true | uu___ -> false
let __proj__Quote__item___0 (projectee : term') : (term * quote_kind)=
  match projectee with | Quote _0 -> _0
let uu___is_VQuote (projectee : term') : Prims.bool=
  match projectee with | VQuote _0 -> true | uu___ -> false
let __proj__VQuote__item___0 (projectee : term') : term=
  match projectee with | VQuote _0 -> _0
let uu___is_CalcProof (projectee : term') : Prims.bool=
  match projectee with | CalcProof _0 -> true | uu___ -> false
let __proj__CalcProof__item___0 (projectee : term') :
  (term * term * calc_step Prims.list)=
  match projectee with | CalcProof _0 -> _0
let uu___is_IntroForall (projectee : term') : Prims.bool=
  match projectee with | IntroForall _0 -> true | uu___ -> false
let __proj__IntroForall__item___0 (projectee : term') :
  (binder Prims.list * term * term)=
  match projectee with | IntroForall _0 -> _0
let uu___is_IntroExists (projectee : term') : Prims.bool=
  match projectee with | IntroExists _0 -> true | uu___ -> false
let __proj__IntroExists__item___0 (projectee : term') :
  (binder Prims.list * term * term Prims.list * term)=
  match projectee with | IntroExists _0 -> _0
let uu___is_IntroImplies (projectee : term') : Prims.bool=
  match projectee with | IntroImplies _0 -> true | uu___ -> false
let __proj__IntroImplies__item___0 (projectee : term') :
  (term * term * binder * term)= match projectee with | IntroImplies _0 -> _0
let uu___is_IntroOr (projectee : term') : Prims.bool=
  match projectee with | IntroOr _0 -> true | uu___ -> false
let __proj__IntroOr__item___0 (projectee : term') :
  (Prims.bool * term * term * term)= match projectee with | IntroOr _0 -> _0
let uu___is_IntroAnd (projectee : term') : Prims.bool=
  match projectee with | IntroAnd _0 -> true | uu___ -> false
let __proj__IntroAnd__item___0 (projectee : term') :
  (term * term * term * term)= match projectee with | IntroAnd _0 -> _0
let uu___is_ElimForall (projectee : term') : Prims.bool=
  match projectee with | ElimForall _0 -> true | uu___ -> false
let __proj__ElimForall__item___0 (projectee : term') :
  (binder Prims.list * term * term Prims.list)=
  match projectee with | ElimForall _0 -> _0
let uu___is_ElimExists (projectee : term') : Prims.bool=
  match projectee with | ElimExists _0 -> true | uu___ -> false
let __proj__ElimExists__item___0 (projectee : term') :
  (binder Prims.list * term * term * binder * term)=
  match projectee with | ElimExists _0 -> _0
let uu___is_ElimImplies (projectee : term') : Prims.bool=
  match projectee with | ElimImplies _0 -> true | uu___ -> false
let __proj__ElimImplies__item___0 (projectee : term') : (term * term * term)=
  match projectee with | ElimImplies _0 -> _0
let uu___is_ElimOr (projectee : term') : Prims.bool=
  match projectee with | ElimOr _0 -> true | uu___ -> false
let __proj__ElimOr__item___0 (projectee : term') :
  (term * term * term * binder * term * binder * term)=
  match projectee with | ElimOr _0 -> _0
let uu___is_ElimAnd (projectee : term') : Prims.bool=
  match projectee with | ElimAnd _0 -> true | uu___ -> false
let __proj__ElimAnd__item___0 (projectee : term') :
  (term * term * term * binder * binder * term)=
  match projectee with | ElimAnd _0 -> _0
let uu___is_ListLiteral (projectee : term') : Prims.bool=
  match projectee with | ListLiteral _0 -> true | uu___ -> false
let __proj__ListLiteral__item___0 (projectee : term') : term Prims.list=
  match projectee with | ListLiteral _0 -> _0
let uu___is_SeqLiteral (projectee : term') : Prims.bool=
  match projectee with | SeqLiteral _0 -> true | uu___ -> false
let __proj__SeqLiteral__item___0 (projectee : term') : term Prims.list=
  match projectee with | SeqLiteral _0 -> _0
let uu___is_LitDoc (projectee : term') : Prims.bool=
  match projectee with | LitDoc _0 -> true | uu___ -> false
let __proj__LitDoc__item___0 (projectee : term') : FStar_Pprint.document=
  match projectee with | LitDoc _0 -> _0
let __proj__Mkterm__item__tm (projectee : term) : term'=
  match projectee with | { tm; range; level = level1;_} -> tm
let __proj__Mkterm__item__range (projectee : term) : FStarC_Range_Type.range=
  match projectee with | { tm; range; level = level1;_} -> range
let __proj__Mkterm__item__level (projectee : term) : level=
  match projectee with | { tm; range; level = level1;_} -> level1
let uu___is_CalcStep (projectee : calc_step) : Prims.bool= true
let __proj__CalcStep__item___0 (projectee : calc_step) :
  (term * term * term)= match projectee with | CalcStep _0 -> _0
let uu___is_Variable (projectee : binder') : Prims.bool=
  match projectee with | Variable _0 -> true | uu___ -> false
let __proj__Variable__item___0 (projectee : binder') : FStarC_Ident.ident=
  match projectee with | Variable _0 -> _0
let uu___is_Annotated (projectee : binder') : Prims.bool=
  match projectee with | Annotated _0 -> true | uu___ -> false
let __proj__Annotated__item___0 (projectee : binder') :
  (FStarC_Ident.ident * term)= match projectee with | Annotated _0 -> _0
let uu___is_NoName (projectee : binder') : Prims.bool=
  match projectee with | NoName _0 -> true | uu___ -> false
let __proj__NoName__item___0 (projectee : binder') : term=
  match projectee with | NoName _0 -> _0
let __proj__Mkbinder__item__b (projectee : binder) : binder'=
  match projectee with | { b; brange; blevel; aqual; battributes;_} -> b
let __proj__Mkbinder__item__brange (projectee : binder) :
  FStarC_Range_Type.range=
  match projectee with | { b; brange; blevel; aqual; battributes;_} -> brange
let __proj__Mkbinder__item__blevel (projectee : binder) : level=
  match projectee with | { b; brange; blevel; aqual; battributes;_} -> blevel
let __proj__Mkbinder__item__aqual (projectee : binder) :
  arg_qualifier FStar_Pervasives_Native.option=
  match projectee with | { b; brange; blevel; aqual; battributes;_} -> aqual
let __proj__Mkbinder__item__battributes (projectee : binder) :
  term Prims.list=
  match projectee with
  | { b; brange; blevel; aqual; battributes;_} -> battributes
let uu___is_PatWild (projectee : pattern') : Prims.bool=
  match projectee with | PatWild _0 -> true | uu___ -> false
let __proj__PatWild__item___0 (projectee : pattern') :
  (arg_qualifier FStar_Pervasives_Native.option * term Prims.list)=
  match projectee with | PatWild _0 -> _0
let uu___is_PatConst (projectee : pattern') : Prims.bool=
  match projectee with | PatConst _0 -> true | uu___ -> false
let __proj__PatConst__item___0 (projectee : pattern') : FStarC_Const.sconst=
  match projectee with | PatConst _0 -> _0
let uu___is_PatApp (projectee : pattern') : Prims.bool=
  match projectee with | PatApp _0 -> true | uu___ -> false
let __proj__PatApp__item___0 (projectee : pattern') :
  (pattern * pattern Prims.list)= match projectee with | PatApp _0 -> _0
let uu___is_PatVar (projectee : pattern') : Prims.bool=
  match projectee with | PatVar _0 -> true | uu___ -> false
let __proj__PatVar__item___0 (projectee : pattern') :
  (FStarC_Ident.ident * arg_qualifier FStar_Pervasives_Native.option * term
    Prims.list)=
  match projectee with | PatVar _0 -> _0
let uu___is_PatName (projectee : pattern') : Prims.bool=
  match projectee with | PatName _0 -> true | uu___ -> false
let __proj__PatName__item___0 (projectee : pattern') : FStarC_Ident.lid=
  match projectee with | PatName _0 -> _0
let uu___is_PatList (projectee : pattern') : Prims.bool=
  match projectee with | PatList _0 -> true | uu___ -> false
let __proj__PatList__item___0 (projectee : pattern') : pattern Prims.list=
  match projectee with | PatList _0 -> _0
let uu___is_PatRest (projectee : pattern') : Prims.bool=
  match projectee with | PatRest -> true | uu___ -> false
let uu___is_PatTuple (projectee : pattern') : Prims.bool=
  match projectee with | PatTuple _0 -> true | uu___ -> false
let __proj__PatTuple__item___0 (projectee : pattern') :
  (pattern Prims.list * Prims.bool)= match projectee with | PatTuple _0 -> _0
let uu___is_PatRecord (projectee : pattern') : Prims.bool=
  match projectee with | PatRecord _0 -> true | uu___ -> false
let __proj__PatRecord__item___0 (projectee : pattern') :
  (FStarC_Ident.lid * pattern) Prims.list=
  match projectee with | PatRecord _0 -> _0
let uu___is_PatAscribed (projectee : pattern') : Prims.bool=
  match projectee with | PatAscribed _0 -> true | uu___ -> false
let __proj__PatAscribed__item___0 (projectee : pattern') :
  (pattern * (term * term FStar_Pervasives_Native.option))=
  match projectee with | PatAscribed _0 -> _0
let uu___is_PatOr (projectee : pattern') : Prims.bool=
  match projectee with | PatOr _0 -> true | uu___ -> false
let __proj__PatOr__item___0 (projectee : pattern') : pattern Prims.list=
  match projectee with | PatOr _0 -> _0
let uu___is_PatOp (projectee : pattern') : Prims.bool=
  match projectee with | PatOp _0 -> true | uu___ -> false
let __proj__PatOp__item___0 (projectee : pattern') : FStarC_Ident.ident=
  match projectee with | PatOp _0 -> _0
let uu___is_PatVQuote (projectee : pattern') : Prims.bool=
  match projectee with | PatVQuote _0 -> true | uu___ -> false
let __proj__PatVQuote__item___0 (projectee : pattern') : term=
  match projectee with | PatVQuote _0 -> _0
let __proj__Mkpattern__item__pat (projectee : pattern) : pattern'=
  match projectee with | { pat; prange;_} -> pat
let __proj__Mkpattern__item__prange (projectee : pattern) :
  FStarC_Range_Type.range= match projectee with | { pat; prange;_} -> prange
let uu___is_Implicit (projectee : arg_qualifier) : Prims.bool=
  match projectee with | Implicit -> true | uu___ -> false
let uu___is_Equality (projectee : arg_qualifier) : Prims.bool=
  match projectee with | Equality -> true | uu___ -> false
let uu___is_Meta (projectee : arg_qualifier) : Prims.bool=
  match projectee with | Meta _0 -> true | uu___ -> false
let __proj__Meta__item___0 (projectee : arg_qualifier) : term=
  match projectee with | Meta _0 -> _0
let uu___is_TypeClassArg (projectee : arg_qualifier) : Prims.bool=
  match projectee with | TypeClassArg -> true | uu___ -> false
let uu___is_Hash (projectee : imp) : Prims.bool=
  match projectee with | Hash -> true | uu___ -> false
let uu___is_UnivApp (projectee : imp) : Prims.bool=
  match projectee with | UnivApp -> true | uu___ -> false
let uu___is_HashBrace (projectee : imp) : Prims.bool=
  match projectee with | HashBrace _0 -> true | uu___ -> false
let __proj__HashBrace__item___0 (projectee : imp) : term=
  match projectee with | HashBrace _0 -> _0
let uu___is_Infix (projectee : imp) : Prims.bool=
  match projectee with | Infix -> true | uu___ -> false
let uu___is_Nothing (projectee : imp) : Prims.bool=
  match projectee with | Nothing -> true | uu___ -> false
type match_returns_annotation =
  (FStarC_Ident.ident FStar_Pervasives_Native.option * term * Prims.bool)
type patterns = (FStarC_Ident.ident Prims.list * term Prims.list Prims.list)
type attributes_ = term Prims.list
type branch = (pattern * term FStar_Pervasives_Native.option * term)
type aqual = arg_qualifier FStar_Pervasives_Native.option
let tagged_term : term FStarC_Class_Tagged.tagged=
  {
    FStarC_Class_Tagged.tag_of =
      (fun t ->
         match t.tm with
         | Wild -> "Wild"
         | Const uu___ -> "Const"
         | Op uu___ -> "Op"
         | Uvar uu___ -> "Uvar"
         | Var uu___ -> "Var"
         | Name uu___ -> "Name"
         | Projector uu___ -> "Projector"
         | Construct uu___ -> "Construct"
         | Abs uu___ -> "Abs"
         | Function uu___ -> "Function"
         | App uu___ -> "App"
         | Let uu___ -> "Let"
         | LetOperator uu___ -> "LetOperator"
         | LetOpen uu___ -> "LetOpen"
         | LetOpenRecord uu___ -> "LetOpenRecord"
         | Seq uu___ -> "Seq"
         | Bind uu___ -> "Bind"
         | If uu___ -> "If"
         | Match uu___ -> "Match"
         | TryWith uu___ -> "TryWith"
         | Ascribed uu___ -> "Ascribed"
         | Record uu___ -> "Record"
         | Project uu___ -> "Project"
         | Product uu___ -> "Product"
         | Sum uu___ -> "Sum"
         | QForall uu___ -> "QForall"
         | QExists uu___ -> "QExists"
         | QuantOp uu___ -> "QuantOp"
         | Refine uu___ -> "Refine"
         | NamedTyp uu___ -> "NamedTyp"
         | Paren uu___ -> "Paren"
         | Requires uu___ -> "Requires"
         | Ensures uu___ -> "Ensures"
         | LexList uu___ -> "LexList"
         | WFOrder uu___ -> "WFOrder"
         | Decreases uu___ -> "Decreases"
         | Labeled uu___ -> "Labeled"
         | Discrim uu___ -> "Discrim"
         | Attributes uu___ -> "Attributes"
         | Antiquote uu___ -> "Antiquote"
         | Quote uu___ -> "Quote"
         | VQuote uu___ -> "VQuote"
         | CalcProof uu___ -> "CalcProof"
         | IntroForall uu___ -> "IntroForall"
         | IntroExists uu___ -> "IntroExists"
         | IntroImplies uu___ -> "IntroImplies"
         | IntroOr uu___ -> "IntroOr"
         | IntroAnd uu___ -> "IntroAnd"
         | ElimForall uu___ -> "ElimForall"
         | ElimExists uu___ -> "ElimExists"
         | ElimImplies uu___ -> "ElimImplies"
         | ElimOr uu___ -> "ElimOr"
         | ElimAnd uu___ -> "ElimAnd"
         | ListLiteral uu___ -> "ListLiteral"
         | SeqLiteral uu___ -> "SeqLiteral"
         | LitDoc uu___ -> "LitDoc")
  }
let hasRange_term : term FStarC_Class_HasRange.hasRange=
  {
    FStarC_Class_HasRange.pos = (fun t -> t.range);
    FStarC_Class_HasRange.setPos =
      (fun r t -> { tm = (t.tm); range = r; level = (t.level) })
  }
let hasRange_pattern : pattern FStarC_Class_HasRange.hasRange=
  {
    FStarC_Class_HasRange.pos = (fun p -> p.prange);
    FStarC_Class_HasRange.setPos = (fun r p -> { pat = (p.pat); prange = r })
  }
let hasRange_binder : binder FStarC_Class_HasRange.hasRange=
  {
    FStarC_Class_HasRange.pos = (fun b -> b.brange);
    FStarC_Class_HasRange.setPos =
      (fun r b ->
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
let uu___is_VpOfNotation (projectee : constructor_payload) : Prims.bool=
  match projectee with | VpOfNotation _0 -> true | uu___ -> false
let __proj__VpOfNotation__item___0 (projectee : constructor_payload) : 
  typ= match projectee with | VpOfNotation _0 -> _0
let uu___is_VpArbitrary (projectee : constructor_payload) : Prims.bool=
  match projectee with | VpArbitrary _0 -> true | uu___ -> false
let __proj__VpArbitrary__item___0 (projectee : constructor_payload) : 
  typ= match projectee with | VpArbitrary _0 -> _0
let uu___is_VpRecord (projectee : constructor_payload) : Prims.bool=
  match projectee with | VpRecord _0 -> true | uu___ -> false
let __proj__VpRecord__item___0 (projectee : constructor_payload) :
  (tycon_record * typ FStar_Pervasives_Native.option)=
  match projectee with | VpRecord _0 -> _0
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
let uu___is_TyconAbstract (projectee : tycon) : Prims.bool=
  match projectee with | TyconAbstract _0 -> true | uu___ -> false
let __proj__TyconAbstract__item___0 (projectee : tycon) :
  (FStarC_Ident.ident * binder Prims.list * knd
    FStar_Pervasives_Native.option)=
  match projectee with | TyconAbstract _0 -> _0
let uu___is_TyconAbbrev (projectee : tycon) : Prims.bool=
  match projectee with | TyconAbbrev _0 -> true | uu___ -> false
let __proj__TyconAbbrev__item___0 (projectee : tycon) :
  (FStarC_Ident.ident * binder Prims.list * knd
    FStar_Pervasives_Native.option * term)=
  match projectee with | TyconAbbrev _0 -> _0
let uu___is_TyconRecord (projectee : tycon) : Prims.bool=
  match projectee with | TyconRecord _0 -> true | uu___ -> false
let __proj__TyconRecord__item___0 (projectee : tycon) :
  (FStarC_Ident.ident * binder Prims.list * knd
    FStar_Pervasives_Native.option * attributes_ * tycon_record)=
  match projectee with | TyconRecord _0 -> _0
let uu___is_TyconVariant (projectee : tycon) : Prims.bool=
  match projectee with | TyconVariant _0 -> true | uu___ -> false
let __proj__TyconVariant__item___0 (projectee : tycon) :
  (FStarC_Ident.ident * binder Prims.list * knd
    FStar_Pervasives_Native.option * (FStarC_Ident.ident *
    constructor_payload FStar_Pervasives_Native.option * attributes_)
    Prims.list)=
  match projectee with | TyconVariant _0 -> _0
type qualifier =
  | Private 
  | Noeq 
  | Unopteq 
  | Assumption 
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
let uu___is_Private (projectee : qualifier) : Prims.bool=
  match projectee with | Private -> true | uu___ -> false
let uu___is_Noeq (projectee : qualifier) : Prims.bool=
  match projectee with | Noeq -> true | uu___ -> false
let uu___is_Unopteq (projectee : qualifier) : Prims.bool=
  match projectee with | Unopteq -> true | uu___ -> false
let uu___is_Assumption (projectee : qualifier) : Prims.bool=
  match projectee with | Assumption -> true | uu___ -> false
let uu___is_TotalEffect (projectee : qualifier) : Prims.bool=
  match projectee with | TotalEffect -> true | uu___ -> false
let uu___is_Effect_qual (projectee : qualifier) : Prims.bool=
  match projectee with | Effect_qual -> true | uu___ -> false
let uu___is_New (projectee : qualifier) : Prims.bool=
  match projectee with | New -> true | uu___ -> false
let uu___is_Inline (projectee : qualifier) : Prims.bool=
  match projectee with | Inline -> true | uu___ -> false
let uu___is_Visible (projectee : qualifier) : Prims.bool=
  match projectee with | Visible -> true | uu___ -> false
let uu___is_Unfold_for_unification_and_vcgen (projectee : qualifier) :
  Prims.bool=
  match projectee with
  | Unfold_for_unification_and_vcgen -> true
  | uu___ -> false
let uu___is_Inline_for_extraction (projectee : qualifier) : Prims.bool=
  match projectee with | Inline_for_extraction -> true | uu___ -> false
let uu___is_Irreducible (projectee : qualifier) : Prims.bool=
  match projectee with | Irreducible -> true | uu___ -> false
let uu___is_NoExtract (projectee : qualifier) : Prims.bool=
  match projectee with | NoExtract -> true | uu___ -> false
let uu___is_Reifiable (projectee : qualifier) : Prims.bool=
  match projectee with | Reifiable -> true | uu___ -> false
let uu___is_Reflectable (projectee : qualifier) : Prims.bool=
  match projectee with | Reflectable -> true | uu___ -> false
let uu___is_Opaque (projectee : qualifier) : Prims.bool=
  match projectee with | Opaque -> true | uu___ -> false
let uu___is_Logic (projectee : qualifier) : Prims.bool=
  match projectee with | Logic -> true | uu___ -> false
type qualifiers = qualifier Prims.list
type decoration =
  | Qualifier of qualifier 
  | DeclAttributes of term Prims.list 
let uu___is_Qualifier (projectee : decoration) : Prims.bool=
  match projectee with | Qualifier _0 -> true | uu___ -> false
let __proj__Qualifier__item___0 (projectee : decoration) : qualifier=
  match projectee with | Qualifier _0 -> _0
let uu___is_DeclAttributes (projectee : decoration) : Prims.bool=
  match projectee with | DeclAttributes _0 -> true | uu___ -> false
let __proj__DeclAttributes__item___0 (projectee : decoration) :
  term Prims.list= match projectee with | DeclAttributes _0 -> _0
type lift_op =
  | NonReifiableLift of term 
  | ReifiableLift of (term * term) 
  | LiftForFree of term 
let uu___is_NonReifiableLift (projectee : lift_op) : Prims.bool=
  match projectee with | NonReifiableLift _0 -> true | uu___ -> false
let __proj__NonReifiableLift__item___0 (projectee : lift_op) : term=
  match projectee with | NonReifiableLift _0 -> _0
let uu___is_ReifiableLift (projectee : lift_op) : Prims.bool=
  match projectee with | ReifiableLift _0 -> true | uu___ -> false
let __proj__ReifiableLift__item___0 (projectee : lift_op) : (term * term)=
  match projectee with | ReifiableLift _0 -> _0
let uu___is_LiftForFree (projectee : lift_op) : Prims.bool=
  match projectee with | LiftForFree _0 -> true | uu___ -> false
let __proj__LiftForFree__item___0 (projectee : lift_op) : term=
  match projectee with | LiftForFree _0 -> _0
type lift =
  {
  msource: FStarC_Ident.lid ;
  mdest: FStarC_Ident.lid ;
  lift_op: lift_op ;
  braced: Prims.bool }
let __proj__Mklift__item__msource (projectee : lift) : FStarC_Ident.lid=
  match projectee with
  | { msource; mdest; lift_op = lift_op1; braced;_} -> msource
let __proj__Mklift__item__mdest (projectee : lift) : FStarC_Ident.lid=
  match projectee with
  | { msource; mdest; lift_op = lift_op1; braced;_} -> mdest
let __proj__Mklift__item__lift_op (projectee : lift) : lift_op=
  match projectee with
  | { msource; mdest; lift_op = lift_op1; braced;_} -> lift_op1
let __proj__Mklift__item__braced (projectee : lift) : Prims.bool=
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
  | Check of term 
let uu___is_ShowOptions (projectee : pragma) : Prims.bool=
  match projectee with | ShowOptions -> true | uu___ -> false
let uu___is_SetOptions (projectee : pragma) : Prims.bool=
  match projectee with | SetOptions _0 -> true | uu___ -> false
let __proj__SetOptions__item___0 (projectee : pragma) : Prims.string=
  match projectee with | SetOptions _0 -> _0
let uu___is_ResetOptions (projectee : pragma) : Prims.bool=
  match projectee with | ResetOptions _0 -> true | uu___ -> false
let __proj__ResetOptions__item___0 (projectee : pragma) :
  Prims.string FStar_Pervasives_Native.option=
  match projectee with | ResetOptions _0 -> _0
let uu___is_PushOptions (projectee : pragma) : Prims.bool=
  match projectee with | PushOptions _0 -> true | uu___ -> false
let __proj__PushOptions__item___0 (projectee : pragma) :
  Prims.string FStar_Pervasives_Native.option=
  match projectee with | PushOptions _0 -> _0
let uu___is_PopOptions (projectee : pragma) : Prims.bool=
  match projectee with | PopOptions -> true | uu___ -> false
let uu___is_RestartSolver (projectee : pragma) : Prims.bool=
  match projectee with | RestartSolver -> true | uu___ -> false
let uu___is_PrintEffectsGraph (projectee : pragma) : Prims.bool=
  match projectee with | PrintEffectsGraph -> true | uu___ -> false
let uu___is_Check (projectee : pragma) : Prims.bool=
  match projectee with | Check _0 -> true | uu___ -> false
let __proj__Check__item___0 (projectee : pragma) : term=
  match projectee with | Check _0 -> _0
type dep_scan_callbacks =
  {
  scan_term: term -> unit ;
  scan_binder: binder -> unit ;
  scan_pattern: pattern -> unit ;
  add_lident: FStarC_Ident.lident -> unit ;
  add_open: FStarC_Ident.lident -> unit }
let __proj__Mkdep_scan_callbacks__item__scan_term
  (projectee : dep_scan_callbacks) : term -> unit=
  match projectee with
  | { scan_term; scan_binder; scan_pattern; add_lident; add_open;_} ->
      scan_term
let __proj__Mkdep_scan_callbacks__item__scan_binder
  (projectee : dep_scan_callbacks) : binder -> unit=
  match projectee with
  | { scan_term; scan_binder; scan_pattern; add_lident; add_open;_} ->
      scan_binder
let __proj__Mkdep_scan_callbacks__item__scan_pattern
  (projectee : dep_scan_callbacks) : pattern -> unit=
  match projectee with
  | { scan_term; scan_binder; scan_pattern; add_lident; add_open;_} ->
      scan_pattern
let __proj__Mkdep_scan_callbacks__item__add_lident
  (projectee : dep_scan_callbacks) : FStarC_Ident.lident -> unit=
  match projectee with
  | { scan_term; scan_binder; scan_pattern; add_lident; add_open;_} ->
      add_lident
let __proj__Mkdep_scan_callbacks__item__add_open
  (projectee : dep_scan_callbacks) : FStarC_Ident.lident -> unit=
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
let __proj__Mkto_be_desugared__item__lang_name (projectee : to_be_desugared)
  : Prims.string=
  match projectee with
  | { lang_name; blob; idents; to_string; eq; dep_scan;_} -> lang_name
let __proj__Mkto_be_desugared__item__blob (projectee : to_be_desugared) :
  FStarC_Dyn.dyn=
  match projectee with
  | { lang_name; blob; idents; to_string; eq; dep_scan;_} -> blob
let __proj__Mkto_be_desugared__item__idents (projectee : to_be_desugared) :
  FStarC_Ident.ident Prims.list=
  match projectee with
  | { lang_name; blob; idents; to_string; eq; dep_scan;_} -> idents
let __proj__Mkto_be_desugared__item__to_string (projectee : to_be_desugared)
  : FStarC_Dyn.dyn -> Prims.string=
  match projectee with
  | { lang_name; blob; idents; to_string; eq; dep_scan;_} -> to_string
let __proj__Mkto_be_desugared__item__eq (projectee : to_be_desugared) :
  FStarC_Dyn.dyn -> FStarC_Dyn.dyn -> Prims.bool=
  match projectee with
  | { lang_name; blob; idents; to_string; eq; dep_scan;_} -> eq
let __proj__Mkto_be_desugared__item__dep_scan (projectee : to_be_desugared) :
  dep_scan_callbacks -> FStarC_Dyn.dyn -> unit=
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
  FStarC_Range_Type.range * FStarC_Range_Type.range) 
  | UseLangDecls of Prims.string 
  | DeclToBeDesugared of to_be_desugared 
  | Unparseable 
and decl =
  {
  d: decl' ;
  drange: FStarC_Range_Type.range ;
  quals: qualifiers ;
  attrs: attributes_ ;
  interleaved: Prims.bool }
and effect_decl =
  | DefineEffect of (FStarC_Ident.ident * binder Prims.list * term * decl
  Prims.list) 
  | RedefineEffect of (FStarC_Ident.ident * binder Prims.list * term) 
let uu___is_TopLevelModule (projectee : decl') : Prims.bool=
  match projectee with | TopLevelModule _0 -> true | uu___ -> false
let __proj__TopLevelModule__item___0 (projectee : decl') : FStarC_Ident.lid=
  match projectee with | TopLevelModule _0 -> _0
let uu___is_Open (projectee : decl') : Prims.bool=
  match projectee with | Open _0 -> true | uu___ -> false
let __proj__Open__item___0 (projectee : decl') :
  (FStarC_Ident.lid * FStarC_Syntax_Syntax.restriction)=
  match projectee with | Open _0 -> _0
let uu___is_Friend (projectee : decl') : Prims.bool=
  match projectee with | Friend _0 -> true | uu___ -> false
let __proj__Friend__item___0 (projectee : decl') : FStarC_Ident.lid=
  match projectee with | Friend _0 -> _0
let uu___is_Include (projectee : decl') : Prims.bool=
  match projectee with | Include _0 -> true | uu___ -> false
let __proj__Include__item___0 (projectee : decl') :
  (FStarC_Ident.lid * FStarC_Syntax_Syntax.restriction)=
  match projectee with | Include _0 -> _0
let uu___is_ModuleAbbrev (projectee : decl') : Prims.bool=
  match projectee with | ModuleAbbrev _0 -> true | uu___ -> false
let __proj__ModuleAbbrev__item___0 (projectee : decl') :
  (FStarC_Ident.ident * FStarC_Ident.lid)=
  match projectee with | ModuleAbbrev _0 -> _0
let uu___is_TopLevelLet (projectee : decl') : Prims.bool=
  match projectee with | TopLevelLet _0 -> true | uu___ -> false
let __proj__TopLevelLet__item___0 (projectee : decl') :
  (let_qualifier * (pattern * term) Prims.list)=
  match projectee with | TopLevelLet _0 -> _0
let uu___is_Tycon (projectee : decl') : Prims.bool=
  match projectee with | Tycon _0 -> true | uu___ -> false
let __proj__Tycon__item___0 (projectee : decl') :
  (Prims.bool * Prims.bool * tycon Prims.list)=
  match projectee with | Tycon _0 -> _0
let uu___is_Val (projectee : decl') : Prims.bool=
  match projectee with | Val _0 -> true | uu___ -> false
let __proj__Val__item___0 (projectee : decl') : (FStarC_Ident.ident * term)=
  match projectee with | Val _0 -> _0
let uu___is_Exception (projectee : decl') : Prims.bool=
  match projectee with | Exception _0 -> true | uu___ -> false
let __proj__Exception__item___0 (projectee : decl') :
  (FStarC_Ident.ident * term FStar_Pervasives_Native.option)=
  match projectee with | Exception _0 -> _0
let uu___is_NewEffect (projectee : decl') : Prims.bool=
  match projectee with | NewEffect _0 -> true | uu___ -> false
let __proj__NewEffect__item___0 (projectee : decl') : effect_decl=
  match projectee with | NewEffect _0 -> _0
let uu___is_LayeredEffect (projectee : decl') : Prims.bool=
  match projectee with | LayeredEffect _0 -> true | uu___ -> false
let __proj__LayeredEffect__item___0 (projectee : decl') : effect_decl=
  match projectee with | LayeredEffect _0 -> _0
let uu___is_SubEffect (projectee : decl') : Prims.bool=
  match projectee with | SubEffect _0 -> true | uu___ -> false
let __proj__SubEffect__item___0 (projectee : decl') : lift=
  match projectee with | SubEffect _0 -> _0
let uu___is_Polymonadic_bind (projectee : decl') : Prims.bool=
  match projectee with | Polymonadic_bind _0 -> true | uu___ -> false
let __proj__Polymonadic_bind__item___0 (projectee : decl') :
  (FStarC_Ident.lid * FStarC_Ident.lid * FStarC_Ident.lid * term)=
  match projectee with | Polymonadic_bind _0 -> _0
let uu___is_Polymonadic_subcomp (projectee : decl') : Prims.bool=
  match projectee with | Polymonadic_subcomp _0 -> true | uu___ -> false
let __proj__Polymonadic_subcomp__item___0 (projectee : decl') :
  (FStarC_Ident.lid * FStarC_Ident.lid * term)=
  match projectee with | Polymonadic_subcomp _0 -> _0
let uu___is_Pragma (projectee : decl') : Prims.bool=
  match projectee with | Pragma _0 -> true | uu___ -> false
let __proj__Pragma__item___0 (projectee : decl') : pragma=
  match projectee with | Pragma _0 -> _0
let uu___is_Assume (projectee : decl') : Prims.bool=
  match projectee with | Assume _0 -> true | uu___ -> false
let __proj__Assume__item___0 (projectee : decl') :
  (FStarC_Ident.ident * term)= match projectee with | Assume _0 -> _0
let uu___is_Splice (projectee : decl') : Prims.bool=
  match projectee with | Splice _0 -> true | uu___ -> false
let __proj__Splice__item___0 (projectee : decl') :
  (Prims.bool * FStarC_Ident.ident Prims.list * term)=
  match projectee with | Splice _0 -> _0
let uu___is_DeclSyntaxExtension (projectee : decl') : Prims.bool=
  match projectee with | DeclSyntaxExtension _0 -> true | uu___ -> false
let __proj__DeclSyntaxExtension__item___0 (projectee : decl') :
  (Prims.string * Prims.string * FStarC_Range_Type.range *
    FStarC_Range_Type.range)=
  match projectee with | DeclSyntaxExtension _0 -> _0
let uu___is_UseLangDecls (projectee : decl') : Prims.bool=
  match projectee with | UseLangDecls _0 -> true | uu___ -> false
let __proj__UseLangDecls__item___0 (projectee : decl') : Prims.string=
  match projectee with | UseLangDecls _0 -> _0
let uu___is_DeclToBeDesugared (projectee : decl') : Prims.bool=
  match projectee with | DeclToBeDesugared _0 -> true | uu___ -> false
let __proj__DeclToBeDesugared__item___0 (projectee : decl') :
  to_be_desugared= match projectee with | DeclToBeDesugared _0 -> _0
let uu___is_Unparseable (projectee : decl') : Prims.bool=
  match projectee with | Unparseable -> true | uu___ -> false
let __proj__Mkdecl__item__d (projectee : decl) : decl'=
  match projectee with | { d; drange; quals; attrs; interleaved;_} -> d
let __proj__Mkdecl__item__drange (projectee : decl) :
  FStarC_Range_Type.range=
  match projectee with | { d; drange; quals; attrs; interleaved;_} -> drange
let __proj__Mkdecl__item__quals (projectee : decl) : qualifiers=
  match projectee with | { d; drange; quals; attrs; interleaved;_} -> quals
let __proj__Mkdecl__item__attrs (projectee : decl) : attributes_=
  match projectee with | { d; drange; quals; attrs; interleaved;_} -> attrs
let __proj__Mkdecl__item__interleaved (projectee : decl) : Prims.bool=
  match projectee with
  | { d; drange; quals; attrs; interleaved;_} -> interleaved
let uu___is_DefineEffect (projectee : effect_decl) : Prims.bool=
  match projectee with | DefineEffect _0 -> true | uu___ -> false
let __proj__DefineEffect__item___0 (projectee : effect_decl) :
  (FStarC_Ident.ident * binder Prims.list * term * decl Prims.list)=
  match projectee with | DefineEffect _0 -> _0
let uu___is_RedefineEffect (projectee : effect_decl) : Prims.bool=
  match projectee with | RedefineEffect _0 -> true | uu___ -> false
let __proj__RedefineEffect__item___0 (projectee : effect_decl) :
  (FStarC_Ident.ident * binder Prims.list * term)=
  match projectee with | RedefineEffect _0 -> _0
let hasRange_decl : decl FStarC_Class_HasRange.hasRange=
  {
    FStarC_Class_HasRange.pos = (fun d -> d.drange);
    FStarC_Class_HasRange.setPos =
      (fun r d ->
         {
           d = (d.d);
           drange = r;
           quals = (d.quals);
           attrs = (d.attrs);
           interleaved = (d.interleaved)
         })
  }
type modul__Module__payload =
  {
  no_prelude: Prims.bool ;
  mname: FStarC_Ident.lid ;
  decls: decl Prims.list }
and modul__Interface__payload =
  {
  no_prelude1: Prims.bool ;
  mname1: FStarC_Ident.lid ;
  decls1: decl Prims.list ;
  admitted: Prims.bool }
and modul =
  | Module of modul__Module__payload 
  | Interface of modul__Interface__payload 
let __proj__Mkmodul__Module__payload__item__no_prelude
  (projectee : modul__Module__payload) : Prims.bool=
  match projectee with | { no_prelude; mname; decls;_} -> no_prelude
let __proj__Mkmodul__Module__payload__item__mname
  (projectee : modul__Module__payload) : FStarC_Ident.lid=
  match projectee with | { no_prelude; mname; decls;_} -> mname
let __proj__Mkmodul__Module__payload__item__decls
  (projectee : modul__Module__payload) : decl Prims.list=
  match projectee with | { no_prelude; mname; decls;_} -> decls
let __proj__Mkmodul__Interface__payload__item__no_prelude
  (projectee : modul__Interface__payload) : Prims.bool=
  match projectee with
  | { no_prelude1 = no_prelude; mname1 = mname; decls1 = decls; admitted;_}
      -> no_prelude
let __proj__Mkmodul__Interface__payload__item__mname
  (projectee : modul__Interface__payload) : FStarC_Ident.lid=
  match projectee with
  | { no_prelude1 = no_prelude; mname1 = mname; decls1 = decls; admitted;_}
      -> mname
let __proj__Mkmodul__Interface__payload__item__decls
  (projectee : modul__Interface__payload) : decl Prims.list=
  match projectee with
  | { no_prelude1 = no_prelude; mname1 = mname; decls1 = decls; admitted;_}
      -> decls
let __proj__Mkmodul__Interface__payload__item__admitted
  (projectee : modul__Interface__payload) : Prims.bool=
  match projectee with
  | { no_prelude1 = no_prelude; mname1 = mname; decls1 = decls; admitted;_}
      -> admitted
let uu___is_Module (projectee : modul) : Prims.bool=
  match projectee with | Module _0 -> true | uu___ -> false
let __proj__Module__item___0 (projectee : modul) : modul__Module__payload=
  match projectee with | Module _0 -> _0
let uu___is_Interface (projectee : modul) : Prims.bool=
  match projectee with | Interface _0 -> true | uu___ -> false
let __proj__Interface__item___0 (projectee : modul) :
  modul__Interface__payload= match projectee with | Interface _0 -> _0
type file = modul
type inputFragment = (file, decl Prims.list) FStar_Pervasives.either
let lid_of_modul (m : modul) : FStarC_Ident.lid=
  match m with
  | Module { no_prelude = uu___; mname; decls = uu___1;_} -> mname
  | Interface
      { no_prelude1 = uu___; mname1 = mname; decls1 = uu___1;
        admitted = uu___2;_}
      -> mname
let decls_of_modul (m : modul) : decl Prims.list=
  match m with
  | Module { no_prelude = uu___; mname = uu___1; decls;_} -> decls
  | Interface
      { no_prelude1 = uu___; mname1 = uu___1; decls1 = decls;
        admitted = uu___2;_}
      -> decls
let check_id (id : FStarC_Ident.ident) : unit=
  let first_char =
    let uu___ = FStarC_Ident.string_of_id id in
    FStarC_String.substring uu___ Prims.int_zero Prims.int_one in
  if Prims.op_Negation ((FStarC_String.lowercase first_char) = first_char)
  then
    let uu___ =
      let uu___1 = FStarC_Class_Show.show FStarC_Ident.showable_ident id in
      FStarC_Format.fmt1
        "Invalid identifer '%s'; expected a symbol that begins with a lower-case character"
        uu___1 in
    FStarC_Errors.raise_error FStarC_Ident.hasrange_ident id
      FStarC_Errors_Codes.Fatal_InvalidIdentifier ()
      (Obj.magic FStarC_Errors_Msg.is_error_message_string) (Obj.magic uu___)
  else ()
let at_most_one (s : Prims.string) (r : FStarC_Range_Type.range)
  (l : 'uuuuu Prims.list) : 'uuuuu FStar_Pervasives_Native.option=
  match l with
  | x::[] -> FStar_Pervasives_Native.Some x
  | [] -> FStar_Pervasives_Native.None
  | uu___ ->
      let uu___1 =
        FStarC_Format.fmt1 "At most one %s is allowed on declarations" s in
      FStarC_Errors.raise_error FStarC_Class_HasRange.hasRange_range r
        FStarC_Errors_Codes.Fatal_MoreThanOneDeclaration ()
        (Obj.magic FStarC_Errors_Msg.is_error_message_string)
        (Obj.magic uu___1)
let mk_binder_with_attrs (b : binder') (r : FStarC_Range_Type.range)
  (l : level) (i : aqual) (attrs : term Prims.list) : binder=
  { b; brange = r; blevel = l; aqual = i; battributes = attrs }
let mk_binder (b : binder') (r : FStarC_Range_Type.range) (l : level)
  (i : aqual) : binder= mk_binder_with_attrs b r l i []
let mk_term (t : term') (r : FStarC_Range_Type.range) (l : level) : term=
  { tm = t; range = r; level = l }
let mk_uminus (t : term) (rminus : FStarC_Range_Type.range)
  (r : FStarC_Range_Type.range) (l : level) : term=
  let t1 =
    match t.tm with
    | Const (FStarC_Const.Const_int
        (s, FStar_Pervasives_Native.Some (FStarC_Const.Signed, width))) ->
        Const
          (FStarC_Const.Const_int
             ((Prims.strcat "-" s),
               (FStar_Pervasives_Native.Some (FStarC_Const.Signed, width))))
    | uu___ ->
        let uu___1 =
          let uu___2 = FStarC_Ident.mk_ident ("-", rminus) in (uu___2, [t]) in
        Op uu___1 in
  mk_term t1 r l
let mk_pattern (p : pattern') (r : FStarC_Range_Type.range) : pattern=
  { pat = p; prange = r }
let un_curry_abs (ps : pattern Prims.list) (body : term) : term'=
  match body.tm with
  | Abs (p', body') -> Abs ((FStarC_List.op_At ps p'), body')
  | uu___ -> Abs (ps, body)
let mk_function (branches : branch Prims.list) (r1 : FStarC_Range_Type.range)
  (r2 : FStarC_Range_Type.range) : term=
  mk_term (Function (branches, r1)) r2 Expr
let un_function (p : pattern) (tm : term) :
  (pattern * term) FStar_Pervasives_Native.option=
  match ((p.pat), (tm.tm)) with
  | (PatVar uu___, Abs (pats, body)) ->
      let uu___1 =
        let uu___2 = mk_pattern (PatApp (p, pats)) p.prange in (uu___2, body) in
      FStar_Pervasives_Native.Some uu___1
  | uu___ -> FStar_Pervasives_Native.None
let mkApp (t : term) (args : (term * imp) Prims.list)
  (r : FStarC_Range_Type.range) : term=
  match args with
  | [] -> t
  | uu___ ->
      (match t.tm with
       | Name s -> mk_term (Construct (s, args)) r Un
       | uu___1 ->
           FStarC_List.fold_left
             (fun t1 uu___2 ->
                match uu___2 with
                | (a, imp1) -> mk_term (App (t1, a, imp1)) r Un) t args)
let consPat (r : FStarC_Range_Type.range) (hd : pattern) (tl : pattern) :
  pattern'=
  let uu___ =
    let uu___1 = mk_pattern (PatName FStarC_Parser_Const.cons_lid) r in
    (uu___1, [hd; tl]) in
  PatApp uu___
let consTerm (r : FStarC_Range_Type.range) (hd : term) (tl : term) : 
  term=
  mk_term
    (Construct (FStarC_Parser_Const.cons_lid, [(hd, Nothing); (tl, Nothing)]))
    r Expr
let mkListLit (r : FStarC_Range_Type.range) (elts : term Prims.list) : 
  term= mk_term (ListLiteral elts) r Expr
let mkSeqLit (r : FStarC_Range_Type.range) (elts : term Prims.list) : 
  term= mk_term (SeqLiteral elts) r Expr
let unit_const (r : FStarC_Range_Type.range) : term=
  mk_term (Const FStarC_Const.Const_unit) r Expr
let ml_comp (t : term) : term=
  let lid = FStarC_Parser_Const.effect_ML_lid () in
  let ml = mk_term (Name lid) t.range Expr in
  let t1 = mk_term (App (ml, t, Nothing)) t.range Expr in t1
let tot_comp (t : term) : term=
  let ml = mk_term (Name FStarC_Parser_Const.effect_Tot_lid) t.range Expr in
  let t1 = mk_term (App (ml, t, Nothing)) t.range Expr in t1
let mkRefSet (r : FStarC_Range_Type.range) (elts : term Prims.list) : 
  term=
  let uu___ =
    (FStarC_Parser_Const.set_empty, FStarC_Parser_Const.set_singleton,
      FStarC_Parser_Const.set_union, FStarC_Parser_Const.heap_addr_of_lid) in
  match uu___ with
  | (empty_lid, singleton_lid, union_lid, addr_of_lid) ->
      let empty =
        let uu___1 =
          let uu___2 = FStarC_Ident.set_lid_range empty_lid r in Var uu___2 in
        mk_term uu___1 r Expr in
      let addr_of =
        let uu___1 =
          let uu___2 = FStarC_Ident.set_lid_range addr_of_lid r in Var uu___2 in
        mk_term uu___1 r Expr in
      let singleton =
        let uu___1 =
          let uu___2 = FStarC_Ident.set_lid_range singleton_lid r in
          Var uu___2 in
        mk_term uu___1 r Expr in
      let union =
        let uu___1 =
          let uu___2 = FStarC_Ident.set_lid_range union_lid r in Var uu___2 in
        mk_term uu___1 r Expr in
      FStarC_List.fold_right
        (fun e tl ->
           let e1 = mkApp addr_of [(e, Nothing)] r in
           let single_e = mkApp singleton [(e1, Nothing)] r in
           mkApp union [(single_e, Nothing); (tl, Nothing)] r) elts empty
let mkExplicitApp (t : term) (args : term Prims.list)
  (r : FStarC_Range_Type.range) : term=
  match args with
  | [] -> t
  | uu___ ->
      (match t.tm with
       | Name s ->
           let uu___1 =
             let uu___2 =
               let uu___3 = FStarC_List.map (fun a -> (a, Nothing)) args in
               (s, uu___3) in
             Construct uu___2 in
           mk_term uu___1 r Un
       | uu___1 ->
           FStarC_List.fold_left
             (fun t1 a -> mk_term (App (t1, a, Nothing)) r Un) t args)
let mkAdmitMagic (r : FStarC_Range_Type.range) : term=
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
let mkWildAdmitMagic (r : FStarC_Range_Type.range) :
  (pattern * 'uuuuu FStar_Pervasives_Native.option * term)=
  let uu___ = mk_pattern (PatWild (FStar_Pervasives_Native.None, [])) r in
  let uu___1 = mkAdmitMagic r in
  (uu___, FStar_Pervasives_Native.None, uu___1)
let focusBranches
  (branches :
    (Prims.bool * (pattern * 'uuuuu FStar_Pervasives_Native.option * term))
      Prims.list)
  (r : FStarC_Range_Type.range) :
  (pattern * 'uuuuu FStar_Pervasives_Native.option * term) Prims.list=
  let should_filter =
    FStarC_Util.for_some FStar_Pervasives_Native.fst branches in
  if should_filter
  then
    (FStarC_Errors.log_issue FStarC_Class_HasRange.hasRange_range r
       FStarC_Errors_Codes.Warning_Filtered ()
       (Obj.magic FStarC_Errors_Msg.is_error_message_string)
       (Obj.magic "Focusing on only some cases");
     (let focussed =
        let uu___1 = FStarC_List.filter FStar_Pervasives_Native.fst branches in
        FStarC_List.map FStar_Pervasives_Native.snd uu___1 in
      let uu___1 = let uu___2 = mkWildAdmitMagic r in [uu___2] in
      FStarC_List.op_At focussed uu___1))
  else FStarC_List.map FStar_Pervasives_Native.snd branches
let focusLetBindings (lbs : (Prims.bool * (pattern * term)) Prims.list)
  (r : FStarC_Range_Type.range) : (pattern * term) Prims.list=
  let should_filter = FStarC_Util.for_some FStar_Pervasives_Native.fst lbs in
  if should_filter
  then
    (FStarC_Errors.log_issue FStarC_Class_HasRange.hasRange_range r
       FStarC_Errors_Codes.Warning_Filtered ()
       (Obj.magic FStarC_Errors_Msg.is_error_message_string)
       (Obj.magic
          "Focusing on only some cases in this (mutually) recursive definition");
     FStarC_List.map
       (fun uu___1 ->
          match uu___1 with
          | (f, lb) ->
              if f
              then lb
              else
                (let uu___3 = mkAdmitMagic r in
                 ((FStar_Pervasives_Native.fst lb), uu___3))) lbs)
  else FStarC_List.map FStar_Pervasives_Native.snd lbs
let focusAttrLetBindings
  (lbs :
    (attributes_ FStar_Pervasives_Native.option * (Prims.bool * (pattern *
      term))) Prims.list)
  (r : FStarC_Range_Type.range) :
  (attributes_ FStar_Pervasives_Native.option * (pattern * term)) Prims.list=
  let should_filter =
    FStarC_Util.for_some
      (fun uu___ -> match uu___ with | (attr, (focus, uu___1)) -> focus) lbs in
  if should_filter
  then
    (FStarC_Errors.log_issue FStarC_Class_HasRange.hasRange_range r
       FStarC_Errors_Codes.Warning_Filtered ()
       (Obj.magic FStarC_Errors_Msg.is_error_message_string)
       (Obj.magic
          "Focusing on only some cases in this (mutually) recursive definition");
     FStarC_List.map
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
    FStarC_List.map
      (fun uu___1 -> match uu___1 with | (attr, (uu___2, lb)) -> (attr, lb))
      lbs
let mkTuple (args : term Prims.list) (r : FStarC_Range_Type.range) : 
  term=
  let cons =
    FStarC_Parser_Const_Tuples.mk_tuple_data_lid (FStarC_List.length args) r in
  let uu___ = mk_term (Name cons) r Expr in
  let uu___1 = FStarC_List.map (fun x -> (x, Nothing)) args in
  mkApp uu___ uu___1 r
let mkDTuple (args : term Prims.list) (r : FStarC_Range_Type.range) : 
  term=
  let cons =
    FStarC_Parser_Const_Tuples.mk_dtuple_data_lid (FStarC_List.length args) r in
  let uu___ = mk_term (Name cons) r Expr in
  let uu___1 = FStarC_List.map (fun x -> (x, Nothing)) args in
  mkApp uu___ uu___1 r
let mkRefinedBinder (id : FStarC_Ident.ident) (t : term)
  (should_bind_var : Prims.bool)
  (refopt : term FStar_Pervasives_Native.option)
  (m : FStarC_Range_Type.range) (implicit : aqual) (attrs : term Prims.list)
  : binder=
  let b =
    mk_binder_with_attrs (Annotated (id, t)) m Type_level implicit attrs in
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
           mk_binder_with_attrs (Annotated (x, t)) m Type_level implicit
             attrs in
         let uu___1 =
           let uu___2 =
             let uu___3 = mk_term (Refine (b1, phi)) m Type_level in
             (id, uu___3) in
           Annotated uu___2 in
         mk_binder_with_attrs uu___1 m Type_level implicit attrs)
let mkRefinedPattern (pat : pattern) (t : term)
  (should_bind_pat : Prims.bool)
  (phi_opt : term FStar_Pervasives_Native.option)
  (t_range : FStarC_Range_Type.range) (range : FStarC_Range_Type.range) :
  pattern=
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
                     mk_binder_with_attrs (Annotated (x, t)) t_range
                       Type_level FStar_Pervasives_Native.None attrs in
                   (uu___3, phi) in
                 Refine uu___2 in
               mk_term uu___1 range Type_level
           | uu___ ->
               let x = FStarC_Ident.gen t_range in
               let phi1 =
                 let x_var =
                   let uu___1 =
                     let uu___2 = FStarC_Ident.lid_of_ids [x] in Var uu___2 in
                   mk_term uu___1 phi.range Formula in
                 let pat_branch = (pat, FStar_Pervasives_Native.None, phi) in
                 let otherwise_branch =
                   let uu___1 =
                     mk_pattern (PatWild (FStar_Pervasives_Native.None, []))
                       phi.range in
                   let uu___2 =
                     let uu___3 =
                       let uu___4 =
                         FStarC_Ident.lid_of_path ["False"] phi.range in
                       Name uu___4 in
                     mk_term uu___3 phi.range Formula in
                   (uu___1, FStar_Pervasives_Native.None, uu___2) in
                 mk_term
                   (Match
                      (x_var, FStar_Pervasives_Native.None,
                        FStar_Pervasives_Native.None,
                        [pat_branch; otherwise_branch])) phi.range Formula in
               let uu___1 =
                 let uu___2 =
                   let uu___3 =
                     mk_binder (Annotated (x, t)) t_range Type_level
                       FStar_Pervasives_Native.None in
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
  mk_pattern (PatAscribed (pat, (t1, FStar_Pervasives_Native.None))) range
let rec extract_named_refinement (remove_parens : Prims.bool) (t1 : term) :
  (FStarC_Ident.ident * term * term FStar_Pervasives_Native.option)
    FStar_Pervasives_Native.option=
  match t1.tm with
  | NamedTyp (x, t) ->
      FStar_Pervasives_Native.Some (x, t, FStar_Pervasives_Native.None)
  | Refine
      ({ b = Annotated (x, t); brange = uu___; blevel = uu___1;
         aqual = uu___2; battributes = uu___3;_},
       t')
      ->
      FStar_Pervasives_Native.Some (x, t, (FStar_Pervasives_Native.Some t'))
  | Paren t when remove_parens -> extract_named_refinement remove_parens t
  | uu___ -> FStar_Pervasives_Native.None
let rec as_mlist
  (cur : ((FStarC_Ident.lid * decl * Prims.bool) * decl Prims.list))
  (ds : decl Prims.list) : modul=
  let uu___ = cur in
  match uu___ with
  | ((m_name, m_decl, no_prelude), cur1) ->
      (match ds with
       | [] ->
           Module
             {
               no_prelude;
               mname = m_name;
               decls = (m_decl :: (FStarC_List.rev cur1))
             }
       | d::ds1 ->
           (match d.d with
            | TopLevelModule m' ->
                FStarC_Errors.raise_error hasRange_decl d
                  FStarC_Errors_Codes.Fatal_UnexpectedModuleDeclaration ()
                  (Obj.magic FStarC_Errors_Msg.is_error_message_string)
                  (Obj.magic "Unexpected module declaration")
            | uu___1 ->
                as_mlist ((m_name, m_decl, no_prelude), (d :: cur1)) ds1))
let as_frag (ds : decl Prims.list) : inputFragment=
  let uu___ =
    match ds with
    | d::ds1 -> (d, ds1)
    | [] -> FStarC_Effect.raise FStarC_Errors.Empty_frag in
  match uu___ with
  | (d, ds1) ->
      (match d.d with
       | TopLevelModule m ->
           let no_prelude =
             (FStarC_Options.no_prelude ()) ||
               (FStarC_List.existsb
                  (fun uu___1 ->
                     match uu___1.tm with
                     | Const (FStarC_Const.Const_string
                         ("no_prelude", uu___2)) -> true
                     | uu___2 -> false) d.attrs) in
           let m1 = as_mlist ((m, d, no_prelude), []) ds1 in
           FStar_Pervasives.Inl m1
       | uu___1 ->
           let ds2 = d :: ds1 in
           (FStarC_List.iter
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
let strip_prefix (prefix : Prims.string) (s : Prims.string) :
  Prims.string FStar_Pervasives_Native.option=
  if FStarC_Util.starts_with s prefix
  then
    let uu___ = FStarC_Util.substring_from s (FStarC_String.length prefix) in
    FStar_Pervasives_Native.Some uu___
  else FStar_Pervasives_Native.None
let compile_op (arity : Prims.int) (s : Prims.string)
  (r : FStarC_Range_Type.range) : Prims.string=
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
          FStarC_Class_Show.show FStarC_Class_Show.showable_int
            (FStarC_Util.int_of_char c) in
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
          (FStarC_Util.starts_with s "let") ||
            (FStarC_Util.starts_with s "and")
        then
          let uu___2 =
            let uu___3 =
              FStarC_Util.substring s Prims.int_zero (Prims.of_int (3)) in
            Prims.strcat uu___3 "_" in
          let uu___3 = FStarC_Util.substring_from s (Prims.of_int (3)) in
          (uu___2, uu___3)
        else
          if
            (FStarC_Util.starts_with s "exists") ||
              (FStarC_Util.starts_with s "forall")
          then
            (let uu___3 =
               let uu___4 =
                 FStarC_Util.substring s Prims.int_zero (Prims.of_int (6)) in
               Prims.strcat uu___4 "_" in
             let uu___4 = FStarC_Util.substring_from s (Prims.of_int (6)) in
             (uu___3, uu___4))
          else ("", s) in
      (match uu___1 with
       | (prefix, s1) ->
           let uu___2 =
             let uu___3 =
               let uu___4 =
                 let uu___5 = FStarC_String.list_of_string s1 in
                 FStarC_List.map name_of_char uu___5 in
               FStarC_String.concat "_" uu___4 in
             Prims.strcat prefix uu___3 in
           Prims.strcat "op_" uu___2)
let compile_op' (s : Prims.string) (r : FStarC_Range_Type.range) :
  Prims.string= compile_op (Prims.of_int (-1)) s r
let string_to_op (s : Prims.string) :
  (Prims.string * Prims.int FStar_Pervasives_Native.option)
    FStar_Pervasives_Native.option=
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
      FStar_Pervasives_Native.Some (".[||]<-", FStar_Pervasives_Native.None)
  | "op_Lens_Assignment" ->
      FStar_Pervasives_Native.Some (".(||)<-", FStar_Pervasives_Native.None)
  | "op_String_Access" ->
      FStar_Pervasives_Native.Some (".[]", FStar_Pervasives_Native.None)
  | "op_Array_Access" ->
      FStar_Pervasives_Native.Some (".()", FStar_Pervasives_Native.None)
  | "op_Brack_Lens_Access" ->
      FStar_Pervasives_Native.Some (".[||]", FStar_Pervasives_Native.None)
  | "op_Lens_Access" ->
      FStar_Pervasives_Native.Some (".(||)", FStar_Pervasives_Native.None)
  | uu___ ->
      if FStarC_Util.starts_with s "op_"
      then
        let frags =
          let uu___1 =
            FStarC_Util.substring_from s (FStarC_String.length "op_") in
          FStarC_Util.split uu___1 "_" in
        (match frags with
         | op::[] ->
             if FStarC_Util.starts_with op "u"
             then
               let uu___1 =
                 let uu___2 = FStarC_Util.substring_from op Prims.int_one in
                 FStarC_Util.safe_int_of_string uu___2 in
               FStarC_Option.map
                 (fun op1 ->
                    ((FStarC_Util.string_of_char
                        (FStarC_Util.char_of_int op1)),
                      FStar_Pervasives_Native.None)) uu___1
             else name_of_op op
         | uu___1 ->
             let maybeop =
               let uu___2 = FStarC_List.map name_of_op frags in
               FStarC_List.fold_left
                 (fun acc x ->
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
             FStarC_Option.map (fun o -> (o, FStar_Pervasives_Native.None))
               maybeop)
      else FStar_Pervasives_Native.None
let string_of_fsdoc
  (uu___ : (Prims.string * (Prims.string * Prims.string) Prims.list)) :
  Prims.string=
  match uu___ with
  | (comment, keywords) ->
      let uu___1 =
        let uu___2 =
          FStarC_List.map
            (fun uu___3 ->
               match uu___3 with
               | (k, v) -> Prims.strcat k (Prims.strcat "->" v)) keywords in
        FStarC_String.concat "," uu___2 in
      Prims.strcat comment uu___1
let string_of_let_qualifier (uu___ : let_qualifier) : Prims.string=
  match uu___ with | NoLetQualifier -> "" | Rec -> "rec"
let string_of_local_let_qualifier (uu___ : local_let_qualifier) :
  Prims.string=
  match uu___ with
  | LocalNoLetQualifier -> ""
  | LocalRec -> "rec"
  | LocalUnfold -> "unfold"
let showable_string_of_let_qualifier :
  let_qualifier FStarC_Class_Show.showable=
  { FStarC_Class_Show.show = string_of_let_qualifier }
let showable_string_of_local_let_qualifier :
  local_let_qualifier FStarC_Class_Show.showable=
  { FStarC_Class_Show.show = string_of_local_let_qualifier }
let to_string_l (sep : Prims.string) (f : 'uuuuu -> Prims.string)
  (l : 'uuuuu Prims.list) : Prims.string=
  let uu___ = FStarC_List.map f l in FStarC_String.concat sep uu___
let imp_to_string (uu___ : imp) : Prims.string=
  match uu___ with | Hash -> "#" | uu___1 -> ""
let rec term_to_string (x : term) : Prims.string=
  match x.tm with
  | Wild -> "_"
  | LexList l ->
      let uu___ =
        match l with
        | [] -> " "
        | hd::tl ->
            let uu___1 = term_to_string hd in
            FStarC_List.fold_left
              (fun s t ->
                 let uu___2 =
                   let uu___3 = term_to_string t in Prims.strcat "; " uu___3 in
                 Prims.strcat s uu___2) uu___1 tl in
      FStarC_Format.fmt1 "%[%s]" uu___
  | WFOrder (rel, e) ->
      let uu___ = term_to_string rel in
      let uu___1 = term_to_string e in
      FStarC_Format.fmt2 "{:well-founded %s %s}" uu___ uu___1
  | Decreases t ->
      let uu___ = term_to_string t in
      FStarC_Format.fmt1 "(decreases %s)" uu___
  | Requires t ->
      let uu___ = term_to_string t in
      FStarC_Format.fmt1 "(requires %s)" uu___
  | Ensures t ->
      let uu___ = term_to_string t in FStarC_Format.fmt1 "(ensures %s)" uu___
  | Labeled (t, l, uu___) ->
      let uu___1 = term_to_string t in
      FStarC_Format.fmt2 "(labeled %s %s)" l uu___1
  | Const c -> FStarC_Parser_Const.const_to_string c
  | Op (s, xs) ->
      let uu___ = FStarC_Ident.string_of_id s in
      let uu___1 =
        let uu___2 = FStarC_List.map (fun x1 -> term_to_string x1) xs in
        FStarC_String.concat ", " uu___2 in
      FStarC_Format.fmt2 "%s(%s)" uu___ uu___1
  | Uvar id -> FStarC_Ident.string_of_id id
  | Var l -> FStarC_Ident.string_of_lid l
  | Name l -> FStarC_Ident.string_of_lid l
  | Projector (rec_lid, field_id) ->
      let uu___ = FStarC_Ident.string_of_lid rec_lid in
      let uu___1 = FStarC_Ident.string_of_id field_id in
      FStarC_Format.fmt2 "%s?.%s" uu___ uu___1
  | Construct (l, args) ->
      let uu___ = FStarC_Ident.string_of_lid l in
      let uu___1 =
        to_string_l " "
          (fun uu___2 ->
             match uu___2 with
             | (a, imp1) ->
                 let uu___3 = term_to_string a in
                 FStarC_Format.fmt2 "%s%s" (imp_to_string imp1) uu___3) args in
      FStarC_Format.fmt2 "(%s %s)" uu___ uu___1
  | Function (branches, r) ->
      let uu___ =
        to_string_l " | "
          (fun uu___1 ->
             match uu___1 with
             | (p, w, e) ->
                 let uu___2 = pat_to_string p in
                 let uu___3 = term_to_string e in
                 FStarC_Format.fmt2 "%s -> %s" uu___2 uu___3) branches in
      FStarC_Format.fmt1 "(function %s)" uu___
  | Abs (pats, t) ->
      let uu___ = to_string_l " " pat_to_string pats in
      let uu___1 = term_to_string t in
      FStarC_Format.fmt2 "(fun %s -> %s)" uu___ uu___1
  | App (t1, t2, imp1) ->
      let uu___ = term_to_string t1 in
      let uu___1 = term_to_string t2 in
      FStarC_Format.fmt3 "%s %s%s" uu___ (imp_to_string imp1) uu___1
  | Let (LocalRec, (a, (p, b))::lbs, body) ->
      let uu___ = attrs_opt_to_string a in
      let uu___1 =
        let uu___2 = pat_to_string p in
        let uu___3 = term_to_string b in
        FStarC_Format.fmt2 "%s=%s" uu___2 uu___3 in
      let uu___2 =
        to_string_l " "
          (fun uu___3 ->
             match uu___3 with
             | (a1, (p1, b1)) ->
                 let uu___4 = attrs_opt_to_string a1 in
                 let uu___5 = pat_to_string p1 in
                 let uu___6 = term_to_string b1 in
                 FStarC_Format.fmt3 "%sand %s=%s" uu___4 uu___5 uu___6) lbs in
      let uu___3 = term_to_string body in
      FStarC_Format.fmt4 "%slet rec %s%s in %s" uu___ uu___1 uu___2 uu___3
  | Let (q, (attrs, (pat, tm))::[], body) ->
      let uu___ = attrs_opt_to_string attrs in
      let uu___1 = pat_to_string pat in
      let uu___2 = term_to_string tm in
      let uu___3 = term_to_string body in
      FStarC_Format.fmt5 "%slet %s %s = %s in %s" uu___
        (string_of_local_let_qualifier q) uu___1 uu___2 uu___3
  | Let (uu___, uu___1, uu___2) -> "invalid_surface_let?"
  | LetOperator ((i, p, b)::lbs, body) ->
      let uu___ = FStarC_Class_Show.show FStarC_Ident.showable_ident i in
      let uu___1 =
        let uu___2 = pat_to_string p in
        let uu___3 = term_to_string b in
        FStarC_Format.fmt2 "%s=%s" uu___2 uu___3 in
      let uu___2 =
        to_string_l " "
          (fun uu___3 ->
             match uu___3 with
             | (i1, p1, b1) ->
                 let uu___4 =
                   FStarC_Class_Show.show FStarC_Ident.showable_ident i1 in
                 let uu___5 = pat_to_string p1 in
                 let uu___6 = term_to_string b1 in
                 FStarC_Format.fmt3 "and%s %s=%s" uu___4 uu___5 uu___6) lbs in
      let uu___3 = term_to_string body in
      FStarC_Format.fmt4 "let%s rec %s%s in %s" uu___ uu___1 uu___2 uu___3
  | LetOpen (lid, t) ->
      let uu___ = FStarC_Ident.string_of_lid lid in
      let uu___1 = term_to_string t in
      FStarC_Format.fmt2 "let open %s in %s" uu___ uu___1
  | LetOpenRecord (e, t, body) ->
      let uu___ = term_to_string e in
      let uu___1 = term_to_string t in
      let uu___2 = term_to_string body in
      FStarC_Format.fmt3 "let open %s <: %s in %s\n" uu___ uu___1 uu___2
  | Seq (t1, t2) ->
      let uu___ = term_to_string t1 in
      let uu___1 = term_to_string t2 in
      FStarC_Format.fmt2 "%s; %s" uu___ uu___1
  | Bind (id, t1, t2) ->
      let uu___ = FStarC_Ident.string_of_id id in
      let uu___1 = term_to_string t1 in
      let uu___2 = term_to_string t2 in
      FStarC_Format.fmt3 "%s <- %s; %s" uu___ uu___1 uu___2
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
                  FStarC_Format.fmt1 " as %s " uu___4 in
            let uu___4 = term_to_string ret in
            FStarC_Format.fmt3 "%s%s %s " uu___3 s uu___4 in
      let uu___3 = term_to_string t2 in
      let uu___4 = term_to_string t3 in
      FStarC_Format.fmt5 "if%s %s %sthen %s else %s" uu___ uu___1 uu___2
        uu___3 uu___4
  | Match (t, op_opt, ret_opt, branches) ->
      try_or_match_to_string x t branches op_opt ret_opt
  | TryWith (t, branches) ->
      try_or_match_to_string x t branches FStar_Pervasives_Native.None
        FStar_Pervasives_Native.None
  | Ascribed (t1, t2, FStar_Pervasives_Native.None, flag) ->
      let s = if flag then "$:" else "<:" in
      let uu___ = term_to_string t1 in
      let uu___1 = term_to_string t2 in
      FStarC_Format.fmt3 "(%s %s %s)" uu___ s uu___1
  | Ascribed (t1, t2, FStar_Pervasives_Native.Some tac, flag) ->
      let s = if flag then "$:" else "<:" in
      let uu___ = term_to_string t1 in
      let uu___1 = term_to_string t2 in
      let uu___2 = term_to_string tac in
      FStarC_Format.fmt4 "(%s %s %s by %s)" uu___ s uu___1 uu___2
  | Record (FStar_Pervasives_Native.Some e, fields) ->
      let uu___ = term_to_string e in
      let uu___1 =
        to_string_l " "
          (fun uu___2 ->
             match uu___2 with
             | (l, e1) ->
                 let uu___3 = FStarC_Ident.string_of_lid l in
                 let uu___4 = term_to_string e1 in
                 FStarC_Format.fmt2 "%s=%s" uu___3 uu___4) fields in
      FStarC_Format.fmt2 "{%s with %s}" uu___ uu___1
  | Record (FStar_Pervasives_Native.None, fields) ->
      let uu___ =
        to_string_l " "
          (fun uu___1 ->
             match uu___1 with
             | (l, e) ->
                 let uu___2 = FStarC_Ident.string_of_lid l in
                 let uu___3 = term_to_string e in
                 FStarC_Format.fmt2 "%s=%s" uu___2 uu___3) fields in
      FStarC_Format.fmt1 "{%s}" uu___
  | Project (e, l) ->
      let uu___ = term_to_string e in
      let uu___1 = FStarC_Ident.string_of_lid l in
      FStarC_Format.fmt2 "%s.%s" uu___ uu___1
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
      FStarC_Format.fmt2 "%s -> %s" uu___ uu___1
  | Product (b::[], t) when x.level = Kind ->
      let uu___ = binder_to_string b in
      let uu___1 = term_to_string t in
      FStarC_Format.fmt2 "%s => %s" uu___ uu___1
  | Sum (binders, t) ->
      let uu___ =
        FStarC_List.map
          (fun uu___1 ->
             match uu___1 with
             | FStar_Pervasives.Inl b -> binder_to_string b
             | FStar_Pervasives.Inr t1 -> term_to_string t1)
          (FStarC_List.op_At binders [FStar_Pervasives.Inr t]) in
      FStarC_String.concat " & " uu___
  | QForall (bs, (uu___, pats), t) ->
      let uu___1 = to_string_l " " binder_to_string bs in
      let uu___2 = to_string_l " \\/ " (to_string_l "; " term_to_string) pats in
      let uu___3 = term_to_string t in
      FStarC_Format.fmt3 "forall %s.{:pattern %s} %s" uu___1 uu___2 uu___3
  | QExists (bs, (uu___, pats), t) ->
      let uu___1 = to_string_l " " binder_to_string bs in
      let uu___2 = to_string_l " \\/ " (to_string_l "; " term_to_string) pats in
      let uu___3 = term_to_string t in
      FStarC_Format.fmt3 "exists %s.{:pattern %s} %s" uu___1 uu___2 uu___3
  | QuantOp (i, bs, (uu___, []), t) ->
      let uu___1 = FStarC_Ident.string_of_id i in
      let uu___2 = to_string_l " " binder_to_string bs in
      let uu___3 = term_to_string t in
      FStarC_Format.fmt3 "%s %s. %s" uu___1 uu___2 uu___3
  | QuantOp (i, bs, (uu___, pats), t) ->
      let uu___1 = FStarC_Ident.string_of_id i in
      let uu___2 = to_string_l " " binder_to_string bs in
      let uu___3 = to_string_l " \\/ " (to_string_l "; " term_to_string) pats in
      let uu___4 = term_to_string t in
      FStarC_Format.fmt4 "%s %s.{:pattern %s} %s" uu___1 uu___2 uu___3 uu___4
  | Refine (b, t) ->
      let uu___ = binder_to_string b in
      let uu___1 = term_to_string t in
      FStarC_Format.fmt2 "%s:{%s}" uu___ uu___1
  | NamedTyp (x1, t) ->
      let uu___ = FStarC_Ident.string_of_id x1 in
      let uu___1 = term_to_string t in
      FStarC_Format.fmt2 "%s:%s" uu___ uu___1
  | Paren t ->
      let uu___ = term_to_string t in FStarC_Format.fmt1 "(%s)" uu___
  | Product (bs, t) ->
      let uu___ =
        let uu___1 = FStarC_List.map binder_to_string bs in
        FStarC_String.concat "," uu___1 in
      let uu___1 = term_to_string t in
      FStarC_Format.fmt2 "Unidentified product: [%s] %s" uu___ uu___1
  | Discrim lid ->
      let uu___ = FStarC_Ident.string_of_lid lid in
      FStarC_Format.fmt1 "%s?" uu___
  | Attributes ts ->
      let uu___ =
        let uu___1 = FStarC_List.map term_to_string ts in
        FStarC_String.concat " " uu___1 in
      FStarC_Format.fmt1 "(attributes %s)" uu___
  | Antiquote t ->
      let uu___ = term_to_string t in FStarC_Format.fmt1 "(`#%s)" uu___
  | Quote (t, Static) ->
      let uu___ = term_to_string t in FStarC_Format.fmt1 "(`(%s))" uu___
  | Quote (t, Dynamic) ->
      let uu___ = term_to_string t in FStarC_Format.fmt1 "quote (%s)" uu___
  | VQuote t ->
      let uu___ = term_to_string t in FStarC_Format.fmt1 "`%%%s" uu___
  | CalcProof (rel, init, steps) ->
      let uu___ = term_to_string rel in
      let uu___1 = term_to_string init in
      let uu___2 =
        let uu___3 = FStarC_List.map calc_step_to_string steps in
        FStarC_String.concat " " uu___3 in
      FStarC_Format.fmt3 "calc (%s) { %s %s }" uu___ uu___1 uu___2
  | ElimForall (bs, t, vs) ->
      let uu___ = binders_to_string " " bs in
      let uu___1 = term_to_string t in
      let uu___2 =
        let uu___3 = FStarC_List.map term_to_string vs in
        FStarC_String.concat " " uu___3 in
      FStarC_Format.fmt3 "_elim_ forall %s. %s using %s" uu___ uu___1 uu___2
  | ElimExists (bs, p, q, b, e) ->
      let uu___ = binders_to_string " " bs in
      let uu___1 = term_to_string p in
      let uu___2 = term_to_string q in
      let uu___3 = binder_to_string b in
      let uu___4 = term_to_string e in
      FStarC_Format.fmt5 "_elim_ exists %s. %s _to_ %s\n\\with %s. %s" uu___
        uu___1 uu___2 uu___3 uu___4
  | ElimImplies (p, q, e) ->
      let uu___ = term_to_string p in
      let uu___1 = term_to_string q in
      let uu___2 = term_to_string e in
      FStarC_Format.fmt3 "_elim_ %s ==> %s with %s" uu___ uu___1 uu___2
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
                  let uu___12 = let uu___13 = term_to_string e' in [uu___13] in
                  uu___11 :: uu___12 in
                uu___9 :: uu___10 in
              uu___7 :: uu___8 in
            uu___5 :: uu___6 in
          uu___3 :: uu___4 in
        uu___1 :: uu___2 in
      FStarC_Format.fmt
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
      FStarC_Format.fmt "_elim_ %s /\\ %s _to_ %s\n\\with %s %s. %s" uu___
  | IntroForall (xs, p, e) ->
      let uu___ = binders_to_string " " xs in
      let uu___1 = term_to_string p in
      let uu___2 = term_to_string e in
      FStarC_Format.fmt3 "_intro_ forall %s. %s with %s" uu___ uu___1 uu___2
  | IntroExists (xs, t, vs, e) ->
      let uu___ = binders_to_string " " xs in
      let uu___1 = term_to_string t in
      let uu___2 =
        let uu___3 = FStarC_List.map term_to_string vs in
        FStarC_String.concat " " uu___3 in
      let uu___3 = term_to_string e in
      FStarC_Format.fmt4 "_intro_ exists %s. %s using %s with %s" uu___
        uu___1 uu___2 uu___3
  | IntroImplies (p, q, x1, e) ->
      let uu___ = term_to_string p in
      let uu___1 = term_to_string q in
      let uu___2 = binder_to_string x1 in
      let uu___3 = term_to_string p in
      FStarC_Format.fmt4 "_intro_ %s ==> %s with %s. %s" uu___ uu___1 uu___2
        uu___3
  | IntroOr (b, p, q, r) ->
      let uu___ = term_to_string p in
      let uu___1 = term_to_string q in
      let uu___2 = term_to_string r in
      FStarC_Format.fmt4 "_intro_ %s \\/ %s using %s with %s" uu___ uu___1
        (if b then "Left" else "Right") uu___2
  | IntroAnd (p, q, e1, e2) ->
      let uu___ = term_to_string p in
      let uu___1 = term_to_string q in
      let uu___2 = term_to_string e1 in
      let uu___3 = term_to_string e2 in
      FStarC_Format.fmt4 "_intro_ %s /\\ %s with %s and %s" uu___ uu___1
        uu___2 uu___3
  | ListLiteral ts ->
      let uu___ = to_string_l "; " term_to_string ts in
      FStarC_Format.fmt1 "[%s]" uu___
  | SeqLiteral ts ->
      let uu___ = to_string_l "; " term_to_string ts in
      FStarC_Format.fmt1 "seq![%s]" uu___
  | LitDoc d -> FStarC_Format.fmt1 "litdoc(%s)" (FStar_Pprint.render d)
  | uu___ ->
      let uu___1 =
        let uu___2 = FStarC_Class_Tagged.tag_of tagged_term x in
        Prims.strcat "AST.term_to_string missing case: " uu___2 in
      failwith uu___1
and binders_to_string (sep : Prims.string) (bs : binder Prims.list) :
  Prims.string=
  let uu___ = FStarC_List.map binder_to_string bs in
  FStarC_String.concat sep uu___
and try_or_match_to_string (x : term) (scrutinee : term)
  (branches :
    (pattern * term FStar_Pervasives_Native.option * term) Prims.list)
  (op_opt : FStarC_Ident.ident FStar_Pervasives_Native.option)
  (ret_opt :
    (FStarC_Ident.ident FStar_Pervasives_Native.option * term * Prims.bool)
      FStar_Pervasives_Native.option)
  : Prims.string=
  let s =
    match x.tm with
    | Match uu___ -> "match"
    | TryWith uu___ -> "try"
    | uu___ -> failwith "impossible" in
  let uu___ =
    match op_opt with
    | FStar_Pervasives_Native.Some op -> FStarC_Ident.string_of_id op
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
              FStarC_Format.fmt1 "as %s " uu___4 in
        let uu___4 = term_to_string ret in
        FStarC_Format.fmt3 "%s%s %s " s1 uu___3 uu___4 in
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
                   FStarC_Format.fmt1 "when %s" uu___7 in
             let uu___7 = term_to_string e in
             FStarC_Format.fmt3 "%s %s -> %s" uu___5 uu___6 uu___7) branches in
  FStarC_Format.fmt5 "%s%s %s %swith %s" s uu___ uu___1 uu___2 uu___3
and calc_step_to_string (uu___ : calc_step) : Prims.string=
  match uu___ with
  | CalcStep (rel, just, next) ->
      let uu___1 = term_to_string rel in
      let uu___2 = term_to_string just in
      let uu___3 = term_to_string next in
      FStarC_Format.fmt3 "%s{ %s } %s" uu___1 uu___2 uu___3
and binder_to_string (x : binder) : Prims.string=
  let pr x1 =
    let s =
      match x1.b with
      | Variable i -> FStarC_Ident.string_of_id i
      | Annotated (i, t) ->
          let uu___ = FStarC_Ident.string_of_id i in
          let uu___1 = term_to_string t in
          FStarC_Format.fmt2 "%s:%s" uu___ uu___1
      | NoName t -> term_to_string t in
    let uu___ = aqual_to_string x1.aqual in
    let uu___1 = attr_list_to_string x1.battributes in
    FStarC_Format.fmt3 "%s%s%s" uu___ uu___1 s in
  match x.aqual with
  | FStar_Pervasives_Native.Some (TypeClassArg) ->
      let uu___ = let uu___1 = pr x in Prims.strcat uu___1 " |}" in
      Prims.strcat "{| " uu___
  | uu___ -> pr x
and aqual_to_string (uu___ : arg_qualifier FStar_Pervasives_Native.option) :
  Prims.string=
  match uu___ with
  | FStar_Pervasives_Native.Some (Equality) -> "$"
  | FStar_Pervasives_Native.Some (Implicit) -> "#"
  | FStar_Pervasives_Native.None -> ""
  | FStar_Pervasives_Native.Some (Meta uu___1) -> "{||}"
  | FStar_Pervasives_Native.Some (TypeClassArg) -> "{||}"
and attr_list_to_string (uu___ : term Prims.list) : Prims.string=
  match uu___ with
  | [] -> ""
  | l -> attrs_opt_to_string (FStar_Pervasives_Native.Some l)
and pat_to_string (x : pattern) : Prims.string=
  match x.pat with
  | PatWild (FStar_Pervasives_Native.None, attrs) ->
      let uu___ = attr_list_to_string attrs in Prims.strcat uu___ "_"
  | PatWild (uu___, attrs) ->
      let uu___1 =
        let uu___2 = attr_list_to_string attrs in Prims.strcat uu___2 "_" in
      Prims.strcat "#" uu___1
  | PatConst c -> FStarC_Parser_Const.const_to_string c
  | PatVQuote t ->
      let uu___ = term_to_string t in FStarC_Format.fmt1 "`%%%s" uu___
  | PatApp (p, ps) ->
      let uu___ = pat_to_string p in
      let uu___1 = to_string_l " " pat_to_string ps in
      FStarC_Format.fmt2 "(%s %s)" uu___ uu___1
  | PatVar (i, aq, attrs) ->
      let uu___ = aqual_to_string aq in
      let uu___1 = attr_list_to_string attrs in
      let uu___2 = FStarC_Ident.string_of_id i in
      FStarC_Format.fmt3 "%s%s%s" uu___ uu___1 uu___2
  | PatName l -> FStarC_Ident.string_of_lid l
  | PatList l ->
      let uu___ = to_string_l "; " pat_to_string l in
      FStarC_Format.fmt1 "[%s]" uu___
  | PatTuple (l, false) ->
      let uu___ = to_string_l ", " pat_to_string l in
      FStarC_Format.fmt1 "(%s)" uu___
  | PatTuple (l, true) ->
      let uu___ = to_string_l ", " pat_to_string l in
      FStarC_Format.fmt1 "(|%s|)" uu___
  | PatRecord l ->
      let uu___ =
        to_string_l "; "
          (fun uu___1 ->
             match uu___1 with
             | (f, e) ->
                 let uu___2 = FStarC_Ident.string_of_lid f in
                 let uu___3 = pat_to_string e in
                 FStarC_Format.fmt2 "%s=%s" uu___2 uu___3) l in
      FStarC_Format.fmt1 "{%s}" uu___
  | PatOr l -> to_string_l "|\n " pat_to_string l
  | PatOp op ->
      let uu___ = FStarC_Ident.string_of_id op in
      FStarC_Format.fmt1 "(%s)" uu___
  | PatAscribed (p, (t, FStar_Pervasives_Native.None)) ->
      let uu___ = pat_to_string p in
      let uu___1 = term_to_string t in
      FStarC_Format.fmt2 "(%s:%s)" uu___ uu___1
  | PatAscribed (p, (t, FStar_Pervasives_Native.Some tac)) ->
      let uu___ = pat_to_string p in
      let uu___1 = term_to_string t in
      let uu___2 = term_to_string tac in
      FStarC_Format.fmt3 "(%s:%s by %s)" uu___ uu___1 uu___2
  | PatRest -> ".."
and attrs_opt_to_string
  (uu___ : term Prims.list FStar_Pervasives_Native.option) : Prims.string=
  match uu___ with
  | FStar_Pervasives_Native.None -> ""
  | FStar_Pervasives_Native.Some attrs ->
      let uu___1 =
        let uu___2 = FStarC_List.map term_to_string attrs in
        FStarC_String.concat "; " uu___2 in
      FStarC_Format.fmt1 "[@ %s]" uu___1
let rec head_id_of_pat (p : pattern) : FStarC_Ident.lident Prims.list=
  match p.pat with
  | PatName l -> [l]
  | PatVar (i, uu___, uu___1) ->
      let uu___2 = FStarC_Ident.lid_of_ids [i] in [uu___2]
  | PatApp (p1, uu___) -> head_id_of_pat p1
  | PatAscribed (p1, uu___) -> head_id_of_pat p1
  | uu___ -> []
let lids_of_let (defs : (pattern * term) Prims.list) :
  FStarC_Ident.lident Prims.list=
  FStarC_List.collect
    (fun uu___ -> match uu___ with | (p, uu___1) -> head_id_of_pat p) defs
let id_of_tycon (uu___ : tycon) : Prims.string=
  match uu___ with
  | TyconAbstract (i, uu___1, uu___2) -> FStarC_Ident.string_of_id i
  | TyconAbbrev (i, uu___1, uu___2, uu___3) -> FStarC_Ident.string_of_id i
  | TyconRecord (i, uu___1, uu___2, uu___3, uu___4) ->
      FStarC_Ident.string_of_id i
  | TyconVariant (i, uu___1, uu___2, uu___3) -> FStarC_Ident.string_of_id i
let string_of_pragma (uu___ : pragma) : Prims.string=
  match uu___ with
  | ShowOptions -> "show-options"
  | SetOptions s -> FStarC_Format.fmt1 "set-options \"%s\"" s
  | ResetOptions s ->
      FStarC_Format.fmt1 "reset-options \"%s\"" (FStarC_Option.dflt "" s)
  | PushOptions s ->
      FStarC_Format.fmt1 "push-options \"%s\"" (FStarC_Option.dflt "" s)
  | PopOptions -> "pop-options"
  | RestartSolver -> "restart-solver"
  | PrintEffectsGraph -> "print-effects-graph"
  | Check t -> let uu___1 = term_to_string t in Prims.strcat "check " uu___1
let restriction_to_string (uu___ : FStarC_Syntax_Syntax.restriction) :
  Prims.string=
  match uu___ with
  | FStarC_Syntax_Syntax.Unrestricted -> ""
  | FStarC_Syntax_Syntax.AllowList allow_list ->
      let uu___1 =
        let uu___2 =
          let uu___3 =
            FStarC_List.map
              (fun uu___4 ->
                 match uu___4 with
                 | (id, renamed) ->
                     let uu___5 = FStarC_Ident.string_of_id id in
                     let uu___6 =
                       let uu___7 =
                         FStarC_Option.map
                           (fun renamed1 ->
                              let uu___8 = FStarC_Ident.string_of_id renamed1 in
                              Prims.strcat " as " uu___8) renamed in
                       FStarC_Option.dflt "" uu___7 in
                     Prims.strcat uu___5 uu___6) allow_list in
          FStarC_String.concat ", " uu___3 in
        Prims.strcat uu___2 "}" in
      Prims.strcat " {" uu___1
let decl_to_string (d : decl) : Prims.string=
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
      FStarC_Format.fmt2 "module %s = %s" uu___ uu___1
  | TopLevelLet (uu___, pats) ->
      let uu___1 =
        let uu___2 =
          FStarC_List.map
            (fun uu___3 ->
               match uu___3 with
               | (p, t) ->
                   let uu___4 = pat_to_string p in
                   let uu___5 =
                     let uu___6 = term_to_string t in
                     Prims.strcat " = " uu___6 in
                   Prims.strcat uu___4 uu___5) pats in
        FStarC_String.concat ", " uu___2 in
      Prims.strcat "let " uu___1
  | Assume (i, uu___) ->
      let uu___1 = FStarC_Ident.string_of_id i in
      Prims.strcat "assume " uu___1
  | Tycon (uu___, uu___1, tys) ->
      let uu___2 =
        let uu___3 = FStarC_List.map id_of_tycon tys in
        FStarC_String.concat ", " uu___3 in
      Prims.strcat "type " uu___2
  | Val (i, uu___) ->
      let uu___1 = FStarC_Ident.string_of_id i in Prims.strcat "val " uu___1
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
      FStarC_Format.fmt3 "polymonadic_bind (%s, %s) |> %s" uu___1 uu___2
        uu___3
  | Polymonadic_subcomp (l1, l2, uu___) ->
      let uu___1 = FStarC_Ident.string_of_lid l1 in
      let uu___2 = FStarC_Ident.string_of_lid l2 in
      FStarC_Format.fmt2 "polymonadic_subcomp %s <: %s" uu___1 uu___2
  | Splice (is_typed, ids, t) ->
      let uu___ =
        let uu___1 =
          let uu___2 =
            let uu___3 =
              let uu___4 =
                FStarC_List.map (fun i -> FStarC_Ident.string_of_id i) ids in
              FStarC_String.concat ";" uu___4 in
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
  | UseLangDecls str -> FStarC_Format.fmt1 "#lang-%s" str
  | Unparseable -> "unparseable"
let modul_to_string (m : modul) : Prims.string=
  match m with
  | Module { no_prelude = uu___; mname = uu___1; decls;_} ->
      let uu___2 = FStarC_List.map decl_to_string decls in
      FStarC_String.concat "\n" uu___2
  | Interface
      { no_prelude1 = uu___; mname1 = uu___1; decls1 = decls;
        admitted = uu___2;_}
      ->
      let uu___3 = FStarC_List.map decl_to_string decls in
      FStarC_String.concat "\n" uu___3
let decl_is_val (id : FStarC_Ident.ident) (decl1 : decl) : Prims.bool=
  match decl1.d with
  | Val (id', uu___) -> FStarC_Ident.ident_equals id id'
  | uu___ -> false
let thunk (ens : term) : term=
  let wildpat =
    mk_pattern (PatWild (FStar_Pervasives_Native.None, [])) ens.range in
  mk_term (Abs ([wildpat], ens)) ens.range Expr
let ident_of_binder (r : FStarC_Range_Type.range) (b : binder) :
  FStarC_Ident.ident=
  match b.b with
  | Variable i -> i
  | Annotated (i, uu___) -> i
  | NoName uu___ ->
      FStarC_Errors.raise_error FStarC_Class_HasRange.hasRange_range r
        FStarC_Errors_Codes.Fatal_MissingQuantifierBinder ()
        (Obj.magic FStarC_Errors_Msg.is_error_message_string)
        (Obj.magic "Wildcard binders in quantifiers are not allowed")
let idents_of_binders (bs : binder Prims.list) (r : FStarC_Range_Type.range)
  : FStarC_Ident.ident Prims.list= FStarC_List.map (ident_of_binder r) bs
let showable_decl : decl FStarC_Class_Show.showable=
  { FStarC_Class_Show.show = decl_to_string }
let showable_term : term FStarC_Class_Show.showable=
  { FStarC_Class_Show.show = term_to_string }
let showable_pattern : pattern FStarC_Class_Show.showable=
  { FStarC_Class_Show.show = pat_to_string }
let showable_binder : binder FStarC_Class_Show.showable=
  { FStarC_Class_Show.show = binder_to_string }
let showable_modul : modul FStarC_Class_Show.showable=
  { FStarC_Class_Show.show = modul_to_string }
let showable_pragma : pragma FStarC_Class_Show.showable=
  { FStarC_Class_Show.show = string_of_pragma }
let showable_imp : imp FStarC_Class_Show.showable=
  { FStarC_Class_Show.show = imp_to_string }
let add_decorations (d : decl) (decorations : decoration Prims.list) : 
  decl=
  let decorations1 =
    let uu___ = FStarC_List.partition uu___is_DeclAttributes decorations in
    match uu___ with
    | (attrs, quals) ->
        let attrs1 =
          match (attrs, (d.attrs)) with
          | (attrs2, []) -> attrs2
          | ((DeclAttributes a)::[], attrs2) ->
              [DeclAttributes (FStarC_List.op_At a attrs2)]
          | ([], attrs2) -> [DeclAttributes attrs2]
          | uu___1 ->
              let uu___2 =
                let uu___3 =
                  let uu___4 =
                    FStarC_List.map
                      (fun uu___5 ->
                         match uu___5 with
                         | DeclAttributes a ->
                             FStarC_Class_Show.show
                               (FStarC_Class_Show.show_list showable_term) a
                         | uu___6 -> "") attrs in
                  FStarC_String.concat ", " uu___4 in
                let uu___4 =
                  let uu___5 =
                    FStarC_List.map (FStarC_Class_Show.show showable_term)
                      d.attrs in
                  FStarC_String.concat ", " uu___5 in
                FStarC_Format.fmt2
                  "At most one attribute set is allowed on declarations\n got %s;\n and %s"
                  uu___3 uu___4 in
              FStarC_Errors.raise_error hasRange_decl d
                FStarC_Errors_Codes.Fatal_MoreThanOneDeclaration ()
                (Obj.magic FStarC_Errors_Msg.is_error_message_string)
                (Obj.magic uu___2) in
        let uu___1 = FStarC_List.map (fun uu___2 -> Qualifier uu___2) d.quals in
        FStarC_List.op_At uu___1 (FStarC_List.op_At quals attrs1) in
  let attributes_1 =
    let uu___ =
      FStarC_List.choose
        (fun uu___1 ->
           match uu___1 with
           | DeclAttributes a -> FStar_Pervasives_Native.Some a
           | uu___2 -> FStar_Pervasives_Native.None) decorations1 in
    at_most_one "attribute set" d.drange uu___ in
  let attributes_2 = FStarC_Option.dflt [] attributes_1 in
  let qualifiers1 =
    FStarC_List.choose
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
let mk_decl (d : decl') (r : FStarC_Range_Type.range)
  (decorations : decoration Prims.list) : decl=
  let d1 = { d; drange = r; quals = []; attrs = []; interleaved = false } in
  add_decorations d1 decorations
let as_interface (m : modul) : modul=
  match m with
  | Module { no_prelude; mname; decls;_} ->
      Interface
        {
          no_prelude1 = no_prelude;
          mname1 = mname;
          decls1 = decls;
          admitted = true
        }
  | i -> i
let inline_let_attribute : term=
  mk_term (Var FStarC_Parser_Const.inline_let_attr)
    FStarC_Range_Type.dummyRange Expr
let inline_let_vc_attribute : term=
  mk_term (Var FStarC_Parser_Const.inline_let_vc_attr)
    FStarC_Range_Type.dummyRange Expr
let showable_quote_kind : quote_kind FStarC_Class_Show.showable=
  {
    FStarC_Class_Show.show =
      (fun uu___ ->
         match uu___ with | Static -> "Static" | Dynamic -> "Dynamic")
  }
let pretty_quote_kind : quote_kind FStarC_Class_PP.pretty=
  {
    FStarC_Class_PP.pp =
      (fun uu___ ->
         match uu___ with
         | Static -> FStar_Pprint.doc_of_string "Static"
         | Dynamic -> FStar_Pprint.doc_of_string "Dynamic")
  }
let ctor (n : Prims.string) (args : FStar_Pprint.document Prims.list) :
  FStar_Pprint.document=
  FStar_Pprint.nest (Prims.of_int (2))
    (FStar_Pprint.group
       (FStar_Pprint.parens
          (FStar_Pprint.flow (FStar_Pprint.break_ Prims.int_one)
             ((FStar_Pprint.doc_of_string n) :: args))))
let pp_list' (f : 'a -> FStar_Pprint.document) (xs : 'a Prims.list) :
  FStar_Pprint.document=
  (FStarC_Class_PP.pp_list { FStarC_Class_PP.pp = f }).FStarC_Class_PP.pp xs
let showable_arg_qualifier : arg_qualifier FStarC_Class_Show.showable=
  {
    FStarC_Class_Show.show =
      (fun uu___ ->
         match uu___ with
         | Implicit -> "Implicit"
         | Equality -> "Equality"
         | Meta i -> "Meta"
         | TypeClassArg -> "TypeClassArg")
  }
let pretty_imp : imp FStarC_Class_PP.pretty=
  FStarC_Class_PP.pretty_from_showable showable_imp
let pretty_arg_qualifier : arg_qualifier FStarC_Class_PP.pretty=
  FStarC_Class_PP.pretty_from_showable showable_arg_qualifier
let rec pp_term (t : term) : FStar_Pprint.document=
  match t.tm with
  | Wild -> ctor "Wild" []
  | Const c ->
      let uu___ =
        let uu___1 =
          let uu___2 = FStarC_Parser_Const.const_to_string c in
          FStar_Pprint.doc_of_string uu___2 in
        [uu___1] in
      ctor "Const" uu___
  | Op (i, args) ->
      let uu___ =
        let uu___1 = FStarC_Class_PP.pp FStarC_Ident.pretty_ident i in
        let uu___2 = let uu___3 = pp_list' pp_term args in [uu___3] in uu___1
          :: uu___2 in
      ctor "Op" uu___
  | Uvar id ->
      let uu___ =
        let uu___1 = FStarC_Class_PP.pp FStarC_Ident.pretty_ident id in
        [uu___1] in
      ctor "Uvar" uu___
  | Var l ->
      let uu___ =
        let uu___1 = FStarC_Class_PP.pp FStarC_Ident.pretty_lident l in
        [uu___1] in
      ctor "Var" uu___
  | Name l ->
      let uu___ =
        let uu___1 = FStarC_Class_PP.pp FStarC_Ident.pretty_lident l in
        [uu___1] in
      ctor "Name" uu___
  | Projector (rec_lid, field_id) ->
      let uu___ =
        let uu___1 = FStarC_Class_PP.pp FStarC_Ident.pretty_lident rec_lid in
        let uu___2 =
          let uu___3 = FStarC_Class_PP.pp FStarC_Ident.pretty_ident field_id in
          [uu___3] in
        uu___1 :: uu___2 in
      ctor "Projector" uu___
  | Construct (l, args) ->
      let uu___ =
        let uu___1 = FStarC_Class_PP.pp FStarC_Ident.pretty_lident l in
        let uu___2 =
          let uu___3 =
            pp_list'
              (fun uu___4 ->
                 match uu___4 with
                 | (a, imp1) ->
                     let uu___5 =
                       let uu___6 = pp_term a in
                       let uu___7 =
                         let uu___8 = FStarC_Class_PP.pp pretty_imp imp1 in
                         [uu___8] in
                       uu___6 :: uu___7 in
                     ctor "Arg" uu___5) args in
          [uu___3] in
        uu___1 :: uu___2 in
      ctor "Construct" uu___
  | Function (branches, r) ->
      let pp_branch uu___ =
        match uu___ with
        | (p, w, e) ->
            let when_doc =
              match w with
              | FStar_Pervasives_Native.None -> FStar_Pprint.empty
              | FStar_Pervasives_Native.Some w1 ->
                  let uu___1 = pp_term w1 in
                  FStar_Pprint.op_Hat_Slash_Hat
                    (FStar_Pprint.doc_of_string "when") uu___1 in
            let uu___1 =
              let uu___2 = pp_pattern p in
              let uu___3 =
                let uu___4 = let uu___5 = pp_term e in [uu___5] in when_doc
                  :: uu___4 in
              uu___2 :: uu___3 in
            ctor "Branch" uu___1 in
      let uu___ =
        let uu___1 = pp_list' pp_branch branches in
        let uu___2 =
          let uu___3 = FStarC_Class_PP.pp FStarC_Range_Ops.pretty_range r in
          [uu___3] in
        uu___1 :: uu___2 in
      ctor "Function" uu___
  | Abs (pats, t1) ->
      let uu___ =
        let uu___1 = pp_list' pp_pattern pats in
        let uu___2 = let uu___3 = pp_term t1 in [uu___3] in uu___1 :: uu___2 in
      ctor "Abs" uu___
  | App (t1, t2, imp1) ->
      let uu___ =
        let uu___1 = pp_term t1 in
        let uu___2 =
          let uu___3 = pp_term t2 in
          let uu___4 =
            let uu___5 = FStarC_Class_PP.pp pretty_imp imp1 in [uu___5] in
          uu___3 :: uu___4 in
        uu___1 :: uu___2 in
      ctor "App" uu___
  | Let (q, lbs, body) ->
      let pp_letbinding uu___ =
        match uu___ with
        | (_attrs, (p, b)) ->
            let uu___1 =
              let uu___2 = pp_pattern p in
              let uu___3 = let uu___4 = pp_term b in [uu___4] in uu___2 ::
                uu___3 in
            ctor "LetBinding" uu___1 in
      let uu___ =
        let uu___1 =
          let uu___2 =
            FStarC_Class_Show.show showable_string_of_local_let_qualifier q in
          FStar_Pprint.doc_of_string uu___2 in
        let uu___2 =
          let uu___3 = pp_list' pp_letbinding lbs in
          let uu___4 = let uu___5 = pp_term body in [uu___5] in uu___3 ::
            uu___4 in
        uu___1 :: uu___2 in
      ctor "Let" uu___
  | LetOperator (lbs, body) ->
      let pp_letopbinding uu___ =
        match uu___ with
        | (i, p, b) ->
            let uu___1 =
              let uu___2 = FStarC_Class_PP.pp FStarC_Ident.pretty_ident i in
              let uu___3 =
                let uu___4 = pp_pattern p in
                let uu___5 = let uu___6 = pp_term b in [uu___6] in uu___4 ::
                  uu___5 in
              uu___2 :: uu___3 in
            ctor "LetOpBinding" uu___1 in
      let uu___ =
        let uu___1 = pp_list' pp_letopbinding lbs in
        let uu___2 = let uu___3 = pp_term body in [uu___3] in uu___1 ::
          uu___2 in
      ctor "LetOperator" uu___
  | LetOpen (lid, t1) ->
      let uu___ =
        let uu___1 = FStarC_Class_PP.pp FStarC_Ident.pretty_lident lid in
        let uu___2 = let uu___3 = pp_term t1 in [uu___3] in uu___1 :: uu___2 in
      ctor "LetOpen" uu___
  | LetOpenRecord (t1, t2, t3) ->
      let uu___ =
        let uu___1 = pp_term t1 in
        let uu___2 =
          let uu___3 = pp_term t2 in
          let uu___4 = let uu___5 = pp_term t3 in [uu___5] in uu___3 ::
            uu___4 in
        uu___1 :: uu___2 in
      ctor "LetOpenRecord" uu___
  | Seq (t1, t2) ->
      let uu___ =
        let uu___1 = pp_term t1 in
        let uu___2 = let uu___3 = pp_term t2 in [uu___3] in uu___1 :: uu___2 in
      ctor "Seq" uu___
  | Bind (i, t1, t2) ->
      let uu___ =
        let uu___1 = FStarC_Class_PP.pp FStarC_Ident.pretty_ident i in
        let uu___2 =
          let uu___3 = pp_term t1 in
          let uu___4 = let uu___5 = pp_term t2 in [uu___5] in uu___3 ::
            uu___4 in
        uu___1 :: uu___2 in
      ctor "Bind" uu___
  | If (t1, i_opt, mra_opt, t2, t3) ->
      let pp_opt_ident uu___ =
        match uu___ with
        | FStar_Pervasives_Native.None -> FStar_Pprint.doc_of_string "None"
        | FStar_Pervasives_Native.Some i ->
            FStarC_Class_PP.pp FStarC_Ident.pretty_ident i in
      let pp_opt_mra uu___ =
        match uu___ with
        | FStar_Pervasives_Native.None -> FStar_Pprint.doc_of_string "None"
        | FStar_Pervasives_Native.Some (i_opt1, t4, b) ->
            let uu___1 =
              let uu___2 = pp_opt_ident i_opt1 in
              let uu___3 =
                let uu___4 = pp_term t4 in
                let uu___5 =
                  let uu___6 =
                    let uu___7 =
                      FStarC_Class_Show.show FStarC_Class_Show.showable_bool
                        b in
                    FStar_Pprint.doc_of_string uu___7 in
                  [uu___6] in
                uu___4 :: uu___5 in
              uu___2 :: uu___3 in
            ctor "MatchReturns" uu___1 in
      let uu___ =
        let uu___1 = pp_term t1 in
        let uu___2 =
          let uu___3 = pp_opt_ident i_opt in
          let uu___4 =
            let uu___5 = pp_opt_mra mra_opt in
            let uu___6 =
              let uu___7 = pp_term t2 in
              let uu___8 = let uu___9 = pp_term t3 in [uu___9] in uu___7 ::
                uu___8 in
            uu___5 :: uu___6 in
          uu___3 :: uu___4 in
        uu___1 :: uu___2 in
      ctor "If" uu___
  | Match (t1, i_opt, mra_opt, branches) ->
      let pp_opt_ident uu___ =
        match uu___ with
        | FStar_Pervasives_Native.None -> FStar_Pprint.doc_of_string "None"
        | FStar_Pervasives_Native.Some i ->
            FStarC_Class_PP.pp FStarC_Ident.pretty_ident i in
      let pp_opt_mra uu___ =
        match uu___ with
        | FStar_Pervasives_Native.None -> FStar_Pprint.doc_of_string "None"
        | FStar_Pervasives_Native.Some (i_opt1, t2, b) ->
            let uu___1 =
              let uu___2 = pp_opt_ident i_opt1 in
              let uu___3 =
                let uu___4 = pp_term t2 in
                let uu___5 =
                  let uu___6 =
                    let uu___7 =
                      FStarC_Class_Show.show FStarC_Class_Show.showable_bool
                        b in
                    FStar_Pprint.doc_of_string uu___7 in
                  [uu___6] in
                uu___4 :: uu___5 in
              uu___2 :: uu___3 in
            ctor "MatchReturns" uu___1 in
      let pp_branch uu___ =
        match uu___ with
        | (p, w, e) ->
            let when_doc =
              match w with
              | FStar_Pervasives_Native.None -> FStar_Pprint.empty
              | FStar_Pervasives_Native.Some w1 ->
                  let uu___1 = pp_term w1 in
                  FStar_Pprint.op_Hat_Slash_Hat
                    (FStar_Pprint.doc_of_string "when") uu___1 in
            let uu___1 =
              let uu___2 = pp_pattern p in
              let uu___3 =
                let uu___4 = let uu___5 = pp_term e in [uu___5] in when_doc
                  :: uu___4 in
              uu___2 :: uu___3 in
            ctor "Branch" uu___1 in
      let uu___ =
        let uu___1 = pp_term t1 in
        let uu___2 =
          let uu___3 = pp_opt_ident i_opt in
          let uu___4 =
            let uu___5 = pp_opt_mra mra_opt in
            let uu___6 = let uu___7 = pp_list' pp_branch branches in [uu___7] in
            uu___5 :: uu___6 in
          uu___3 :: uu___4 in
        uu___1 :: uu___2 in
      ctor "Match" uu___
  | TryWith (t1, branches) ->
      let pp_branch uu___ =
        match uu___ with
        | (p, w, e) ->
            let when_doc =
              match w with
              | FStar_Pervasives_Native.None -> FStar_Pprint.empty
              | FStar_Pervasives_Native.Some w1 ->
                  let uu___1 = pp_term w1 in
                  FStar_Pprint.op_Hat_Slash_Hat
                    (FStar_Pprint.doc_of_string "when") uu___1 in
            let uu___1 =
              let uu___2 = pp_pattern p in
              let uu___3 =
                let uu___4 = let uu___5 = pp_term e in [uu___5] in when_doc
                  :: uu___4 in
              uu___2 :: uu___3 in
            ctor "Branch" uu___1 in
      let uu___ =
        let uu___1 = pp_term t1 in
        let uu___2 = let uu___3 = pp_list' pp_branch branches in [uu___3] in
        uu___1 :: uu___2 in
      ctor "TryWith" uu___
  | Ascribed (t1, t2, t3_opt, b) ->
      let pp_opt_term uu___ =
        match uu___ with
        | FStar_Pervasives_Native.None -> FStar_Pprint.doc_of_string "None"
        | FStar_Pervasives_Native.Some t3 -> pp_term t3 in
      let uu___ =
        let uu___1 = pp_term t1 in
        let uu___2 =
          let uu___3 = pp_term t2 in
          let uu___4 =
            let uu___5 = pp_opt_term t3_opt in
            let uu___6 =
              let uu___7 =
                let uu___8 =
                  FStarC_Class_Show.show FStarC_Class_Show.showable_bool b in
                FStar_Pprint.doc_of_string uu___8 in
              [uu___7] in
            uu___5 :: uu___6 in
          uu___3 :: uu___4 in
        uu___1 :: uu___2 in
      ctor "Ascribed" uu___
  | Record (t_opt, fields) ->
      let pp_opt_term uu___ =
        match uu___ with
        | FStar_Pervasives_Native.None -> FStar_Pprint.doc_of_string "None"
        | FStar_Pervasives_Native.Some t1 -> pp_term t1 in
      let pp_field uu___ =
        match uu___ with
        | (l, t1) ->
            let uu___1 =
              let uu___2 = FStarC_Class_PP.pp FStarC_Ident.pretty_lident l in
              let uu___3 = let uu___4 = pp_term t1 in [uu___4] in uu___2 ::
                uu___3 in
            ctor "Field" uu___1 in
      let uu___ =
        let uu___1 = pp_opt_term t_opt in
        let uu___2 = let uu___3 = pp_list' pp_field fields in [uu___3] in
        uu___1 :: uu___2 in
      ctor "Record" uu___
  | Project (t1, l) ->
      let uu___ =
        let uu___1 = pp_term t1 in
        let uu___2 =
          let uu___3 = FStarC_Class_PP.pp FStarC_Ident.pretty_lident l in
          [uu___3] in
        uu___1 :: uu___2 in
      ctor "Project" uu___
  | Product (binders, t1) ->
      let uu___ =
        let uu___1 = pp_list' pp_binder binders in
        let uu___2 = let uu___3 = pp_term t1 in [uu___3] in uu___1 :: uu___2 in
      ctor "Product" uu___
  | Sum (binders_or_terms, t1) ->
      let pp_either uu___ =
        match uu___ with
        | FStar_Pervasives.Inl b ->
            let uu___1 = let uu___2 = pp_binder b in [uu___2] in
            ctor "Inl" uu___1
        | FStar_Pervasives.Inr t2 ->
            let uu___1 = let uu___2 = pp_term t2 in [uu___2] in
            ctor "Inr" uu___1 in
      let uu___ =
        let uu___1 = pp_list' pp_either binders_or_terms in
        let uu___2 = let uu___3 = pp_term t1 in [uu___3] in uu___1 :: uu___2 in
      ctor "Sum" uu___
  | QForall (binders, pats, t1) ->
      let pp_patterns uu___ =
        match uu___ with
        | (idents, patterns_list) ->
            let uu___1 =
              let uu___2 =
                pp_list' (FStarC_Class_PP.pp FStarC_Ident.pretty_ident)
                  idents in
              let uu___3 =
                let uu___4 = pp_list' (pp_list' pp_term) patterns_list in
                [uu___4] in
              uu___2 :: uu___3 in
            ctor "Patterns" uu___1 in
      let uu___ =
        let uu___1 = pp_list' pp_binder binders in
        let uu___2 =
          let uu___3 = pp_patterns pats in
          let uu___4 = let uu___5 = pp_term t1 in [uu___5] in uu___3 ::
            uu___4 in
        uu___1 :: uu___2 in
      ctor "QForall" uu___
  | QExists (binders, pats, t1) ->
      let pp_patterns uu___ =
        match uu___ with
        | (idents, patterns_list) ->
            let uu___1 =
              let uu___2 =
                pp_list' (FStarC_Class_PP.pp FStarC_Ident.pretty_ident)
                  idents in
              let uu___3 =
                let uu___4 = pp_list' (pp_list' pp_term) patterns_list in
                [uu___4] in
              uu___2 :: uu___3 in
            ctor "Patterns" uu___1 in
      let uu___ =
        let uu___1 = pp_list' pp_binder binders in
        let uu___2 =
          let uu___3 = pp_patterns pats in
          let uu___4 = let uu___5 = pp_term t1 in [uu___5] in uu___3 ::
            uu___4 in
        uu___1 :: uu___2 in
      ctor "QExists" uu___
  | QuantOp (i, binders, pats, t1) ->
      let pp_patterns uu___ =
        match uu___ with
        | (idents, patterns_list) ->
            let uu___1 =
              let uu___2 =
                pp_list' (FStarC_Class_PP.pp FStarC_Ident.pretty_ident)
                  idents in
              let uu___3 =
                let uu___4 = pp_list' (pp_list' pp_term) patterns_list in
                [uu___4] in
              uu___2 :: uu___3 in
            ctor "Patterns" uu___1 in
      let uu___ =
        let uu___1 = FStarC_Class_PP.pp FStarC_Ident.pretty_ident i in
        let uu___2 =
          let uu___3 = pp_list' pp_binder binders in
          let uu___4 =
            let uu___5 = pp_patterns pats in
            let uu___6 = let uu___7 = pp_term t1 in [uu___7] in uu___5 ::
              uu___6 in
          uu___3 :: uu___4 in
        uu___1 :: uu___2 in
      ctor "QuantOp" uu___
  | Refine (b, t1) ->
      let uu___ =
        let uu___1 = pp_binder b in
        let uu___2 = let uu___3 = pp_term t1 in [uu___3] in uu___1 :: uu___2 in
      ctor "Refine" uu___
  | NamedTyp (i, t1) ->
      let uu___ =
        let uu___1 = FStarC_Class_PP.pp FStarC_Ident.pretty_ident i in
        let uu___2 = let uu___3 = pp_term t1 in [uu___3] in uu___1 :: uu___2 in
      ctor "NamedTyp" uu___
  | Paren t1 ->
      let uu___ = let uu___1 = pp_term t1 in [uu___1] in ctor "Paren" uu___
  | Requires t1 ->
      let uu___ = let uu___1 = pp_term t1 in [uu___1] in
      ctor "Requires" uu___
  | Ensures t1 ->
      let uu___ = let uu___1 = pp_term t1 in [uu___1] in ctor "Ensures" uu___
  | LexList ts ->
      let uu___ = let uu___1 = pp_list' pp_term ts in [uu___1] in
      ctor "LexList" uu___
  | WFOrder (t1, t2) ->
      let uu___ =
        let uu___1 = pp_term t1 in
        let uu___2 = let uu___3 = pp_term t2 in [uu___3] in uu___1 :: uu___2 in
      ctor "WFOrder" uu___
  | Decreases t1 ->
      let uu___ = let uu___1 = pp_term t1 in [uu___1] in
      ctor "Decreases" uu___
  | Labeled (t1, s, b) ->
      let uu___ =
        let uu___1 = pp_term t1 in
        let uu___2 =
          let uu___3 =
            let uu___4 =
              let uu___5 =
                FStarC_Class_Show.show FStarC_Class_Show.showable_bool b in
              FStar_Pprint.doc_of_string uu___5 in
            [uu___4] in
          (FStar_Pprint.doc_of_string s) :: uu___3 in
        uu___1 :: uu___2 in
      ctor "Labeled" uu___
  | Discrim l ->
      let uu___ =
        let uu___1 = FStarC_Class_PP.pp FStarC_Ident.pretty_lident l in
        [uu___1] in
      ctor "Discrim" uu___
  | Attributes ts ->
      let uu___ = let uu___1 = pp_list' pp_term ts in [uu___1] in
      ctor "Attributes" uu___
  | Antiquote t1 ->
      let uu___ = let uu___1 = pp_term t1 in [uu___1] in
      ctor "Antiquote" uu___
  | Quote (t1, qk) ->
      let uu___ =
        let uu___1 = pp_term t1 in
        let uu___2 =
          let uu___3 =
            let uu___4 = FStarC_Class_Show.show showable_quote_kind qk in
            FStar_Pprint.doc_of_string uu___4 in
          [uu___3] in
        uu___1 :: uu___2 in
      ctor "Quote" uu___
  | VQuote t1 ->
      let uu___ = let uu___1 = pp_term t1 in [uu___1] in ctor "VQuote" uu___
  | CalcProof (rel, init, steps) ->
      let uu___ =
        let uu___1 = pp_term rel in
        let uu___2 =
          let uu___3 = pp_term init in
          let uu___4 = let uu___5 = pp_list' pp_calc_step steps in [uu___5] in
          uu___3 :: uu___4 in
        uu___1 :: uu___2 in
      ctor "CalcProof" uu___
  | IntroForall (binders, t1, t2) ->
      let uu___ =
        let uu___1 = pp_list' pp_binder binders in
        let uu___2 =
          let uu___3 = pp_term t1 in
          let uu___4 = let uu___5 = pp_term t2 in [uu___5] in uu___3 ::
            uu___4 in
        uu___1 :: uu___2 in
      ctor "IntroForall" uu___
  | IntroExists (binders, t1, ts, t2) ->
      let uu___ =
        let uu___1 = pp_list' pp_binder binders in
        let uu___2 =
          let uu___3 = pp_term t1 in
          let uu___4 =
            let uu___5 = pp_list' pp_term ts in
            let uu___6 = let uu___7 = pp_term t2 in [uu___7] in uu___5 ::
              uu___6 in
          uu___3 :: uu___4 in
        uu___1 :: uu___2 in
      ctor "IntroExists" uu___
  | IntroImplies (t1, t2, b, t3) ->
      let uu___ =
        let uu___1 = pp_term t1 in
        let uu___2 =
          let uu___3 = pp_term t2 in
          let uu___4 =
            let uu___5 = pp_binder b in
            let uu___6 = let uu___7 = pp_term t3 in [uu___7] in uu___5 ::
              uu___6 in
          uu___3 :: uu___4 in
        uu___1 :: uu___2 in
      ctor "IntroImplies" uu___
  | IntroOr (is_left, t1, t2, t3) ->
      let uu___ =
        let uu___1 =
          let uu___2 =
            FStarC_Class_Show.show FStarC_Class_Show.showable_bool is_left in
          FStar_Pprint.doc_of_string uu___2 in
        let uu___2 =
          let uu___3 = pp_term t1 in
          let uu___4 =
            let uu___5 = pp_term t2 in
            let uu___6 = let uu___7 = pp_term t3 in [uu___7] in uu___5 ::
              uu___6 in
          uu___3 :: uu___4 in
        uu___1 :: uu___2 in
      ctor "IntroOr" uu___
  | IntroAnd (t1, t2, t3, t4) ->
      let uu___ =
        let uu___1 = pp_term t1 in
        let uu___2 =
          let uu___3 = pp_term t2 in
          let uu___4 =
            let uu___5 = pp_term t3 in
            let uu___6 = let uu___7 = pp_term t4 in [uu___7] in uu___5 ::
              uu___6 in
          uu___3 :: uu___4 in
        uu___1 :: uu___2 in
      ctor "IntroAnd" uu___
  | ElimForall (binders, t1, ts) ->
      let uu___ =
        let uu___1 = pp_list' pp_binder binders in
        let uu___2 =
          let uu___3 = pp_term t1 in
          let uu___4 = let uu___5 = pp_list' pp_term ts in [uu___5] in uu___3
            :: uu___4 in
        uu___1 :: uu___2 in
      ctor "ElimForall" uu___
  | ElimExists (binders, t1, t2, b, t3) ->
      let uu___ =
        let uu___1 = pp_list' pp_binder binders in
        let uu___2 =
          let uu___3 = pp_term t1 in
          let uu___4 =
            let uu___5 = pp_term t2 in
            let uu___6 =
              let uu___7 = pp_binder b in
              let uu___8 = let uu___9 = pp_term t3 in [uu___9] in uu___7 ::
                uu___8 in
            uu___5 :: uu___6 in
          uu___3 :: uu___4 in
        uu___1 :: uu___2 in
      ctor "ElimExists" uu___
  | ElimImplies (t1, t2, t3) ->
      let uu___ =
        let uu___1 = pp_term t1 in
        let uu___2 =
          let uu___3 = pp_term t2 in
          let uu___4 = let uu___5 = pp_term t3 in [uu___5] in uu___3 ::
            uu___4 in
        uu___1 :: uu___2 in
      ctor "ElimImplies" uu___
  | ElimOr (t1, t2, t3, b1, t4, b2, t5) ->
      let uu___ =
        let uu___1 = pp_term t1 in
        let uu___2 =
          let uu___3 = pp_term t2 in
          let uu___4 =
            let uu___5 = pp_term t3 in
            let uu___6 =
              let uu___7 = pp_binder b1 in
              let uu___8 =
                let uu___9 = pp_term t4 in
                let uu___10 =
                  let uu___11 = pp_binder b2 in
                  let uu___12 = let uu___13 = pp_term t5 in [uu___13] in
                  uu___11 :: uu___12 in
                uu___9 :: uu___10 in
              uu___7 :: uu___8 in
            uu___5 :: uu___6 in
          uu___3 :: uu___4 in
        uu___1 :: uu___2 in
      ctor "ElimOr" uu___
  | ElimAnd (t1, t2, t3, b1, b2, t4) ->
      let uu___ =
        let uu___1 = pp_term t1 in
        let uu___2 =
          let uu___3 = pp_term t2 in
          let uu___4 =
            let uu___5 = pp_term t3 in
            let uu___6 =
              let uu___7 = pp_binder b1 in
              let uu___8 =
                let uu___9 = pp_binder b2 in
                let uu___10 = let uu___11 = pp_term t4 in [uu___11] in uu___9
                  :: uu___10 in
              uu___7 :: uu___8 in
            uu___5 :: uu___6 in
          uu___3 :: uu___4 in
        uu___1 :: uu___2 in
      ctor "ElimAnd" uu___
  | ListLiteral ts ->
      let uu___ = let uu___1 = pp_list' pp_term ts in [uu___1] in
      ctor "ListLiteral" uu___
  | SeqLiteral ts ->
      let uu___ = let uu___1 = pp_list' pp_term ts in [uu___1] in
      ctor "SeqLiteral" uu___
  | LitDoc d -> ctor "LitDoc" [d]
and pp_binder (b : binder) : FStar_Pprint.document=
  match b.b with
  | Variable i ->
      let uu___ =
        let uu___1 = FStarC_Class_PP.pp FStarC_Ident.pretty_ident i in
        [uu___1] in
      ctor "Variable" uu___
  | Annotated (i, t) ->
      let uu___ =
        let uu___1 = FStarC_Class_PP.pp FStarC_Ident.pretty_ident i in
        let uu___2 = let uu___3 = pp_term t in [uu___3] in uu___1 :: uu___2 in
      ctor "Annotated" uu___
  | NoName t ->
      let uu___ = let uu___1 = pp_term t in [uu___1] in ctor "NoName" uu___
and pp_calc_step (uu___ : calc_step) : FStar_Pprint.document=
  match uu___ with
  | CalcStep (rel, just, next) ->
      let uu___1 =
        let uu___2 = pp_term rel in
        let uu___3 =
          let uu___4 = pp_term just in
          let uu___5 = let uu___6 = pp_term next in [uu___6] in uu___4 ::
            uu___5 in
        uu___2 :: uu___3 in
      ctor "CalcStep" uu___1
and pp_pattern (p : pattern) : FStar_Pprint.document=
  match p.pat with
  | PatWild (i_opt, attrs) ->
      let pp_opt_id uu___ =
        match uu___ with
        | FStar_Pervasives_Native.None -> FStar_Pprint.doc_of_string "None"
        | FStar_Pervasives_Native.Some i ->
            FStarC_Class_PP.pp pretty_arg_qualifier i in
      let pp_attrs = pp_list' pp_term attrs in
      let uu___ = let uu___1 = pp_opt_id i_opt in [uu___1; pp_attrs] in
      ctor "PatWild" uu___
  | PatConst c ->
      let uu___ =
        let uu___1 =
          let uu___2 = FStarC_Parser_Const.const_to_string c in
          FStar_Pprint.doc_of_string uu___2 in
        [uu___1] in
      ctor "PatConst" uu___
  | PatVQuote t ->
      let uu___ = let uu___1 = pp_term t in [uu___1] in
      ctor "PatVQuote" uu___
  | PatApp (p1, ps) ->
      let uu___ =
        let uu___1 = pp_pattern p1 in
        let uu___2 = let uu___3 = pp_list' pp_pattern ps in [uu___3] in
        uu___1 :: uu___2 in
      ctor "PatApp" uu___
  | PatVar (i, aq, attrs) ->
      let pp_attrs = pp_list' pp_term attrs in
      let uu___ =
        let uu___1 = FStarC_Class_PP.pp FStarC_Ident.pretty_ident i in
        let uu___2 =
          let uu___3 =
            let uu___4 =
              FStarC_Class_Show.show
                (FStarC_Class_Show.show_option showable_arg_qualifier) aq in
            FStar_Pprint.doc_of_string uu___4 in
          [uu___3; pp_attrs] in
        uu___1 :: uu___2 in
      ctor "PatVar" uu___
  | PatName l ->
      let uu___ =
        let uu___1 = FStarC_Class_PP.pp FStarC_Ident.pretty_lident l in
        [uu___1] in
      ctor "PatName" uu___
  | PatList ps ->
      let uu___ = let uu___1 = pp_list' pp_pattern ps in [uu___1] in
      ctor "PatList" uu___
  | PatTuple (ps, b) ->
      let uu___ =
        let uu___1 = pp_list' pp_pattern ps in
        let uu___2 =
          let uu___3 =
            let uu___4 =
              FStarC_Class_Show.show FStarC_Class_Show.showable_bool b in
            FStar_Pprint.doc_of_string uu___4 in
          [uu___3] in
        uu___1 :: uu___2 in
      ctor "PatTuple" uu___
  | PatRecord fields ->
      let pp_field uu___ =
        match uu___ with
        | (l, p1) ->
            let uu___1 =
              let uu___2 = FStarC_Class_PP.pp FStarC_Ident.pretty_lident l in
              let uu___3 = let uu___4 = pp_pattern p1 in [uu___4] in uu___2
                :: uu___3 in
            ctor "Field" uu___1 in
      let uu___ = let uu___1 = pp_list' pp_field fields in [uu___1] in
      ctor "PatRecord" uu___
  | PatOr ps ->
      let uu___ = let uu___1 = pp_list' pp_pattern ps in [uu___1] in
      ctor "PatOr" uu___
  | PatOp op ->
      let uu___ =
        let uu___1 = FStarC_Class_PP.pp FStarC_Ident.pretty_ident op in
        [uu___1] in
      ctor "PatOp" uu___
  | PatAscribed (p1, (t, tac_opt)) ->
      let pp_opt_term uu___ =
        match uu___ with
        | FStar_Pervasives_Native.None -> FStar_Pprint.doc_of_string "None"
        | FStar_Pervasives_Native.Some t1 -> pp_term t1 in
      let uu___ =
        let uu___1 = pp_pattern p1 in
        let uu___2 =
          let uu___3 = pp_term t in
          let uu___4 = let uu___5 = pp_opt_term tac_opt in [uu___5] in uu___3
            :: uu___4 in
        uu___1 :: uu___2 in
      ctor "PatAscribed" uu___
  | PatRest -> ctor "PatRest" []
let pretty_term : term FStarC_Class_PP.pretty=
  { FStarC_Class_PP.pp = pp_term }
let pretty_binder : binder FStarC_Class_PP.pretty=
  { FStarC_Class_PP.pp = pp_binder }
let pretty_pattern : pattern FStarC_Class_PP.pretty=
  { FStarC_Class_PP.pp = pp_pattern }
let pretty_pragma : pragma FStarC_Class_PP.pretty=
  FStarC_Class_PP.pretty_from_showable showable_pragma
let pp_constructor_payload (cp : constructor_payload) :
  FStar_Pprint.document=
  match cp with
  | VpOfNotation t ->
      let uu___ = let uu___1 = pp_term t in [uu___1] in
      ctor "VpOfNotation" uu___
  | VpArbitrary t ->
      let uu___ = let uu___1 = pp_term t in [uu___1] in
      ctor "VpArbitrary" uu___
  | VpRecord (fields, tyopt) ->
      let pp_field uu___ =
        match uu___ with
        | (id, q, attrs, tm) ->
            let uu___1 =
              let uu___2 = FStarC_Class_PP.pp FStarC_Ident.pretty_ident id in
              let uu___3 =
                let uu___4 =
                  FStarC_Class_PP.pp
                    (FStarC_Class_PP.pp_option pretty_arg_qualifier) q in
                let uu___5 =
                  let uu___6 =
                    FStarC_Class_PP.pp (FStarC_Class_PP.pp_list pretty_term)
                      attrs in
                  let uu___7 = let uu___8 = pp_term tm in [uu___8] in uu___6
                    :: uu___7 in
                uu___4 :: uu___5 in
              uu___2 :: uu___3 in
            ctor "Field" uu___1 in
      let uu___ =
        let uu___1 = pp_list' pp_field fields in
        let uu___2 =
          let uu___3 =
            FStarC_Class_PP.pp (FStarC_Class_PP.pp_option pretty_term) tyopt in
          [uu___3] in
        uu___1 :: uu___2 in
      ctor "VpRecord" uu___
let pretty_constructor_payload : constructor_payload FStarC_Class_PP.pretty=
  { FStarC_Class_PP.pp = pp_constructor_payload }
let pp_tycon (tc : tycon) : FStar_Pprint.document=
  match tc with
  | TyconAbstract (i, bs, knd1) ->
      let uu___ =
        let uu___1 = FStarC_Class_PP.pp FStarC_Ident.pretty_ident i in
        let uu___2 =
          let uu___3 =
            FStarC_Class_PP.pp (FStarC_Class_PP.pp_list pretty_binder) bs in
          let uu___4 =
            let uu___5 =
              FStarC_Class_PP.pp (FStarC_Class_PP.pp_option pretty_term) knd1 in
            [uu___5] in
          uu___3 :: uu___4 in
        uu___1 :: uu___2 in
      ctor "TyconAbstract" uu___
  | TyconAbbrev (i, bs, knd1, t) ->
      let uu___ =
        let uu___1 = FStarC_Class_PP.pp FStarC_Ident.pretty_ident i in
        let uu___2 =
          let uu___3 =
            FStarC_Class_PP.pp (FStarC_Class_PP.pp_list pretty_binder) bs in
          let uu___4 =
            let uu___5 =
              FStarC_Class_PP.pp (FStarC_Class_PP.pp_option pretty_term) knd1 in
            [uu___5; FStar_Pprint.doc_of_string "_"] in
          uu___3 :: uu___4 in
        uu___1 :: uu___2 in
      ctor "TyconAbbrev" uu___
  | TyconRecord (i, bs, knd1, attrs, fields) ->
      let pp_field uu___ =
        match uu___ with
        | (id, q, attrs1, tm) ->
            let uu___1 =
              let uu___2 = FStarC_Class_PP.pp FStarC_Ident.pretty_ident id in
              let uu___3 =
                let uu___4 =
                  FStarC_Class_PP.pp
                    (FStarC_Class_PP.pp_option pretty_arg_qualifier) q in
                let uu___5 =
                  let uu___6 =
                    FStarC_Class_PP.pp (FStarC_Class_PP.pp_list pretty_term)
                      attrs1 in
                  let uu___7 = let uu___8 = pp_term tm in [uu___8] in uu___6
                    :: uu___7 in
                uu___4 :: uu___5 in
              uu___2 :: uu___3 in
            ctor "Field" uu___1 in
      let uu___ =
        let uu___1 = FStarC_Class_PP.pp FStarC_Ident.pretty_ident i in
        let uu___2 =
          let uu___3 =
            FStarC_Class_PP.pp (FStarC_Class_PP.pp_list pretty_binder) bs in
          let uu___4 =
            let uu___5 =
              FStarC_Class_PP.pp (FStarC_Class_PP.pp_option pretty_term) knd1 in
            let uu___6 =
              let uu___7 =
                FStarC_Class_PP.pp (FStarC_Class_PP.pp_list pretty_term)
                  attrs in
              let uu___8 = let uu___9 = pp_list' pp_field fields in [uu___9] in
              uu___7 :: uu___8 in
            uu___5 :: uu___6 in
          uu___3 :: uu___4 in
        uu___1 :: uu___2 in
      ctor "TyconRecord" uu___
  | TyconVariant (i, bs, knd1, ctors) ->
      let pp_ctor uu___ =
        match uu___ with
        | (id, payload, attrs) ->
            let uu___1 =
              let uu___2 = FStarC_Class_PP.pp FStarC_Ident.pretty_ident id in
              let uu___3 =
                let uu___4 =
                  FStarC_Class_PP.pp
                    (FStarC_Class_PP.pp_option pretty_constructor_payload)
                    payload in
                let uu___5 =
                  let uu___6 =
                    FStarC_Class_PP.pp (FStarC_Class_PP.pp_list pretty_term)
                      attrs in
                  [uu___6] in
                uu___4 :: uu___5 in
              uu___2 :: uu___3 in
            ctor "Constructor" uu___1 in
      let uu___ =
        let uu___1 = FStarC_Class_PP.pp FStarC_Ident.pretty_ident i in
        let uu___2 =
          let uu___3 =
            FStarC_Class_PP.pp (FStarC_Class_PP.pp_list pretty_binder) bs in
          let uu___4 =
            let uu___5 =
              FStarC_Class_PP.pp (FStarC_Class_PP.pp_option pretty_term) knd1 in
            let uu___6 = let uu___7 = pp_list' pp_ctor ctors in [uu___7] in
            uu___5 :: uu___6 in
          uu___3 :: uu___4 in
        uu___1 :: uu___2 in
      ctor "TyconVariant" uu___
let pretty_tycon : tycon FStarC_Class_PP.pretty=
  { FStarC_Class_PP.pp = pp_tycon }
let pp_decl (d : decl) : FStar_Pprint.document=
  match d.d with
  | TopLevelModule l ->
      let uu___ =
        let uu___1 = FStarC_Class_PP.pp FStarC_Ident.pretty_lident l in
        [uu___1] in
      ctor "TopLevelModule" uu___
  | Open (l, r) ->
      let uu___ =
        let uu___1 = FStarC_Class_PP.pp FStarC_Ident.pretty_lident l in
        let uu___2 =
          let uu___3 =
            let uu___4 =
              FStarC_Class_Show.show
                FStarC_Syntax_Syntax.showable_restriction r in
            FStar_Pprint.doc_of_string uu___4 in
          [uu___3] in
        uu___1 :: uu___2 in
      ctor "Open" uu___
  | Friend l ->
      let uu___ =
        let uu___1 = FStarC_Class_PP.pp FStarC_Ident.pretty_lident l in
        [uu___1] in
      ctor "Friend" uu___
  | Include (l, r) ->
      let uu___ =
        let uu___1 = FStarC_Class_PP.pp FStarC_Ident.pretty_lident l in
        let uu___2 =
          let uu___3 =
            let uu___4 =
              FStarC_Class_Show.show
                FStarC_Syntax_Syntax.showable_restriction r in
            FStar_Pprint.doc_of_string uu___4 in
          [uu___3] in
        uu___1 :: uu___2 in
      ctor "Include" uu___
  | ModuleAbbrev (i, l) ->
      let uu___ =
        let uu___1 = FStarC_Class_PP.pp FStarC_Ident.pretty_ident i in
        let uu___2 =
          let uu___3 = FStarC_Class_PP.pp FStarC_Ident.pretty_lident l in
          [uu___3] in
        uu___1 :: uu___2 in
      ctor "ModuleAbbrev" uu___
  | TopLevelLet (q, pats) ->
      let pp_pat_term uu___ =
        match uu___ with
        | (p, t) ->
            let uu___1 =
              let uu___2 = FStarC_Class_PP.pp pretty_pattern p in
              let uu___3 =
                let uu___4 = FStarC_Class_PP.pp pretty_term t in [uu___4] in
              uu___2 :: uu___3 in
            ctor "PatTerm" uu___1 in
      let uu___ =
        let uu___1 =
          let uu___2 =
            FStarC_Class_Show.show showable_string_of_let_qualifier q in
          FStar_Pprint.doc_of_string uu___2 in
        let uu___2 = let uu___3 = pp_list' pp_pat_term pats in [uu___3] in
        uu___1 :: uu___2 in
      ctor "TopLevelLet" uu___
  | Assume (i, t_opt) ->
      let pp_opt_term uu___ =
        match uu___ with
        | FStar_Pervasives_Native.None -> FStar_Pprint.doc_of_string "None"
        | FStar_Pervasives_Native.Some t -> pp_term t in
      let uu___ =
        let uu___1 = FStarC_Class_PP.pp FStarC_Ident.pretty_ident i in
        let uu___2 = let uu___3 = pp_term t_opt in [uu___3] in uu___1 ::
          uu___2 in
      ctor "Assume" uu___
  | Tycon (r, tps, tys) ->
      let uu___ =
        let uu___1 = FStarC_Class_PP.pp FStarC_Class_PP.pp_bool r in
        let uu___2 =
          let uu___3 = FStarC_Class_PP.pp FStarC_Class_PP.pp_bool tps in
          let uu___4 =
            let uu___5 =
              FStarC_Class_PP.pp (FStarC_Class_PP.pp_list pretty_tycon) tys in
            [uu___5] in
          uu___3 :: uu___4 in
        uu___1 :: uu___2 in
      ctor "Tycon" uu___
  | Val (i, t) ->
      let uu___ =
        let uu___1 = FStarC_Class_PP.pp FStarC_Ident.pretty_ident i in
        let uu___2 = let uu___3 = pp_term t in [uu___3] in uu___1 :: uu___2 in
      ctor "Val" uu___
  | Exception (i, t_opt) ->
      let pp_opt_term uu___ =
        match uu___ with
        | FStar_Pervasives_Native.None -> FStar_Pprint.doc_of_string "None"
        | FStar_Pervasives_Native.Some t -> pp_term t in
      let uu___ =
        let uu___1 = FStarC_Class_PP.pp FStarC_Ident.pretty_ident i in
        let uu___2 = let uu___3 = pp_opt_term t_opt in [uu___3] in uu___1 ::
          uu___2 in
      ctor "Exception" uu___
  | NewEffect eff_def -> ctor "NewEffect" []
  | LayeredEffect eff_def -> ctor "LayeredEffect" []
  | Polymonadic_bind (l1, l2, l3, t) ->
      let uu___ =
        let uu___1 = FStarC_Class_PP.pp FStarC_Ident.pretty_lident l1 in
        let uu___2 =
          let uu___3 = FStarC_Class_PP.pp FStarC_Ident.pretty_lident l2 in
          let uu___4 =
            let uu___5 = FStarC_Class_PP.pp FStarC_Ident.pretty_lident l3 in
            let uu___6 = let uu___7 = pp_term t in [uu___7] in uu___5 ::
              uu___6 in
          uu___3 :: uu___4 in
        uu___1 :: uu___2 in
      ctor "Polymonadic_bind" uu___
  | Polymonadic_subcomp (l1, l2, t) ->
      let uu___ =
        let uu___1 = FStarC_Class_PP.pp FStarC_Ident.pretty_lident l1 in
        let uu___2 =
          let uu___3 = FStarC_Class_PP.pp FStarC_Ident.pretty_lident l2 in
          let uu___4 = let uu___5 = pp_term t in [uu___5] in uu___3 :: uu___4 in
        uu___1 :: uu___2 in
      ctor "Polymonadic_subcomp" uu___
  | Splice (is_typed, ids, t) ->
      let uu___ =
        let uu___1 =
          let uu___2 =
            FStarC_Class_Show.show FStarC_Class_Show.showable_bool is_typed in
          FStar_Pprint.doc_of_string uu___2 in
        let uu___2 =
          let uu___3 =
            pp_list' (FStarC_Class_PP.pp FStarC_Ident.pretty_ident) ids in
          let uu___4 = let uu___5 = pp_term t in [uu___5] in uu___3 :: uu___4 in
        uu___1 :: uu___2 in
      ctor "Splice" uu___
  | SubEffect se -> ctor "SubEffect" []
  | Pragma p ->
      let uu___ = let uu___1 = FStarC_Class_PP.pp pretty_pragma p in [uu___1] in
      ctor "Pragma" uu___
  | DeclSyntaxExtension (id, content, uu___, uu___1) ->
      ctor "DeclSyntaxExtension"
        [FStar_Pprint.doc_of_string id; FStar_Pprint.doc_of_string content]
  | DeclToBeDesugared tbs ->
      let uu___ =
        let uu___1 =
          let uu___2 =
            let uu___3 =
              let uu___4 = tbs.to_string tbs.blob in Prims.strcat uu___4 ")" in
            Prims.strcat "(to_be_desugared: " uu___3 in
          FStar_Pprint.doc_of_string uu___2 in
        [uu___1] in
      ctor "DeclToBeDesugared" uu___
  | UseLangDecls str -> ctor "UseLangDecls" [FStar_Pprint.doc_of_string str]
  | Unparseable -> ctor "Unparseable" []
let pretty_decl : decl FStarC_Class_PP.pretty=
  { FStarC_Class_PP.pp = pp_decl }
let pp_modul (m : modul) : FStar_Pprint.document=
  match m with
  | Module { no_prelude = uu___; mname = uu___1; decls;_} ->
      let uu___2 =
        let uu___3 =
          FStarC_Class_PP.pp (FStarC_Class_PP.pp_list pretty_decl) decls in
        [uu___3] in
      ctor "Module" uu___2
  | Interface
      { no_prelude1 = uu___; mname1 = uu___1; decls1 = decls;
        admitted = uu___2;_}
      ->
      let uu___3 =
        let uu___4 =
          FStarC_Class_PP.pp (FStarC_Class_PP.pp_list pretty_decl) decls in
        [uu___4] in
      ctor "Interface" uu___3
let pretty_modul : modul FStarC_Class_PP.pretty=
  { FStarC_Class_PP.pp = pp_modul }
