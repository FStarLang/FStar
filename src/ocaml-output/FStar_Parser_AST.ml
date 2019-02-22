open Prims
type level =
  | Un 
  | Expr 
  | Type_level 
  | Kind 
  | Formula 
let (uu___is_Un : level -> Prims.bool) =
  fun projectee  -> match projectee with | Un  -> true | uu____39040 -> false 
let (uu___is_Expr : level -> Prims.bool) =
  fun projectee  ->
    match projectee with | Expr  -> true | uu____39051 -> false
  
let (uu___is_Type_level : level -> Prims.bool) =
  fun projectee  ->
    match projectee with | Type_level  -> true | uu____39062 -> false
  
let (uu___is_Kind : level -> Prims.bool) =
  fun projectee  ->
    match projectee with | Kind  -> true | uu____39073 -> false
  
let (uu___is_Formula : level -> Prims.bool) =
  fun projectee  ->
    match projectee with | Formula  -> true | uu____39084 -> false
  
type let_qualifier =
  | NoLetQualifier 
  | Rec 
let (uu___is_NoLetQualifier : let_qualifier -> Prims.bool) =
  fun projectee  ->
    match projectee with | NoLetQualifier  -> true | uu____39095 -> false
  
let (uu___is_Rec : let_qualifier -> Prims.bool) =
  fun projectee  ->
    match projectee with | Rec  -> true | uu____39106 -> false
  
type quote_kind =
  | Static 
  | Dynamic 
let (uu___is_Static : quote_kind -> Prims.bool) =
  fun projectee  ->
    match projectee with | Static  -> true | uu____39117 -> false
  
let (uu___is_Dynamic : quote_kind -> Prims.bool) =
  fun projectee  ->
    match projectee with | Dynamic  -> true | uu____39128 -> false
  
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
  | Seq of (term * term) 
  | Bind of (FStar_Ident.ident * term * term) 
  | If of (term * term * term) 
  | Match of (term * (pattern * term FStar_Pervasives_Native.option * term)
  Prims.list) 
  | TryWith of (term * (pattern * term FStar_Pervasives_Native.option * term)
  Prims.list) 
  | Ascribed of (term * term * term FStar_Pervasives_Native.option) 
  | Record of (term FStar_Pervasives_Native.option * (FStar_Ident.lid * term)
  Prims.list) 
  | Project of (term * FStar_Ident.lid) 
  | Product of (binder Prims.list * term) 
  | Sum of ((binder,term) FStar_Util.either Prims.list * term) 
  | QForall of (binder Prims.list * term Prims.list Prims.list * term) 
  | QExists of (binder Prims.list * term Prims.list Prims.list * term) 
  | Refine of (binder * term) 
  | NamedTyp of (FStar_Ident.ident * term) 
  | Paren of term 
  | Requires of (term * Prims.string FStar_Pervasives_Native.option) 
  | Ensures of (term * Prims.string FStar_Pervasives_Native.option) 
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
  aqual: arg_qualifier FStar_Pervasives_Native.option }
and pattern' =
  | PatWild of arg_qualifier FStar_Pervasives_Native.option 
  | PatConst of FStar_Const.sconst 
  | PatApp of (pattern * pattern Prims.list) 
  | PatVar of (FStar_Ident.ident * arg_qualifier
  FStar_Pervasives_Native.option) 
  | PatName of FStar_Ident.lid 
  | PatTvar of (FStar_Ident.ident * arg_qualifier
  FStar_Pervasives_Native.option) 
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
  fun projectee  ->
    match projectee with | Wild  -> true | uu____39735 -> false
  
let (uu___is_Const : term' -> Prims.bool) =
  fun projectee  ->
    match projectee with | Const _0 -> true | uu____39747 -> false
  
let (__proj__Const__item___0 : term' -> FStar_Const.sconst) =
  fun projectee  -> match projectee with | Const _0 -> _0 
let (uu___is_Op : term' -> Prims.bool) =
  fun projectee  ->
    match projectee with | Op _0 -> true | uu____39773 -> false
  
let (__proj__Op__item___0 : term' -> (FStar_Ident.ident * term Prims.list)) =
  fun projectee  -> match projectee with | Op _0 -> _0 
let (uu___is_Tvar : term' -> Prims.bool) =
  fun projectee  ->
    match projectee with | Tvar _0 -> true | uu____39811 -> false
  
let (__proj__Tvar__item___0 : term' -> FStar_Ident.ident) =
  fun projectee  -> match projectee with | Tvar _0 -> _0 
let (uu___is_Uvar : term' -> Prims.bool) =
  fun projectee  ->
    match projectee with | Uvar _0 -> true | uu____39831 -> false
  
let (__proj__Uvar__item___0 : term' -> FStar_Ident.ident) =
  fun projectee  -> match projectee with | Uvar _0 -> _0 
let (uu___is_Var : term' -> Prims.bool) =
  fun projectee  ->
    match projectee with | Var _0 -> true | uu____39851 -> false
  
let (__proj__Var__item___0 : term' -> FStar_Ident.lid) =
  fun projectee  -> match projectee with | Var _0 -> _0 
let (uu___is_Name : term' -> Prims.bool) =
  fun projectee  ->
    match projectee with | Name _0 -> true | uu____39871 -> false
  
let (__proj__Name__item___0 : term' -> FStar_Ident.lid) =
  fun projectee  -> match projectee with | Name _0 -> _0 
let (uu___is_Projector : term' -> Prims.bool) =
  fun projectee  ->
    match projectee with | Projector _0 -> true | uu____39895 -> false
  
let (__proj__Projector__item___0 :
  term' -> (FStar_Ident.lid * FStar_Ident.ident)) =
  fun projectee  -> match projectee with | Projector _0 -> _0 
let (uu___is_Construct : term' -> Prims.bool) =
  fun projectee  ->
    match projectee with | Construct _0 -> true | uu____39937 -> false
  
let (__proj__Construct__item___0 :
  term' -> (FStar_Ident.lid * (term * imp) Prims.list)) =
  fun projectee  -> match projectee with | Construct _0 -> _0 
let (uu___is_Abs : term' -> Prims.bool) =
  fun projectee  ->
    match projectee with | Abs _0 -> true | uu____39993 -> false
  
let (__proj__Abs__item___0 : term' -> (pattern Prims.list * term)) =
  fun projectee  -> match projectee with | Abs _0 -> _0 
let (uu___is_App : term' -> Prims.bool) =
  fun projectee  ->
    match projectee with | App _0 -> true | uu____40037 -> false
  
let (__proj__App__item___0 : term' -> (term * term * imp)) =
  fun projectee  -> match projectee with | App _0 -> _0 
let (uu___is_Let : term' -> Prims.bool) =
  fun projectee  ->
    match projectee with | Let _0 -> true | uu____40095 -> false
  
let (__proj__Let__item___0 :
  term' ->
    (let_qualifier * (term Prims.list FStar_Pervasives_Native.option *
      (pattern * term)) Prims.list * term))
  = fun projectee  -> match projectee with | Let _0 -> _0 
let (uu___is_LetOpen : term' -> Prims.bool) =
  fun projectee  ->
    match projectee with | LetOpen _0 -> true | uu____40179 -> false
  
let (__proj__LetOpen__item___0 : term' -> (FStar_Ident.lid * term)) =
  fun projectee  -> match projectee with | LetOpen _0 -> _0 
let (uu___is_Seq : term' -> Prims.bool) =
  fun projectee  ->
    match projectee with | Seq _0 -> true | uu____40215 -> false
  
let (__proj__Seq__item___0 : term' -> (term * term)) =
  fun projectee  -> match projectee with | Seq _0 -> _0 
let (uu___is_Bind : term' -> Prims.bool) =
  fun projectee  ->
    match projectee with | Bind _0 -> true | uu____40253 -> false
  
let (__proj__Bind__item___0 : term' -> (FStar_Ident.ident * term * term)) =
  fun projectee  -> match projectee with | Bind _0 -> _0 
let (uu___is_If : term' -> Prims.bool) =
  fun projectee  ->
    match projectee with | If _0 -> true | uu____40297 -> false
  
let (__proj__If__item___0 : term' -> (term * term * term)) =
  fun projectee  -> match projectee with | If _0 -> _0 
let (uu___is_Match : term' -> Prims.bool) =
  fun projectee  ->
    match projectee with | Match _0 -> true | uu____40349 -> false
  
let (__proj__Match__item___0 :
  term' ->
    (term * (pattern * term FStar_Pervasives_Native.option * term)
      Prims.list))
  = fun projectee  -> match projectee with | Match _0 -> _0 
let (uu___is_TryWith : term' -> Prims.bool) =
  fun projectee  ->
    match projectee with | TryWith _0 -> true | uu____40425 -> false
  
let (__proj__TryWith__item___0 :
  term' ->
    (term * (pattern * term FStar_Pervasives_Native.option * term)
      Prims.list))
  = fun projectee  -> match projectee with | TryWith _0 -> _0 
let (uu___is_Ascribed : term' -> Prims.bool) =
  fun projectee  ->
    match projectee with | Ascribed _0 -> true | uu____40495 -> false
  
let (__proj__Ascribed__item___0 :
  term' -> (term * term * term FStar_Pervasives_Native.option)) =
  fun projectee  -> match projectee with | Ascribed _0 -> _0 
let (uu___is_Record : term' -> Prims.bool) =
  fun projectee  ->
    match projectee with | Record _0 -> true | uu____40551 -> false
  
let (__proj__Record__item___0 :
  term' ->
    (term FStar_Pervasives_Native.option * (FStar_Ident.lid * term)
      Prims.list))
  = fun projectee  -> match projectee with | Record _0 -> _0 
let (uu___is_Project : term' -> Prims.bool) =
  fun projectee  ->
    match projectee with | Project _0 -> true | uu____40611 -> false
  
let (__proj__Project__item___0 : term' -> (term * FStar_Ident.lid)) =
  fun projectee  -> match projectee with | Project _0 -> _0 
let (uu___is_Product : term' -> Prims.bool) =
  fun projectee  ->
    match projectee with | Product _0 -> true | uu____40649 -> false
  
let (__proj__Product__item___0 : term' -> (binder Prims.list * term)) =
  fun projectee  -> match projectee with | Product _0 -> _0 
let (uu___is_Sum : term' -> Prims.bool) =
  fun projectee  ->
    match projectee with | Sum _0 -> true | uu____40697 -> false
  
let (__proj__Sum__item___0 :
  term' -> ((binder,term) FStar_Util.either Prims.list * term)) =
  fun projectee  -> match projectee with | Sum _0 -> _0 
let (uu___is_QForall : term' -> Prims.bool) =
  fun projectee  ->
    match projectee with | QForall _0 -> true | uu____40759 -> false
  
let (__proj__QForall__item___0 :
  term' -> (binder Prims.list * term Prims.list Prims.list * term)) =
  fun projectee  -> match projectee with | QForall _0 -> _0 
let (uu___is_QExists : term' -> Prims.bool) =
  fun projectee  ->
    match projectee with | QExists _0 -> true | uu____40827 -> false
  
let (__proj__QExists__item___0 :
  term' -> (binder Prims.list * term Prims.list Prims.list * term)) =
  fun projectee  -> match projectee with | QExists _0 -> _0 
let (uu___is_Refine : term' -> Prims.bool) =
  fun projectee  ->
    match projectee with | Refine _0 -> true | uu____40887 -> false
  
let (__proj__Refine__item___0 : term' -> (binder * term)) =
  fun projectee  -> match projectee with | Refine _0 -> _0 
let (uu___is_NamedTyp : term' -> Prims.bool) =
  fun projectee  ->
    match projectee with | NamedTyp _0 -> true | uu____40923 -> false
  
let (__proj__NamedTyp__item___0 : term' -> (FStar_Ident.ident * term)) =
  fun projectee  -> match projectee with | NamedTyp _0 -> _0 
let (uu___is_Paren : term' -> Prims.bool) =
  fun projectee  ->
    match projectee with | Paren _0 -> true | uu____40955 -> false
  
let (__proj__Paren__item___0 : term' -> term) =
  fun projectee  -> match projectee with | Paren _0 -> _0 
let (uu___is_Requires : term' -> Prims.bool) =
  fun projectee  ->
    match projectee with | Requires _0 -> true | uu____40982 -> false
  
let (__proj__Requires__item___0 :
  term' -> (term * Prims.string FStar_Pervasives_Native.option)) =
  fun projectee  -> match projectee with | Requires _0 -> _0 
let (uu___is_Ensures : term' -> Prims.bool) =
  fun projectee  ->
    match projectee with | Ensures _0 -> true | uu____41030 -> false
  
let (__proj__Ensures__item___0 :
  term' -> (term * Prims.string FStar_Pervasives_Native.option)) =
  fun projectee  -> match projectee with | Ensures _0 -> _0 
let (uu___is_Labeled : term' -> Prims.bool) =
  fun projectee  ->
    match projectee with | Labeled _0 -> true | uu____41079 -> false
  
let (__proj__Labeled__item___0 : term' -> (term * Prims.string * Prims.bool))
  = fun projectee  -> match projectee with | Labeled _0 -> _0 
let (uu___is_Discrim : term' -> Prims.bool) =
  fun projectee  ->
    match projectee with | Discrim _0 -> true | uu____41123 -> false
  
let (__proj__Discrim__item___0 : term' -> FStar_Ident.lid) =
  fun projectee  -> match projectee with | Discrim _0 -> _0 
let (uu___is_Attributes : term' -> Prims.bool) =
  fun projectee  ->
    match projectee with | Attributes _0 -> true | uu____41145 -> false
  
let (__proj__Attributes__item___0 : term' -> term Prims.list) =
  fun projectee  -> match projectee with | Attributes _0 -> _0 
let (uu___is_Antiquote : term' -> Prims.bool) =
  fun projectee  ->
    match projectee with | Antiquote _0 -> true | uu____41171 -> false
  
let (__proj__Antiquote__item___0 : term' -> term) =
  fun projectee  -> match projectee with | Antiquote _0 -> _0 
let (uu___is_Quote : term' -> Prims.bool) =
  fun projectee  ->
    match projectee with | Quote _0 -> true | uu____41195 -> false
  
let (__proj__Quote__item___0 : term' -> (term * quote_kind)) =
  fun projectee  -> match projectee with | Quote _0 -> _0 
let (uu___is_VQuote : term' -> Prims.bool) =
  fun projectee  ->
    match projectee with | VQuote _0 -> true | uu____41227 -> false
  
let (__proj__VQuote__item___0 : term' -> term) =
  fun projectee  -> match projectee with | VQuote _0 -> _0 
let (uu___is_CalcProof : term' -> Prims.bool) =
  fun projectee  ->
    match projectee with | CalcProof _0 -> true | uu____41255 -> false
  
let (__proj__CalcProof__item___0 :
  term' -> (term * term * calc_step Prims.list)) =
  fun projectee  -> match projectee with | CalcProof _0 -> _0 
let (__proj__Mkterm__item__tm : term -> term') =
  fun projectee  -> match projectee with | { tm; range; level;_} -> tm 
let (__proj__Mkterm__item__range : term -> FStar_Range.range) =
  fun projectee  -> match projectee with | { tm; range; level;_} -> range 
let (__proj__Mkterm__item__level : term -> level) =
  fun projectee  -> match projectee with | { tm; range; level;_} -> level 
let (uu___is_CalcStep : calc_step -> Prims.bool) = fun projectee  -> true 
let (__proj__CalcStep__item___0 : calc_step -> (term * term * term)) =
  fun projectee  -> match projectee with | CalcStep _0 -> _0 
let (uu___is_Variable : binder' -> Prims.bool) =
  fun projectee  ->
    match projectee with | Variable _0 -> true | uu____41359 -> false
  
let (__proj__Variable__item___0 : binder' -> FStar_Ident.ident) =
  fun projectee  -> match projectee with | Variable _0 -> _0 
let (uu___is_TVariable : binder' -> Prims.bool) =
  fun projectee  ->
    match projectee with | TVariable _0 -> true | uu____41379 -> false
  
let (__proj__TVariable__item___0 : binder' -> FStar_Ident.ident) =
  fun projectee  -> match projectee with | TVariable _0 -> _0 
let (uu___is_Annotated : binder' -> Prims.bool) =
  fun projectee  ->
    match projectee with | Annotated _0 -> true | uu____41403 -> false
  
let (__proj__Annotated__item___0 : binder' -> (FStar_Ident.ident * term)) =
  fun projectee  -> match projectee with | Annotated _0 -> _0 
let (uu___is_TAnnotated : binder' -> Prims.bool) =
  fun projectee  ->
    match projectee with | TAnnotated _0 -> true | uu____41439 -> false
  
let (__proj__TAnnotated__item___0 : binder' -> (FStar_Ident.ident * term)) =
  fun projectee  -> match projectee with | TAnnotated _0 -> _0 
let (uu___is_NoName : binder' -> Prims.bool) =
  fun projectee  ->
    match projectee with | NoName _0 -> true | uu____41471 -> false
  
let (__proj__NoName__item___0 : binder' -> term) =
  fun projectee  -> match projectee with | NoName _0 -> _0 
let (__proj__Mkbinder__item__b : binder -> binder') =
  fun projectee  -> match projectee with | { b; brange; blevel; aqual;_} -> b 
let (__proj__Mkbinder__item__brange : binder -> FStar_Range.range) =
  fun projectee  ->
    match projectee with | { b; brange; blevel; aqual;_} -> brange
  
let (__proj__Mkbinder__item__blevel : binder -> level) =
  fun projectee  ->
    match projectee with | { b; brange; blevel; aqual;_} -> blevel
  
let (__proj__Mkbinder__item__aqual :
  binder -> arg_qualifier FStar_Pervasives_Native.option) =
  fun projectee  ->
    match projectee with | { b; brange; blevel; aqual;_} -> aqual
  
let (uu___is_PatWild : pattern' -> Prims.bool) =
  fun projectee  ->
    match projectee with | PatWild _0 -> true | uu____41545 -> false
  
let (__proj__PatWild__item___0 :
  pattern' -> arg_qualifier FStar_Pervasives_Native.option) =
  fun projectee  -> match projectee with | PatWild _0 -> _0 
let (uu___is_PatConst : pattern' -> Prims.bool) =
  fun projectee  ->
    match projectee with | PatConst _0 -> true | uu____41571 -> false
  
let (__proj__PatConst__item___0 : pattern' -> FStar_Const.sconst) =
  fun projectee  -> match projectee with | PatConst _0 -> _0 
let (uu___is_PatApp : pattern' -> Prims.bool) =
  fun projectee  ->
    match projectee with | PatApp _0 -> true | uu____41597 -> false
  
let (__proj__PatApp__item___0 : pattern' -> (pattern * pattern Prims.list)) =
  fun projectee  -> match projectee with | PatApp _0 -> _0 
let (uu___is_PatVar : pattern' -> Prims.bool) =
  fun projectee  ->
    match projectee with | PatVar _0 -> true | uu____41641 -> false
  
let (__proj__PatVar__item___0 :
  pattern' ->
    (FStar_Ident.ident * arg_qualifier FStar_Pervasives_Native.option))
  = fun projectee  -> match projectee with | PatVar _0 -> _0 
let (uu___is_PatName : pattern' -> Prims.bool) =
  fun projectee  ->
    match projectee with | PatName _0 -> true | uu____41679 -> false
  
let (__proj__PatName__item___0 : pattern' -> FStar_Ident.lid) =
  fun projectee  -> match projectee with | PatName _0 -> _0 
let (uu___is_PatTvar : pattern' -> Prims.bool) =
  fun projectee  ->
    match projectee with | PatTvar _0 -> true | uu____41705 -> false
  
let (__proj__PatTvar__item___0 :
  pattern' ->
    (FStar_Ident.ident * arg_qualifier FStar_Pervasives_Native.option))
  = fun projectee  -> match projectee with | PatTvar _0 -> _0 
let (uu___is_PatList : pattern' -> Prims.bool) =
  fun projectee  ->
    match projectee with | PatList _0 -> true | uu____41745 -> false
  
let (__proj__PatList__item___0 : pattern' -> pattern Prims.list) =
  fun projectee  -> match projectee with | PatList _0 -> _0 
let (uu___is_PatTuple : pattern' -> Prims.bool) =
  fun projectee  ->
    match projectee with | PatTuple _0 -> true | uu____41778 -> false
  
let (__proj__PatTuple__item___0 :
  pattern' -> (pattern Prims.list * Prims.bool)) =
  fun projectee  -> match projectee with | PatTuple _0 -> _0 
let (uu___is_PatRecord : pattern' -> Prims.bool) =
  fun projectee  ->
    match projectee with | PatRecord _0 -> true | uu____41825 -> false
  
let (__proj__PatRecord__item___0 :
  pattern' -> (FStar_Ident.lid * pattern) Prims.list) =
  fun projectee  -> match projectee with | PatRecord _0 -> _0 
let (uu___is_PatAscribed : pattern' -> Prims.bool) =
  fun projectee  ->
    match projectee with | PatAscribed _0 -> true | uu____41873 -> false
  
let (__proj__PatAscribed__item___0 :
  pattern' -> (pattern * (term * term FStar_Pervasives_Native.option))) =
  fun projectee  -> match projectee with | PatAscribed _0 -> _0 
let (uu___is_PatOr : pattern' -> Prims.bool) =
  fun projectee  ->
    match projectee with | PatOr _0 -> true | uu____41925 -> false
  
let (__proj__PatOr__item___0 : pattern' -> pattern Prims.list) =
  fun projectee  -> match projectee with | PatOr _0 -> _0 
let (uu___is_PatOp : pattern' -> Prims.bool) =
  fun projectee  ->
    match projectee with | PatOp _0 -> true | uu____41951 -> false
  
let (__proj__PatOp__item___0 : pattern' -> FStar_Ident.ident) =
  fun projectee  -> match projectee with | PatOp _0 -> _0 
let (__proj__Mkpattern__item__pat : pattern -> pattern') =
  fun projectee  -> match projectee with | { pat; prange;_} -> pat 
let (__proj__Mkpattern__item__prange : pattern -> FStar_Range.range) =
  fun projectee  -> match projectee with | { pat; prange;_} -> prange 
let (uu___is_Implicit : arg_qualifier -> Prims.bool) =
  fun projectee  ->
    match projectee with | Implicit  -> true | uu____41986 -> false
  
let (uu___is_Equality : arg_qualifier -> Prims.bool) =
  fun projectee  ->
    match projectee with | Equality  -> true | uu____41997 -> false
  
let (uu___is_Meta : arg_qualifier -> Prims.bool) =
  fun projectee  ->
    match projectee with | Meta _0 -> true | uu____42009 -> false
  
let (__proj__Meta__item___0 : arg_qualifier -> term) =
  fun projectee  -> match projectee with | Meta _0 -> _0 
let (uu___is_FsTypApp : imp -> Prims.bool) =
  fun projectee  ->
    match projectee with | FsTypApp  -> true | uu____42028 -> false
  
let (uu___is_Hash : imp -> Prims.bool) =
  fun projectee  ->
    match projectee with | Hash  -> true | uu____42039 -> false
  
let (uu___is_UnivApp : imp -> Prims.bool) =
  fun projectee  ->
    match projectee with | UnivApp  -> true | uu____42050 -> false
  
let (uu___is_HashBrace : imp -> Prims.bool) =
  fun projectee  ->
    match projectee with | HashBrace _0 -> true | uu____42062 -> false
  
let (__proj__HashBrace__item___0 : imp -> term) =
  fun projectee  -> match projectee with | HashBrace _0 -> _0 
let (uu___is_Infix : imp -> Prims.bool) =
  fun projectee  ->
    match projectee with | Infix  -> true | uu____42081 -> false
  
let (uu___is_Nothing : imp -> Prims.bool) =
  fun projectee  ->
    match projectee with | Nothing  -> true | uu____42092 -> false
  
type attributes_ = term Prims.list
type branch = (pattern * term FStar_Pervasives_Native.option * term)
type aqual = arg_qualifier FStar_Pervasives_Native.option
type knd = term
type typ = term
type expr = term
type fsdoc = (Prims.string * (Prims.string * Prims.string) Prims.list)
type tycon =
  | TyconAbstract of (FStar_Ident.ident * binder Prims.list * knd
  FStar_Pervasives_Native.option) 
  | TyconAbbrev of (FStar_Ident.ident * binder Prims.list * knd
  FStar_Pervasives_Native.option * term) 
  | TyconRecord of (FStar_Ident.ident * binder Prims.list * knd
  FStar_Pervasives_Native.option * (FStar_Ident.ident * term * fsdoc
  FStar_Pervasives_Native.option) Prims.list) 
  | TyconVariant of (FStar_Ident.ident * binder Prims.list * knd
  FStar_Pervasives_Native.option * (FStar_Ident.ident * term
  FStar_Pervasives_Native.option * fsdoc FStar_Pervasives_Native.option *
  Prims.bool) Prims.list) 
let (uu___is_TyconAbstract : tycon -> Prims.bool) =
  fun projectee  ->
    match projectee with | TyconAbstract _0 -> true | uu____42230 -> false
  
let (__proj__TyconAbstract__item___0 :
  tycon ->
    (FStar_Ident.ident * binder Prims.list * knd
      FStar_Pervasives_Native.option))
  = fun projectee  -> match projectee with | TyconAbstract _0 -> _0 
let (uu___is_TyconAbbrev : tycon -> Prims.bool) =
  fun projectee  ->
    match projectee with | TyconAbbrev _0 -> true | uu____42292 -> false
  
let (__proj__TyconAbbrev__item___0 :
  tycon ->
    (FStar_Ident.ident * binder Prims.list * knd
      FStar_Pervasives_Native.option * term))
  = fun projectee  -> match projectee with | TyconAbbrev _0 -> _0 
let (uu___is_TyconRecord : tycon -> Prims.bool) =
  fun projectee  ->
    match projectee with | TyconRecord _0 -> true | uu____42370 -> false
  
let (__proj__TyconRecord__item___0 :
  tycon ->
    (FStar_Ident.ident * binder Prims.list * knd
      FStar_Pervasives_Native.option * (FStar_Ident.ident * term * fsdoc
      FStar_Pervasives_Native.option) Prims.list))
  = fun projectee  -> match projectee with | TyconRecord _0 -> _0 
let (uu___is_TyconVariant : tycon -> Prims.bool) =
  fun projectee  ->
    match projectee with | TyconVariant _0 -> true | uu____42483 -> false
  
let (__proj__TyconVariant__item___0 :
  tycon ->
    (FStar_Ident.ident * binder Prims.list * knd
      FStar_Pervasives_Native.option * (FStar_Ident.ident * term
      FStar_Pervasives_Native.option * fsdoc FStar_Pervasives_Native.option *
      Prims.bool) Prims.list))
  = fun projectee  -> match projectee with | TyconVariant _0 -> _0 
type qualifier =
  | Private 
  | Abstract 
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
  fun projectee  ->
    match projectee with | Private  -> true | uu____42583 -> false
  
let (uu___is_Abstract : qualifier -> Prims.bool) =
  fun projectee  ->
    match projectee with | Abstract  -> true | uu____42594 -> false
  
let (uu___is_Noeq : qualifier -> Prims.bool) =
  fun projectee  ->
    match projectee with | Noeq  -> true | uu____42605 -> false
  
let (uu___is_Unopteq : qualifier -> Prims.bool) =
  fun projectee  ->
    match projectee with | Unopteq  -> true | uu____42616 -> false
  
let (uu___is_Assumption : qualifier -> Prims.bool) =
  fun projectee  ->
    match projectee with | Assumption  -> true | uu____42627 -> false
  
let (uu___is_DefaultEffect : qualifier -> Prims.bool) =
  fun projectee  ->
    match projectee with | DefaultEffect  -> true | uu____42638 -> false
  
let (uu___is_TotalEffect : qualifier -> Prims.bool) =
  fun projectee  ->
    match projectee with | TotalEffect  -> true | uu____42649 -> false
  
let (uu___is_Effect_qual : qualifier -> Prims.bool) =
  fun projectee  ->
    match projectee with | Effect_qual  -> true | uu____42660 -> false
  
let (uu___is_New : qualifier -> Prims.bool) =
  fun projectee  ->
    match projectee with | New  -> true | uu____42671 -> false
  
let (uu___is_Inline : qualifier -> Prims.bool) =
  fun projectee  ->
    match projectee with | Inline  -> true | uu____42682 -> false
  
let (uu___is_Visible : qualifier -> Prims.bool) =
  fun projectee  ->
    match projectee with | Visible  -> true | uu____42693 -> false
  
let (uu___is_Unfold_for_unification_and_vcgen : qualifier -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | Unfold_for_unification_and_vcgen  -> true
    | uu____42704 -> false
  
let (uu___is_Inline_for_extraction : qualifier -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | Inline_for_extraction  -> true
    | uu____42715 -> false
  
let (uu___is_Irreducible : qualifier -> Prims.bool) =
  fun projectee  ->
    match projectee with | Irreducible  -> true | uu____42726 -> false
  
let (uu___is_NoExtract : qualifier -> Prims.bool) =
  fun projectee  ->
    match projectee with | NoExtract  -> true | uu____42737 -> false
  
let (uu___is_Reifiable : qualifier -> Prims.bool) =
  fun projectee  ->
    match projectee with | Reifiable  -> true | uu____42748 -> false
  
let (uu___is_Reflectable : qualifier -> Prims.bool) =
  fun projectee  ->
    match projectee with | Reflectable  -> true | uu____42759 -> false
  
let (uu___is_Opaque : qualifier -> Prims.bool) =
  fun projectee  ->
    match projectee with | Opaque  -> true | uu____42770 -> false
  
let (uu___is_Logic : qualifier -> Prims.bool) =
  fun projectee  ->
    match projectee with | Logic  -> true | uu____42781 -> false
  
type qualifiers = qualifier Prims.list
type decoration =
  | Qualifier of qualifier 
  | DeclAttributes of term Prims.list 
  | Doc of fsdoc 
let (uu___is_Qualifier : decoration -> Prims.bool) =
  fun projectee  ->
    match projectee with | Qualifier _0 -> true | uu____42812 -> false
  
let (__proj__Qualifier__item___0 : decoration -> qualifier) =
  fun projectee  -> match projectee with | Qualifier _0 -> _0 
let (uu___is_DeclAttributes : decoration -> Prims.bool) =
  fun projectee  ->
    match projectee with | DeclAttributes _0 -> true | uu____42834 -> false
  
let (__proj__DeclAttributes__item___0 : decoration -> term Prims.list) =
  fun projectee  -> match projectee with | DeclAttributes _0 -> _0 
let (uu___is_Doc : decoration -> Prims.bool) =
  fun projectee  ->
    match projectee with | Doc _0 -> true | uu____42860 -> false
  
let (__proj__Doc__item___0 : decoration -> fsdoc) =
  fun projectee  -> match projectee with | Doc _0 -> _0 
type lift_op =
  | NonReifiableLift of term 
  | ReifiableLift of (term * term) 
  | LiftForFree of term 
let (uu___is_NonReifiableLift : lift_op -> Prims.bool) =
  fun projectee  ->
    match projectee with | NonReifiableLift _0 -> true | uu____42899 -> false
  
let (__proj__NonReifiableLift__item___0 : lift_op -> term) =
  fun projectee  -> match projectee with | NonReifiableLift _0 -> _0 
let (uu___is_ReifiableLift : lift_op -> Prims.bool) =
  fun projectee  ->
    match projectee with | ReifiableLift _0 -> true | uu____42923 -> false
  
let (__proj__ReifiableLift__item___0 : lift_op -> (term * term)) =
  fun projectee  -> match projectee with | ReifiableLift _0 -> _0 
let (uu___is_LiftForFree : lift_op -> Prims.bool) =
  fun projectee  ->
    match projectee with | LiftForFree _0 -> true | uu____42955 -> false
  
let (__proj__LiftForFree__item___0 : lift_op -> term) =
  fun projectee  -> match projectee with | LiftForFree _0 -> _0 
type lift =
  {
  msource: FStar_Ident.lid ;
  mdest: FStar_Ident.lid ;
  lift_op: lift_op }
let (__proj__Mklift__item__msource : lift -> FStar_Ident.lid) =
  fun projectee  ->
    match projectee with | { msource; mdest; lift_op;_} -> msource
  
let (__proj__Mklift__item__mdest : lift -> FStar_Ident.lid) =
  fun projectee  ->
    match projectee with | { msource; mdest; lift_op;_} -> mdest
  
let (__proj__Mklift__item__lift_op : lift -> lift_op) =
  fun projectee  ->
    match projectee with | { msource; mdest; lift_op;_} -> lift_op
  
type pragma =
  | SetOptions of Prims.string 
  | ResetOptions of Prims.string FStar_Pervasives_Native.option 
  | PushOptions of Prims.string FStar_Pervasives_Native.option 
  | PopOptions 
  | LightOff 
let (uu___is_SetOptions : pragma -> Prims.bool) =
  fun projectee  ->
    match projectee with | SetOptions _0 -> true | uu____43040 -> false
  
let (__proj__SetOptions__item___0 : pragma -> Prims.string) =
  fun projectee  -> match projectee with | SetOptions _0 -> _0 
let (uu___is_ResetOptions : pragma -> Prims.bool) =
  fun projectee  ->
    match projectee with | ResetOptions _0 -> true | uu____43066 -> false
  
let (__proj__ResetOptions__item___0 :
  pragma -> Prims.string FStar_Pervasives_Native.option) =
  fun projectee  -> match projectee with | ResetOptions _0 -> _0 
let (uu___is_PushOptions : pragma -> Prims.bool) =
  fun projectee  ->
    match projectee with | PushOptions _0 -> true | uu____43098 -> false
  
let (__proj__PushOptions__item___0 :
  pragma -> Prims.string FStar_Pervasives_Native.option) =
  fun projectee  -> match projectee with | PushOptions _0 -> _0 
let (uu___is_PopOptions : pragma -> Prims.bool) =
  fun projectee  ->
    match projectee with | PopOptions  -> true | uu____43126 -> false
  
let (uu___is_LightOff : pragma -> Prims.bool) =
  fun projectee  ->
    match projectee with | LightOff  -> true | uu____43137 -> false
  
type decl' =
  | TopLevelModule of FStar_Ident.lid 
  | Open of FStar_Ident.lid 
  | Friend of FStar_Ident.lid 
  | Include of FStar_Ident.lid 
  | ModuleAbbrev of (FStar_Ident.ident * FStar_Ident.lid) 
  | TopLevelLet of (let_qualifier * (pattern * term) Prims.list) 
  | Main of term 
  | Tycon of (Prims.bool * Prims.bool * (tycon * fsdoc
  FStar_Pervasives_Native.option) Prims.list) 
  | Val of (FStar_Ident.ident * term) 
  | Exception of (FStar_Ident.ident * term FStar_Pervasives_Native.option) 
  | NewEffect of effect_decl 
  | SubEffect of lift 
  | Pragma of pragma 
  | Fsdoc of fsdoc 
  | Assume of (FStar_Ident.ident * term) 
  | Splice of (FStar_Ident.ident Prims.list * term) 
and decl =
  {
  d: decl' ;
  drange: FStar_Range.range ;
  doc: fsdoc FStar_Pervasives_Native.option ;
  quals: qualifiers ;
  attrs: attributes_ }
and effect_decl =
  | DefineEffect of (FStar_Ident.ident * binder Prims.list * term * decl
  Prims.list) 
  | RedefineEffect of (FStar_Ident.ident * binder Prims.list * term) 
let (uu___is_TopLevelModule : decl' -> Prims.bool) =
  fun projectee  ->
    match projectee with | TopLevelModule _0 -> true | uu____43336 -> false
  
let (__proj__TopLevelModule__item___0 : decl' -> FStar_Ident.lid) =
  fun projectee  -> match projectee with | TopLevelModule _0 -> _0 
let (uu___is_Open : decl' -> Prims.bool) =
  fun projectee  ->
    match projectee with | Open _0 -> true | uu____43356 -> false
  
let (__proj__Open__item___0 : decl' -> FStar_Ident.lid) =
  fun projectee  -> match projectee with | Open _0 -> _0 
let (uu___is_Friend : decl' -> Prims.bool) =
  fun projectee  ->
    match projectee with | Friend _0 -> true | uu____43376 -> false
  
let (__proj__Friend__item___0 : decl' -> FStar_Ident.lid) =
  fun projectee  -> match projectee with | Friend _0 -> _0 
let (uu___is_Include : decl' -> Prims.bool) =
  fun projectee  ->
    match projectee with | Include _0 -> true | uu____43396 -> false
  
let (__proj__Include__item___0 : decl' -> FStar_Ident.lid) =
  fun projectee  -> match projectee with | Include _0 -> _0 
let (uu___is_ModuleAbbrev : decl' -> Prims.bool) =
  fun projectee  ->
    match projectee with | ModuleAbbrev _0 -> true | uu____43420 -> false
  
let (__proj__ModuleAbbrev__item___0 :
  decl' -> (FStar_Ident.ident * FStar_Ident.lid)) =
  fun projectee  -> match projectee with | ModuleAbbrev _0 -> _0 
let (uu___is_TopLevelLet : decl' -> Prims.bool) =
  fun projectee  ->
    match projectee with | TopLevelLet _0 -> true | uu____43462 -> false
  
let (__proj__TopLevelLet__item___0 :
  decl' -> (let_qualifier * (pattern * term) Prims.list)) =
  fun projectee  -> match projectee with | TopLevelLet _0 -> _0 
let (uu___is_Main : decl' -> Prims.bool) =
  fun projectee  ->
    match projectee with | Main _0 -> true | uu____43512 -> false
  
let (__proj__Main__item___0 : decl' -> term) =
  fun projectee  -> match projectee with | Main _0 -> _0 
let (uu___is_Tycon : decl' -> Prims.bool) =
  fun projectee  ->
    match projectee with | Tycon _0 -> true | uu____43548 -> false
  
let (__proj__Tycon__item___0 :
  decl' ->
    (Prims.bool * Prims.bool * (tycon * fsdoc FStar_Pervasives_Native.option)
      Prims.list))
  = fun projectee  -> match projectee with | Tycon _0 -> _0 
let (uu___is_Val : decl' -> Prims.bool) =
  fun projectee  ->
    match projectee with | Val _0 -> true | uu____43620 -> false
  
let (__proj__Val__item___0 : decl' -> (FStar_Ident.ident * term)) =
  fun projectee  -> match projectee with | Val _0 -> _0 
let (uu___is_Exception : decl' -> Prims.bool) =
  fun projectee  ->
    match projectee with | Exception _0 -> true | uu____43658 -> false
  
let (__proj__Exception__item___0 :
  decl' -> (FStar_Ident.ident * term FStar_Pervasives_Native.option)) =
  fun projectee  -> match projectee with | Exception _0 -> _0 
let (uu___is_NewEffect : decl' -> Prims.bool) =
  fun projectee  ->
    match projectee with | NewEffect _0 -> true | uu____43696 -> false
  
let (__proj__NewEffect__item___0 : decl' -> effect_decl) =
  fun projectee  -> match projectee with | NewEffect _0 -> _0 
let (uu___is_SubEffect : decl' -> Prims.bool) =
  fun projectee  ->
    match projectee with | SubEffect _0 -> true | uu____43716 -> false
  
let (__proj__SubEffect__item___0 : decl' -> lift) =
  fun projectee  -> match projectee with | SubEffect _0 -> _0 
let (uu___is_Pragma : decl' -> Prims.bool) =
  fun projectee  ->
    match projectee with | Pragma _0 -> true | uu____43736 -> false
  
let (__proj__Pragma__item___0 : decl' -> pragma) =
  fun projectee  -> match projectee with | Pragma _0 -> _0 
let (uu___is_Fsdoc : decl' -> Prims.bool) =
  fun projectee  ->
    match projectee with | Fsdoc _0 -> true | uu____43756 -> false
  
let (__proj__Fsdoc__item___0 : decl' -> fsdoc) =
  fun projectee  -> match projectee with | Fsdoc _0 -> _0 
let (uu___is_Assume : decl' -> Prims.bool) =
  fun projectee  ->
    match projectee with | Assume _0 -> true | uu____43780 -> false
  
let (__proj__Assume__item___0 : decl' -> (FStar_Ident.ident * term)) =
  fun projectee  -> match projectee with | Assume _0 -> _0 
let (uu___is_Splice : decl' -> Prims.bool) =
  fun projectee  ->
    match projectee with | Splice _0 -> true | uu____43818 -> false
  
let (__proj__Splice__item___0 :
  decl' -> (FStar_Ident.ident Prims.list * term)) =
  fun projectee  -> match projectee with | Splice _0 -> _0 
let (__proj__Mkdecl__item__d : decl -> decl') =
  fun projectee  ->
    match projectee with | { d; drange; doc = doc1; quals; attrs;_} -> d
  
let (__proj__Mkdecl__item__drange : decl -> FStar_Range.range) =
  fun projectee  ->
    match projectee with | { d; drange; doc = doc1; quals; attrs;_} -> drange
  
let (__proj__Mkdecl__item__doc :
  decl -> fsdoc FStar_Pervasives_Native.option) =
  fun projectee  ->
    match projectee with | { d; drange; doc = doc1; quals; attrs;_} -> doc1
  
let (__proj__Mkdecl__item__quals : decl -> qualifiers) =
  fun projectee  ->
    match projectee with | { d; drange; doc = doc1; quals; attrs;_} -> quals
  
let (__proj__Mkdecl__item__attrs : decl -> attributes_) =
  fun projectee  ->
    match projectee with | { d; drange; doc = doc1; quals; attrs;_} -> attrs
  
let (uu___is_DefineEffect : effect_decl -> Prims.bool) =
  fun projectee  ->
    match projectee with | DefineEffect _0 -> true | uu____43937 -> false
  
let (__proj__DefineEffect__item___0 :
  effect_decl ->
    (FStar_Ident.ident * binder Prims.list * term * decl Prims.list))
  = fun projectee  -> match projectee with | DefineEffect _0 -> _0 
let (uu___is_RedefineEffect : effect_decl -> Prims.bool) =
  fun projectee  ->
    match projectee with | RedefineEffect _0 -> true | uu____44001 -> false
  
let (__proj__RedefineEffect__item___0 :
  effect_decl -> (FStar_Ident.ident * binder Prims.list * term)) =
  fun projectee  -> match projectee with | RedefineEffect _0 -> _0 
type modul =
  | Module of (FStar_Ident.lid * decl Prims.list) 
  | Interface of (FStar_Ident.lid * decl Prims.list * Prims.bool) 
let (uu___is_Module : modul -> Prims.bool) =
  fun projectee  ->
    match projectee with | Module _0 -> true | uu____44076 -> false
  
let (__proj__Module__item___0 : modul -> (FStar_Ident.lid * decl Prims.list))
  = fun projectee  -> match projectee with | Module _0 -> _0 
let (uu___is_Interface : modul -> Prims.bool) =
  fun projectee  ->
    match projectee with | Interface _0 -> true | uu____44123 -> false
  
let (__proj__Interface__item___0 :
  modul -> (FStar_Ident.lid * decl Prims.list * Prims.bool)) =
  fun projectee  -> match projectee with | Interface _0 -> _0 
type file = modul
type inputFragment = (file,decl Prims.list) FStar_Util.either
let (decl_drange : decl -> FStar_Range.range) = fun decl  -> decl.drange 
let (check_id : FStar_Ident.ident -> unit) =
  fun id1  ->
    let first_char =
      FStar_String.substring id1.FStar_Ident.idText (Prims.parse_int "0")
        (Prims.parse_int "1")
       in
    if (FStar_String.lowercase first_char) = first_char
    then ()
    else
      (let uu____44186 =
         let uu____44192 =
           FStar_Util.format1
             "Invalid identifer '%s'; expected a symbol that begins with a lower-case character"
             id1.FStar_Ident.idText
            in
         (FStar_Errors.Fatal_InvalidIdentifier, uu____44192)  in
       FStar_Errors.raise_error uu____44186 id1.FStar_Ident.idRange)
  
let at_most_one :
  'Auu____44205 .
    Prims.string ->
      FStar_Range.range ->
        'Auu____44205 Prims.list ->
          'Auu____44205 FStar_Pervasives_Native.option
  =
  fun s  ->
    fun r  ->
      fun l  ->
        match l with
        | x::[] -> FStar_Pervasives_Native.Some x
        | [] -> FStar_Pervasives_Native.None
        | uu____44230 ->
            let uu____44233 =
              let uu____44239 =
                FStar_Util.format1
                  "At most one %s is allowed on declarations" s
                 in
              (FStar_Errors.Fatal_MoreThanOneDeclaration, uu____44239)  in
            FStar_Errors.raise_error uu____44233 r
  
let (mk_decl : decl' -> FStar_Range.range -> decoration Prims.list -> decl) =
  fun d  ->
    fun r  ->
      fun decorations  ->
        let doc1 =
          let uu____44268 =
            FStar_List.choose
              (fun uu___306_44273  ->
                 match uu___306_44273 with
                 | Doc d1 -> FStar_Pervasives_Native.Some d1
                 | uu____44277 -> FStar_Pervasives_Native.None) decorations
             in
          at_most_one "fsdoc" r uu____44268  in
        let attributes_ =
          let uu____44284 =
            FStar_List.choose
              (fun uu___307_44293  ->
                 match uu___307_44293 with
                 | DeclAttributes a -> FStar_Pervasives_Native.Some a
                 | uu____44303 -> FStar_Pervasives_Native.None) decorations
             in
          at_most_one "attribute set" r uu____44284  in
        let attributes_1 = FStar_Util.dflt [] attributes_  in
        let qualifiers =
          FStar_List.choose
            (fun uu___308_44319  ->
               match uu___308_44319 with
               | Qualifier q -> FStar_Pervasives_Native.Some q
               | uu____44323 -> FStar_Pervasives_Native.None) decorations
           in
        { d; drange = r; doc = doc1; quals = qualifiers; attrs = attributes_1
        }
  
let (mk_binder :
  binder' ->
    FStar_Range.range ->
      level -> arg_qualifier FStar_Pervasives_Native.option -> binder)
  =
  fun b  ->
    fun r  -> fun l  -> fun i  -> { b; brange = r; blevel = l; aqual = i }
  
let (mk_term : term' -> FStar_Range.range -> level -> term) =
  fun t  -> fun r  -> fun l  -> { tm = t; range = r; level = l } 
let (mk_uminus :
  term -> FStar_Range.range -> FStar_Range.range -> level -> term) =
  fun t  ->
    fun rminus  ->
      fun r  ->
        fun l  ->
          let t1 =
            match t.tm with
            | Const (FStar_Const.Const_int
                (s,FStar_Pervasives_Native.Some (FStar_Const.Signed ,width)))
                ->
                Const
                  (FStar_Const.Const_int
                     ((Prims.op_Hat "-" s),
                       (FStar_Pervasives_Native.Some
                          (FStar_Const.Signed, width))))
            | uu____44413 ->
                let uu____44414 =
                  let uu____44421 = FStar_Ident.mk_ident ("-", rminus)  in
                  (uu____44421, [t])  in
                Op uu____44414
             in
          mk_term t1 r l
  
let (mk_pattern : pattern' -> FStar_Range.range -> pattern) =
  fun p  -> fun r  -> { pat = p; prange = r } 
let (un_curry_abs : pattern Prims.list -> term -> term') =
  fun ps  ->
    fun body  ->
      match body.tm with
      | Abs (p',body') -> Abs ((FStar_List.append ps p'), body')
      | uu____44460 -> Abs (ps, body)
  
let (mk_function :
  (pattern * term FStar_Pervasives_Native.option * term) Prims.list ->
    FStar_Range.range -> FStar_Range.range -> term)
  =
  fun branches  ->
    fun r1  ->
      fun r2  ->
        let x = let i = FStar_Parser_Const.next_id ()  in FStar_Ident.gen r1
           in
        let uu____44502 =
          let uu____44503 =
            let uu____44510 =
              let uu____44511 =
                let uu____44512 =
                  let uu____44527 =
                    let uu____44528 =
                      let uu____44529 = FStar_Ident.lid_of_ids [x]  in
                      Var uu____44529  in
                    mk_term uu____44528 r1 Expr  in
                  (uu____44527, branches)  in
                Match uu____44512  in
              mk_term uu____44511 r2 Expr  in
            ([mk_pattern (PatVar (x, FStar_Pervasives_Native.None)) r1],
              uu____44510)
             in
          Abs uu____44503  in
        mk_term uu____44502 r2 Expr
  
let (un_function :
  pattern -> term -> (pattern * term) FStar_Pervasives_Native.option) =
  fun p  ->
    fun tm  ->
      match ((p.pat), (tm.tm)) with
      | (PatVar uu____44567,Abs (pats,body)) ->
          FStar_Pervasives_Native.Some
            ((mk_pattern (PatApp (p, pats)) p.prange), body)
      | uu____44586 -> FStar_Pervasives_Native.None
  
let (lid_with_range :
  FStar_Ident.lident -> FStar_Range.range -> FStar_Ident.lident) =
  fun lid  ->
    fun r  ->
      let uu____44606 = FStar_Ident.path_of_lid lid  in
      FStar_Ident.lid_of_path uu____44606 r
  
let (consPat : FStar_Range.range -> pattern -> pattern -> pattern') =
  fun r  ->
    fun hd1  ->
      fun tl1  ->
        PatApp
          ((mk_pattern (PatName FStar_Parser_Const.cons_lid) r), [hd1; tl1])
  
let (consTerm : FStar_Range.range -> term -> term -> term) =
  fun r  ->
    fun hd1  ->
      fun tl1  ->
        mk_term
          (Construct
             (FStar_Parser_Const.cons_lid, [(hd1, Nothing); (tl1, Nothing)]))
          r Expr
  
let (lexConsTerm : FStar_Range.range -> term -> term -> term) =
  fun r  ->
    fun hd1  ->
      fun tl1  ->
        mk_term
          (Construct
             (FStar_Parser_Const.lexcons_lid,
               [(hd1, Nothing); (tl1, Nothing)])) r Expr
  
let (mkConsList : FStar_Range.range -> term Prims.list -> term) =
  fun r  ->
    fun elts  ->
      let nil = mk_term (Construct (FStar_Parser_Const.nil_lid, [])) r Expr
         in
      FStar_List.fold_right (fun e  -> fun tl1  -> consTerm r e tl1) elts nil
  
let (mkLexList : FStar_Range.range -> term Prims.list -> term) =
  fun r  ->
    fun elts  ->
      let nil =
        mk_term (Construct (FStar_Parser_Const.lextop_lid, [])) r Expr  in
      FStar_List.fold_right (fun e  -> fun tl1  -> lexConsTerm r e tl1) elts
        nil
  
let (ml_comp : term -> term) =
  fun t  ->
    let ml = mk_term (Name FStar_Parser_Const.effect_ML_lid) t.range Expr  in
    let t1 = mk_term (App (ml, t, Nothing)) t.range Expr  in t1
  
let (tot_comp : term -> term) =
  fun t  ->
    let ml = mk_term (Name FStar_Parser_Const.effect_Tot_lid) t.range Expr
       in
    let t1 = mk_term (App (ml, t, Nothing)) t.range Expr  in t1
  
let (mkApp : term -> (term * imp) Prims.list -> FStar_Range.range -> term) =
  fun t  ->
    fun args  ->
      fun r  ->
        match args with
        | [] -> t
        | uu____44801 ->
            (match t.tm with
             | Name s -> mk_term (Construct (s, args)) r Un
             | uu____44815 ->
                 FStar_List.fold_left
                   (fun t1  ->
                      fun uu____44825  ->
                        match uu____44825 with
                        | (a,imp) -> mk_term (App (t1, a, imp)) r Un) t args)
  
let (mkRefSet : FStar_Range.range -> term Prims.list -> term) =
  fun r  ->
    fun elts  ->
      let uu____44847 =
        (FStar_Parser_Const.set_empty, FStar_Parser_Const.set_singleton,
          FStar_Parser_Const.set_union, FStar_Parser_Const.heap_addr_of_lid)
         in
      match uu____44847 with
      | (empty_lid,singleton_lid,union_lid,addr_of_lid) ->
          let empty1 =
            let uu____44861 =
              let uu____44862 = FStar_Ident.set_lid_range empty_lid r  in
              Var uu____44862  in
            mk_term uu____44861 r Expr  in
          let addr_of =
            let uu____44864 =
              let uu____44865 = FStar_Ident.set_lid_range addr_of_lid r  in
              Var uu____44865  in
            mk_term uu____44864 r Expr  in
          let singleton1 =
            let uu____44867 =
              let uu____44868 = FStar_Ident.set_lid_range singleton_lid r  in
              Var uu____44868  in
            mk_term uu____44867 r Expr  in
          let union1 =
            let uu____44870 =
              let uu____44871 = FStar_Ident.set_lid_range union_lid r  in
              Var uu____44871  in
            mk_term uu____44870 r Expr  in
          FStar_List.fold_right
            (fun e  ->
               fun tl1  ->
                 let e1 = mkApp addr_of [(e, Nothing)] r  in
                 let single_e = mkApp singleton1 [(e1, Nothing)] r  in
                 mkApp union1 [(single_e, Nothing); (tl1, Nothing)] r) elts
            empty1
  
let (mkExplicitApp : term -> term Prims.list -> FStar_Range.range -> term) =
  fun t  ->
    fun args  ->
      fun r  ->
        match args with
        | [] -> t
        | uu____44928 ->
            (match t.tm with
             | Name s ->
                 let uu____44932 =
                   let uu____44933 =
                     let uu____44944 =
                       FStar_List.map (fun a  -> (a, Nothing)) args  in
                     (s, uu____44944)  in
                   Construct uu____44933  in
                 mk_term uu____44932 r Un
             | uu____44963 ->
                 FStar_List.fold_left
                   (fun t1  -> fun a  -> mk_term (App (t1, a, Nothing)) r Un)
                   t args)
  
let (unit_const : FStar_Range.range -> term) =
  fun r  -> mk_term (Const FStar_Const.Const_unit) r Expr 
let (mkAdmitMagic : FStar_Range.range -> term) =
  fun r  ->
    let admit1 =
      let admit_name =
        let uu____44982 =
          let uu____44983 =
            FStar_Ident.set_lid_range FStar_Parser_Const.admit_lid r  in
          Var uu____44983  in
        mk_term uu____44982 r Expr  in
      mkExplicitApp admit_name [unit_const r] r  in
    let magic1 =
      let magic_name =
        let uu____44986 =
          let uu____44987 =
            FStar_Ident.set_lid_range FStar_Parser_Const.magic_lid r  in
          Var uu____44987  in
        mk_term uu____44986 r Expr  in
      mkExplicitApp magic_name [unit_const r] r  in
    let admit_magic = mk_term (Seq (admit1, magic1)) r Expr  in admit_magic
  
let mkWildAdmitMagic :
  'Auu____44994 .
    FStar_Range.range ->
      (pattern * 'Auu____44994 FStar_Pervasives_Native.option * term)
  =
  fun r  ->
    let uu____45008 = mkAdmitMagic r  in
    ((mk_pattern (PatWild FStar_Pervasives_Native.None) r),
      FStar_Pervasives_Native.None, uu____45008)
  
let focusBranches :
  'Auu____45018 .
    (Prims.bool * (pattern * 'Auu____45018 FStar_Pervasives_Native.option *
      term)) Prims.list ->
      FStar_Range.range ->
        (pattern * 'Auu____45018 FStar_Pervasives_Native.option * term)
          Prims.list
  =
  fun branches  ->
    fun r  ->
      let should_filter =
        FStar_Util.for_some FStar_Pervasives_Native.fst branches  in
      if should_filter
      then
        (FStar_Errors.log_issue r
           (FStar_Errors.Warning_Filtered, "Focusing on only some cases");
         (let focussed =
            let uu____45118 =
              FStar_List.filter FStar_Pervasives_Native.fst branches  in
            FStar_All.pipe_right uu____45118
              (FStar_List.map FStar_Pervasives_Native.snd)
             in
          let uu____45211 =
            let uu____45222 = mkWildAdmitMagic r  in [uu____45222]  in
          FStar_List.append focussed uu____45211))
      else
        FStar_All.pipe_right branches
          (FStar_List.map FStar_Pervasives_Native.snd)
  
let focusLetBindings :
  'Auu____45319 .
    (Prims.bool * ('Auu____45319 * term)) Prims.list ->
      FStar_Range.range -> ('Auu____45319 * term) Prims.list
  =
  fun lbs  ->
    fun r  ->
      let should_filter = FStar_Util.for_some FStar_Pervasives_Native.fst lbs
         in
      if should_filter
      then
        (FStar_Errors.log_issue r
           (FStar_Errors.Warning_Filtered,
             "Focusing on only some cases in this (mutually) recursive definition");
         FStar_List.map
           (fun uu____45400  ->
              match uu____45400 with
              | (f,lb) ->
                  if f
                  then lb
                  else
                    (let uu____45433 = mkAdmitMagic r  in
                     ((FStar_Pervasives_Native.fst lb), uu____45433))) lbs)
      else
        FStar_All.pipe_right lbs (FStar_List.map FStar_Pervasives_Native.snd)
  
let focusAttrLetBindings :
  'Auu____45480 'Auu____45481 .
    ('Auu____45480 * (Prims.bool * ('Auu____45481 * term))) Prims.list ->
      FStar_Range.range ->
        ('Auu____45480 * ('Auu____45481 * term)) Prims.list
  =
  fun lbs  ->
    fun r  ->
      let should_filter =
        FStar_Util.for_some
          (fun uu____45551  ->
             match uu____45551 with | (attr,(focus,uu____45568)) -> focus)
          lbs
         in
      if should_filter
      then
        (FStar_Errors.log_issue r
           (FStar_Errors.Warning_Filtered,
             "Focusing on only some cases in this (mutually) recursive definition");
         FStar_List.map
           (fun uu____45627  ->
              match uu____45627 with
              | (attr,(f,lb)) ->
                  if f
                  then (attr, lb)
                  else
                    (let uu____45686 =
                       let uu____45691 = mkAdmitMagic r  in
                       ((FStar_Pervasives_Native.fst lb), uu____45691)  in
                     (attr, uu____45686))) lbs)
      else
        FStar_All.pipe_right lbs
          (FStar_List.map
             (fun uu____45748  ->
                match uu____45748 with
                | (attr,(uu____45771,lb)) -> (attr, lb)))
  
let (mkFsTypApp : term -> term Prims.list -> FStar_Range.range -> term) =
  fun t  ->
    fun args  ->
      fun r  ->
        let uu____45816 = FStar_List.map (fun a  -> (a, FsTypApp)) args  in
        mkApp t uu____45816 r
  
let (mkTuple : term Prims.list -> FStar_Range.range -> term) =
  fun args  ->
    fun r  ->
      let cons1 =
        FStar_Parser_Const.mk_tuple_data_lid (FStar_List.length args) r  in
      let uu____45845 = FStar_List.map (fun x  -> (x, Nothing)) args  in
      mkApp (mk_term (Name cons1) r Expr) uu____45845 r
  
let (mkDTuple : term Prims.list -> FStar_Range.range -> term) =
  fun args  ->
    fun r  ->
      let cons1 =
        FStar_Parser_Const.mk_dtuple_data_lid (FStar_List.length args) r  in
      let uu____45874 = FStar_List.map (fun x  -> (x, Nothing)) args  in
      mkApp (mk_term (Name cons1) r Expr) uu____45874 r
  
let (mkRefinedBinder :
  FStar_Ident.ident ->
    term ->
      Prims.bool ->
        term FStar_Pervasives_Native.option ->
          FStar_Range.range ->
            arg_qualifier FStar_Pervasives_Native.option -> binder)
  =
  fun id1  ->
    fun t  ->
      fun should_bind_var  ->
        fun refopt  ->
          fun m  ->
            fun implicit  ->
              let b = mk_binder (Annotated (id1, t)) m Type_level implicit
                 in
              match refopt with
              | FStar_Pervasives_Native.None  -> b
              | FStar_Pervasives_Native.Some phi ->
                  if should_bind_var
                  then
                    mk_binder
                      (Annotated
                         (id1, (mk_term (Refine (b, phi)) m Type_level))) m
                      Type_level implicit
                  else
                    (let x = FStar_Ident.gen t.range  in
                     let b1 =
                       mk_binder (Annotated (x, t)) m Type_level implicit  in
                     mk_binder
                       (Annotated
                          (id1, (mk_term (Refine (b1, phi)) m Type_level))) m
                       Type_level implicit)
  
let (mkRefinedPattern :
  pattern ->
    term ->
      Prims.bool ->
        term FStar_Pervasives_Native.option ->
          FStar_Range.range -> FStar_Range.range -> pattern)
  =
  fun pat  ->
    fun t  ->
      fun should_bind_pat  ->
        fun phi_opt  ->
          fun t_range  ->
            fun range  ->
              let t1 =
                match phi_opt with
                | FStar_Pervasives_Native.None  -> t
                | FStar_Pervasives_Native.Some phi ->
                    if should_bind_pat
                    then
                      (match pat.pat with
                       | PatVar (x,uu____45976) ->
                           mk_term
                             (Refine
                                ((mk_binder (Annotated (x, t)) t_range
                                    Type_level FStar_Pervasives_Native.None),
                                  phi)) range Type_level
                       | uu____45981 ->
                           let x = FStar_Ident.gen t_range  in
                           let phi1 =
                             let x_var =
                               let uu____45985 =
                                 let uu____45986 = FStar_Ident.lid_of_ids [x]
                                    in
                                 Var uu____45986  in
                               mk_term uu____45985 phi.range Formula  in
                             let pat_branch =
                               (pat, FStar_Pervasives_Native.None, phi)  in
                             let otherwise_branch =
                               let uu____46007 =
                                 let uu____46008 =
                                   let uu____46009 =
                                     FStar_Ident.lid_of_path ["False"]
                                       phi.range
                                      in
                                   Name uu____46009  in
                                 mk_term uu____46008 phi.range Formula  in
                               ((mk_pattern
                                   (PatWild FStar_Pervasives_Native.None)
                                   phi.range), FStar_Pervasives_Native.None,
                                 uu____46007)
                                in
                             mk_term
                               (Match (x_var, [pat_branch; otherwise_branch]))
                               phi.range Formula
                              in
                           mk_term
                             (Refine
                                ((mk_binder (Annotated (x, t)) t_range
                                    Type_level FStar_Pervasives_Native.None),
                                  phi1)) range Type_level)
                    else
                      (let x = FStar_Ident.gen t.range  in
                       mk_term
                         (Refine
                            ((mk_binder (Annotated (x, t)) t_range Type_level
                                FStar_Pervasives_Native.None), phi)) range
                         Type_level)
                 in
              mk_pattern
                (PatAscribed (pat, (t1, FStar_Pervasives_Native.None))) range
  
let rec (extract_named_refinement :
  term ->
    (FStar_Ident.ident * term * term FStar_Pervasives_Native.option)
      FStar_Pervasives_Native.option)
  =
  fun t1  ->
    match t1.tm with
    | NamedTyp (x,t) ->
        FStar_Pervasives_Native.Some (x, t, FStar_Pervasives_Native.None)
    | Refine
        ({ b = Annotated (x,t); brange = uu____46100; blevel = uu____46101;
           aqual = uu____46102;_},t')
        ->
        FStar_Pervasives_Native.Some
          (x, t, (FStar_Pervasives_Native.Some t'))
    | Paren t -> extract_named_refinement t
    | uu____46117 -> FStar_Pervasives_Native.None
  
let rec (as_mlist :
  ((FStar_Ident.lid * decl) * decl Prims.list) -> decl Prims.list -> modul) =
  fun cur  ->
    fun ds  ->
      let uu____46161 = cur  in
      match uu____46161 with
      | ((m_name,m_decl),cur1) ->
          (match ds with
           | [] -> Module (m_name, (m_decl :: (FStar_List.rev cur1)))
           | d::ds1 ->
               (match d.d with
                | TopLevelModule m' ->
                    FStar_Errors.raise_error
                      (FStar_Errors.Fatal_UnexpectedModuleDeclaration,
                        "Unexpected module declaration") d.drange
                | uu____46192 -> as_mlist ((m_name, m_decl), (d :: cur1)) ds1))
  
let (as_frag :
  Prims.bool -> FStar_Range.range -> decl Prims.list -> inputFragment) =
  fun is_light  ->
    fun light_range  ->
      fun ds  ->
        let uu____46221 =
          match ds with
          | d::ds1 -> (d, ds1)
          | [] -> FStar_Exn.raise FStar_Errors.Empty_frag  in
        match uu____46221 with
        | (d,ds1) ->
            (match d.d with
             | TopLevelModule m ->
                 let ds2 =
                   if is_light
                   then
                     let uu____46259 =
                       mk_decl (Pragma LightOff) light_range []  in
                     uu____46259 :: ds1
                   else ds1  in
                 let m1 = as_mlist ((m, d), []) ds2  in FStar_Util.Inl m1
             | uu____46271 ->
                 let ds2 = d :: ds1  in
                 (FStar_List.iter
                    (fun uu___309_46282  ->
                       match uu___309_46282 with
                       | { d = TopLevelModule uu____46283; drange = r;
                           doc = uu____46285; quals = uu____46286;
                           attrs = uu____46287;_} ->
                           FStar_Errors.raise_error
                             (FStar_Errors.Fatal_UnexpectedModuleDeclaration,
                               "Unexpected module declaration") r
                       | uu____46292 -> ()) ds2;
                  FStar_Util.Inr ds2))
  
let (compile_op :
  Prims.int -> Prims.string -> FStar_Range.range -> Prims.string) =
  fun arity  ->
    fun s  ->
      fun r  ->
        let name_of_char uu___310_46323 =
          match uu___310_46323 with
          | 38 -> "Amp"
          | 64 -> "At"
          | 43 -> "Plus"
          | 45 when arity = (Prims.parse_int "1") -> "Minus"
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
                     (Prims.op_Hat (FStar_Util.string_of_char c) "'"))) r
           in
        match s with
        | ".[]<-" -> "op_String_Assignment"
        | ".()<-" -> "op_Array_Assignment"
        | ".[||]<-" -> "op_Brack_Lens_Assignment"
        | ".(||)<-" -> "op_Lens_Assignment"
        | ".[]" -> "op_String_Access"
        | ".()" -> "op_Array_Access"
        | ".[||]" -> "op_Brack_Lens_Access"
        | ".(||)" -> "op_Lens_Access"
        | uu____46393 ->
            let uu____46395 =
              let uu____46397 =
                let uu____46401 = FStar_String.list_of_string s  in
                FStar_List.map name_of_char uu____46401  in
              FStar_String.concat "_" uu____46397  in
            Prims.op_Hat "op_" uu____46395
  
let (compile_op' : Prims.string -> FStar_Range.range -> Prims.string) =
  fun s  -> fun r  -> compile_op (~- (Prims.parse_int "1")) s r 
let (string_of_fsdoc :
  (Prims.string * (Prims.string * Prims.string) Prims.list) -> Prims.string)
  =
  fun uu____46443  ->
    match uu____46443 with
    | (comment,keywords) ->
        let uu____46478 =
          let uu____46480 =
            FStar_List.map
              (fun uu____46494  ->
                 match uu____46494 with
                 | (k,v1) -> Prims.op_Hat k (Prims.op_Hat "->" v1)) keywords
             in
          FStar_String.concat "," uu____46480  in
        Prims.op_Hat comment uu____46478
  
let (string_of_let_qualifier : let_qualifier -> Prims.string) =
  fun uu___311_46516  ->
    match uu___311_46516 with | NoLetQualifier  -> "" | Rec  -> "rec"
  
let to_string_l :
  'Auu____46529 .
    Prims.string ->
      ('Auu____46529 -> Prims.string) ->
        'Auu____46529 Prims.list -> Prims.string
  =
  fun sep  ->
    fun f  ->
      fun l  ->
        let uu____46559 = FStar_List.map f l  in
        FStar_String.concat sep uu____46559
  
let (imp_to_string : imp -> Prims.string) =
  fun uu___312_46570  ->
    match uu___312_46570 with | Hash  -> "#" | uu____46573 -> ""
  
let rec (term_to_string : term -> Prims.string) =
  fun x  ->
    match x.tm with
    | Wild  -> "_"
    | Requires (t,uu____46616) ->
        let uu____46623 = term_to_string t  in
        FStar_Util.format1 "(requires %s)" uu____46623
    | Ensures (t,uu____46627) ->
        let uu____46634 = term_to_string t  in
        FStar_Util.format1 "(ensures %s)" uu____46634
    | Labeled (t,l,uu____46639) ->
        let uu____46644 = term_to_string t  in
        FStar_Util.format2 "(labeled %s %s)" l uu____46644
    | Const c -> FStar_Parser_Const.const_to_string c
    | Op (s,xs) ->
        let uu____46654 = FStar_Ident.text_of_id s  in
        let uu____46656 =
          let uu____46658 =
            FStar_List.map
              (fun x1  -> FStar_All.pipe_right x1 term_to_string) xs
             in
          FStar_String.concat ", " uu____46658  in
        FStar_Util.format2 "%s(%s)" uu____46654 uu____46656
    | Tvar id1 -> id1.FStar_Ident.idText
    | Uvar id1 -> id1.FStar_Ident.idText
    | Var l -> l.FStar_Ident.str
    | Name l -> l.FStar_Ident.str
    | Projector (rec_lid,field_id) ->
        let uu____46674 = FStar_Ident.string_of_lid rec_lid  in
        FStar_Util.format2 "%s?.%s" uu____46674 field_id.FStar_Ident.idText
    | Construct (l,args) ->
        let uu____46691 =
          to_string_l " "
            (fun uu____46702  ->
               match uu____46702 with
               | (a,imp) ->
                   let uu____46710 = term_to_string a  in
                   FStar_Util.format2 "%s%s" (imp_to_string imp) uu____46710)
            args
           in
        FStar_Util.format2 "(%s %s)" l.FStar_Ident.str uu____46691
    | Abs (pats,t) ->
        let uu____46720 = to_string_l " " pat_to_string pats  in
        let uu____46723 = FStar_All.pipe_right t term_to_string  in
        FStar_Util.format2 "(fun %s -> %s)" uu____46720 uu____46723
    | App (t1,t2,imp) ->
        let uu____46730 = FStar_All.pipe_right t1 term_to_string  in
        let uu____46733 = FStar_All.pipe_right t2 term_to_string  in
        FStar_Util.format3 "%s %s%s" uu____46730 (imp_to_string imp)
          uu____46733
    | Let (Rec ,(a,(p,b))::lbs,body) ->
        let uu____46794 = attrs_opt_to_string a  in
        let uu____46796 =
          let uu____46798 = FStar_All.pipe_right p pat_to_string  in
          let uu____46801 = FStar_All.pipe_right b term_to_string  in
          FStar_Util.format2 "%s=%s" uu____46798 uu____46801  in
        let uu____46805 =
          to_string_l " "
            (fun uu____46827  ->
               match uu____46827 with
               | (a1,(p1,b1)) ->
                   let uu____46856 = attrs_opt_to_string a1  in
                   let uu____46858 = FStar_All.pipe_right p1 pat_to_string
                      in
                   let uu____46861 = FStar_All.pipe_right b1 term_to_string
                      in
                   FStar_Util.format3 "%sand %s=%s" uu____46856 uu____46858
                     uu____46861) lbs
           in
        let uu____46865 = FStar_All.pipe_right body term_to_string  in
        FStar_Util.format4 "%slet rec %s%s in %s" uu____46794 uu____46796
          uu____46805 uu____46865
    | Let (q,(attrs,(pat,tm))::[],body) ->
        let uu____46924 = attrs_opt_to_string attrs  in
        let uu____46926 = FStar_All.pipe_right pat pat_to_string  in
        let uu____46929 = FStar_All.pipe_right tm term_to_string  in
        let uu____46932 = FStar_All.pipe_right body term_to_string  in
        FStar_Util.format5 "%slet %s %s = %s in %s" uu____46924
          (string_of_let_qualifier q) uu____46926 uu____46929 uu____46932
    | Let (uu____46936,uu____46937,uu____46938) ->
        FStar_Errors.raise_error
          (FStar_Errors.Fatal_EmptySurfaceLet,
            "Internal error: found an invalid surface Let") x.range
    | LetOpen (lid,t) ->
        let uu____46972 = FStar_Ident.string_of_lid lid  in
        let uu____46974 = term_to_string t  in
        FStar_Util.format2 "let open %s in %s" uu____46972 uu____46974
    | Seq (t1,t2) ->
        let uu____46979 = FStar_All.pipe_right t1 term_to_string  in
        let uu____46982 = FStar_All.pipe_right t2 term_to_string  in
        FStar_Util.format2 "%s; %s" uu____46979 uu____46982
    | Bind (id1,t1,t2) ->
        let uu____46989 = term_to_string t1  in
        let uu____46991 = term_to_string t2  in
        FStar_Util.format3 "%s <- %s; %s" id1.FStar_Ident.idText uu____46989
          uu____46991
    | If (t1,t2,t3) ->
        let uu____46997 = FStar_All.pipe_right t1 term_to_string  in
        let uu____47000 = FStar_All.pipe_right t2 term_to_string  in
        let uu____47003 = FStar_All.pipe_right t3 term_to_string  in
        FStar_Util.format3 "if %s then %s else %s" uu____46997 uu____47000
          uu____47003
    | Match (t,branches) ->
        let s =
          match x.tm with
          | Match uu____47032 -> "match"
          | TryWith uu____47048 -> "try"
          | uu____47064 -> failwith "impossible"  in
        let uu____47067 = FStar_All.pipe_right t term_to_string  in
        let uu____47070 =
          to_string_l " | "
            (fun uu____47088  ->
               match uu____47088 with
               | (p,w,e) ->
                   let uu____47105 = FStar_All.pipe_right p pat_to_string  in
                   let uu____47108 =
                     match w with
                     | FStar_Pervasives_Native.None  -> ""
                     | FStar_Pervasives_Native.Some e1 ->
                         let uu____47113 = term_to_string e1  in
                         FStar_Util.format1 "when %s" uu____47113
                      in
                   let uu____47116 = FStar_All.pipe_right e term_to_string
                      in
                   FStar_Util.format3 "%s %s -> %s" uu____47105 uu____47108
                     uu____47116) branches
           in
        FStar_Util.format3 "%s %s with %s" s uu____47067 uu____47070
    | TryWith (t,branches) ->
        let s =
          match x.tm with
          | Match uu____47146 -> "match"
          | TryWith uu____47162 -> "try"
          | uu____47178 -> failwith "impossible"  in
        let uu____47181 = FStar_All.pipe_right t term_to_string  in
        let uu____47184 =
          to_string_l " | "
            (fun uu____47202  ->
               match uu____47202 with
               | (p,w,e) ->
                   let uu____47219 = FStar_All.pipe_right p pat_to_string  in
                   let uu____47222 =
                     match w with
                     | FStar_Pervasives_Native.None  -> ""
                     | FStar_Pervasives_Native.Some e1 ->
                         let uu____47227 = term_to_string e1  in
                         FStar_Util.format1 "when %s" uu____47227
                      in
                   let uu____47230 = FStar_All.pipe_right e term_to_string
                      in
                   FStar_Util.format3 "%s %s -> %s" uu____47219 uu____47222
                     uu____47230) branches
           in
        FStar_Util.format3 "%s %s with %s" s uu____47181 uu____47184
    | Ascribed (t1,t2,FStar_Pervasives_Native.None ) ->
        let uu____47239 = FStar_All.pipe_right t1 term_to_string  in
        let uu____47242 = FStar_All.pipe_right t2 term_to_string  in
        FStar_Util.format2 "(%s : %s)" uu____47239 uu____47242
    | Ascribed (t1,t2,FStar_Pervasives_Native.Some tac) ->
        let uu____47251 = FStar_All.pipe_right t1 term_to_string  in
        let uu____47254 = FStar_All.pipe_right t2 term_to_string  in
        let uu____47257 = FStar_All.pipe_right tac term_to_string  in
        FStar_Util.format3 "(%s : %s by %s)" uu____47251 uu____47254
          uu____47257
    | Record (FStar_Pervasives_Native.Some e,fields) ->
        let uu____47277 = FStar_All.pipe_right e term_to_string  in
        let uu____47280 =
          to_string_l " "
            (fun uu____47291  ->
               match uu____47291 with
               | (l,e1) ->
                   let uu____47299 = FStar_All.pipe_right e1 term_to_string
                      in
                   FStar_Util.format2 "%s=%s" l.FStar_Ident.str uu____47299)
            fields
           in
        FStar_Util.format2 "{%s with %s}" uu____47277 uu____47280
    | Record (FStar_Pervasives_Native.None ,fields) ->
        let uu____47319 =
          to_string_l " "
            (fun uu____47330  ->
               match uu____47330 with
               | (l,e) ->
                   let uu____47338 = FStar_All.pipe_right e term_to_string
                      in
                   FStar_Util.format2 "%s=%s" l.FStar_Ident.str uu____47338)
            fields
           in
        FStar_Util.format1 "{%s}" uu____47319
    | Project (e,l) ->
        let uu____47345 = FStar_All.pipe_right e term_to_string  in
        FStar_Util.format2 "%s.%s" uu____47345 l.FStar_Ident.str
    | Product ([],t) -> term_to_string t
    | Product (b::hd1::tl1,t) ->
        term_to_string
          (mk_term
             (Product
                ([b], (mk_term (Product ((hd1 :: tl1), t)) x.range x.level)))
             x.range x.level)
    | Product (b::[],t) when x.level = Type_level ->
        let uu____47368 = FStar_All.pipe_right b binder_to_string  in
        let uu____47371 = FStar_All.pipe_right t term_to_string  in
        FStar_Util.format2 "%s -> %s" uu____47368 uu____47371
    | Product (b::[],t) when x.level = Kind ->
        let uu____47379 = FStar_All.pipe_right b binder_to_string  in
        let uu____47382 = FStar_All.pipe_right t term_to_string  in
        FStar_Util.format2 "%s => %s" uu____47379 uu____47382
    | Sum (binders,t) ->
        let uu____47400 =
          FStar_All.pipe_right (FStar_List.append binders [FStar_Util.Inr t])
            (FStar_List.map
               (fun uu___313_47432  ->
                  match uu___313_47432 with
                  | FStar_Util.Inl b -> binder_to_string b
                  | FStar_Util.Inr t1 -> term_to_string t1))
           in
        FStar_All.pipe_right uu____47400 (FStar_String.concat " & ")
    | QForall (bs,pats,t) ->
        let uu____47460 = to_string_l " " binder_to_string bs  in
        let uu____47463 =
          to_string_l " \\/ " (to_string_l "; " term_to_string) pats  in
        let uu____47469 = FStar_All.pipe_right t term_to_string  in
        FStar_Util.format3 "forall %s.{:pattern %s} %s" uu____47460
          uu____47463 uu____47469
    | QExists (bs,pats,t) ->
        let uu____47488 = to_string_l " " binder_to_string bs  in
        let uu____47491 =
          to_string_l " \\/ " (to_string_l "; " term_to_string) pats  in
        let uu____47497 = FStar_All.pipe_right t term_to_string  in
        FStar_Util.format3 "exists %s.{:pattern %s} %s" uu____47488
          uu____47491 uu____47497
    | Refine (b,t) ->
        let uu____47503 = FStar_All.pipe_right b binder_to_string  in
        let uu____47506 = FStar_All.pipe_right t term_to_string  in
        FStar_Util.format2 "%s:{%s}" uu____47503 uu____47506
    | NamedTyp (x1,t) ->
        let uu____47512 = FStar_All.pipe_right t term_to_string  in
        FStar_Util.format2 "%s:%s" x1.FStar_Ident.idText uu____47512
    | Paren t ->
        let uu____47517 = FStar_All.pipe_right t term_to_string  in
        FStar_Util.format1 "(%s)" uu____47517
    | Product (bs,t) ->
        let uu____47527 =
          let uu____47529 =
            FStar_All.pipe_right bs (FStar_List.map binder_to_string)  in
          FStar_All.pipe_right uu____47529 (FStar_String.concat ",")  in
        let uu____47544 = FStar_All.pipe_right t term_to_string  in
        FStar_Util.format2 "Unidentified product: [%s] %s" uu____47527
          uu____47544
    | Discrim lid ->
        let uu____47549 = FStar_Ident.string_of_lid lid  in
        FStar_Util.format1 "%s?" uu____47549
    | Attributes ts ->
        let uu____47555 =
          let uu____47557 = FStar_List.map term_to_string ts  in
          FStar_All.pipe_left (FStar_String.concat " ") uu____47557  in
        FStar_Util.format1 "(attributes %s)" uu____47555
    | Antiquote t ->
        let uu____47569 = term_to_string t  in
        FStar_Util.format1 "(`#%s)" uu____47569
    | Quote (t,Static ) ->
        let uu____47573 = term_to_string t  in
        FStar_Util.format1 "(`(%s))" uu____47573
    | Quote (t,Dynamic ) ->
        let uu____47577 = term_to_string t  in
        FStar_Util.format1 "quote (%s)" uu____47577
    | VQuote t ->
        let uu____47581 = term_to_string t  in
        FStar_Util.format1 "`%%%s" uu____47581
    | CalcProof (rel,init1,steps) ->
        let uu____47591 = term_to_string rel  in
        let uu____47593 = term_to_string init1  in
        let uu____47595 =
          let uu____47597 = FStar_List.map calc_step_to_string steps  in
          FStar_All.pipe_left (FStar_String.concat " ") uu____47597  in
        FStar_Util.format3 "calc (%s) { %s %s }" uu____47591 uu____47593
          uu____47595

and (calc_step_to_string : calc_step -> Prims.string) =
  fun uu____47608  ->
    match uu____47608 with
    | CalcStep (rel,just,next) ->
        let uu____47613 = term_to_string rel  in
        let uu____47615 = term_to_string just  in
        let uu____47617 = term_to_string next  in
        FStar_Util.format3 "%s{ %s } %s" uu____47613 uu____47615 uu____47617

and (binder_to_string : binder -> Prims.string) =
  fun x  ->
    let s =
      match x.b with
      | Variable i -> i.FStar_Ident.idText
      | TVariable i -> FStar_Util.format1 "%s:_" i.FStar_Ident.idText
      | TAnnotated (i,t) ->
          let uu____47629 = FStar_All.pipe_right t term_to_string  in
          FStar_Util.format2 "%s:%s" i.FStar_Ident.idText uu____47629
      | Annotated (i,t) ->
          let uu____47635 = FStar_All.pipe_right t term_to_string  in
          FStar_Util.format2 "%s:%s" i.FStar_Ident.idText uu____47635
      | NoName t -> FStar_All.pipe_right t term_to_string  in
    let uu____47641 = aqual_to_string x.aqual  in
    FStar_Util.format2 "%s%s" uu____47641 s

and (aqual_to_string :
  arg_qualifier FStar_Pervasives_Native.option -> Prims.string) =
  fun uu___314_47644  ->
    match uu___314_47644 with
    | FStar_Pervasives_Native.Some (Equality ) -> "$"
    | FStar_Pervasives_Native.Some (Implicit ) -> "#"
    | uu____47650 -> ""

and (pat_to_string : pattern -> Prims.string) =
  fun x  ->
    match x.pat with
    | PatWild (FStar_Pervasives_Native.None ) -> "_"
    | PatWild uu____47657 -> "#_"
    | PatConst c -> FStar_Parser_Const.const_to_string c
    | PatApp (p,ps) ->
        let uu____47668 = FStar_All.pipe_right p pat_to_string  in
        let uu____47671 = to_string_l " " pat_to_string ps  in
        FStar_Util.format2 "(%s %s)" uu____47668 uu____47671
    | PatTvar (i,aq) ->
        let uu____47681 = aqual_to_string aq  in
        FStar_Util.format2 "%s%s" uu____47681 i.FStar_Ident.idText
    | PatVar (i,aq) ->
        let uu____47690 = aqual_to_string aq  in
        FStar_Util.format2 "%s%s" uu____47690 i.FStar_Ident.idText
    | PatName l -> l.FStar_Ident.str
    | PatList l ->
        let uu____47697 = to_string_l "; " pat_to_string l  in
        FStar_Util.format1 "[%s]" uu____47697
    | PatTuple (l,false ) ->
        let uu____47708 = to_string_l ", " pat_to_string l  in
        FStar_Util.format1 "(%s)" uu____47708
    | PatTuple (l,true ) ->
        let uu____47719 = to_string_l ", " pat_to_string l  in
        FStar_Util.format1 "(|%s|)" uu____47719
    | PatRecord l ->
        let uu____47730 =
          to_string_l "; "
            (fun uu____47741  ->
               match uu____47741 with
               | (f,e) ->
                   let uu____47749 = FStar_All.pipe_right e pat_to_string  in
                   FStar_Util.format2 "%s=%s" f.FStar_Ident.str uu____47749)
            l
           in
        FStar_Util.format1 "{%s}" uu____47730
    | PatOr l -> to_string_l "|\n " pat_to_string l
    | PatOp op ->
        let uu____47759 = FStar_Ident.text_of_id op  in
        FStar_Util.format1 "(%s)" uu____47759
    | PatAscribed (p,(t,FStar_Pervasives_Native.None )) ->
        let uu____47772 = FStar_All.pipe_right p pat_to_string  in
        let uu____47775 = FStar_All.pipe_right t term_to_string  in
        FStar_Util.format2 "(%s:%s)" uu____47772 uu____47775
    | PatAscribed (p,(t,FStar_Pervasives_Native.Some tac)) ->
        let uu____47790 = FStar_All.pipe_right p pat_to_string  in
        let uu____47793 = FStar_All.pipe_right t term_to_string  in
        let uu____47796 = FStar_All.pipe_right tac term_to_string  in
        FStar_Util.format3 "(%s:%s by %s)" uu____47790 uu____47793
          uu____47796

and (attrs_opt_to_string :
  term Prims.list FStar_Pervasives_Native.option -> Prims.string) =
  fun uu___315_47800  ->
    match uu___315_47800 with
    | FStar_Pervasives_Native.None  -> ""
    | FStar_Pervasives_Native.Some attrs ->
        let uu____47814 =
          let uu____47816 = FStar_List.map term_to_string attrs  in
          FStar_All.pipe_right uu____47816 (FStar_String.concat "; ")  in
        FStar_Util.format1 "[@ %s]" uu____47814

let rec (head_id_of_pat : pattern -> FStar_Ident.lident Prims.list) =
  fun p  ->
    match p.pat with
    | PatName l -> [l]
    | PatVar (i,uu____47839) ->
        let uu____47844 = FStar_Ident.lid_of_ids [i]  in [uu____47844]
    | PatApp (p1,uu____47846) -> head_id_of_pat p1
    | PatAscribed (p1,uu____47852) -> head_id_of_pat p1
    | uu____47865 -> []
  
let lids_of_let :
  'Auu____47871 .
    (pattern * 'Auu____47871) Prims.list -> FStar_Ident.lident Prims.list
  =
  fun defs  ->
    FStar_All.pipe_right defs
      (FStar_List.collect
         (fun uu____47906  ->
            match uu____47906 with | (p,uu____47914) -> head_id_of_pat p))
  
let (id_of_tycon : tycon -> Prims.string) =
  fun uu___316_47921  ->
    match uu___316_47921 with
    | TyconAbstract (i,uu____47924,uu____47925) -> i.FStar_Ident.idText
    | TyconAbbrev (i,uu____47935,uu____47936,uu____47937) ->
        i.FStar_Ident.idText
    | TyconRecord (i,uu____47947,uu____47948,uu____47949) ->
        i.FStar_Ident.idText
    | TyconVariant (i,uu____47979,uu____47980,uu____47981) ->
        i.FStar_Ident.idText
  
let (decl_to_string : decl -> Prims.string) =
  fun d  ->
    match d.d with
    | TopLevelModule l -> Prims.op_Hat "module " l.FStar_Ident.str
    | Open l -> Prims.op_Hat "open " l.FStar_Ident.str
    | Friend l -> Prims.op_Hat "friend " l.FStar_Ident.str
    | Include l -> Prims.op_Hat "include " l.FStar_Ident.str
    | ModuleAbbrev (i,l) ->
        FStar_Util.format2 "module %s = %s" i.FStar_Ident.idText
          l.FStar_Ident.str
    | TopLevelLet (uu____48039,pats) ->
        let uu____48053 =
          let uu____48055 =
            let uu____48059 = lids_of_let pats  in
            FStar_All.pipe_right uu____48059
              (FStar_List.map (fun l  -> l.FStar_Ident.str))
             in
          FStar_All.pipe_right uu____48055 (FStar_String.concat ", ")  in
        Prims.op_Hat "let " uu____48053
    | Main uu____48076 -> "main ..."
    | Assume (i,uu____48079) -> Prims.op_Hat "assume " i.FStar_Ident.idText
    | Tycon (uu____48081,uu____48082,tys) ->
        let uu____48104 =
          let uu____48106 =
            FStar_All.pipe_right tys
              (FStar_List.map
                 (fun uu____48131  ->
                    match uu____48131 with | (x,uu____48140) -> id_of_tycon x))
             in
          FStar_All.pipe_right uu____48106 (FStar_String.concat ", ")  in
        Prims.op_Hat "type " uu____48104
    | Val (i,uu____48152) -> Prims.op_Hat "val " i.FStar_Ident.idText
    | Exception (i,uu____48155) ->
        Prims.op_Hat "exception " i.FStar_Ident.idText
    | NewEffect (DefineEffect (i,uu____48162,uu____48163,uu____48164)) ->
        Prims.op_Hat "new_effect " i.FStar_Ident.idText
    | NewEffect (RedefineEffect (i,uu____48175,uu____48176)) ->
        Prims.op_Hat "new_effect " i.FStar_Ident.idText
    | Splice (ids,t) ->
        let uu____48188 =
          let uu____48190 =
            let uu____48192 =
              FStar_List.map (fun i  -> i.FStar_Ident.idText) ids  in
            FStar_All.pipe_left (FStar_String.concat ";") uu____48192  in
          let uu____48204 =
            let uu____48206 =
              let uu____48208 = term_to_string t  in
              Prims.op_Hat uu____48208 ")"  in
            Prims.op_Hat "] (" uu____48206  in
          Prims.op_Hat uu____48190 uu____48204  in
        Prims.op_Hat "splice[" uu____48188
    | SubEffect uu____48213 -> "sub_effect"
    | Pragma uu____48215 -> "pragma"
    | Fsdoc uu____48217 -> "fsdoc"
  
let (modul_to_string : modul -> Prims.string) =
  fun m  ->
    match m with
    | Module (uu____48227,decls) ->
        let uu____48233 =
          FStar_All.pipe_right decls (FStar_List.map decl_to_string)  in
        FStar_All.pipe_right uu____48233 (FStar_String.concat "\n")
    | Interface (uu____48248,decls,uu____48250) ->
        let uu____48257 =
          FStar_All.pipe_right decls (FStar_List.map decl_to_string)  in
        FStar_All.pipe_right uu____48257 (FStar_String.concat "\n")
  
let (decl_is_val : FStar_Ident.ident -> decl -> Prims.bool) =
  fun id1  ->
    fun decl  ->
      match decl.d with
      | Val (id',uu____48286) -> FStar_Ident.ident_equals id1 id'
      | uu____48287 -> false
  
let (thunk : term -> term) =
  fun ens  ->
    let wildpat = mk_pattern (PatWild FStar_Pervasives_Native.None) ens.range
       in
    mk_term (Abs ([wildpat], ens)) ens.range Expr
  