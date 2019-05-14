open Prims
type level =
  | Un 
  | Expr 
  | Type_level 
  | Kind 
  | Formula 
let (uu___is_Un : level -> Prims.bool) =
  fun projectee  -> match projectee with | Un  -> true | uu____26 -> false 
let (uu___is_Expr : level -> Prims.bool) =
  fun projectee  -> match projectee with | Expr  -> true | uu____37 -> false 
let (uu___is_Type_level : level -> Prims.bool) =
  fun projectee  ->
    match projectee with | Type_level  -> true | uu____48 -> false
  
let (uu___is_Kind : level -> Prims.bool) =
  fun projectee  -> match projectee with | Kind  -> true | uu____59 -> false 
let (uu___is_Formula : level -> Prims.bool) =
  fun projectee  ->
    match projectee with | Formula  -> true | uu____70 -> false
  
type let_qualifier =
  | NoLetQualifier 
  | Rec 
let (uu___is_NoLetQualifier : let_qualifier -> Prims.bool) =
  fun projectee  ->
    match projectee with | NoLetQualifier  -> true | uu____81 -> false
  
let (uu___is_Rec : let_qualifier -> Prims.bool) =
  fun projectee  -> match projectee with | Rec  -> true | uu____92 -> false 
type quote_kind =
  | Static 
  | Dynamic 
let (uu___is_Static : quote_kind -> Prims.bool) =
  fun projectee  ->
    match projectee with | Static  -> true | uu____103 -> false
  
let (uu___is_Dynamic : quote_kind -> Prims.bool) =
  fun projectee  ->
    match projectee with | Dynamic  -> true | uu____114 -> false
  
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
  | QForall of (binder Prims.list * (FStar_Ident.ident Prims.list * term
  Prims.list Prims.list) * term) 
  | QExists of (binder Prims.list * (FStar_Ident.ident Prims.list * term
  Prims.list Prims.list) * term) 
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
    match projectee with | Wild  -> true | uu____1047 -> false
  
let (uu___is_Const : term' -> Prims.bool) =
  fun projectee  ->
    match projectee with | Const _0 -> true | uu____1059 -> false
  
let (__proj__Const__item___0 : term' -> FStar_Const.sconst) =
  fun projectee  -> match projectee with | Const _0 -> _0 
let (uu___is_Op : term' -> Prims.bool) =
  fun projectee  ->
    match projectee with | Op _0 -> true | uu____1089 -> false
  
let (__proj__Op__item___0 : term' -> (FStar_Ident.ident * term Prims.list)) =
  fun projectee  -> match projectee with | Op _0 -> _0 
let (uu___is_Tvar : term' -> Prims.bool) =
  fun projectee  ->
    match projectee with | Tvar _0 -> true | uu____1143 -> false
  
let (__proj__Tvar__item___0 : term' -> FStar_Ident.ident) =
  fun projectee  -> match projectee with | Tvar _0 -> _0 
let (uu___is_Uvar : term' -> Prims.bool) =
  fun projectee  ->
    match projectee with | Uvar _0 -> true | uu____1174 -> false
  
let (__proj__Uvar__item___0 : term' -> FStar_Ident.ident) =
  fun projectee  -> match projectee with | Uvar _0 -> _0 
let (uu___is_Var : term' -> Prims.bool) =
  fun projectee  ->
    match projectee with | Var _0 -> true | uu____1207 -> false
  
let (__proj__Var__item___0 : term' -> FStar_Ident.lid) =
  fun projectee  -> match projectee with | Var _0 -> _0 
let (uu___is_Name : term' -> Prims.bool) =
  fun projectee  ->
    match projectee with | Name _0 -> true | uu____1250 -> false
  
let (__proj__Name__item___0 : term' -> FStar_Ident.lid) =
  fun projectee  -> match projectee with | Name _0 -> _0 
let (uu___is_Projector : term' -> Prims.bool) =
  fun projectee  ->
    match projectee with | Projector _0 -> true | uu____1299 -> false
  
let (__proj__Projector__item___0 :
  term' -> (FStar_Ident.lid * FStar_Ident.ident)) =
  fun projectee  -> match projectee with | Projector _0 -> _0 
let (uu___is_Construct : term' -> Prims.bool) =
  fun projectee  ->
    match projectee with | Construct _0 -> true | uu____1365 -> false
  
let (__proj__Construct__item___0 :
  term' -> (FStar_Ident.lid * (term * imp) Prims.list)) =
  fun projectee  -> match projectee with | Construct _0 -> _0 
let (uu___is_Abs : term' -> Prims.bool) =
  fun projectee  ->
    match projectee with | Abs _0 -> true | uu____1446 -> false
  
let (__proj__Abs__item___0 : term' -> (pattern Prims.list * term)) =
  fun projectee  -> match projectee with | Abs _0 -> _0 
let (uu___is_App : term' -> Prims.bool) =
  fun projectee  ->
    match projectee with | App _0 -> true | uu____1510 -> false
  
let (__proj__App__item___0 : term' -> (term * term * imp)) =
  fun projectee  -> match projectee with | App _0 -> _0 
let (uu___is_Let : term' -> Prims.bool) =
  fun projectee  ->
    match projectee with | Let _0 -> true | uu____1596 -> false
  
let (__proj__Let__item___0 :
  term' ->
    (let_qualifier * (term Prims.list FStar_Pervasives_Native.option *
      (pattern * term)) Prims.list * term))
  = fun projectee  -> match projectee with | Let _0 -> _0 
let (uu___is_LetOpen : term' -> Prims.bool) =
  fun projectee  ->
    match projectee with | LetOpen _0 -> true | uu____1719 -> false
  
let (__proj__LetOpen__item___0 : term' -> (FStar_Ident.lid * term)) =
  fun projectee  -> match projectee with | LetOpen _0 -> _0 
let (uu___is_Seq : term' -> Prims.bool) =
  fun projectee  ->
    match projectee with | Seq _0 -> true | uu____1781 -> false
  
let (__proj__Seq__item___0 : term' -> (term * term)) =
  fun projectee  -> match projectee with | Seq _0 -> _0 
let (uu___is_Bind : term' -> Prims.bool) =
  fun projectee  ->
    match projectee with | Bind _0 -> true | uu____1844 -> false
  
let (__proj__Bind__item___0 : term' -> (FStar_Ident.ident * term * term)) =
  fun projectee  -> match projectee with | Bind _0 -> _0 
let (uu___is_If : term' -> Prims.bool) =
  fun projectee  ->
    match projectee with | If _0 -> true | uu____1920 -> false
  
let (__proj__If__item___0 : term' -> (term * term * term)) =
  fun projectee  -> match projectee with | If _0 -> _0 
let (uu___is_Match : term' -> Prims.bool) =
  fun projectee  ->
    match projectee with | Match _0 -> true | uu____2009 -> false
  
let (__proj__Match__item___0 :
  term' ->
    (term * (pattern * term FStar_Pervasives_Native.option * term)
      Prims.list))
  = fun projectee  -> match projectee with | Match _0 -> _0 
let (uu___is_TryWith : term' -> Prims.bool) =
  fun projectee  ->
    match projectee with | TryWith _0 -> true | uu____2128 -> false
  
let (__proj__TryWith__item___0 :
  term' ->
    (term * (pattern * term FStar_Pervasives_Native.option * term)
      Prims.list))
  = fun projectee  -> match projectee with | TryWith _0 -> _0 
let (uu___is_Ascribed : term' -> Prims.bool) =
  fun projectee  ->
    match projectee with | Ascribed _0 -> true | uu____2239 -> false
  
let (__proj__Ascribed__item___0 :
  term' -> (term * term * term FStar_Pervasives_Native.option)) =
  fun projectee  -> match projectee with | Ascribed _0 -> _0 
let (uu___is_Record : term' -> Prims.bool) =
  fun projectee  ->
    match projectee with | Record _0 -> true | uu____2331 -> false
  
let (__proj__Record__item___0 :
  term' ->
    (term FStar_Pervasives_Native.option * (FStar_Ident.lid * term)
      Prims.list))
  = fun projectee  -> match projectee with | Record _0 -> _0 
let (uu___is_Project : term' -> Prims.bool) =
  fun projectee  ->
    match projectee with | Project _0 -> true | uu____2427 -> false
  
let (__proj__Project__item___0 : term' -> (term * FStar_Ident.lid)) =
  fun projectee  -> match projectee with | Project _0 -> _0 
let (uu___is_Product : term' -> Prims.bool) =
  fun projectee  ->
    match projectee with | Product _0 -> true | uu____2492 -> false
  
let (__proj__Product__item___0 : term' -> (binder Prims.list * term)) =
  fun projectee  -> match projectee with | Product _0 -> _0 
let (uu___is_Sum : term' -> Prims.bool) =
  fun projectee  ->
    match projectee with | Sum _0 -> true | uu____2570 -> false
  
let (__proj__Sum__item___0 :
  term' -> ((binder,term) FStar_Util.either Prims.list * term)) =
  fun projectee  -> match projectee with | Sum _0 -> _0 
let (uu___is_QForall : term' -> Prims.bool) =
  fun projectee  ->
    match projectee with | QForall _0 -> true | uu____2679 -> false
  
let (__proj__QForall__item___0 :
  term' ->
    (binder Prims.list * (FStar_Ident.ident Prims.list * term Prims.list
      Prims.list) * term))
  = fun projectee  -> match projectee with | QForall _0 -> _0 
let (uu___is_QExists : term' -> Prims.bool) =
  fun projectee  ->
    match projectee with | QExists _0 -> true | uu____2818 -> false
  
let (__proj__QExists__item___0 :
  term' ->
    (binder Prims.list * (FStar_Ident.ident Prims.list * term Prims.list
      Prims.list) * term))
  = fun projectee  -> match projectee with | QExists _0 -> _0 
let (uu___is_Refine : term' -> Prims.bool) =
  fun projectee  ->
    match projectee with | Refine _0 -> true | uu____2938 -> false
  
let (__proj__Refine__item___0 : term' -> (binder * term)) =
  fun projectee  -> match projectee with | Refine _0 -> _0 
let (uu___is_NamedTyp : term' -> Prims.bool) =
  fun projectee  ->
    match projectee with | NamedTyp _0 -> true | uu____2999 -> false
  
let (__proj__NamedTyp__item___0 : term' -> (FStar_Ident.ident * term)) =
  fun projectee  -> match projectee with | NamedTyp _0 -> _0 
let (uu___is_Paren : term' -> Prims.bool) =
  fun projectee  ->
    match projectee with | Paren _0 -> true | uu____3048 -> false
  
let (__proj__Paren__item___0 : term' -> term) =
  fun projectee  -> match projectee with | Paren _0 -> _0 
let (uu___is_Requires : term' -> Prims.bool) =
  fun projectee  ->
    match projectee with | Requires _0 -> true | uu____3092 -> false
  
let (__proj__Requires__item___0 :
  term' -> (term * Prims.string FStar_Pervasives_Native.option)) =
  fun projectee  -> match projectee with | Requires _0 -> _0 
let (uu___is_Ensures : term' -> Prims.bool) =
  fun projectee  ->
    match projectee with | Ensures _0 -> true | uu____3151 -> false
  
let (__proj__Ensures__item___0 :
  term' -> (term * Prims.string FStar_Pervasives_Native.option)) =
  fun projectee  -> match projectee with | Ensures _0 -> _0 
let (uu___is_Labeled : term' -> Prims.bool) =
  fun projectee  ->
    match projectee with | Labeled _0 -> true | uu____3211 -> false
  
let (__proj__Labeled__item___0 : term' -> (term * Prims.string * Prims.bool))
  = fun projectee  -> match projectee with | Labeled _0 -> _0 
let (uu___is_Discrim : term' -> Prims.bool) =
  fun projectee  ->
    match projectee with | Discrim _0 -> true | uu____3267 -> false
  
let (__proj__Discrim__item___0 : term' -> FStar_Ident.lid) =
  fun projectee  -> match projectee with | Discrim _0 -> _0 
let (uu___is_Attributes : term' -> Prims.bool) =
  fun projectee  ->
    match projectee with | Attributes _0 -> true | uu____3311 -> false
  
let (__proj__Attributes__item___0 : term' -> term Prims.list) =
  fun projectee  -> match projectee with | Attributes _0 -> _0 
let (uu___is_Antiquote : term' -> Prims.bool) =
  fun projectee  ->
    match projectee with | Antiquote _0 -> true | uu____3348 -> false
  
let (__proj__Antiquote__item___0 : term' -> term) =
  fun projectee  -> match projectee with | Antiquote _0 -> _0 
let (uu___is_Quote : term' -> Prims.bool) =
  fun projectee  ->
    match projectee with | Quote _0 -> true | uu____3389 -> false
  
let (__proj__Quote__item___0 : term' -> (term * quote_kind)) =
  fun projectee  -> match projectee with | Quote _0 -> _0 
let (uu___is_VQuote : term' -> Prims.bool) =
  fun projectee  ->
    match projectee with | VQuote _0 -> true | uu____3432 -> false
  
let (__proj__VQuote__item___0 : term' -> term) =
  fun projectee  -> match projectee with | VQuote _0 -> _0 
let (uu___is_CalcProof : term' -> Prims.bool) =
  fun projectee  ->
    match projectee with | CalcProof _0 -> true | uu____3481 -> false
  
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
    match projectee with | Variable _0 -> true | uu____3656 -> false
  
let (__proj__Variable__item___0 : binder' -> FStar_Ident.ident) =
  fun projectee  -> match projectee with | Variable _0 -> _0 
let (uu___is_TVariable : binder' -> Prims.bool) =
  fun projectee  ->
    match projectee with | TVariable _0 -> true | uu____3687 -> false
  
let (__proj__TVariable__item___0 : binder' -> FStar_Ident.ident) =
  fun projectee  -> match projectee with | TVariable _0 -> _0 
let (uu___is_Annotated : binder' -> Prims.bool) =
  fun projectee  ->
    match projectee with | Annotated _0 -> true | uu____3725 -> false
  
let (__proj__Annotated__item___0 : binder' -> (FStar_Ident.ident * term)) =
  fun projectee  -> match projectee with | Annotated _0 -> _0 
let (uu___is_TAnnotated : binder' -> Prims.bool) =
  fun projectee  ->
    match projectee with | TAnnotated _0 -> true | uu____3780 -> false
  
let (__proj__TAnnotated__item___0 : binder' -> (FStar_Ident.ident * term)) =
  fun projectee  -> match projectee with | TAnnotated _0 -> _0 
let (uu___is_NoName : binder' -> Prims.bool) =
  fun projectee  ->
    match projectee with | NoName _0 -> true | uu____3829 -> false
  
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
    match projectee with | PatWild _0 -> true | uu____3949 -> false
  
let (__proj__PatWild__item___0 :
  pattern' -> arg_qualifier FStar_Pervasives_Native.option) =
  fun projectee  -> match projectee with | PatWild _0 -> _0 
let (uu___is_PatConst : pattern' -> Prims.bool) =
  fun projectee  ->
    match projectee with | PatConst _0 -> true | uu____3974 -> false
  
let (__proj__PatConst__item___0 : pattern' -> FStar_Const.sconst) =
  fun projectee  -> match projectee with | PatConst _0 -> _0 
let (uu___is_PatApp : pattern' -> Prims.bool) =
  fun projectee  ->
    match projectee with | PatApp _0 -> true | uu____4003 -> false
  
let (__proj__PatApp__item___0 : pattern' -> (pattern * pattern Prims.list)) =
  fun projectee  -> match projectee with | PatApp _0 -> _0 
let (uu___is_PatVar : pattern' -> Prims.bool) =
  fun projectee  ->
    match projectee with | PatVar _0 -> true | uu____4060 -> false
  
let (__proj__PatVar__item___0 :
  pattern' ->
    (FStar_Ident.ident * arg_qualifier FStar_Pervasives_Native.option))
  = fun projectee  -> match projectee with | PatVar _0 -> _0 
let (uu___is_PatName : pattern' -> Prims.bool) =
  fun projectee  ->
    match projectee with | PatName _0 -> true | uu____4107 -> false
  
let (__proj__PatName__item___0 : pattern' -> FStar_Ident.lid) =
  fun projectee  -> match projectee with | PatName _0 -> _0 
let (uu___is_PatTvar : pattern' -> Prims.bool) =
  fun projectee  ->
    match projectee with | PatTvar _0 -> true | uu____4154 -> false
  
let (__proj__PatTvar__item___0 :
  pattern' ->
    (FStar_Ident.ident * arg_qualifier FStar_Pervasives_Native.option))
  = fun projectee  -> match projectee with | PatTvar _0 -> _0 
let (uu___is_PatList : pattern' -> Prims.bool) =
  fun projectee  ->
    match projectee with | PatList _0 -> true | uu____4201 -> false
  
let (__proj__PatList__item___0 : pattern' -> pattern Prims.list) =
  fun projectee  -> match projectee with | PatList _0 -> _0 
let (uu___is_PatTuple : pattern' -> Prims.bool) =
  fun projectee  ->
    match projectee with | PatTuple _0 -> true | uu____4241 -> false
  
let (__proj__PatTuple__item___0 :
  pattern' -> (pattern Prims.list * Prims.bool)) =
  fun projectee  -> match projectee with | PatTuple _0 -> _0 
let (uu___is_PatRecord : pattern' -> Prims.bool) =
  fun projectee  ->
    match projectee with | PatRecord _0 -> true | uu____4299 -> false
  
let (__proj__PatRecord__item___0 :
  pattern' -> (FStar_Ident.lid * pattern) Prims.list) =
  fun projectee  -> match projectee with | PatRecord _0 -> _0 
let (uu___is_PatAscribed : pattern' -> Prims.bool) =
  fun projectee  ->
    match projectee with | PatAscribed _0 -> true | uu____4372 -> false
  
let (__proj__PatAscribed__item___0 :
  pattern' -> (pattern * (term * term FStar_Pervasives_Native.option))) =
  fun projectee  -> match projectee with | PatAscribed _0 -> _0 
let (uu___is_PatOr : pattern' -> Prims.bool) =
  fun projectee  ->
    match projectee with | PatOr _0 -> true | uu____4449 -> false
  
let (__proj__PatOr__item___0 : pattern' -> pattern Prims.list) =
  fun projectee  -> match projectee with | PatOr _0 -> _0 
let (uu___is_PatOp : pattern' -> Prims.bool) =
  fun projectee  ->
    match projectee with | PatOp _0 -> true | uu____4482 -> false
  
let (__proj__PatOp__item___0 : pattern' -> FStar_Ident.ident) =
  fun projectee  -> match projectee with | PatOp _0 -> _0 
let (__proj__Mkpattern__item__pat : pattern -> pattern') =
  fun projectee  -> match projectee with | { pat; prange;_} -> pat 
let (__proj__Mkpattern__item__prange : pattern -> FStar_Range.range) =
  fun projectee  -> match projectee with | { pat; prange;_} -> prange 
let (uu___is_Implicit : arg_qualifier -> Prims.bool) =
  fun projectee  ->
    match projectee with | Implicit  -> true | uu____4534 -> false
  
let (uu___is_Equality : arg_qualifier -> Prims.bool) =
  fun projectee  ->
    match projectee with | Equality  -> true | uu____4545 -> false
  
let (uu___is_Meta : arg_qualifier -> Prims.bool) =
  fun projectee  ->
    match projectee with | Meta _0 -> true | uu____4560 -> false
  
let (__proj__Meta__item___0 : arg_qualifier -> term) =
  fun projectee  -> match projectee with | Meta _0 -> _0 
let (uu___is_FsTypApp : imp -> Prims.bool) =
  fun projectee  ->
    match projectee with | FsTypApp  -> true | uu____4593 -> false
  
let (uu___is_Hash : imp -> Prims.bool) =
  fun projectee  ->
    match projectee with | Hash  -> true | uu____4604 -> false
  
let (uu___is_UnivApp : imp -> Prims.bool) =
  fun projectee  ->
    match projectee with | UnivApp  -> true | uu____4615 -> false
  
let (uu___is_HashBrace : imp -> Prims.bool) =
  fun projectee  ->
    match projectee with | HashBrace _0 -> true | uu____4630 -> false
  
let (__proj__HashBrace__item___0 : imp -> term) =
  fun projectee  -> match projectee with | HashBrace _0 -> _0 
let (uu___is_Infix : imp -> Prims.bool) =
  fun projectee  ->
    match projectee with | Infix  -> true | uu____4663 -> false
  
let (uu___is_Nothing : imp -> Prims.bool) =
  fun projectee  ->
    match projectee with | Nothing  -> true | uu____4674 -> false
  
type patterns = (FStar_Ident.ident Prims.list * term Prims.list Prims.list)
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
    match projectee with | TyconAbstract _0 -> true | uu____4905 -> false
  
let (__proj__TyconAbstract__item___0 :
  tycon ->
    (FStar_Ident.ident * binder Prims.list * knd
      FStar_Pervasives_Native.option))
  = fun projectee  -> match projectee with | TyconAbstract _0 -> _0 
let (uu___is_TyconAbbrev : tycon -> Prims.bool) =
  fun projectee  ->
    match projectee with | TyconAbbrev _0 -> true | uu____5005 -> false
  
let (__proj__TyconAbbrev__item___0 :
  tycon ->
    (FStar_Ident.ident * binder Prims.list * knd
      FStar_Pervasives_Native.option * term))
  = fun projectee  -> match projectee with | TyconAbbrev _0 -> _0 
let (uu___is_TyconRecord : tycon -> Prims.bool) =
  fun projectee  ->
    match projectee with | TyconRecord _0 -> true | uu____5132 -> false
  
let (__proj__TyconRecord__item___0 :
  tycon ->
    (FStar_Ident.ident * binder Prims.list * knd
      FStar_Pervasives_Native.option * (FStar_Ident.ident * term * fsdoc
      FStar_Pervasives_Native.option) Prims.list))
  = fun projectee  -> match projectee with | TyconRecord _0 -> _0 
let (uu___is_TyconVariant : tycon -> Prims.bool) =
  fun projectee  ->
    match projectee with | TyconVariant _0 -> true | uu____5300 -> false
  
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
    match projectee with | Private  -> true | uu____5441 -> false
  
let (uu___is_Abstract : qualifier -> Prims.bool) =
  fun projectee  ->
    match projectee with | Abstract  -> true | uu____5452 -> false
  
let (uu___is_Noeq : qualifier -> Prims.bool) =
  fun projectee  ->
    match projectee with | Noeq  -> true | uu____5463 -> false
  
let (uu___is_Unopteq : qualifier -> Prims.bool) =
  fun projectee  ->
    match projectee with | Unopteq  -> true | uu____5474 -> false
  
let (uu___is_Assumption : qualifier -> Prims.bool) =
  fun projectee  ->
    match projectee with | Assumption  -> true | uu____5485 -> false
  
let (uu___is_DefaultEffect : qualifier -> Prims.bool) =
  fun projectee  ->
    match projectee with | DefaultEffect  -> true | uu____5496 -> false
  
let (uu___is_TotalEffect : qualifier -> Prims.bool) =
  fun projectee  ->
    match projectee with | TotalEffect  -> true | uu____5507 -> false
  
let (uu___is_Effect_qual : qualifier -> Prims.bool) =
  fun projectee  ->
    match projectee with | Effect_qual  -> true | uu____5518 -> false
  
let (uu___is_New : qualifier -> Prims.bool) =
  fun projectee  -> match projectee with | New  -> true | uu____5529 -> false 
let (uu___is_Inline : qualifier -> Prims.bool) =
  fun projectee  ->
    match projectee with | Inline  -> true | uu____5540 -> false
  
let (uu___is_Visible : qualifier -> Prims.bool) =
  fun projectee  ->
    match projectee with | Visible  -> true | uu____5551 -> false
  
let (uu___is_Unfold_for_unification_and_vcgen : qualifier -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | Unfold_for_unification_and_vcgen  -> true
    | uu____5562 -> false
  
let (uu___is_Inline_for_extraction : qualifier -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | Inline_for_extraction  -> true
    | uu____5573 -> false
  
let (uu___is_Irreducible : qualifier -> Prims.bool) =
  fun projectee  ->
    match projectee with | Irreducible  -> true | uu____5584 -> false
  
let (uu___is_NoExtract : qualifier -> Prims.bool) =
  fun projectee  ->
    match projectee with | NoExtract  -> true | uu____5595 -> false
  
let (uu___is_Reifiable : qualifier -> Prims.bool) =
  fun projectee  ->
    match projectee with | Reifiable  -> true | uu____5606 -> false
  
let (uu___is_Reflectable : qualifier -> Prims.bool) =
  fun projectee  ->
    match projectee with | Reflectable  -> true | uu____5617 -> false
  
let (uu___is_Opaque : qualifier -> Prims.bool) =
  fun projectee  ->
    match projectee with | Opaque  -> true | uu____5628 -> false
  
let (uu___is_Logic : qualifier -> Prims.bool) =
  fun projectee  ->
    match projectee with | Logic  -> true | uu____5639 -> false
  
type qualifiers = qualifier Prims.list
type decoration =
  | Qualifier of qualifier 
  | DeclAttributes of term Prims.list 
  | Doc of fsdoc 
let (uu___is_Qualifier : decoration -> Prims.bool) =
  fun projectee  ->
    match projectee with | Qualifier _0 -> true | uu____5673 -> false
  
let (__proj__Qualifier__item___0 : decoration -> qualifier) =
  fun projectee  -> match projectee with | Qualifier _0 -> _0 
let (uu___is_DeclAttributes : decoration -> Prims.bool) =
  fun projectee  ->
    match projectee with | DeclAttributes _0 -> true | uu____5697 -> false
  
let (__proj__DeclAttributes__item___0 : decoration -> term Prims.list) =
  fun projectee  -> match projectee with | DeclAttributes _0 -> _0 
let (uu___is_Doc : decoration -> Prims.bool) =
  fun projectee  ->
    match projectee with | Doc _0 -> true | uu____5731 -> false
  
let (__proj__Doc__item___0 : decoration -> fsdoc) =
  fun projectee  -> match projectee with | Doc _0 -> _0 
type lift_op =
  | NonReifiableLift of term 
  | ReifiableLift of (term * term) 
  | LiftForFree of term 
let (uu___is_NonReifiableLift : lift_op -> Prims.bool) =
  fun projectee  ->
    match projectee with | NonReifiableLift _0 -> true | uu____5784 -> false
  
let (__proj__NonReifiableLift__item___0 : lift_op -> term) =
  fun projectee  -> match projectee with | NonReifiableLift _0 -> _0 
let (uu___is_ReifiableLift : lift_op -> Prims.bool) =
  fun projectee  ->
    match projectee with | ReifiableLift _0 -> true | uu____5828 -> false
  
let (__proj__ReifiableLift__item___0 : lift_op -> (term * term)) =
  fun projectee  -> match projectee with | ReifiableLift _0 -> _0 
let (uu___is_LiftForFree : lift_op -> Prims.bool) =
  fun projectee  ->
    match projectee with | LiftForFree _0 -> true | uu____5880 -> false
  
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
    match projectee with | SetOptions _0 -> true | uu____6106 -> false
  
let (__proj__SetOptions__item___0 : pragma -> Prims.string) =
  fun projectee  -> match projectee with | SetOptions _0 -> _0 
let (uu___is_ResetOptions : pragma -> Prims.bool) =
  fun projectee  ->
    match projectee with | ResetOptions _0 -> true | uu____6131 -> false
  
let (__proj__ResetOptions__item___0 :
  pragma -> Prims.string FStar_Pervasives_Native.option) =
  fun projectee  -> match projectee with | ResetOptions _0 -> _0 
let (uu___is_PushOptions : pragma -> Prims.bool) =
  fun projectee  ->
    match projectee with | PushOptions _0 -> true | uu____6162 -> false
  
let (__proj__PushOptions__item___0 :
  pragma -> Prims.string FStar_Pervasives_Native.option) =
  fun projectee  -> match projectee with | PushOptions _0 -> _0 
let (uu___is_PopOptions : pragma -> Prims.bool) =
  fun projectee  ->
    match projectee with | PopOptions  -> true | uu____6189 -> false
  
let (uu___is_LightOff : pragma -> Prims.bool) =
  fun projectee  ->
    match projectee with | LightOff  -> true | uu____6200 -> false
  
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
    match projectee with | TopLevelModule _0 -> true | uu____6498 -> false
  
let (__proj__TopLevelModule__item___0 : decl' -> FStar_Ident.lid) =
  fun projectee  -> match projectee with | TopLevelModule _0 -> _0 
let (uu___is_Open : decl' -> Prims.bool) =
  fun projectee  ->
    match projectee with | Open _0 -> true | uu____6541 -> false
  
let (__proj__Open__item___0 : decl' -> FStar_Ident.lid) =
  fun projectee  -> match projectee with | Open _0 -> _0 
let (uu___is_Friend : decl' -> Prims.bool) =
  fun projectee  ->
    match projectee with | Friend _0 -> true | uu____6584 -> false
  
let (__proj__Friend__item___0 : decl' -> FStar_Ident.lid) =
  fun projectee  -> match projectee with | Friend _0 -> _0 
let (uu___is_Include : decl' -> Prims.bool) =
  fun projectee  ->
    match projectee with | Include _0 -> true | uu____6627 -> false
  
let (__proj__Include__item___0 : decl' -> FStar_Ident.lid) =
  fun projectee  -> match projectee with | Include _0 -> _0 
let (uu___is_ModuleAbbrev : decl' -> Prims.bool) =
  fun projectee  ->
    match projectee with | ModuleAbbrev _0 -> true | uu____6676 -> false
  
let (__proj__ModuleAbbrev__item___0 :
  decl' -> (FStar_Ident.ident * FStar_Ident.lid)) =
  fun projectee  -> match projectee with | ModuleAbbrev _0 -> _0 
let (uu___is_TopLevelLet : decl' -> Prims.bool) =
  fun projectee  ->
    match projectee with | TopLevelLet _0 -> true | uu____6740 -> false
  
let (__proj__TopLevelLet__item___0 :
  decl' -> (let_qualifier * (pattern * term) Prims.list)) =
  fun projectee  -> match projectee with | TopLevelLet _0 -> _0 
let (uu___is_Main : decl' -> Prims.bool) =
  fun projectee  ->
    match projectee with | Main _0 -> true | uu____6807 -> false
  
let (__proj__Main__item___0 : decl' -> term) =
  fun projectee  -> match projectee with | Main _0 -> _0 
let (uu___is_Tycon : decl' -> Prims.bool) =
  fun projectee  ->
    match projectee with | Tycon _0 -> true | uu____6857 -> false
  
let (__proj__Tycon__item___0 :
  decl' ->
    (Prims.bool * Prims.bool * (tycon * fsdoc FStar_Pervasives_Native.option)
      Prims.list))
  = fun projectee  -> match projectee with | Tycon _0 -> _0 
let (uu___is_Val : decl' -> Prims.bool) =
  fun projectee  ->
    match projectee with | Val _0 -> true | uu____6933 -> false
  
let (__proj__Val__item___0 : decl' -> (FStar_Ident.ident * term)) =
  fun projectee  -> match projectee with | Val _0 -> _0 
let (uu___is_Exception : decl' -> Prims.bool) =
  fun projectee  ->
    match projectee with | Exception _0 -> true | uu____6990 -> false
  
let (__proj__Exception__item___0 :
  decl' -> (FStar_Ident.ident * term FStar_Pervasives_Native.option)) =
  fun projectee  -> match projectee with | Exception _0 -> _0 
let (uu___is_NewEffect : decl' -> Prims.bool) =
  fun projectee  ->
    match projectee with | NewEffect _0 -> true | uu____7042 -> false
  
let (__proj__NewEffect__item___0 : decl' -> effect_decl) =
  fun projectee  -> match projectee with | NewEffect _0 -> _0 
let (uu___is_SubEffect : decl' -> Prims.bool) =
  fun projectee  ->
    match projectee with | SubEffect _0 -> true | uu____7068 -> false
  
let (__proj__SubEffect__item___0 : decl' -> lift) =
  fun projectee  -> match projectee with | SubEffect _0 -> _0 
let (uu___is_Pragma : decl' -> Prims.bool) =
  fun projectee  ->
    match projectee with | Pragma _0 -> true | uu____7122 -> false
  
let (__proj__Pragma__item___0 : decl' -> pragma) =
  fun projectee  -> match projectee with | Pragma _0 -> _0 
let (uu___is_Fsdoc : decl' -> Prims.bool) =
  fun projectee  ->
    match projectee with | Fsdoc _0 -> true | uu____7141 -> false
  
let (__proj__Fsdoc__item___0 : decl' -> fsdoc) =
  fun projectee  -> match projectee with | Fsdoc _0 -> _0 
let (uu___is_Assume : decl' -> Prims.bool) =
  fun projectee  ->
    match projectee with | Assume _0 -> true | uu____7169 -> false
  
let (__proj__Assume__item___0 : decl' -> (FStar_Ident.ident * term)) =
  fun projectee  -> match projectee with | Assume _0 -> _0 
let (uu___is_Splice : decl' -> Prims.bool) =
  fun projectee  ->
    match projectee with | Splice _0 -> true | uu____7226 -> false
  
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
    match projectee with | DefineEffect _0 -> true | uu____7423 -> false
  
let (__proj__DefineEffect__item___0 :
  effect_decl ->
    (FStar_Ident.ident * binder Prims.list * term * decl Prims.list))
  = fun projectee  -> match projectee with | DefineEffect _0 -> _0 
let (uu___is_RedefineEffect : effect_decl -> Prims.bool) =
  fun projectee  ->
    match projectee with | RedefineEffect _0 -> true | uu____7537 -> false
  
let (__proj__RedefineEffect__item___0 :
  effect_decl -> (FStar_Ident.ident * binder Prims.list * term)) =
  fun projectee  -> match projectee with | RedefineEffect _0 -> _0 
type modul =
  | Module of (FStar_Ident.lid * decl Prims.list) 
  | Interface of (FStar_Ident.lid * decl Prims.list * Prims.bool) 
let (uu___is_Module : modul -> Prims.bool) =
  fun projectee  ->
    match projectee with | Module _0 -> true | uu____7665 -> false
  
let (__proj__Module__item___0 : modul -> (FStar_Ident.lid * decl Prims.list))
  = fun projectee  -> match projectee with | Module _0 -> _0 
let (uu___is_Interface : modul -> Prims.bool) =
  fun projectee  ->
    match projectee with | Interface _0 -> true | uu____7747 -> false
  
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
      (let uu____7855 =
         let uu____7861 =
           FStar_Util.format1
             "Invalid identifer '%s'; expected a symbol that begins with a lower-case character"
             id1.FStar_Ident.idText
            in
         (FStar_Errors.Fatal_InvalidIdentifier, uu____7861)  in
       FStar_Errors.raise_error uu____7855 id1.FStar_Ident.idRange)
  
let at_most_one :
  'Auu____7874 .
    Prims.string ->
      FStar_Range.range ->
        'Auu____7874 Prims.list ->
          'Auu____7874 FStar_Pervasives_Native.option
  =
  fun s  ->
    fun r  ->
      fun l  ->
        match l with
        | x::[] -> FStar_Pervasives_Native.Some x
        | [] -> FStar_Pervasives_Native.None
        | uu____7899 ->
            let uu____7902 =
              let uu____7908 =
                FStar_Util.format1
                  "At most one %s is allowed on declarations" s
                 in
              (FStar_Errors.Fatal_MoreThanOneDeclaration, uu____7908)  in
            FStar_Errors.raise_error uu____7902 r
  
let (mk_decl : decl' -> FStar_Range.range -> decoration Prims.list -> decl) =
  fun d  ->
    fun r  ->
      fun decorations  ->
        let doc1 =
          let uu____7942 =
            FStar_List.choose
              (fun uu___0_7947  ->
                 match uu___0_7947 with
                 | Doc d1 -> FStar_Pervasives_Native.Some d1
                 | uu____7951 -> FStar_Pervasives_Native.None) decorations
             in
          at_most_one "fsdoc" r uu____7942  in
        let attributes_ =
          let uu____7961 =
            FStar_List.choose
              (fun uu___1_7976  ->
                 match uu___1_7976 with
                 | DeclAttributes a -> FStar_Pervasives_Native.Some a
                 | uu____7995 -> FStar_Pervasives_Native.None) decorations
             in
          at_most_one "attribute set" r uu____7961  in
        let attributes_1 = FStar_Util.dflt [] attributes_  in
        let qualifiers =
          FStar_List.choose
            (fun uu___2_8026  ->
               match uu___2_8026 with
               | Qualifier q -> FStar_Pervasives_Native.Some q
               | uu____8030 -> FStar_Pervasives_Native.None) decorations
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
            | uu____8150 ->
                let uu____8151 =
                  let uu____8163 = FStar_Ident.mk_ident ("-", rminus)  in
                  (uu____8163, [t])  in
                Op uu____8151
             in
          mk_term t1 r l
  
let (mk_pattern : pattern' -> FStar_Range.range -> pattern) =
  fun p  -> fun r  -> { pat = p; prange = r } 
let (un_curry_abs : pattern Prims.list -> term -> term') =
  fun ps  ->
    fun body  ->
      match body.tm with
      | Abs (p',body') -> Abs ((FStar_List.append ps p'), body')
      | uu____8250 -> Abs (ps, body)
  
let (mk_function :
  (pattern * term FStar_Pervasives_Native.option * term) Prims.list ->
    FStar_Range.range -> FStar_Range.range -> term)
  =
  fun branches  ->
    fun r1  ->
      fun r2  ->
        let x = FStar_Ident.gen r1  in
        let uu____8318 =
          let uu____8319 =
            let uu____8331 =
              let uu____8338 =
                let uu____8339 =
                  let uu____8365 =
                    let uu____8372 =
                      let uu____8373 = FStar_Ident.lid_of_ids [x]  in
                      Var uu____8373  in
                    mk_term uu____8372 r1 Expr  in
                  (uu____8365, branches)  in
                Match uu____8339  in
              mk_term uu____8338 r2 Expr  in
            ([mk_pattern (PatVar (x, FStar_Pervasives_Native.None)) r1],
              uu____8331)
             in
          Abs uu____8319  in
        mk_term uu____8318 r2 Expr
  
let (un_function :
  pattern -> term -> (pattern * term) FStar_Pervasives_Native.option) =
  fun p  ->
    fun tm  ->
      match ((p.pat), (tm.tm)) with
      | (PatVar uu____8465,Abs (pats,body)) ->
          FStar_Pervasives_Native.Some
            ((mk_pattern (PatApp (p, pats)) p.prange), body)
      | uu____8510 -> FStar_Pervasives_Native.None
  
let (lid_with_range :
  FStar_Ident.lident -> FStar_Range.range -> FStar_Ident.lident) =
  fun lid  ->
    fun r  ->
      let uu____8547 = FStar_Ident.path_of_lid lid  in
      FStar_Ident.lid_of_path uu____8547 r
  
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
        | uu____9007 ->
            (match t.tm with
             | Name s -> mk_term (Construct (s, args)) r Un
             | uu____9038 ->
                 FStar_List.fold_left
                   (fun t1  ->
                      fun uu____9054  ->
                        match uu____9054 with
                        | (a,imp) -> mk_term (App (t1, a, imp)) r Un) t args)
  
let (mkRefSet : FStar_Range.range -> term Prims.list -> term) =
  fun r  ->
    fun elts  ->
      let uu____9106 =
        (FStar_Parser_Const.set_empty, FStar_Parser_Const.set_singleton,
          FStar_Parser_Const.set_union, FStar_Parser_Const.heap_addr_of_lid)
         in
      match uu____9106 with
      | (empty_lid,singleton_lid,union_lid,addr_of_lid) ->
          let empty1 =
            let uu____9193 =
              let uu____9194 = FStar_Ident.set_lid_range empty_lid r  in
              Var uu____9194  in
            mk_term uu____9193 r Expr  in
          let addr_of =
            let uu____9210 =
              let uu____9211 = FStar_Ident.set_lid_range addr_of_lid r  in
              Var uu____9211  in
            mk_term uu____9210 r Expr  in
          let singleton1 =
            let uu____9227 =
              let uu____9228 = FStar_Ident.set_lid_range singleton_lid r  in
              Var uu____9228  in
            mk_term uu____9227 r Expr  in
          let union1 =
            let uu____9244 =
              let uu____9245 = FStar_Ident.set_lid_range union_lid r  in
              Var uu____9245  in
            mk_term uu____9244 r Expr  in
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
        | uu____9388 ->
            (match t.tm with
             | Name s ->
                 let uu____9402 =
                   let uu____9403 =
                     let uu____9421 =
                       FStar_List.map (fun a  -> (a, Nothing)) args  in
                     (s, uu____9421)  in
                   Construct uu____9403  in
                 mk_term uu____9402 r Un
             | uu____9462 ->
                 FStar_List.fold_left
                   (fun t1  -> fun a  -> mk_term (App (t1, a, Nothing)) r Un)
                   t args)
  
let (unit_const : FStar_Range.range -> term) =
  fun r  -> mk_term (Const FStar_Const.Const_unit) r Expr 
let (mkAdmitMagic : FStar_Range.range -> term) =
  fun r  ->
    let admit1 =
      let admit_name =
        let uu____9523 =
          let uu____9524 =
            FStar_Ident.set_lid_range FStar_Parser_Const.admit_lid r  in
          Var uu____9524  in
        mk_term uu____9523 r Expr  in
      mkExplicitApp admit_name [unit_const r] r  in
    let magic1 =
      let magic_name =
        let uu____9553 =
          let uu____9554 =
            FStar_Ident.set_lid_range FStar_Parser_Const.magic_lid r  in
          Var uu____9554  in
        mk_term uu____9553 r Expr  in
      mkExplicitApp magic_name [unit_const r] r  in
    let admit_magic = mk_term (Seq (admit1, magic1)) r Expr  in admit_magic
  
let mkWildAdmitMagic :
  'Auu____9587 .
    FStar_Range.range ->
      (pattern * 'Auu____9587 FStar_Pervasives_Native.option * term)
  =
  fun r  ->
    let uu____9606 = mkAdmitMagic r  in
    ((mk_pattern (PatWild FStar_Pervasives_Native.None) r),
      FStar_Pervasives_Native.None, uu____9606)
  
let focusBranches :
  'Auu____9627 .
    (Prims.bool * (pattern * 'Auu____9627 FStar_Pervasives_Native.option *
      term)) Prims.list ->
      FStar_Range.range ->
        (pattern * 'Auu____9627 FStar_Pervasives_Native.option * term)
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
            let uu____9762 =
              FStar_List.filter FStar_Pervasives_Native.fst branches  in
            FStar_All.pipe_right uu____9762
              (FStar_List.map FStar_Pervasives_Native.snd)
             in
          let uu____9895 =
            let uu____9911 = mkWildAdmitMagic r  in [uu____9911]  in
          FStar_List.append focussed uu____9895))
      else
        FStar_All.pipe_right branches
          (FStar_List.map FStar_Pervasives_Native.snd)
  
let focusLetBindings :
  'Auu____10053 .
    (Prims.bool * ('Auu____10053 * term)) Prims.list ->
      FStar_Range.range -> ('Auu____10053 * term) Prims.list
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
           (fun uu____10158  ->
              match uu____10158 with
              | (f,lb) ->
                  if f
                  then lb
                  else
                    (let uu____10206 = mkAdmitMagic r  in
                     ((FStar_Pervasives_Native.fst lb), uu____10206))) lbs)
      else
        FStar_All.pipe_right lbs (FStar_List.map FStar_Pervasives_Native.snd)
  
let focusAttrLetBindings :
  'Auu____10280 'Auu____10281 .
    ('Auu____10280 * (Prims.bool * ('Auu____10281 * term))) Prims.list ->
      FStar_Range.range ->
        ('Auu____10280 * ('Auu____10281 * term)) Prims.list
  =
  fun lbs  ->
    fun r  ->
      let should_filter =
        FStar_Util.for_some
          (fun uu____10363  ->
             match uu____10363 with | (attr,(focus,uu____10383)) -> focus)
          lbs
         in
      if should_filter
      then
        (FStar_Errors.log_issue r
           (FStar_Errors.Warning_Filtered,
             "Focusing on only some cases in this (mutually) recursive definition");
         FStar_List.map
           (fun uu____10460  ->
              match uu____10460 with
              | (attr,(f,lb)) ->
                  if f
                  then (attr, lb)
                  else
                    (let uu____10540 =
                       let uu____10548 = mkAdmitMagic r  in
                       ((FStar_Pervasives_Native.fst lb), uu____10548)  in
                     (attr, uu____10540))) lbs)
      else
        FStar_All.pipe_right lbs
          (FStar_List.map
             (fun uu____10632  ->
                match uu____10632 with
                | (attr,(uu____10661,lb)) -> (attr, lb)))
  
let (mkFsTypApp : term -> term Prims.list -> FStar_Range.range -> term) =
  fun t  ->
    fun args  ->
      fun r  ->
        let uu____10733 = FStar_List.map (fun a  -> (a, FsTypApp)) args  in
        mkApp t uu____10733 r
  
let (mkTuple : term Prims.list -> FStar_Range.range -> term) =
  fun args  ->
    fun r  ->
      let cons1 =
        FStar_Parser_Const.mk_tuple_data_lid (FStar_List.length args) r  in
      let uu____10797 = FStar_List.map (fun x  -> (x, Nothing)) args  in
      mkApp (mk_term (Name cons1) r Expr) uu____10797 r
  
let (mkDTuple : term Prims.list -> FStar_Range.range -> term) =
  fun args  ->
    fun r  ->
      let cons1 =
        FStar_Parser_Const.mk_dtuple_data_lid (FStar_List.length args) r  in
      let uu____10861 = FStar_List.map (fun x  -> (x, Nothing)) args  in
      mkApp (mk_term (Name cons1) r Expr) uu____10861 r
  
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
                       | PatVar (x,uu____11111) ->
                           mk_term
                             (Refine
                                ((mk_binder (Annotated (x, t)) t_range
                                    Type_level FStar_Pervasives_Native.None),
                                  phi)) range Type_level
                       | uu____11132 ->
                           let x = FStar_Ident.gen t_range  in
                           let phi1 =
                             let x_var =
                               let uu____11152 =
                                 let uu____11153 = FStar_Ident.lid_of_ids [x]
                                    in
                                 Var uu____11153  in
                               mk_term uu____11152 phi.range Formula  in
                             let pat_branch =
                               (pat, FStar_Pervasives_Native.None, phi)  in
                             let otherwise_branch =
                               let uu____11213 =
                                 let uu____11220 =
                                   let uu____11221 =
                                     FStar_Ident.lid_of_path ["False"]
                                       phi.range
                                      in
                                   Name uu____11221  in
                                 mk_term uu____11220 phi.range Formula  in
                               ((mk_pattern
                                   (PatWild FStar_Pervasives_Native.None)
                                   phi.range), FStar_Pervasives_Native.None,
                                 uu____11213)
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
        ({ b = Annotated (x,t); brange = uu____11462; blevel = uu____11463;
           aqual = uu____11464;_},t')
        ->
        FStar_Pervasives_Native.Some
          (x, t, (FStar_Pervasives_Native.Some t'))
    | Paren t -> extract_named_refinement t
    | uu____11521 -> FStar_Pervasives_Native.None
  
let rec (as_mlist :
  ((FStar_Ident.lid * decl) * decl Prims.list) -> decl Prims.list -> modul) =
  fun cur  ->
    fun ds  ->
      let uu____11611 = cur  in
      match uu____11611 with
      | ((m_name,m_decl),cur1) ->
          (match ds with
           | [] -> Module (m_name, (m_decl :: (FStar_List.rev cur1)))
           | d::ds1 ->
               (match d.d with
                | TopLevelModule m' ->
                    FStar_Errors.raise_error
                      (FStar_Errors.Fatal_UnexpectedModuleDeclaration,
                        "Unexpected module declaration") d.drange
                | uu____11736 -> as_mlist ((m_name, m_decl), (d :: cur1)) ds1))
  
let (as_frag :
  Prims.bool -> FStar_Range.range -> decl Prims.list -> inputFragment) =
  fun is_light  ->
    fun light_range  ->
      fun ds  ->
        let uu____11803 =
          match ds with
          | d::ds1 -> (d, ds1)
          | [] -> FStar_Exn.raise FStar_Errors.Empty_frag  in
        match uu____11803 with
        | (d,ds1) ->
            (match d.d with
             | TopLevelModule m ->
                 let ds2 =
                   if is_light
                   then
                     let uu____11935 =
                       mk_decl (Pragma LightOff) light_range []  in
                     uu____11935 :: ds1
                   else ds1  in
                 let m1 = as_mlist ((m, d), []) ds2  in FStar_Util.Inl m1
             | uu____11995 ->
                 let ds2 = d :: ds1  in
                 (FStar_List.iter
                    (fun uu___3_12021  ->
                       match uu___3_12021 with
                       | { d = TopLevelModule uu____12027; drange = r;
                           doc = uu____12029; quals = uu____12030;
                           attrs = uu____12031;_} ->
                           FStar_Errors.raise_error
                             (FStar_Errors.Fatal_UnexpectedModuleDeclaration,
                               "Unexpected module declaration") r
                       | uu____12040 -> ()) ds2;
                  FStar_Util.Inr ds2))
  
let (compile_op :
  Prims.int -> Prims.string -> FStar_Range.range -> Prims.string) =
  fun arity  ->
    fun s  ->
      fun r  ->
        let name_of_char uu___4_12081 =
          match uu___4_12081 with
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
        | uu____12151 ->
            let uu____12153 =
              let uu____12155 =
                let uu____12159 = FStar_String.list_of_string s  in
                FStar_List.map name_of_char uu____12159  in
              FStar_String.concat "_" uu____12155  in
            Prims.op_Hat "op_" uu____12153
  
let (compile_op' : Prims.string -> FStar_Range.range -> Prims.string) =
  fun s  -> fun r  -> compile_op (~- (Prims.parse_int "1")) s r 
let (string_of_fsdoc :
  (Prims.string * (Prims.string * Prims.string) Prims.list) -> Prims.string)
  =
  fun uu____12201  ->
    match uu____12201 with
    | (comment,keywords) ->
        let uu____12236 =
          let uu____12238 =
            FStar_List.map
              (fun uu____12252  ->
                 match uu____12252 with
                 | (k,v1) -> Prims.op_Hat k (Prims.op_Hat "->" v1)) keywords
             in
          FStar_String.concat "," uu____12238  in
        Prims.op_Hat comment uu____12236
  
let (string_of_let_qualifier : let_qualifier -> Prims.string) =
  fun uu___5_12274  ->
    match uu___5_12274 with | NoLetQualifier  -> "" | Rec  -> "rec"
  
let to_string_l :
  'Auu____12287 .
    Prims.string ->
      ('Auu____12287 -> Prims.string) ->
        'Auu____12287 Prims.list -> Prims.string
  =
  fun sep  ->
    fun f  ->
      fun l  ->
        let uu____12317 = FStar_List.map f l  in
        FStar_String.concat sep uu____12317
  
let (imp_to_string : imp -> Prims.string) =
  fun uu___6_12328  ->
    match uu___6_12328 with | Hash  -> "#" | uu____12331 -> ""
  
let rec (term_to_string : term -> Prims.string) =
  fun x  ->
    match x.tm with
    | Wild  -> "_"
    | Requires (t,uu____12390) ->
        let uu____12403 = term_to_string t  in
        FStar_Util.format1 "(requires %s)" uu____12403
    | Ensures (t,uu____12407) ->
        let uu____12420 = term_to_string t  in
        FStar_Util.format1 "(ensures %s)" uu____12420
    | Labeled (t,l,uu____12425) ->
        let uu____12436 = term_to_string t  in
        FStar_Util.format2 "(labeled %s %s)" l uu____12436
    | Const c -> FStar_Parser_Const.const_to_string c
    | Op (s,xs) ->
        let uu____12456 = FStar_Ident.text_of_id s  in
        let uu____12458 =
          let uu____12460 =
            FStar_List.map
              (fun x1  -> FStar_All.pipe_right x1 term_to_string) xs
             in
          FStar_String.concat ", " uu____12460  in
        FStar_Util.format2 "%s(%s)" uu____12456 uu____12458
    | Tvar id1 -> id1.FStar_Ident.idText
    | Uvar id1 -> id1.FStar_Ident.idText
    | Var l -> l.FStar_Ident.str
    | Name l -> l.FStar_Ident.str
    | Projector (rec_lid,field_id) ->
        let uu____12509 = FStar_Ident.string_of_lid rec_lid  in
        FStar_Util.format2 "%s?.%s" uu____12509 field_id.FStar_Ident.idText
    | Construct (l,args) ->
        let uu____12540 =
          to_string_l " "
            (fun uu____12554  ->
               match uu____12554 with
               | (a,imp) ->
                   let uu____12571 = term_to_string a  in
                   FStar_Util.format2 "%s%s" (imp_to_string imp) uu____12571)
            args
           in
        FStar_Util.format2 "(%s %s)" l.FStar_Ident.str uu____12540
    | Abs (pats,t) ->
        let uu____12591 = to_string_l " " pat_to_string pats  in
        let uu____12596 = FStar_All.pipe_right t term_to_string  in
        FStar_Util.format2 "(fun %s -> %s)" uu____12591 uu____12596
    | App (t1,t2,imp) ->
        let uu____12618 = FStar_All.pipe_right t1 term_to_string  in
        let uu____12624 = FStar_All.pipe_right t2 term_to_string  in
        FStar_Util.format3 "%s %s%s" uu____12618 (imp_to_string imp)
          uu____12624
    | Let (Rec ,(a,(p,b))::lbs,body) ->
        let uu____12739 = attrs_opt_to_string a  in
        let uu____12741 =
          let uu____12743 = FStar_All.pipe_right p pat_to_string  in
          let uu____12748 = FStar_All.pipe_right b term_to_string  in
          FStar_Util.format2 "%s=%s" uu____12743 uu____12748  in
        let uu____12755 =
          to_string_l " "
            (fun uu____12785  ->
               match uu____12785 with
               | (a1,(p1,b1)) ->
                   let uu____12843 = attrs_opt_to_string a1  in
                   let uu____12845 = FStar_All.pipe_right p1 pat_to_string
                      in
                   let uu____12850 = FStar_All.pipe_right b1 term_to_string
                      in
                   FStar_Util.format3 "%sand %s=%s" uu____12843 uu____12845
                     uu____12850) lbs
           in
        let uu____12857 = FStar_All.pipe_right body term_to_string  in
        FStar_Util.format4 "%slet rec %s%s in %s" uu____12739 uu____12741
          uu____12755 uu____12857
    | Let (q,(attrs,(pat,tm))::[],body) ->
        let uu____12970 = attrs_opt_to_string attrs  in
        let uu____12972 = FStar_All.pipe_right pat pat_to_string  in
        let uu____12977 = FStar_All.pipe_right tm term_to_string  in
        let uu____12983 = FStar_All.pipe_right body term_to_string  in
        FStar_Util.format5 "%slet %s %s = %s in %s" uu____12970
          (string_of_let_qualifier q) uu____12972 uu____12977 uu____12983
    | Let (uu____12990,uu____12991,uu____12992) ->
        FStar_Errors.raise_error
          (FStar_Errors.Fatal_EmptySurfaceLet,
            "Internal error: found an invalid surface Let") x.range
    | LetOpen (lid,t) ->
        let uu____13062 = FStar_Ident.string_of_lid lid  in
        let uu____13064 = term_to_string t  in
        FStar_Util.format2 "let open %s in %s" uu____13062 uu____13064
    | Seq (t1,t2) ->
        let uu____13081 = FStar_All.pipe_right t1 term_to_string  in
        let uu____13087 = FStar_All.pipe_right t2 term_to_string  in
        FStar_Util.format2 "%s; %s" uu____13081 uu____13087
    | Bind (id1,t1,t2) ->
        let uu____13113 = term_to_string t1  in
        let uu____13115 = term_to_string t2  in
        FStar_Util.format3 "%s <- %s; %s" id1.FStar_Ident.idText uu____13113
          uu____13115
    | If (t1,t2,t3) ->
        let uu____13139 = FStar_All.pipe_right t1 term_to_string  in
        let uu____13145 = FStar_All.pipe_right t2 term_to_string  in
        let uu____13151 = FStar_All.pipe_right t3 term_to_string  in
        FStar_Util.format3 "if %s then %s else %s" uu____13139 uu____13145
          uu____13151
    | Match (t,branches) ->
        let s =
          match x.tm with
          | Match uu____13205 -> "match"
          | TryWith uu____13232 -> "try"
          | uu____13259 -> failwith "impossible"  in
        let uu____13262 = FStar_All.pipe_right t term_to_string  in
        let uu____13268 =
          to_string_l " | "
            (fun uu____13294  ->
               match uu____13294 with
               | (p,w,e) ->
                   let uu____13335 = FStar_All.pipe_right p pat_to_string  in
                   let uu____13340 =
                     match w with
                     | FStar_Pervasives_Native.None  -> ""
                     | FStar_Pervasives_Native.Some e1 ->
                         let uu____13354 = term_to_string e1  in
                         FStar_Util.format1 "when %s" uu____13354
                      in
                   let uu____13357 = FStar_All.pipe_right e term_to_string
                      in
                   FStar_Util.format3 "%s %s -> %s" uu____13335 uu____13340
                     uu____13357) branches
           in
        FStar_Util.format3 "%s %s with %s" s uu____13262 uu____13268
    | TryWith (t,branches) ->
        let s =
          match x.tm with
          | Match uu____13412 -> "match"
          | TryWith uu____13439 -> "try"
          | uu____13466 -> failwith "impossible"  in
        let uu____13469 = FStar_All.pipe_right t term_to_string  in
        let uu____13475 =
          to_string_l " | "
            (fun uu____13501  ->
               match uu____13501 with
               | (p,w,e) ->
                   let uu____13542 = FStar_All.pipe_right p pat_to_string  in
                   let uu____13547 =
                     match w with
                     | FStar_Pervasives_Native.None  -> ""
                     | FStar_Pervasives_Native.Some e1 ->
                         let uu____13561 = term_to_string e1  in
                         FStar_Util.format1 "when %s" uu____13561
                      in
                   let uu____13564 = FStar_All.pipe_right e term_to_string
                      in
                   FStar_Util.format3 "%s %s -> %s" uu____13542 uu____13547
                     uu____13564) branches
           in
        FStar_Util.format3 "%s %s with %s" s uu____13469 uu____13475
    | Ascribed (t1,t2,FStar_Pervasives_Native.None ) ->
        let uu____13594 = FStar_All.pipe_right t1 term_to_string  in
        let uu____13600 = FStar_All.pipe_right t2 term_to_string  in
        FStar_Util.format2 "(%s : %s)" uu____13594 uu____13600
    | Ascribed (t1,t2,FStar_Pervasives_Native.Some tac) ->
        let uu____13633 = FStar_All.pipe_right t1 term_to_string  in
        let uu____13639 = FStar_All.pipe_right t2 term_to_string  in
        let uu____13645 = FStar_All.pipe_right tac term_to_string  in
        FStar_Util.format3 "(%s : %s by %s)" uu____13633 uu____13639
          uu____13645
    | Record (FStar_Pervasives_Native.Some e,fields) ->
        let uu____13691 = FStar_All.pipe_right e term_to_string  in
        let uu____13697 =
          to_string_l " "
            (fun uu____13715  ->
               match uu____13715 with
               | (l,e1) ->
                   let uu____13744 = FStar_All.pipe_right e1 term_to_string
                      in
                   FStar_Util.format2 "%s=%s" l.FStar_Ident.str uu____13744)
            fields
           in
        FStar_Util.format2 "{%s with %s}" uu____13691 uu____13697
    | Record (FStar_Pervasives_Native.None ,fields) ->
        let uu____13787 =
          to_string_l " "
            (fun uu____13805  ->
               match uu____13805 with
               | (l,e) ->
                   let uu____13834 = FStar_All.pipe_right e term_to_string
                      in
                   FStar_Util.format2 "%s=%s" l.FStar_Ident.str uu____13834)
            fields
           in
        FStar_Util.format1 "{%s}" uu____13787
    | Project (e,l) ->
        let uu____13858 = FStar_All.pipe_right e term_to_string  in
        FStar_Util.format2 "%s.%s" uu____13858 l.FStar_Ident.str
    | Product ([],t) -> term_to_string t
    | Product (b::hd1::tl1,t) ->
        term_to_string
          (mk_term
             (Product
                ([b], (mk_term (Product ((hd1 :: tl1), t)) x.range x.level)))
             x.range x.level)
    | Product (b::[],t) when x.level = Type_level ->
        let uu____13976 = FStar_All.pipe_right b binder_to_string  in
        let uu____13983 = FStar_All.pipe_right t term_to_string  in
        FStar_Util.format2 "%s -> %s" uu____13976 uu____13983
    | Product (b::[],t) when x.level = Kind ->
        let uu____14016 = FStar_All.pipe_right b binder_to_string  in
        let uu____14023 = FStar_All.pipe_right t term_to_string  in
        FStar_Util.format2 "%s => %s" uu____14016 uu____14023
    | Sum (binders,t) ->
        let uu____14064 =
          FStar_All.pipe_right (FStar_List.append binders [FStar_Util.Inr t])
            (FStar_List.map
               (fun uu___7_14138  ->
                  match uu___7_14138 with
                  | FStar_Util.Inl b -> binder_to_string b
                  | FStar_Util.Inr t1 -> term_to_string t1))
           in
        FStar_All.pipe_right uu____14064 (FStar_String.concat " & ")
    | QForall (bs,(uu____14180,pats),t) ->
        let uu____14238 = to_string_l " " binder_to_string bs  in
        let uu____14245 =
          to_string_l " \\/ " (to_string_l "; " term_to_string) pats  in
        let uu____14257 = FStar_All.pipe_right t term_to_string  in
        FStar_Util.format3 "forall %s.{:pattern %s} %s" uu____14238
          uu____14245 uu____14257
    | QExists (bs,(uu____14265,pats),t) ->
        let uu____14323 = to_string_l " " binder_to_string bs  in
        let uu____14330 =
          to_string_l " \\/ " (to_string_l "; " term_to_string) pats  in
        let uu____14342 = FStar_All.pipe_right t term_to_string  in
        FStar_Util.format3 "exists %s.{:pattern %s} %s" uu____14323
          uu____14330 uu____14342
    | Refine (b,t) ->
        let uu____14365 = FStar_All.pipe_right b binder_to_string  in
        let uu____14372 = FStar_All.pipe_right t term_to_string  in
        FStar_Util.format2 "%s:{%s}" uu____14365 uu____14372
    | NamedTyp (x1,t) ->
        let uu____14391 = FStar_All.pipe_right t term_to_string  in
        FStar_Util.format2 "%s:%s" x1.FStar_Ident.idText uu____14391
    | Paren t ->
        let uu____14402 = FStar_All.pipe_right t term_to_string  in
        FStar_Util.format1 "(%s)" uu____14402
    | Product (bs,t) ->
        let uu____14429 =
          let uu____14431 =
            FStar_All.pipe_right bs (FStar_List.map binder_to_string)  in
          FStar_All.pipe_right uu____14431 (FStar_String.concat ",")  in
        let uu____14454 = FStar_All.pipe_right t term_to_string  in
        FStar_Util.format2 "Unidentified product: [%s] %s" uu____14429
          uu____14454
    | Discrim lid ->
        let uu____14466 = FStar_Ident.string_of_lid lid  in
        FStar_Util.format1 "%s?" uu____14466
    | Attributes ts ->
        let uu____14475 =
          let uu____14477 = FStar_List.map term_to_string ts  in
          FStar_All.pipe_left (FStar_String.concat " ") uu____14477  in
        FStar_Util.format1 "(attributes %s)" uu____14475
    | Antiquote t ->
        let uu____14495 = term_to_string t  in
        FStar_Util.format1 "(`#%s)" uu____14495
    | Quote (t,Static ) ->
        let uu____14505 = term_to_string t  in
        FStar_Util.format1 "(`(%s))" uu____14505
    | Quote (t,Dynamic ) ->
        let uu____14515 = term_to_string t  in
        FStar_Util.format1 "quote (%s)" uu____14515
    | VQuote t ->
        let uu____14522 = term_to_string t  in
        FStar_Util.format1 "`%%%s" uu____14522
    | CalcProof (rel,init1,steps) ->
        let uu____14546 = term_to_string rel  in
        let uu____14548 = term_to_string init1  in
        let uu____14550 =
          let uu____14552 = FStar_List.map calc_step_to_string steps  in
          FStar_All.pipe_left (FStar_String.concat " ") uu____14552  in
        FStar_Util.format3 "calc (%s) { %s %s }" uu____14546 uu____14548
          uu____14550

and (calc_step_to_string : calc_step -> Prims.string) =
  fun uu____14564  ->
    match uu____14564 with
    | CalcStep (rel,just,next) ->
        let uu____14588 = term_to_string rel  in
        let uu____14590 = term_to_string just  in
        let uu____14592 = term_to_string next  in
        FStar_Util.format3 "%s{ %s } %s" uu____14588 uu____14590 uu____14592

and (binder_to_string : binder -> Prims.string) =
  fun x  ->
    let s =
      match x.b with
      | Variable i -> i.FStar_Ident.idText
      | TVariable i -> FStar_Util.format1 "%s:_" i.FStar_Ident.idText
      | TAnnotated (i,t) ->
          let uu____14622 = FStar_All.pipe_right t term_to_string  in
          FStar_Util.format2 "%s:%s" i.FStar_Ident.idText uu____14622
      | Annotated (i,t) ->
          let uu____14641 = FStar_All.pipe_right t term_to_string  in
          FStar_Util.format2 "%s:%s" i.FStar_Ident.idText uu____14641
      | NoName t -> FStar_All.pipe_right t term_to_string  in
    let uu____14656 = aqual_to_string x.aqual  in
    FStar_Util.format2 "%s%s" uu____14656 s

and (aqual_to_string :
  arg_qualifier FStar_Pervasives_Native.option -> Prims.string) =
  fun uu___8_14659  ->
    match uu___8_14659 with
    | FStar_Pervasives_Native.Some (Equality ) -> "$"
    | FStar_Pervasives_Native.Some (Implicit ) -> "#"
    | uu____14665 -> ""

and (pat_to_string : pattern -> Prims.string) =
  fun x  ->
    match x.pat with
    | PatWild (FStar_Pervasives_Native.None ) -> "_"
    | PatWild uu____14674 -> "#_"
    | PatConst c -> FStar_Parser_Const.const_to_string c
    | PatApp (p,ps) ->
        let uu____14693 = FStar_All.pipe_right p pat_to_string  in
        let uu____14698 = to_string_l " " pat_to_string ps  in
        FStar_Util.format2 "(%s %s)" uu____14693 uu____14698
    | PatTvar (i,aq) ->
        let uu____14714 = aqual_to_string aq  in
        FStar_Util.format2 "%s%s" uu____14714 i.FStar_Ident.idText
    | PatVar (i,aq) ->
        let uu____14727 = aqual_to_string aq  in
        FStar_Util.format2 "%s%s" uu____14727 i.FStar_Ident.idText
    | PatName l -> l.FStar_Ident.str
    | PatList l ->
        let uu____14740 = to_string_l "; " pat_to_string l  in
        FStar_Util.format1 "[%s]" uu____14740
    | PatTuple (l,false ) ->
        let uu____14757 = to_string_l ", " pat_to_string l  in
        FStar_Util.format1 "(%s)" uu____14757
    | PatTuple (l,true ) ->
        let uu____14774 = to_string_l ", " pat_to_string l  in
        FStar_Util.format1 "(|%s|)" uu____14774
    | PatRecord l ->
        let uu____14793 =
          to_string_l "; "
            (fun uu____14810  ->
               match uu____14810 with
               | (f,e) ->
                   let uu____14836 = FStar_All.pipe_right e pat_to_string  in
                   FStar_Util.format2 "%s=%s" f.FStar_Ident.str uu____14836)
            l
           in
        FStar_Util.format1 "{%s}" uu____14793
    | PatOr l -> to_string_l "|\n " pat_to_string l
    | PatOp op ->
        let uu____14854 = FStar_Ident.text_of_id op  in
        FStar_Util.format1 "(%s)" uu____14854
    | PatAscribed (p,(t,FStar_Pervasives_Native.None )) ->
        let uu____14889 = FStar_All.pipe_right p pat_to_string  in
        let uu____14894 = FStar_All.pipe_right t term_to_string  in
        FStar_Util.format2 "(%s:%s)" uu____14889 uu____14894
    | PatAscribed (p,(t,FStar_Pervasives_Native.Some tac)) ->
        let uu____14937 = FStar_All.pipe_right p pat_to_string  in
        let uu____14942 = FStar_All.pipe_right t term_to_string  in
        let uu____14948 = FStar_All.pipe_right tac term_to_string  in
        FStar_Util.format3 "(%s:%s by %s)" uu____14937 uu____14942
          uu____14948

and (attrs_opt_to_string :
  term Prims.list FStar_Pervasives_Native.option -> Prims.string) =
  fun uu___9_14955  ->
    match uu___9_14955 with
    | FStar_Pervasives_Native.None  -> ""
    | FStar_Pervasives_Native.Some attrs ->
        let uu____14981 =
          let uu____14983 = FStar_List.map term_to_string attrs  in
          FStar_All.pipe_right uu____14983 (FStar_String.concat "; ")  in
        FStar_Util.format1 "[@ %s]" uu____14981

let rec (head_id_of_pat : pattern -> FStar_Ident.lident Prims.list) =
  fun p  ->
    match p.pat with
    | PatName l -> [l]
    | PatVar (i,uu____15033) ->
        let uu____15042 = FStar_Ident.lid_of_ids [i]  in [uu____15042]
    | PatApp (p1,uu____15064) -> head_id_of_pat p1
    | PatAscribed (p1,uu____15078) -> head_id_of_pat p1
    | uu____15107 -> []
  
let lids_of_let :
  'Auu____15117 .
    (pattern * 'Auu____15117) Prims.list -> FStar_Ident.lident Prims.list
  =
  fun defs  ->
    FStar_All.pipe_right defs
      (FStar_List.collect
         (fun uu____15172  ->
            match uu____15172 with | (p,uu____15186) -> head_id_of_pat p))
  
let (id_of_tycon : tycon -> Prims.string) =
  fun uu___10_15197  ->
    match uu___10_15197 with
    | TyconAbstract (i,uu____15200,uu____15201) -> i.FStar_Ident.idText
    | TyconAbbrev (i,uu____15229,uu____15230,uu____15231) ->
        i.FStar_Ident.idText
    | TyconRecord (i,uu____15265,uu____15266,uu____15267) ->
        i.FStar_Ident.idText
    | TyconVariant (i,uu____15325,uu____15326,uu____15327) ->
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
    | TopLevelLet (uu____15451,pats) ->
        let uu____15475 =
          let uu____15477 =
            let uu____15481 = lids_of_let pats  in
            FStar_All.pipe_right uu____15481
              (FStar_List.map (fun l  -> l.FStar_Ident.str))
             in
          FStar_All.pipe_right uu____15477 (FStar_String.concat ", ")  in
        Prims.op_Hat "let " uu____15475
    | Main uu____15517 -> "main ..."
    | Assume (i,uu____15523) -> Prims.op_Hat "assume " i.FStar_Ident.idText
    | Tycon (uu____15535,uu____15536,tys) ->
        let uu____15558 =
          let uu____15560 =
            FStar_All.pipe_right tys
              (FStar_List.map
                 (fun uu____15585  ->
                    match uu____15585 with | (x,uu____15594) -> id_of_tycon x))
             in
          FStar_All.pipe_right uu____15560 (FStar_String.concat ", ")  in
        Prims.op_Hat "type " uu____15558
    | Val (i,uu____15606) -> Prims.op_Hat "val " i.FStar_Ident.idText
    | Exception (i,uu____15619) ->
        Prims.op_Hat "exception " i.FStar_Ident.idText
    | NewEffect (DefineEffect (i,uu____15636,uu____15637,uu____15638)) ->
        Prims.op_Hat "new_effect " i.FStar_Ident.idText
    | NewEffect (RedefineEffect (i,uu____15677,uu____15678)) ->
        Prims.op_Hat "new_effect " i.FStar_Ident.idText
    | Splice (ids,t) ->
        let uu____15718 =
          let uu____15720 =
            let uu____15722 =
              FStar_List.map (fun i  -> i.FStar_Ident.idText) ids  in
            FStar_All.pipe_left (FStar_String.concat ";") uu____15722  in
          let uu____15738 =
            let uu____15740 =
              let uu____15742 = term_to_string t  in
              Prims.op_Hat uu____15742 ")"  in
            Prims.op_Hat "] (" uu____15740  in
          Prims.op_Hat uu____15720 uu____15738  in
        Prims.op_Hat "splice[" uu____15718
    | SubEffect uu____15747 -> "sub_effect"
    | Pragma uu____15756 -> "pragma"
    | Fsdoc uu____15758 -> "fsdoc"
  
let (modul_to_string : modul -> Prims.string) =
  fun m  ->
    match m with
    | Module (uu____15768,decls) ->
        let uu____15792 =
          FStar_All.pipe_right decls (FStar_List.map decl_to_string)  in
        FStar_All.pipe_right uu____15792 (FStar_String.concat "\n")
    | Interface (uu____15817,decls,uu____15819) ->
        let uu____15844 =
          FStar_All.pipe_right decls (FStar_List.map decl_to_string)  in
        FStar_All.pipe_right uu____15844 (FStar_String.concat "\n")
  
let (decl_is_val : FStar_Ident.ident -> decl -> Prims.bool) =
  fun id1  ->
    fun decl  ->
      match decl.d with
      | Val (id',uu____15897) -> FStar_Ident.ident_equals id1 id'
      | uu____15908 -> false
  
let (thunk : term -> term) =
  fun ens  ->
    let wildpat = mk_pattern (PatWild FStar_Pervasives_Native.None) ens.range
       in
    mk_term (Abs ([wildpat], ens)) ens.range Expr
  
let (idents_of_binders :
  binder Prims.list -> FStar_Range.range -> FStar_Ident.ident Prims.list) =
  fun bs  ->
    fun r  ->
      FStar_All.pipe_right bs
        (FStar_List.map
           (fun b  ->
              match b.b with
              | Variable i -> i
              | TVariable i -> i
              | Annotated (i,uu____16003) -> i
              | TAnnotated (i,uu____16015) -> i
              | NoName uu____16026 ->
                  FStar_Errors.raise_error
                    (FStar_Errors.Fatal_MissingQuantifierBinder,
                      "Wildcard binders in quantifiers are not allowed") r))
  