open Prims
type level =
  | Un 
  | Expr 
  | Type_level 
  | Kind 
  | Formula 
let (uu___is_Un : level -> Prims.bool) =
  fun projectee  -> match projectee with | Un  -> true | uu____25 -> false 
let (uu___is_Expr : level -> Prims.bool) =
  fun projectee  -> match projectee with | Expr  -> true | uu____36 -> false 
let (uu___is_Type_level : level -> Prims.bool) =
  fun projectee  ->
    match projectee with | Type_level  -> true | uu____47 -> false
  
let (uu___is_Kind : level -> Prims.bool) =
  fun projectee  -> match projectee with | Kind  -> true | uu____58 -> false 
let (uu___is_Formula : level -> Prims.bool) =
  fun projectee  ->
    match projectee with | Formula  -> true | uu____69 -> false
  
type let_qualifier =
  | NoLetQualifier 
  | Rec 
let (uu___is_NoLetQualifier : let_qualifier -> Prims.bool) =
  fun projectee  ->
    match projectee with | NoLetQualifier  -> true | uu____80 -> false
  
let (uu___is_Rec : let_qualifier -> Prims.bool) =
  fun projectee  -> match projectee with | Rec  -> true | uu____91 -> false 
type quote_kind =
  | Static 
  | Dynamic 
let (uu___is_Static : quote_kind -> Prims.bool) =
  fun projectee  ->
    match projectee with | Static  -> true | uu____102 -> false
  
let (uu___is_Dynamic : quote_kind -> Prims.bool) =
  fun projectee  ->
    match projectee with | Dynamic  -> true | uu____113 -> false
  
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
  fun projectee  -> match projectee with | Wild  -> true | uu____732 -> false 
let (uu___is_Const : term' -> Prims.bool) =
  fun projectee  ->
    match projectee with | Const _0 -> true | uu____744 -> false
  
let (__proj__Const__item___0 : term' -> FStar_Const.sconst) =
  fun projectee  -> match projectee with | Const _0 -> _0 
let (uu___is_Op : term' -> Prims.bool) =
  fun projectee  -> match projectee with | Op _0 -> true | uu____769 -> false 
let (__proj__Op__item___0 : term' -> (FStar_Ident.ident * term Prims.list)) =
  fun projectee  -> match projectee with | Op _0 -> _0 
let (uu___is_Tvar : term' -> Prims.bool) =
  fun projectee  ->
    match projectee with | Tvar _0 -> true | uu____806 -> false
  
let (__proj__Tvar__item___0 : term' -> FStar_Ident.ident) =
  fun projectee  -> match projectee with | Tvar _0 -> _0 
let (uu___is_Uvar : term' -> Prims.bool) =
  fun projectee  ->
    match projectee with | Uvar _0 -> true | uu____825 -> false
  
let (__proj__Uvar__item___0 : term' -> FStar_Ident.ident) =
  fun projectee  -> match projectee with | Uvar _0 -> _0 
let (uu___is_Var : term' -> Prims.bool) =
  fun projectee  ->
    match projectee with | Var _0 -> true | uu____844 -> false
  
let (__proj__Var__item___0 : term' -> FStar_Ident.lid) =
  fun projectee  -> match projectee with | Var _0 -> _0 
let (uu___is_Name : term' -> Prims.bool) =
  fun projectee  ->
    match projectee with | Name _0 -> true | uu____863 -> false
  
let (__proj__Name__item___0 : term' -> FStar_Ident.lid) =
  fun projectee  -> match projectee with | Name _0 -> _0 
let (uu___is_Projector : term' -> Prims.bool) =
  fun projectee  ->
    match projectee with | Projector _0 -> true | uu____886 -> false
  
let (__proj__Projector__item___0 :
  term' -> (FStar_Ident.lid * FStar_Ident.ident)) =
  fun projectee  -> match projectee with | Projector _0 -> _0 
let (uu___is_Construct : term' -> Prims.bool) =
  fun projectee  ->
    match projectee with | Construct _0 -> true | uu____927 -> false
  
let (__proj__Construct__item___0 :
  term' -> (FStar_Ident.lid * (term * imp) Prims.list)) =
  fun projectee  -> match projectee with | Construct _0 -> _0 
let (uu___is_Abs : term' -> Prims.bool) =
  fun projectee  ->
    match projectee with | Abs _0 -> true | uu____982 -> false
  
let (__proj__Abs__item___0 : term' -> (pattern Prims.list * term)) =
  fun projectee  -> match projectee with | Abs _0 -> _0 
let (uu___is_App : term' -> Prims.bool) =
  fun projectee  ->
    match projectee with | App _0 -> true | uu____1025 -> false
  
let (__proj__App__item___0 : term' -> (term * term * imp)) =
  fun projectee  -> match projectee with | App _0 -> _0 
let (uu___is_Let : term' -> Prims.bool) =
  fun projectee  ->
    match projectee with | Let _0 -> true | uu____1082 -> false
  
let (__proj__Let__item___0 :
  term' ->
    (let_qualifier * (term Prims.list FStar_Pervasives_Native.option *
      (pattern * term)) Prims.list * term))
  = fun projectee  -> match projectee with | Let _0 -> _0 
let (uu___is_LetOpen : term' -> Prims.bool) =
  fun projectee  ->
    match projectee with | LetOpen _0 -> true | uu____1165 -> false
  
let (__proj__LetOpen__item___0 : term' -> (FStar_Ident.lid * term)) =
  fun projectee  -> match projectee with | LetOpen _0 -> _0 
let (uu___is_Seq : term' -> Prims.bool) =
  fun projectee  ->
    match projectee with | Seq _0 -> true | uu____1200 -> false
  
let (__proj__Seq__item___0 : term' -> (term * term)) =
  fun projectee  -> match projectee with | Seq _0 -> _0 
let (uu___is_Bind : term' -> Prims.bool) =
  fun projectee  ->
    match projectee with | Bind _0 -> true | uu____1237 -> false
  
let (__proj__Bind__item___0 : term' -> (FStar_Ident.ident * term * term)) =
  fun projectee  -> match projectee with | Bind _0 -> _0 
let (uu___is_If : term' -> Prims.bool) =
  fun projectee  ->
    match projectee with | If _0 -> true | uu____1280 -> false
  
let (__proj__If__item___0 : term' -> (term * term * term)) =
  fun projectee  -> match projectee with | If _0 -> _0 
let (uu___is_Match : term' -> Prims.bool) =
  fun projectee  ->
    match projectee with | Match _0 -> true | uu____1331 -> false
  
let (__proj__Match__item___0 :
  term' ->
    (term * (pattern * term FStar_Pervasives_Native.option * term)
      Prims.list))
  = fun projectee  -> match projectee with | Match _0 -> _0 
let (uu___is_TryWith : term' -> Prims.bool) =
  fun projectee  ->
    match projectee with | TryWith _0 -> true | uu____1406 -> false
  
let (__proj__TryWith__item___0 :
  term' ->
    (term * (pattern * term FStar_Pervasives_Native.option * term)
      Prims.list))
  = fun projectee  -> match projectee with | TryWith _0 -> _0 
let (uu___is_Ascribed : term' -> Prims.bool) =
  fun projectee  ->
    match projectee with | Ascribed _0 -> true | uu____1475 -> false
  
let (__proj__Ascribed__item___0 :
  term' -> (term * term * term FStar_Pervasives_Native.option)) =
  fun projectee  -> match projectee with | Ascribed _0 -> _0 
let (uu___is_Record : term' -> Prims.bool) =
  fun projectee  ->
    match projectee with | Record _0 -> true | uu____1530 -> false
  
let (__proj__Record__item___0 :
  term' ->
    (term FStar_Pervasives_Native.option * (FStar_Ident.lid * term)
      Prims.list))
  = fun projectee  -> match projectee with | Record _0 -> _0 
let (uu___is_Project : term' -> Prims.bool) =
  fun projectee  ->
    match projectee with | Project _0 -> true | uu____1589 -> false
  
let (__proj__Project__item___0 : term' -> (term * FStar_Ident.lid)) =
  fun projectee  -> match projectee with | Project _0 -> _0 
let (uu___is_Product : term' -> Prims.bool) =
  fun projectee  ->
    match projectee with | Product _0 -> true | uu____1626 -> false
  
let (__proj__Product__item___0 : term' -> (binder Prims.list * term)) =
  fun projectee  -> match projectee with | Product _0 -> _0 
let (uu___is_Sum : term' -> Prims.bool) =
  fun projectee  ->
    match projectee with | Sum _0 -> true | uu____1673 -> false
  
let (__proj__Sum__item___0 :
  term' -> ((binder,term) FStar_Util.either Prims.list * term)) =
  fun projectee  -> match projectee with | Sum _0 -> _0 
let (uu___is_QForall : term' -> Prims.bool) =
  fun projectee  ->
    match projectee with | QForall _0 -> true | uu____1740 -> false
  
let (__proj__QForall__item___0 :
  term' ->
    (binder Prims.list * (FStar_Ident.ident Prims.list * term Prims.list
      Prims.list) * term))
  = fun projectee  -> match projectee with | QForall _0 -> _0 
let (uu___is_QExists : term' -> Prims.bool) =
  fun projectee  ->
    match projectee with | QExists _0 -> true | uu____1831 -> false
  
let (__proj__QExists__item___0 :
  term' ->
    (binder Prims.list * (FStar_Ident.ident Prims.list * term Prims.list
      Prims.list) * term))
  = fun projectee  -> match projectee with | QExists _0 -> _0 
let (uu___is_Refine : term' -> Prims.bool) =
  fun projectee  ->
    match projectee with | Refine _0 -> true | uu____1908 -> false
  
let (__proj__Refine__item___0 : term' -> (binder * term)) =
  fun projectee  -> match projectee with | Refine _0 -> _0 
let (uu___is_NamedTyp : term' -> Prims.bool) =
  fun projectee  ->
    match projectee with | NamedTyp _0 -> true | uu____1943 -> false
  
let (__proj__NamedTyp__item___0 : term' -> (FStar_Ident.ident * term)) =
  fun projectee  -> match projectee with | NamedTyp _0 -> _0 
let (uu___is_Paren : term' -> Prims.bool) =
  fun projectee  ->
    match projectee with | Paren _0 -> true | uu____1974 -> false
  
let (__proj__Paren__item___0 : term' -> term) =
  fun projectee  -> match projectee with | Paren _0 -> _0 
let (uu___is_Requires : term' -> Prims.bool) =
  fun projectee  ->
    match projectee with | Requires _0 -> true | uu____2000 -> false
  
let (__proj__Requires__item___0 :
  term' -> (term * Prims.string FStar_Pervasives_Native.option)) =
  fun projectee  -> match projectee with | Requires _0 -> _0 
let (uu___is_Ensures : term' -> Prims.bool) =
  fun projectee  ->
    match projectee with | Ensures _0 -> true | uu____2047 -> false
  
let (__proj__Ensures__item___0 :
  term' -> (term * Prims.string FStar_Pervasives_Native.option)) =
  fun projectee  -> match projectee with | Ensures _0 -> _0 
let (uu___is_Labeled : term' -> Prims.bool) =
  fun projectee  ->
    match projectee with | Labeled _0 -> true | uu____2095 -> false
  
let (__proj__Labeled__item___0 : term' -> (term * Prims.string * Prims.bool))
  = fun projectee  -> match projectee with | Labeled _0 -> _0 
let (uu___is_Discrim : term' -> Prims.bool) =
  fun projectee  ->
    match projectee with | Discrim _0 -> true | uu____2138 -> false
  
let (__proj__Discrim__item___0 : term' -> FStar_Ident.lid) =
  fun projectee  -> match projectee with | Discrim _0 -> _0 
let (uu___is_Attributes : term' -> Prims.bool) =
  fun projectee  ->
    match projectee with | Attributes _0 -> true | uu____2159 -> false
  
let (__proj__Attributes__item___0 : term' -> term Prims.list) =
  fun projectee  -> match projectee with | Attributes _0 -> _0 
let (uu___is_Antiquote : term' -> Prims.bool) =
  fun projectee  ->
    match projectee with | Antiquote _0 -> true | uu____2184 -> false
  
let (__proj__Antiquote__item___0 : term' -> term) =
  fun projectee  -> match projectee with | Antiquote _0 -> _0 
let (uu___is_Quote : term' -> Prims.bool) =
  fun projectee  ->
    match projectee with | Quote _0 -> true | uu____2207 -> false
  
let (__proj__Quote__item___0 : term' -> (term * quote_kind)) =
  fun projectee  -> match projectee with | Quote _0 -> _0 
let (uu___is_VQuote : term' -> Prims.bool) =
  fun projectee  ->
    match projectee with | VQuote _0 -> true | uu____2238 -> false
  
let (__proj__VQuote__item___0 : term' -> term) =
  fun projectee  -> match projectee with | VQuote _0 -> _0 
let (uu___is_CalcProof : term' -> Prims.bool) =
  fun projectee  ->
    match projectee with | CalcProof _0 -> true | uu____2265 -> false
  
let (__proj__CalcProof__item___0 :
  term' -> (term * term * calc_step Prims.list)) =
  fun projectee  -> match projectee with | CalcProof _0 -> _0 
let (__proj__Mkterm__item__tm : term -> term') =
  fun projectee  ->
    match projectee with | { tm; range; level = level1;_} -> tm
  
let (__proj__Mkterm__item__range : term -> FStar_Range.range) =
  fun projectee  ->
    match projectee with | { tm; range; level = level1;_} -> range
  
let (__proj__Mkterm__item__level : term -> level) =
  fun projectee  ->
    match projectee with | { tm; range; level = level1;_} -> level1
  
let (uu___is_CalcStep : calc_step -> Prims.bool) = fun projectee  -> true 
let (__proj__CalcStep__item___0 : calc_step -> (term * term * term)) =
  fun projectee  -> match projectee with | CalcStep _0 -> _0 
let (uu___is_Variable : binder' -> Prims.bool) =
  fun projectee  ->
    match projectee with | Variable _0 -> true | uu____2368 -> false
  
let (__proj__Variable__item___0 : binder' -> FStar_Ident.ident) =
  fun projectee  -> match projectee with | Variable _0 -> _0 
let (uu___is_TVariable : binder' -> Prims.bool) =
  fun projectee  ->
    match projectee with | TVariable _0 -> true | uu____2387 -> false
  
let (__proj__TVariable__item___0 : binder' -> FStar_Ident.ident) =
  fun projectee  -> match projectee with | TVariable _0 -> _0 
let (uu___is_Annotated : binder' -> Prims.bool) =
  fun projectee  ->
    match projectee with | Annotated _0 -> true | uu____2410 -> false
  
let (__proj__Annotated__item___0 : binder' -> (FStar_Ident.ident * term)) =
  fun projectee  -> match projectee with | Annotated _0 -> _0 
let (uu___is_TAnnotated : binder' -> Prims.bool) =
  fun projectee  ->
    match projectee with | TAnnotated _0 -> true | uu____2445 -> false
  
let (__proj__TAnnotated__item___0 : binder' -> (FStar_Ident.ident * term)) =
  fun projectee  -> match projectee with | TAnnotated _0 -> _0 
let (uu___is_NoName : binder' -> Prims.bool) =
  fun projectee  ->
    match projectee with | NoName _0 -> true | uu____2476 -> false
  
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
    match projectee with | PatWild _0 -> true | uu____2549 -> false
  
let (__proj__PatWild__item___0 :
  pattern' -> arg_qualifier FStar_Pervasives_Native.option) =
  fun projectee  -> match projectee with | PatWild _0 -> _0 
let (uu___is_PatConst : pattern' -> Prims.bool) =
  fun projectee  ->
    match projectee with | PatConst _0 -> true | uu____2574 -> false
  
let (__proj__PatConst__item___0 : pattern' -> FStar_Const.sconst) =
  fun projectee  -> match projectee with | PatConst _0 -> _0 
let (uu___is_PatApp : pattern' -> Prims.bool) =
  fun projectee  ->
    match projectee with | PatApp _0 -> true | uu____2599 -> false
  
let (__proj__PatApp__item___0 : pattern' -> (pattern * pattern Prims.list)) =
  fun projectee  -> match projectee with | PatApp _0 -> _0 
let (uu___is_PatVar : pattern' -> Prims.bool) =
  fun projectee  ->
    match projectee with | PatVar _0 -> true | uu____2642 -> false
  
let (__proj__PatVar__item___0 :
  pattern' ->
    (FStar_Ident.ident * arg_qualifier FStar_Pervasives_Native.option))
  = fun projectee  -> match projectee with | PatVar _0 -> _0 
let (uu___is_PatName : pattern' -> Prims.bool) =
  fun projectee  ->
    match projectee with | PatName _0 -> true | uu____2679 -> false
  
let (__proj__PatName__item___0 : pattern' -> FStar_Ident.lid) =
  fun projectee  -> match projectee with | PatName _0 -> _0 
let (uu___is_PatTvar : pattern' -> Prims.bool) =
  fun projectee  ->
    match projectee with | PatTvar _0 -> true | uu____2704 -> false
  
let (__proj__PatTvar__item___0 :
  pattern' ->
    (FStar_Ident.ident * arg_qualifier FStar_Pervasives_Native.option))
  = fun projectee  -> match projectee with | PatTvar _0 -> _0 
let (uu___is_PatList : pattern' -> Prims.bool) =
  fun projectee  ->
    match projectee with | PatList _0 -> true | uu____2743 -> false
  
let (__proj__PatList__item___0 : pattern' -> pattern Prims.list) =
  fun projectee  -> match projectee with | PatList _0 -> _0 
let (uu___is_PatTuple : pattern' -> Prims.bool) =
  fun projectee  ->
    match projectee with | PatTuple _0 -> true | uu____2775 -> false
  
let (__proj__PatTuple__item___0 :
  pattern' -> (pattern Prims.list * Prims.bool)) =
  fun projectee  -> match projectee with | PatTuple _0 -> _0 
let (uu___is_PatRecord : pattern' -> Prims.bool) =
  fun projectee  ->
    match projectee with | PatRecord _0 -> true | uu____2821 -> false
  
let (__proj__PatRecord__item___0 :
  pattern' -> (FStar_Ident.lid * pattern) Prims.list) =
  fun projectee  -> match projectee with | PatRecord _0 -> _0 
let (uu___is_PatAscribed : pattern' -> Prims.bool) =
  fun projectee  ->
    match projectee with | PatAscribed _0 -> true | uu____2868 -> false
  
let (__proj__PatAscribed__item___0 :
  pattern' -> (pattern * (term * term FStar_Pervasives_Native.option))) =
  fun projectee  -> match projectee with | PatAscribed _0 -> _0 
let (uu___is_PatOr : pattern' -> Prims.bool) =
  fun projectee  ->
    match projectee with | PatOr _0 -> true | uu____2919 -> false
  
let (__proj__PatOr__item___0 : pattern' -> pattern Prims.list) =
  fun projectee  -> match projectee with | PatOr _0 -> _0 
let (uu___is_PatOp : pattern' -> Prims.bool) =
  fun projectee  ->
    match projectee with | PatOp _0 -> true | uu____2944 -> false
  
let (__proj__PatOp__item___0 : pattern' -> FStar_Ident.ident) =
  fun projectee  -> match projectee with | PatOp _0 -> _0 
let (__proj__Mkpattern__item__pat : pattern -> pattern') =
  fun projectee  -> match projectee with | { pat; prange;_} -> pat 
let (__proj__Mkpattern__item__prange : pattern -> FStar_Range.range) =
  fun projectee  -> match projectee with | { pat; prange;_} -> prange 
let (uu___is_Implicit : arg_qualifier -> Prims.bool) =
  fun projectee  ->
    match projectee with | Implicit  -> true | uu____2978 -> false
  
let (uu___is_Equality : arg_qualifier -> Prims.bool) =
  fun projectee  ->
    match projectee with | Equality  -> true | uu____2989 -> false
  
let (uu___is_Meta : arg_qualifier -> Prims.bool) =
  fun projectee  ->
    match projectee with | Meta _0 -> true | uu____3001 -> false
  
let (__proj__Meta__item___0 : arg_qualifier -> term) =
  fun projectee  -> match projectee with | Meta _0 -> _0 
let (uu___is_FsTypApp : imp -> Prims.bool) =
  fun projectee  ->
    match projectee with | FsTypApp  -> true | uu____3019 -> false
  
let (uu___is_Hash : imp -> Prims.bool) =
  fun projectee  ->
    match projectee with | Hash  -> true | uu____3030 -> false
  
let (uu___is_UnivApp : imp -> Prims.bool) =
  fun projectee  ->
    match projectee with | UnivApp  -> true | uu____3041 -> false
  
let (uu___is_HashBrace : imp -> Prims.bool) =
  fun projectee  ->
    match projectee with | HashBrace _0 -> true | uu____3053 -> false
  
let (__proj__HashBrace__item___0 : imp -> term) =
  fun projectee  -> match projectee with | HashBrace _0 -> _0 
let (uu___is_Infix : imp -> Prims.bool) =
  fun projectee  ->
    match projectee with | Infix  -> true | uu____3071 -> false
  
let (uu___is_Nothing : imp -> Prims.bool) =
  fun projectee  ->
    match projectee with | Nothing  -> true | uu____3082 -> false
  
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
  FStar_Pervasives_Native.option * (FStar_Ident.ident * term) Prims.list) 
  | TyconVariant of (FStar_Ident.ident * binder Prims.list * knd
  FStar_Pervasives_Native.option * (FStar_Ident.ident * term
  FStar_Pervasives_Native.option * Prims.bool) Prims.list) 
let (uu___is_TyconAbstract : tycon -> Prims.bool) =
  fun projectee  ->
    match projectee with | TyconAbstract _0 -> true | uu____3209 -> false
  
let (__proj__TyconAbstract__item___0 :
  tycon ->
    (FStar_Ident.ident * binder Prims.list * knd
      FStar_Pervasives_Native.option))
  = fun projectee  -> match projectee with | TyconAbstract _0 -> _0 
let (uu___is_TyconAbbrev : tycon -> Prims.bool) =
  fun projectee  ->
    match projectee with | TyconAbbrev _0 -> true | uu____3270 -> false
  
let (__proj__TyconAbbrev__item___0 :
  tycon ->
    (FStar_Ident.ident * binder Prims.list * knd
      FStar_Pervasives_Native.option * term))
  = fun projectee  -> match projectee with | TyconAbbrev _0 -> _0 
let (uu___is_TyconRecord : tycon -> Prims.bool) =
  fun projectee  ->
    match projectee with | TyconRecord _0 -> true | uu____3343 -> false
  
let (__proj__TyconRecord__item___0 :
  tycon ->
    (FStar_Ident.ident * binder Prims.list * knd
      FStar_Pervasives_Native.option * (FStar_Ident.ident * term) Prims.list))
  = fun projectee  -> match projectee with | TyconRecord _0 -> _0 
let (uu___is_TyconVariant : tycon -> Prims.bool) =
  fun projectee  ->
    match projectee with | TyconVariant _0 -> true | uu____3439 -> false
  
let (__proj__TyconVariant__item___0 :
  tycon ->
    (FStar_Ident.ident * binder Prims.list * knd
      FStar_Pervasives_Native.option * (FStar_Ident.ident * term
      FStar_Pervasives_Native.option * Prims.bool) Prims.list))
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
    match projectee with | Private  -> true | uu____3526 -> false
  
let (uu___is_Abstract : qualifier -> Prims.bool) =
  fun projectee  ->
    match projectee with | Abstract  -> true | uu____3537 -> false
  
let (uu___is_Noeq : qualifier -> Prims.bool) =
  fun projectee  ->
    match projectee with | Noeq  -> true | uu____3548 -> false
  
let (uu___is_Unopteq : qualifier -> Prims.bool) =
  fun projectee  ->
    match projectee with | Unopteq  -> true | uu____3559 -> false
  
let (uu___is_Assumption : qualifier -> Prims.bool) =
  fun projectee  ->
    match projectee with | Assumption  -> true | uu____3570 -> false
  
let (uu___is_DefaultEffect : qualifier -> Prims.bool) =
  fun projectee  ->
    match projectee with | DefaultEffect  -> true | uu____3581 -> false
  
let (uu___is_TotalEffect : qualifier -> Prims.bool) =
  fun projectee  ->
    match projectee with | TotalEffect  -> true | uu____3592 -> false
  
let (uu___is_Effect_qual : qualifier -> Prims.bool) =
  fun projectee  ->
    match projectee with | Effect_qual  -> true | uu____3603 -> false
  
let (uu___is_New : qualifier -> Prims.bool) =
  fun projectee  -> match projectee with | New  -> true | uu____3614 -> false 
let (uu___is_Inline : qualifier -> Prims.bool) =
  fun projectee  ->
    match projectee with | Inline  -> true | uu____3625 -> false
  
let (uu___is_Visible : qualifier -> Prims.bool) =
  fun projectee  ->
    match projectee with | Visible  -> true | uu____3636 -> false
  
let (uu___is_Unfold_for_unification_and_vcgen : qualifier -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | Unfold_for_unification_and_vcgen  -> true
    | uu____3647 -> false
  
let (uu___is_Inline_for_extraction : qualifier -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | Inline_for_extraction  -> true
    | uu____3658 -> false
  
let (uu___is_Irreducible : qualifier -> Prims.bool) =
  fun projectee  ->
    match projectee with | Irreducible  -> true | uu____3669 -> false
  
let (uu___is_NoExtract : qualifier -> Prims.bool) =
  fun projectee  ->
    match projectee with | NoExtract  -> true | uu____3680 -> false
  
let (uu___is_Reifiable : qualifier -> Prims.bool) =
  fun projectee  ->
    match projectee with | Reifiable  -> true | uu____3691 -> false
  
let (uu___is_Reflectable : qualifier -> Prims.bool) =
  fun projectee  ->
    match projectee with | Reflectable  -> true | uu____3702 -> false
  
let (uu___is_Opaque : qualifier -> Prims.bool) =
  fun projectee  ->
    match projectee with | Opaque  -> true | uu____3713 -> false
  
let (uu___is_Logic : qualifier -> Prims.bool) =
  fun projectee  ->
    match projectee with | Logic  -> true | uu____3724 -> false
  
type qualifiers = qualifier Prims.list
type decoration =
  | Qualifier of qualifier 
  | DeclAttributes of term Prims.list 
let (uu___is_Qualifier : decoration -> Prims.bool) =
  fun projectee  ->
    match projectee with | Qualifier _0 -> true | uu____3750 -> false
  
let (__proj__Qualifier__item___0 : decoration -> qualifier) =
  fun projectee  -> match projectee with | Qualifier _0 -> _0 
let (uu___is_DeclAttributes : decoration -> Prims.bool) =
  fun projectee  ->
    match projectee with | DeclAttributes _0 -> true | uu____3771 -> false
  
let (__proj__DeclAttributes__item___0 : decoration -> term Prims.list) =
  fun projectee  -> match projectee with | DeclAttributes _0 -> _0 
type lift_op =
  | NonReifiableLift of term 
  | ReifiableLift of (term * term) 
  | LiftForFree of term 
let (uu___is_NonReifiableLift : lift_op -> Prims.bool) =
  fun projectee  ->
    match projectee with | NonReifiableLift _0 -> true | uu____3815 -> false
  
let (__proj__NonReifiableLift__item___0 : lift_op -> term) =
  fun projectee  -> match projectee with | NonReifiableLift _0 -> _0 
let (uu___is_ReifiableLift : lift_op -> Prims.bool) =
  fun projectee  ->
    match projectee with | ReifiableLift _0 -> true | uu____3838 -> false
  
let (__proj__ReifiableLift__item___0 : lift_op -> (term * term)) =
  fun projectee  -> match projectee with | ReifiableLift _0 -> _0 
let (uu___is_LiftForFree : lift_op -> Prims.bool) =
  fun projectee  ->
    match projectee with | LiftForFree _0 -> true | uu____3869 -> false
  
let (__proj__LiftForFree__item___0 : lift_op -> term) =
  fun projectee  -> match projectee with | LiftForFree _0 -> _0 
type lift =
  {
  msource: FStar_Ident.lid ;
  mdest: FStar_Ident.lid ;
  lift_op: lift_op }
let (__proj__Mklift__item__msource : lift -> FStar_Ident.lid) =
  fun projectee  ->
    match projectee with | { msource; mdest; lift_op = lift_op1;_} -> msource
  
let (__proj__Mklift__item__mdest : lift -> FStar_Ident.lid) =
  fun projectee  ->
    match projectee with | { msource; mdest; lift_op = lift_op1;_} -> mdest
  
let (__proj__Mklift__item__lift_op : lift -> lift_op) =
  fun projectee  ->
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
  fun projectee  ->
    match projectee with | SetOptions _0 -> true | uu____3953 -> false
  
let (__proj__SetOptions__item___0 : pragma -> Prims.string) =
  fun projectee  -> match projectee with | SetOptions _0 -> _0 
let (uu___is_ResetOptions : pragma -> Prims.bool) =
  fun projectee  ->
    match projectee with | ResetOptions _0 -> true | uu____3978 -> false
  
let (__proj__ResetOptions__item___0 :
  pragma -> Prims.string FStar_Pervasives_Native.option) =
  fun projectee  -> match projectee with | ResetOptions _0 -> _0 
let (uu___is_PushOptions : pragma -> Prims.bool) =
  fun projectee  ->
    match projectee with | PushOptions _0 -> true | uu____4009 -> false
  
let (__proj__PushOptions__item___0 :
  pragma -> Prims.string FStar_Pervasives_Native.option) =
  fun projectee  -> match projectee with | PushOptions _0 -> _0 
let (uu___is_PopOptions : pragma -> Prims.bool) =
  fun projectee  ->
    match projectee with | PopOptions  -> true | uu____4036 -> false
  
let (uu___is_RestartSolver : pragma -> Prims.bool) =
  fun projectee  ->
    match projectee with | RestartSolver  -> true | uu____4047 -> false
  
let (uu___is_LightOff : pragma -> Prims.bool) =
  fun projectee  ->
    match projectee with | LightOff  -> true | uu____4058 -> false
  
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
  fun projectee  ->
    match projectee with | TopLevelModule _0 -> true | uu____4252 -> false
  
let (__proj__TopLevelModule__item___0 : decl' -> FStar_Ident.lid) =
  fun projectee  -> match projectee with | TopLevelModule _0 -> _0 
let (uu___is_Open : decl' -> Prims.bool) =
  fun projectee  ->
    match projectee with | Open _0 -> true | uu____4271 -> false
  
let (__proj__Open__item___0 : decl' -> FStar_Ident.lid) =
  fun projectee  -> match projectee with | Open _0 -> _0 
let (uu___is_Friend : decl' -> Prims.bool) =
  fun projectee  ->
    match projectee with | Friend _0 -> true | uu____4290 -> false
  
let (__proj__Friend__item___0 : decl' -> FStar_Ident.lid) =
  fun projectee  -> match projectee with | Friend _0 -> _0 
let (uu___is_Include : decl' -> Prims.bool) =
  fun projectee  ->
    match projectee with | Include _0 -> true | uu____4309 -> false
  
let (__proj__Include__item___0 : decl' -> FStar_Ident.lid) =
  fun projectee  -> match projectee with | Include _0 -> _0 
let (uu___is_ModuleAbbrev : decl' -> Prims.bool) =
  fun projectee  ->
    match projectee with | ModuleAbbrev _0 -> true | uu____4332 -> false
  
let (__proj__ModuleAbbrev__item___0 :
  decl' -> (FStar_Ident.ident * FStar_Ident.lid)) =
  fun projectee  -> match projectee with | ModuleAbbrev _0 -> _0 
let (uu___is_TopLevelLet : decl' -> Prims.bool) =
  fun projectee  ->
    match projectee with | TopLevelLet _0 -> true | uu____4373 -> false
  
let (__proj__TopLevelLet__item___0 :
  decl' -> (let_qualifier * (pattern * term) Prims.list)) =
  fun projectee  -> match projectee with | TopLevelLet _0 -> _0 
let (uu___is_Tycon : decl' -> Prims.bool) =
  fun projectee  ->
    match projectee with | Tycon _0 -> true | uu____4432 -> false
  
let (__proj__Tycon__item___0 :
  decl' -> (Prims.bool * Prims.bool * tycon Prims.list)) =
  fun projectee  -> match projectee with | Tycon _0 -> _0 
let (uu___is_Val : decl' -> Prims.bool) =
  fun projectee  ->
    match projectee with | Val _0 -> true | uu____4485 -> false
  
let (__proj__Val__item___0 : decl' -> (FStar_Ident.ident * term)) =
  fun projectee  -> match projectee with | Val _0 -> _0 
let (uu___is_Exception : decl' -> Prims.bool) =
  fun projectee  ->
    match projectee with | Exception _0 -> true | uu____4522 -> false
  
let (__proj__Exception__item___0 :
  decl' -> (FStar_Ident.ident * term FStar_Pervasives_Native.option)) =
  fun projectee  -> match projectee with | Exception _0 -> _0 
let (uu___is_NewEffect : decl' -> Prims.bool) =
  fun projectee  ->
    match projectee with | NewEffect _0 -> true | uu____4559 -> false
  
let (__proj__NewEffect__item___0 : decl' -> effect_decl) =
  fun projectee  -> match projectee with | NewEffect _0 -> _0 
let (uu___is_LayeredEffect : decl' -> Prims.bool) =
  fun projectee  ->
    match projectee with | LayeredEffect _0 -> true | uu____4578 -> false
  
let (__proj__LayeredEffect__item___0 : decl' -> effect_decl) =
  fun projectee  -> match projectee with | LayeredEffect _0 -> _0 
let (uu___is_SubEffect : decl' -> Prims.bool) =
  fun projectee  ->
    match projectee with | SubEffect _0 -> true | uu____4597 -> false
  
let (__proj__SubEffect__item___0 : decl' -> lift) =
  fun projectee  -> match projectee with | SubEffect _0 -> _0 
let (uu___is_Polymonadic_bind : decl' -> Prims.bool) =
  fun projectee  ->
    match projectee with | Polymonadic_bind _0 -> true | uu____4624 -> false
  
let (__proj__Polymonadic_bind__item___0 :
  decl' -> (FStar_Ident.lid * FStar_Ident.lid * FStar_Ident.lid * term)) =
  fun projectee  -> match projectee with | Polymonadic_bind _0 -> _0 
let (uu___is_Pragma : decl' -> Prims.bool) =
  fun projectee  ->
    match projectee with | Pragma _0 -> true | uu____4667 -> false
  
let (__proj__Pragma__item___0 : decl' -> pragma) =
  fun projectee  -> match projectee with | Pragma _0 -> _0 
let (uu___is_Assume : decl' -> Prims.bool) =
  fun projectee  ->
    match projectee with | Assume _0 -> true | uu____4690 -> false
  
let (__proj__Assume__item___0 : decl' -> (FStar_Ident.ident * term)) =
  fun projectee  -> match projectee with | Assume _0 -> _0 
let (uu___is_Splice : decl' -> Prims.bool) =
  fun projectee  ->
    match projectee with | Splice _0 -> true | uu____4727 -> false
  
let (__proj__Splice__item___0 :
  decl' -> (FStar_Ident.ident Prims.list * term)) =
  fun projectee  -> match projectee with | Splice _0 -> _0 
let (__proj__Mkdecl__item__d : decl -> decl') =
  fun projectee  -> match projectee with | { d; drange; quals; attrs;_} -> d 
let (__proj__Mkdecl__item__drange : decl -> FStar_Range.range) =
  fun projectee  ->
    match projectee with | { d; drange; quals; attrs;_} -> drange
  
let (__proj__Mkdecl__item__quals : decl -> qualifiers) =
  fun projectee  ->
    match projectee with | { d; drange; quals; attrs;_} -> quals
  
let (__proj__Mkdecl__item__attrs : decl -> attributes_) =
  fun projectee  ->
    match projectee with | { d; drange; quals; attrs;_} -> attrs
  
let (uu___is_DefineEffect : effect_decl -> Prims.bool) =
  fun projectee  ->
    match projectee with | DefineEffect _0 -> true | uu____4816 -> false
  
let (__proj__DefineEffect__item___0 :
  effect_decl ->
    (FStar_Ident.ident * binder Prims.list * term * decl Prims.list))
  = fun projectee  -> match projectee with | DefineEffect _0 -> _0 
let (uu___is_RedefineEffect : effect_decl -> Prims.bool) =
  fun projectee  ->
    match projectee with | RedefineEffect _0 -> true | uu____4879 -> false
  
let (__proj__RedefineEffect__item___0 :
  effect_decl -> (FStar_Ident.ident * binder Prims.list * term)) =
  fun projectee  -> match projectee with | RedefineEffect _0 -> _0 
type modul =
  | Module of (FStar_Ident.lid * decl Prims.list) 
  | Interface of (FStar_Ident.lid * decl Prims.list * Prims.bool) 
let (uu___is_Module : modul -> Prims.bool) =
  fun projectee  ->
    match projectee with | Module _0 -> true | uu____4953 -> false
  
let (__proj__Module__item___0 : modul -> (FStar_Ident.lid * decl Prims.list))
  = fun projectee  -> match projectee with | Module _0 -> _0 
let (uu___is_Interface : modul -> Prims.bool) =
  fun projectee  ->
    match projectee with | Interface _0 -> true | uu____4999 -> false
  
let (__proj__Interface__item___0 :
  modul -> (FStar_Ident.lid * decl Prims.list * Prims.bool)) =
  fun projectee  -> match projectee with | Interface _0 -> _0 
type file = modul
type inputFragment = (file,decl Prims.list) FStar_Util.either
let (decl_drange : decl -> FStar_Range.range) = fun decl1  -> decl1.drange 
let (check_id : FStar_Ident.ident -> unit) =
  fun id  ->
    let first_char =
      let uu____5055 = FStar_Ident.text_of_id id  in
      FStar_String.substring uu____5055 Prims.int_zero Prims.int_one  in
    if (FStar_String.lowercase first_char) = first_char
    then ()
    else
      (let uu____5063 =
         let uu____5069 =
           let uu____5071 = FStar_Ident.text_of_id id  in
           FStar_Util.format1
             "Invalid identifer '%s'; expected a symbol that begins with a lower-case character"
             uu____5071
            in
         (FStar_Errors.Fatal_InvalidIdentifier, uu____5069)  in
       let uu____5075 = FStar_Ident.range_of_id id  in
       FStar_Errors.raise_error uu____5063 uu____5075)
  
let at_most_one :
  'uuuuuu5085 .
    Prims.string ->
      FStar_Range.range ->
        'uuuuuu5085 Prims.list -> 'uuuuuu5085 FStar_Pervasives_Native.option
  =
  fun s  ->
    fun r  ->
      fun l  ->
        match l with
        | x::[] -> FStar_Pervasives_Native.Some x
        | [] -> FStar_Pervasives_Native.None
        | uu____5110 ->
            let uu____5113 =
              let uu____5119 =
                FStar_Util.format1
                  "At most one %s is allowed on declarations" s
                 in
              (FStar_Errors.Fatal_MoreThanOneDeclaration, uu____5119)  in
            FStar_Errors.raise_error uu____5113 r
  
let (mk_decl : decl' -> FStar_Range.range -> decoration Prims.list -> decl) =
  fun d  ->
    fun r  ->
      fun decorations  ->
        let attributes_1 =
          let uu____5150 =
            FStar_List.choose
              (fun uu___0_5159  ->
                 match uu___0_5159 with
                 | DeclAttributes a -> FStar_Pervasives_Native.Some a
                 | uu____5169 -> FStar_Pervasives_Native.None) decorations
             in
          at_most_one "attribute set" r uu____5150  in
        let attributes_2 = FStar_Util.dflt [] attributes_1  in
        let qualifiers1 =
          FStar_List.choose
            (fun uu___1_5185  ->
               match uu___1_5185 with
               | Qualifier q -> FStar_Pervasives_Native.Some q
               | uu____5189 -> FStar_Pervasives_Native.None) decorations
           in
        { d; drange = r; quals = qualifiers1; attrs = attributes_2 }
  
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
            | uu____5279 ->
                let uu____5280 =
                  let uu____5287 = FStar_Ident.mk_ident ("-", rminus)  in
                  (uu____5287, [t])  in
                Op uu____5280
             in
          mk_term t1 r l
  
let (mk_pattern : pattern' -> FStar_Range.range -> pattern) =
  fun p  -> fun r  -> { pat = p; prange = r } 
let (un_curry_abs : pattern Prims.list -> term -> term') =
  fun ps  ->
    fun body  ->
      match body.tm with
      | Abs (p',body') -> Abs ((FStar_List.append ps p'), body')
      | uu____5326 -> Abs (ps, body)
  
let (mk_function :
  (pattern * term FStar_Pervasives_Native.option * term) Prims.list ->
    FStar_Range.range -> FStar_Range.range -> term)
  =
  fun branches  ->
    fun r1  ->
      fun r2  ->
        let x = FStar_Ident.gen r1  in
        let uu____5366 =
          let uu____5367 =
            let uu____5374 =
              let uu____5375 =
                let uu____5376 =
                  let uu____5391 =
                    let uu____5392 =
                      let uu____5393 = FStar_Ident.lid_of_ids [x]  in
                      Var uu____5393  in
                    mk_term uu____5392 r1 Expr  in
                  (uu____5391, branches)  in
                Match uu____5376  in
              mk_term uu____5375 r2 Expr  in
            ([mk_pattern (PatVar (x, FStar_Pervasives_Native.None)) r1],
              uu____5374)
             in
          Abs uu____5367  in
        mk_term uu____5366 r2 Expr
  
let (un_function :
  pattern -> term -> (pattern * term) FStar_Pervasives_Native.option) =
  fun p  ->
    fun tm  ->
      match ((p.pat), (tm.tm)) with
      | (PatVar uu____5431,Abs (pats,body)) ->
          FStar_Pervasives_Native.Some
            ((mk_pattern (PatApp (p, pats)) p.prange), body)
      | uu____5450 -> FStar_Pervasives_Native.None
  
let (lid_with_range :
  FStar_Ident.lident -> FStar_Range.range -> FStar_Ident.lident) =
  fun lid  ->
    fun r  ->
      let uu____5470 = FStar_Ident.path_of_lid lid  in
      FStar_Ident.lid_of_path uu____5470 r
  
let (consPat : FStar_Range.range -> pattern -> pattern -> pattern') =
  fun r  ->
    fun hd  ->
      fun tl  ->
        PatApp
          ((mk_pattern (PatName FStar_Parser_Const.cons_lid) r), [hd; tl])
  
let (consTerm : FStar_Range.range -> term -> term -> term) =
  fun r  ->
    fun hd  ->
      fun tl  ->
        mk_term
          (Construct
             (FStar_Parser_Const.cons_lid, [(hd, Nothing); (tl, Nothing)])) r
          Expr
  
let (lexConsTerm : FStar_Range.range -> term -> term -> term) =
  fun r  ->
    fun hd  ->
      fun tl  ->
        mk_term
          (Construct
             (FStar_Parser_Const.lexcons_lid, [(hd, Nothing); (tl, Nothing)]))
          r Expr
  
let (mkConsList : FStar_Range.range -> term Prims.list -> term) =
  fun r  ->
    fun elts  ->
      let nil = mk_term (Construct (FStar_Parser_Const.nil_lid, [])) r Expr
         in
      FStar_List.fold_right (fun e  -> fun tl  -> consTerm r e tl) elts nil
  
let (mkLexList : FStar_Range.range -> term Prims.list -> term) =
  fun r  ->
    fun elts  ->
      let nil =
        mk_term (Construct (FStar_Parser_Const.lextop_lid, [])) r Expr  in
      FStar_List.fold_right (fun e  -> fun tl  -> lexConsTerm r e tl) elts
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
        | uu____5665 ->
            (match t.tm with
             | Name s -> mk_term (Construct (s, args)) r Un
             | uu____5679 ->
                 FStar_List.fold_left
                   (fun t1  ->
                      fun uu____5689  ->
                        match uu____5689 with
                        | (a,imp1) -> mk_term (App (t1, a, imp1)) r Un) t
                   args)
  
let (mkRefSet : FStar_Range.range -> term Prims.list -> term) =
  fun r  ->
    fun elts  ->
      let uu____5711 =
        (FStar_Parser_Const.set_empty, FStar_Parser_Const.set_singleton,
          FStar_Parser_Const.set_union, FStar_Parser_Const.heap_addr_of_lid)
         in
      match uu____5711 with
      | (empty_lid,singleton_lid,union_lid,addr_of_lid) ->
          let empty =
            let uu____5725 =
              let uu____5726 = FStar_Ident.set_lid_range empty_lid r  in
              Var uu____5726  in
            mk_term uu____5725 r Expr  in
          let addr_of =
            let uu____5728 =
              let uu____5729 = FStar_Ident.set_lid_range addr_of_lid r  in
              Var uu____5729  in
            mk_term uu____5728 r Expr  in
          let singleton =
            let uu____5731 =
              let uu____5732 = FStar_Ident.set_lid_range singleton_lid r  in
              Var uu____5732  in
            mk_term uu____5731 r Expr  in
          let union =
            let uu____5734 =
              let uu____5735 = FStar_Ident.set_lid_range union_lid r  in
              Var uu____5735  in
            mk_term uu____5734 r Expr  in
          FStar_List.fold_right
            (fun e  ->
               fun tl  ->
                 let e1 = mkApp addr_of [(e, Nothing)] r  in
                 let single_e = mkApp singleton [(e1, Nothing)] r  in
                 mkApp union [(single_e, Nothing); (tl, Nothing)] r) elts
            empty
  
let (mkExplicitApp : term -> term Prims.list -> FStar_Range.range -> term) =
  fun t  ->
    fun args  ->
      fun r  ->
        match args with
        | [] -> t
        | uu____5792 ->
            (match t.tm with
             | Name s ->
                 let uu____5796 =
                   let uu____5797 =
                     let uu____5808 =
                       FStar_List.map (fun a  -> (a, Nothing)) args  in
                     (s, uu____5808)  in
                   Construct uu____5797  in
                 mk_term uu____5796 r Un
             | uu____5827 ->
                 FStar_List.fold_left
                   (fun t1  -> fun a  -> mk_term (App (t1, a, Nothing)) r Un)
                   t args)
  
let (unit_const : FStar_Range.range -> term) =
  fun r  -> mk_term (Const FStar_Const.Const_unit) r Expr 
let (mkAdmitMagic : FStar_Range.range -> term) =
  fun r  ->
    let admit =
      let admit_name =
        let uu____5846 =
          let uu____5847 =
            FStar_Ident.set_lid_range FStar_Parser_Const.admit_lid r  in
          Var uu____5847  in
        mk_term uu____5846 r Expr  in
      mkExplicitApp admit_name [unit_const r] r  in
    let magic =
      let magic_name =
        let uu____5850 =
          let uu____5851 =
            FStar_Ident.set_lid_range FStar_Parser_Const.magic_lid r  in
          Var uu____5851  in
        mk_term uu____5850 r Expr  in
      mkExplicitApp magic_name [unit_const r] r  in
    let admit_magic = mk_term (Seq (admit, magic)) r Expr  in admit_magic
  
let mkWildAdmitMagic :
  'uuuuuu5858 .
    FStar_Range.range ->
      (pattern * 'uuuuuu5858 FStar_Pervasives_Native.option * term)
  =
  fun r  ->
    let uu____5872 = mkAdmitMagic r  in
    ((mk_pattern (PatWild FStar_Pervasives_Native.None) r),
      FStar_Pervasives_Native.None, uu____5872)
  
let focusBranches :
  'uuuuuu5882 .
    (Prims.bool * (pattern * 'uuuuuu5882 FStar_Pervasives_Native.option *
      term)) Prims.list ->
      FStar_Range.range ->
        (pattern * 'uuuuuu5882 FStar_Pervasives_Native.option * term)
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
            let uu____5982 =
              FStar_List.filter FStar_Pervasives_Native.fst branches  in
            FStar_All.pipe_right uu____5982
              (FStar_List.map FStar_Pervasives_Native.snd)
             in
          let uu____6075 =
            let uu____6086 = mkWildAdmitMagic r  in [uu____6086]  in
          FStar_List.append focussed uu____6075))
      else
        FStar_All.pipe_right branches
          (FStar_List.map FStar_Pervasives_Native.snd)
  
let focusLetBindings :
  'uuuuuu6183 .
    (Prims.bool * ('uuuuuu6183 * term)) Prims.list ->
      FStar_Range.range -> ('uuuuuu6183 * term) Prims.list
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
           (fun uu____6264  ->
              match uu____6264 with
              | (f,lb) ->
                  if f
                  then lb
                  else
                    (let uu____6297 = mkAdmitMagic r  in
                     ((FStar_Pervasives_Native.fst lb), uu____6297))) lbs)
      else
        FStar_All.pipe_right lbs (FStar_List.map FStar_Pervasives_Native.snd)
  
let focusAttrLetBindings :
  'uuuuuu6344 'uuuuuu6345 .
    ('uuuuuu6344 * (Prims.bool * ('uuuuuu6345 * term))) Prims.list ->
      FStar_Range.range -> ('uuuuuu6344 * ('uuuuuu6345 * term)) Prims.list
  =
  fun lbs  ->
    fun r  ->
      let should_filter =
        FStar_Util.for_some
          (fun uu____6415  ->
             match uu____6415 with | (attr,(focus,uu____6432)) -> focus) lbs
         in
      if should_filter
      then
        (FStar_Errors.log_issue r
           (FStar_Errors.Warning_Filtered,
             "Focusing on only some cases in this (mutually) recursive definition");
         FStar_List.map
           (fun uu____6491  ->
              match uu____6491 with
              | (attr,(f,lb)) ->
                  if f
                  then (attr, lb)
                  else
                    (let uu____6550 =
                       let uu____6555 = mkAdmitMagic r  in
                       ((FStar_Pervasives_Native.fst lb), uu____6555)  in
                     (attr, uu____6550))) lbs)
      else
        FStar_All.pipe_right lbs
          (FStar_List.map
             (fun uu____6612  ->
                match uu____6612 with | (attr,(uu____6635,lb)) -> (attr, lb)))
  
let (mkFsTypApp : term -> term Prims.list -> FStar_Range.range -> term) =
  fun t  ->
    fun args  ->
      fun r  ->
        let uu____6680 = FStar_List.map (fun a  -> (a, FsTypApp)) args  in
        mkApp t uu____6680 r
  
let (mkTuple : term Prims.list -> FStar_Range.range -> term) =
  fun args  ->
    fun r  ->
      let cons =
        FStar_Parser_Const.mk_tuple_data_lid (FStar_List.length args) r  in
      let uu____6709 = FStar_List.map (fun x  -> (x, Nothing)) args  in
      mkApp (mk_term (Name cons) r Expr) uu____6709 r
  
let (mkDTuple : term Prims.list -> FStar_Range.range -> term) =
  fun args  ->
    fun r  ->
      let cons =
        FStar_Parser_Const.mk_dtuple_data_lid (FStar_List.length args) r  in
      let uu____6738 = FStar_List.map (fun x  -> (x, Nothing)) args  in
      mkApp (mk_term (Name cons) r Expr) uu____6738 r
  
let (mkRefinedBinder :
  FStar_Ident.ident ->
    term ->
      Prims.bool ->
        term FStar_Pervasives_Native.option ->
          FStar_Range.range ->
            arg_qualifier FStar_Pervasives_Native.option -> binder)
  =
  fun id  ->
    fun t  ->
      fun should_bind_var  ->
        fun refopt  ->
          fun m  ->
            fun implicit  ->
              let b = mk_binder (Annotated (id, t)) m Type_level implicit  in
              match refopt with
              | FStar_Pervasives_Native.None  -> b
              | FStar_Pervasives_Native.Some phi ->
                  if should_bind_var
                  then
                    mk_binder
                      (Annotated
                         (id, (mk_term (Refine (b, phi)) m Type_level))) m
                      Type_level implicit
                  else
                    (let x = FStar_Ident.gen t.range  in
                     let b1 =
                       mk_binder (Annotated (x, t)) m Type_level implicit  in
                     mk_binder
                       (Annotated
                          (id, (mk_term (Refine (b1, phi)) m Type_level))) m
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
                       | PatVar (x,uu____6840) ->
                           mk_term
                             (Refine
                                ((mk_binder (Annotated (x, t)) t_range
                                    Type_level FStar_Pervasives_Native.None),
                                  phi)) range Type_level
                       | uu____6845 ->
                           let x = FStar_Ident.gen t_range  in
                           let phi1 =
                             let x_var =
                               let uu____6849 =
                                 let uu____6850 = FStar_Ident.lid_of_ids [x]
                                    in
                                 Var uu____6850  in
                               mk_term uu____6849 phi.range Formula  in
                             let pat_branch =
                               (pat, FStar_Pervasives_Native.None, phi)  in
                             let otherwise_branch =
                               let uu____6871 =
                                 let uu____6872 =
                                   let uu____6873 =
                                     FStar_Ident.lid_of_path ["False"]
                                       phi.range
                                      in
                                   Name uu____6873  in
                                 mk_term uu____6872 phi.range Formula  in
                               ((mk_pattern
                                   (PatWild FStar_Pervasives_Native.None)
                                   phi.range), FStar_Pervasives_Native.None,
                                 uu____6871)
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
        ({ b = Annotated (x,t); brange = uu____6964; blevel = uu____6965;
           aqual = uu____6966;_},t')
        ->
        FStar_Pervasives_Native.Some
          (x, t, (FStar_Pervasives_Native.Some t'))
    | Paren t -> extract_named_refinement t
    | uu____6981 -> FStar_Pervasives_Native.None
  
let rec (as_mlist :
  ((FStar_Ident.lid * decl) * decl Prims.list) -> decl Prims.list -> modul) =
  fun cur  ->
    fun ds  ->
      let uu____7025 = cur  in
      match uu____7025 with
      | ((m_name,m_decl),cur1) ->
          (match ds with
           | [] -> Module (m_name, (m_decl :: (FStar_List.rev cur1)))
           | d::ds1 ->
               (match d.d with
                | TopLevelModule m' ->
                    FStar_Errors.raise_error
                      (FStar_Errors.Fatal_UnexpectedModuleDeclaration,
                        "Unexpected module declaration") d.drange
                | uu____7056 -> as_mlist ((m_name, m_decl), (d :: cur1)) ds1))
  
let (as_frag :
  Prims.bool -> FStar_Range.range -> decl Prims.list -> inputFragment) =
  fun is_light  ->
    fun light_range  ->
      fun ds  ->
        let uu____7085 =
          match ds with
          | d::ds1 -> (d, ds1)
          | [] -> FStar_Exn.raise FStar_Errors.Empty_frag  in
        match uu____7085 with
        | (d,ds1) ->
            (match d.d with
             | TopLevelModule m ->
                 let ds2 =
                   if is_light
                   then
                     let uu____7123 =
                       mk_decl (Pragma LightOff) light_range []  in
                     uu____7123 :: ds1
                   else ds1  in
                 let m1 = as_mlist ((m, d), []) ds2  in FStar_Util.Inl m1
             | uu____7135 ->
                 let ds2 = d :: ds1  in
                 (FStar_List.iter
                    (fun uu___2_7145  ->
                       match uu___2_7145 with
                       | { d = TopLevelModule uu____7146; drange = r;
                           quals = uu____7148; attrs = uu____7149;_} ->
                           FStar_Errors.raise_error
                             (FStar_Errors.Fatal_UnexpectedModuleDeclaration,
                               "Unexpected module declaration") r
                       | uu____7152 -> ()) ds2;
                  FStar_Util.Inr ds2))
  
let (compile_op :
  Prims.int -> Prims.string -> FStar_Range.range -> Prims.string) =
  fun arity  ->
    fun s  ->
      fun r  ->
        let name_of_char uu___3_7183 =
          match uu___3_7183 with
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
        | uu____7253 ->
            let uu____7255 =
              let uu____7257 =
                let uu____7261 = FStar_String.list_of_string s  in
                FStar_List.map name_of_char uu____7261  in
              FStar_String.concat "_" uu____7257  in
            Prims.op_Hat "op_" uu____7255
  
let (compile_op' : Prims.string -> FStar_Range.range -> Prims.string) =
  fun s  -> fun r  -> compile_op (~- Prims.int_one) s r 
let (string_of_fsdoc :
  (Prims.string * (Prims.string * Prims.string) Prims.list) -> Prims.string)
  =
  fun uu____7303  ->
    match uu____7303 with
    | (comment,keywords) ->
        let uu____7338 =
          let uu____7340 =
            FStar_List.map
              (fun uu____7354  ->
                 match uu____7354 with
                 | (k,v) -> Prims.op_Hat k (Prims.op_Hat "->" v)) keywords
             in
          FStar_String.concat "," uu____7340  in
        Prims.op_Hat comment uu____7338
  
let (string_of_let_qualifier : let_qualifier -> Prims.string) =
  fun uu___4_7376  ->
    match uu___4_7376 with | NoLetQualifier  -> "" | Rec  -> "rec"
  
let to_string_l :
  'uuuuuu7389 .
    Prims.string ->
      ('uuuuuu7389 -> Prims.string) -> 'uuuuuu7389 Prims.list -> Prims.string
  =
  fun sep  ->
    fun f  ->
      fun l  ->
        let uu____7419 = FStar_List.map f l  in
        FStar_String.concat sep uu____7419
  
let (imp_to_string : imp -> Prims.string) =
  fun uu___5_7430  ->
    match uu___5_7430 with | Hash  -> "#" | uu____7433 -> ""
  
let rec (term_to_string : term -> Prims.string) =
  fun x  ->
    match x.tm with
    | Wild  -> "_"
    | Requires (t,uu____7476) ->
        let uu____7483 = term_to_string t  in
        FStar_Util.format1 "(requires %s)" uu____7483
    | Ensures (t,uu____7487) ->
        let uu____7494 = term_to_string t  in
        FStar_Util.format1 "(ensures %s)" uu____7494
    | Labeled (t,l,uu____7499) ->
        let uu____7504 = term_to_string t  in
        FStar_Util.format2 "(labeled %s %s)" l uu____7504
    | Const c -> FStar_Parser_Const.const_to_string c
    | Op (s,xs) ->
        let uu____7514 = FStar_Ident.text_of_id s  in
        let uu____7516 =
          let uu____7518 =
            FStar_List.map
              (fun x1  -> FStar_All.pipe_right x1 term_to_string) xs
             in
          FStar_String.concat ", " uu____7518  in
        FStar_Util.format2 "%s(%s)" uu____7514 uu____7516
    | Tvar id -> FStar_Ident.text_of_id id
    | Uvar id -> FStar_Ident.text_of_id id
    | Var l -> FStar_Ident.string_of_lid l
    | Name l -> FStar_Ident.string_of_lid l
    | Projector (rec_lid,field_id) ->
        let uu____7534 = FStar_Ident.string_of_lid rec_lid  in
        let uu____7536 = FStar_Ident.text_of_id field_id  in
        FStar_Util.format2 "%s?.%s" uu____7534 uu____7536
    | Construct (l,args) ->
        let uu____7553 = FStar_Ident.string_of_lid l  in
        let uu____7555 =
          to_string_l " "
            (fun uu____7566  ->
               match uu____7566 with
               | (a,imp1) ->
                   let uu____7574 = term_to_string a  in
                   FStar_Util.format2 "%s%s" (imp_to_string imp1) uu____7574)
            args
           in
        FStar_Util.format2 "(%s %s)" uu____7553 uu____7555
    | Abs (pats,t) ->
        let uu____7584 = to_string_l " " pat_to_string pats  in
        let uu____7587 = FStar_All.pipe_right t term_to_string  in
        FStar_Util.format2 "(fun %s -> %s)" uu____7584 uu____7587
    | App (t1,t2,imp1) ->
        let uu____7594 = FStar_All.pipe_right t1 term_to_string  in
        let uu____7597 = FStar_All.pipe_right t2 term_to_string  in
        FStar_Util.format3 "%s %s%s" uu____7594 (imp_to_string imp1)
          uu____7597
    | Let (Rec ,(a,(p,b))::lbs,body) ->
        let uu____7658 = attrs_opt_to_string a  in
        let uu____7660 =
          let uu____7662 = FStar_All.pipe_right p pat_to_string  in
          let uu____7665 = FStar_All.pipe_right b term_to_string  in
          FStar_Util.format2 "%s=%s" uu____7662 uu____7665  in
        let uu____7669 =
          to_string_l " "
            (fun uu____7691  ->
               match uu____7691 with
               | (a1,(p1,b1)) ->
                   let uu____7720 = attrs_opt_to_string a1  in
                   let uu____7722 = FStar_All.pipe_right p1 pat_to_string  in
                   let uu____7725 = FStar_All.pipe_right b1 term_to_string
                      in
                   FStar_Util.format3 "%sand %s=%s" uu____7720 uu____7722
                     uu____7725) lbs
           in
        let uu____7729 = FStar_All.pipe_right body term_to_string  in
        FStar_Util.format4 "%slet rec %s%s in %s" uu____7658 uu____7660
          uu____7669 uu____7729
    | Let (q,(attrs,(pat,tm))::[],body) ->
        let uu____7788 = attrs_opt_to_string attrs  in
        let uu____7790 = FStar_All.pipe_right pat pat_to_string  in
        let uu____7793 = FStar_All.pipe_right tm term_to_string  in
        let uu____7796 = FStar_All.pipe_right body term_to_string  in
        FStar_Util.format5 "%slet %s %s = %s in %s" uu____7788
          (string_of_let_qualifier q) uu____7790 uu____7793 uu____7796
    | Let (uu____7800,uu____7801,uu____7802) ->
        FStar_Errors.raise_error
          (FStar_Errors.Fatal_EmptySurfaceLet,
            "Internal error: found an invalid surface Let") x.range
    | LetOpen (lid,t) ->
        let uu____7836 = FStar_Ident.string_of_lid lid  in
        let uu____7838 = term_to_string t  in
        FStar_Util.format2 "let open %s in %s" uu____7836 uu____7838
    | Seq (t1,t2) ->
        let uu____7843 = FStar_All.pipe_right t1 term_to_string  in
        let uu____7846 = FStar_All.pipe_right t2 term_to_string  in
        FStar_Util.format2 "%s; %s" uu____7843 uu____7846
    | Bind (id,t1,t2) ->
        let uu____7853 = FStar_Ident.text_of_id id  in
        let uu____7855 = term_to_string t1  in
        let uu____7857 = term_to_string t2  in
        FStar_Util.format3 "%s <- %s; %s" uu____7853 uu____7855 uu____7857
    | If (t1,t2,t3) ->
        let uu____7863 = FStar_All.pipe_right t1 term_to_string  in
        let uu____7866 = FStar_All.pipe_right t2 term_to_string  in
        let uu____7869 = FStar_All.pipe_right t3 term_to_string  in
        FStar_Util.format3 "if %s then %s else %s" uu____7863 uu____7866
          uu____7869
    | Match (t,branches) ->
        let s =
          match x.tm with
          | Match uu____7898 -> "match"
          | TryWith uu____7914 -> "try"
          | uu____7930 -> failwith "impossible"  in
        let uu____7933 = FStar_All.pipe_right t term_to_string  in
        let uu____7936 =
          to_string_l " | "
            (fun uu____7954  ->
               match uu____7954 with
               | (p,w,e) ->
                   let uu____7971 = FStar_All.pipe_right p pat_to_string  in
                   let uu____7974 =
                     match w with
                     | FStar_Pervasives_Native.None  -> ""
                     | FStar_Pervasives_Native.Some e1 ->
                         let uu____7979 = term_to_string e1  in
                         FStar_Util.format1 "when %s" uu____7979
                      in
                   let uu____7982 = FStar_All.pipe_right e term_to_string  in
                   FStar_Util.format3 "%s %s -> %s" uu____7971 uu____7974
                     uu____7982) branches
           in
        FStar_Util.format3 "%s %s with %s" s uu____7933 uu____7936
    | TryWith (t,branches) ->
        let s =
          match x.tm with
          | Match uu____8012 -> "match"
          | TryWith uu____8028 -> "try"
          | uu____8044 -> failwith "impossible"  in
        let uu____8047 = FStar_All.pipe_right t term_to_string  in
        let uu____8050 =
          to_string_l " | "
            (fun uu____8068  ->
               match uu____8068 with
               | (p,w,e) ->
                   let uu____8085 = FStar_All.pipe_right p pat_to_string  in
                   let uu____8088 =
                     match w with
                     | FStar_Pervasives_Native.None  -> ""
                     | FStar_Pervasives_Native.Some e1 ->
                         let uu____8093 = term_to_string e1  in
                         FStar_Util.format1 "when %s" uu____8093
                      in
                   let uu____8096 = FStar_All.pipe_right e term_to_string  in
                   FStar_Util.format3 "%s %s -> %s" uu____8085 uu____8088
                     uu____8096) branches
           in
        FStar_Util.format3 "%s %s with %s" s uu____8047 uu____8050
    | Ascribed (t1,t2,FStar_Pervasives_Native.None ) ->
        let uu____8105 = FStar_All.pipe_right t1 term_to_string  in
        let uu____8108 = FStar_All.pipe_right t2 term_to_string  in
        FStar_Util.format2 "(%s : %s)" uu____8105 uu____8108
    | Ascribed (t1,t2,FStar_Pervasives_Native.Some tac) ->
        let uu____8117 = FStar_All.pipe_right t1 term_to_string  in
        let uu____8120 = FStar_All.pipe_right t2 term_to_string  in
        let uu____8123 = FStar_All.pipe_right tac term_to_string  in
        FStar_Util.format3 "(%s : %s by %s)" uu____8117 uu____8120 uu____8123
    | Record (FStar_Pervasives_Native.Some e,fields) ->
        let uu____8143 = FStar_All.pipe_right e term_to_string  in
        let uu____8146 =
          to_string_l " "
            (fun uu____8158  ->
               match uu____8158 with
               | (l,e1) ->
                   let uu____8166 = FStar_Ident.string_of_lid l  in
                   let uu____8168 = FStar_All.pipe_right e1 term_to_string
                      in
                   FStar_Util.format2 "%s=%s" uu____8166 uu____8168) fields
           in
        FStar_Util.format2 "{%s with %s}" uu____8143 uu____8146
    | Record (FStar_Pervasives_Native.None ,fields) ->
        let uu____8188 =
          to_string_l " "
            (fun uu____8200  ->
               match uu____8200 with
               | (l,e) ->
                   let uu____8208 = FStar_Ident.string_of_lid l  in
                   let uu____8210 = FStar_All.pipe_right e term_to_string  in
                   FStar_Util.format2 "%s=%s" uu____8208 uu____8210) fields
           in
        FStar_Util.format1 "{%s}" uu____8188
    | Project (e,l) ->
        let uu____8217 = FStar_All.pipe_right e term_to_string  in
        let uu____8220 = FStar_Ident.string_of_lid l  in
        FStar_Util.format2 "%s.%s" uu____8217 uu____8220
    | Product ([],t) -> term_to_string t
    | Product (b::hd::tl,t) ->
        term_to_string
          (mk_term
             (Product
                ([b], (mk_term (Product ((hd :: tl), t)) x.range x.level)))
             x.range x.level)
    | Product (b::[],t) when x.level = Type_level ->
        let uu____8242 = FStar_All.pipe_right b binder_to_string  in
        let uu____8245 = FStar_All.pipe_right t term_to_string  in
        FStar_Util.format2 "%s -> %s" uu____8242 uu____8245
    | Product (b::[],t) when x.level = Kind ->
        let uu____8253 = FStar_All.pipe_right b binder_to_string  in
        let uu____8256 = FStar_All.pipe_right t term_to_string  in
        FStar_Util.format2 "%s => %s" uu____8253 uu____8256
    | Sum (binders,t) ->
        let uu____8274 =
          FStar_All.pipe_right (FStar_List.append binders [FStar_Util.Inr t])
            (FStar_List.map
               (fun uu___6_8306  ->
                  match uu___6_8306 with
                  | FStar_Util.Inl b -> binder_to_string b
                  | FStar_Util.Inr t1 -> term_to_string t1))
           in
        FStar_All.pipe_right uu____8274 (FStar_String.concat " & ")
    | QForall (bs,(uu____8320,pats),t) ->
        let uu____8349 = to_string_l " " binder_to_string bs  in
        let uu____8352 =
          to_string_l " \\/ " (to_string_l "; " term_to_string) pats  in
        let uu____8358 = FStar_All.pipe_right t term_to_string  in
        FStar_Util.format3 "forall %s.{:pattern %s} %s" uu____8349 uu____8352
          uu____8358
    | QExists (bs,(uu____8363,pats),t) ->
        let uu____8392 = to_string_l " " binder_to_string bs  in
        let uu____8395 =
          to_string_l " \\/ " (to_string_l "; " term_to_string) pats  in
        let uu____8401 = FStar_All.pipe_right t term_to_string  in
        FStar_Util.format3 "exists %s.{:pattern %s} %s" uu____8392 uu____8395
          uu____8401
    | Refine (b,t) ->
        let uu____8407 = FStar_All.pipe_right b binder_to_string  in
        let uu____8410 = FStar_All.pipe_right t term_to_string  in
        FStar_Util.format2 "%s:{%s}" uu____8407 uu____8410
    | NamedTyp (x1,t) ->
        let uu____8416 = FStar_Ident.text_of_id x1  in
        let uu____8418 = FStar_All.pipe_right t term_to_string  in
        FStar_Util.format2 "%s:%s" uu____8416 uu____8418
    | Paren t ->
        let uu____8423 = FStar_All.pipe_right t term_to_string  in
        FStar_Util.format1 "(%s)" uu____8423
    | Product (bs,t) ->
        let uu____8433 =
          let uu____8435 =
            FStar_All.pipe_right bs (FStar_List.map binder_to_string)  in
          FStar_All.pipe_right uu____8435 (FStar_String.concat ",")  in
        let uu____8450 = FStar_All.pipe_right t term_to_string  in
        FStar_Util.format2 "Unidentified product: [%s] %s" uu____8433
          uu____8450
    | Discrim lid ->
        let uu____8455 = FStar_Ident.string_of_lid lid  in
        FStar_Util.format1 "%s?" uu____8455
    | Attributes ts ->
        let uu____8461 =
          let uu____8463 = FStar_List.map term_to_string ts  in
          FStar_All.pipe_left (FStar_String.concat " ") uu____8463  in
        FStar_Util.format1 "(attributes %s)" uu____8461
    | Antiquote t ->
        let uu____8475 = term_to_string t  in
        FStar_Util.format1 "(`#%s)" uu____8475
    | Quote (t,Static ) ->
        let uu____8479 = term_to_string t  in
        FStar_Util.format1 "(`(%s))" uu____8479
    | Quote (t,Dynamic ) ->
        let uu____8483 = term_to_string t  in
        FStar_Util.format1 "quote (%s)" uu____8483
    | VQuote t ->
        let uu____8487 = term_to_string t  in
        FStar_Util.format1 "`%%%s" uu____8487
    | CalcProof (rel,init,steps) ->
        let uu____8497 = term_to_string rel  in
        let uu____8499 = term_to_string init  in
        let uu____8501 =
          let uu____8503 = FStar_List.map calc_step_to_string steps  in
          FStar_All.pipe_left (FStar_String.concat " ") uu____8503  in
        FStar_Util.format3 "calc (%s) { %s %s }" uu____8497 uu____8499
          uu____8501

and (calc_step_to_string : calc_step -> Prims.string) =
  fun uu____8514  ->
    match uu____8514 with
    | CalcStep (rel,just,next) ->
        let uu____8519 = term_to_string rel  in
        let uu____8521 = term_to_string just  in
        let uu____8523 = term_to_string next  in
        FStar_Util.format3 "%s{ %s } %s" uu____8519 uu____8521 uu____8523

and (binder_to_string : binder -> Prims.string) =
  fun x  ->
    let s =
      match x.b with
      | Variable i -> FStar_Ident.text_of_id i
      | TVariable i ->
          let uu____8532 = FStar_Ident.text_of_id i  in
          FStar_Util.format1 "%s:_" uu____8532
      | TAnnotated (i,t) ->
          let uu____8537 = FStar_Ident.text_of_id i  in
          let uu____8539 = FStar_All.pipe_right t term_to_string  in
          FStar_Util.format2 "%s:%s" uu____8537 uu____8539
      | Annotated (i,t) ->
          let uu____8545 = FStar_Ident.text_of_id i  in
          let uu____8547 = FStar_All.pipe_right t term_to_string  in
          FStar_Util.format2 "%s:%s" uu____8545 uu____8547
      | NoName t -> FStar_All.pipe_right t term_to_string  in
    let uu____8553 = aqual_to_string x.aqual  in
    FStar_Util.format2 "%s%s" uu____8553 s

and (aqual_to_string :
  arg_qualifier FStar_Pervasives_Native.option -> Prims.string) =
  fun uu___7_8556  ->
    match uu___7_8556 with
    | FStar_Pervasives_Native.Some (Equality ) -> "$"
    | FStar_Pervasives_Native.Some (Implicit ) -> "#"
    | uu____8562 -> ""

and (pat_to_string : pattern -> Prims.string) =
  fun x  ->
    match x.pat with
    | PatWild (FStar_Pervasives_Native.None ) -> "_"
    | PatWild uu____8569 -> "#_"
    | PatConst c -> FStar_Parser_Const.const_to_string c
    | PatApp (p,ps) ->
        let uu____8580 = FStar_All.pipe_right p pat_to_string  in
        let uu____8583 = to_string_l " " pat_to_string ps  in
        FStar_Util.format2 "(%s %s)" uu____8580 uu____8583
    | PatTvar (i,aq) ->
        let uu____8593 = aqual_to_string aq  in
        let uu____8595 = FStar_Ident.text_of_id i  in
        FStar_Util.format2 "%s%s" uu____8593 uu____8595
    | PatVar (i,aq) ->
        let uu____8604 = aqual_to_string aq  in
        let uu____8606 = FStar_Ident.text_of_id i  in
        FStar_Util.format2 "%s%s" uu____8604 uu____8606
    | PatName l -> FStar_Ident.string_of_lid l
    | PatList l ->
        let uu____8613 = to_string_l "; " pat_to_string l  in
        FStar_Util.format1 "[%s]" uu____8613
    | PatTuple (l,false ) ->
        let uu____8624 = to_string_l ", " pat_to_string l  in
        FStar_Util.format1 "(%s)" uu____8624
    | PatTuple (l,true ) ->
        let uu____8635 = to_string_l ", " pat_to_string l  in
        FStar_Util.format1 "(|%s|)" uu____8635
    | PatRecord l ->
        let uu____8646 =
          to_string_l "; "
            (fun uu____8658  ->
               match uu____8658 with
               | (f,e) ->
                   let uu____8666 = FStar_Ident.string_of_lid f  in
                   let uu____8668 = FStar_All.pipe_right e pat_to_string  in
                   FStar_Util.format2 "%s=%s" uu____8666 uu____8668) l
           in
        FStar_Util.format1 "{%s}" uu____8646
    | PatOr l -> to_string_l "|\n " pat_to_string l
    | PatOp op ->
        let uu____8678 = FStar_Ident.text_of_id op  in
        FStar_Util.format1 "(%s)" uu____8678
    | PatAscribed (p,(t,FStar_Pervasives_Native.None )) ->
        let uu____8691 = FStar_All.pipe_right p pat_to_string  in
        let uu____8694 = FStar_All.pipe_right t term_to_string  in
        FStar_Util.format2 "(%s:%s)" uu____8691 uu____8694
    | PatAscribed (p,(t,FStar_Pervasives_Native.Some tac)) ->
        let uu____8709 = FStar_All.pipe_right p pat_to_string  in
        let uu____8712 = FStar_All.pipe_right t term_to_string  in
        let uu____8715 = FStar_All.pipe_right tac term_to_string  in
        FStar_Util.format3 "(%s:%s by %s)" uu____8709 uu____8712 uu____8715

and (attrs_opt_to_string :
  term Prims.list FStar_Pervasives_Native.option -> Prims.string) =
  fun uu___8_8719  ->
    match uu___8_8719 with
    | FStar_Pervasives_Native.None  -> ""
    | FStar_Pervasives_Native.Some attrs ->
        let uu____8733 =
          let uu____8735 = FStar_List.map term_to_string attrs  in
          FStar_All.pipe_right uu____8735 (FStar_String.concat "; ")  in
        FStar_Util.format1 "[@ %s]" uu____8733

let rec (head_id_of_pat : pattern -> FStar_Ident.lident Prims.list) =
  fun p  ->
    match p.pat with
    | PatName l -> [l]
    | PatVar (i,uu____8758) ->
        let uu____8763 = FStar_Ident.lid_of_ids [i]  in [uu____8763]
    | PatApp (p1,uu____8765) -> head_id_of_pat p1
    | PatAscribed (p1,uu____8771) -> head_id_of_pat p1
    | uu____8784 -> []
  
let lids_of_let :
  'uuuuuu8790 .
    (pattern * 'uuuuuu8790) Prims.list -> FStar_Ident.lident Prims.list
  =
  fun defs  ->
    FStar_All.pipe_right defs
      (FStar_List.collect
         (fun uu____8825  ->
            match uu____8825 with | (p,uu____8833) -> head_id_of_pat p))
  
let (id_of_tycon : tycon -> Prims.string) =
  fun uu___9_8840  ->
    match uu___9_8840 with
    | TyconAbstract (i,uu____8843,uu____8844) -> FStar_Ident.text_of_id i
    | TyconAbbrev (i,uu____8854,uu____8855,uu____8856) ->
        FStar_Ident.text_of_id i
    | TyconRecord (i,uu____8866,uu____8867,uu____8868) ->
        FStar_Ident.text_of_id i
    | TyconVariant (i,uu____8890,uu____8891,uu____8892) ->
        FStar_Ident.text_of_id i
  
let (decl_to_string : decl -> Prims.string) =
  fun d  ->
    match d.d with
    | TopLevelModule l ->
        let uu____8932 = FStar_Ident.string_of_lid l  in
        Prims.op_Hat "module " uu____8932
    | Open l ->
        let uu____8936 = FStar_Ident.string_of_lid l  in
        Prims.op_Hat "open " uu____8936
    | Friend l ->
        let uu____8940 = FStar_Ident.string_of_lid l  in
        Prims.op_Hat "friend " uu____8940
    | Include l ->
        let uu____8944 = FStar_Ident.string_of_lid l  in
        Prims.op_Hat "include " uu____8944
    | ModuleAbbrev (i,l) ->
        let uu____8949 = FStar_Ident.text_of_id i  in
        let uu____8951 = FStar_Ident.string_of_lid l  in
        FStar_Util.format2 "module %s = %s" uu____8949 uu____8951
    | TopLevelLet (uu____8954,pats) ->
        let uu____8968 =
          let uu____8970 =
            let uu____8974 = lids_of_let pats  in
            FStar_All.pipe_right uu____8974
              (FStar_List.map (fun l  -> FStar_Ident.string_of_lid l))
             in
          FStar_All.pipe_right uu____8970 (FStar_String.concat ", ")  in
        Prims.op_Hat "let " uu____8968
    | Assume (i,uu____8992) ->
        let uu____8993 = FStar_Ident.text_of_id i  in
        Prims.op_Hat "assume " uu____8993
    | Tycon (uu____8996,uu____8997,tys) ->
        let uu____9007 =
          let uu____9009 =
            FStar_All.pipe_right tys (FStar_List.map id_of_tycon)  in
          FStar_All.pipe_right uu____9009 (FStar_String.concat ", ")  in
        Prims.op_Hat "type " uu____9007
    | Val (i,uu____9026) ->
        let uu____9027 = FStar_Ident.text_of_id i  in
        Prims.op_Hat "val " uu____9027
    | Exception (i,uu____9031) ->
        let uu____9036 = FStar_Ident.text_of_id i  in
        Prims.op_Hat "exception " uu____9036
    | NewEffect (DefineEffect (i,uu____9040,uu____9041,uu____9042)) ->
        let uu____9051 = FStar_Ident.text_of_id i  in
        Prims.op_Hat "new_effect " uu____9051
    | NewEffect (RedefineEffect (i,uu____9055,uu____9056)) ->
        let uu____9061 = FStar_Ident.text_of_id i  in
        Prims.op_Hat "new_effect " uu____9061
    | LayeredEffect (DefineEffect (i,uu____9065,uu____9066,uu____9067)) ->
        let uu____9076 = FStar_Ident.text_of_id i  in
        Prims.op_Hat "layered_effect " uu____9076
    | LayeredEffect (RedefineEffect (i,uu____9080,uu____9081)) ->
        let uu____9086 = FStar_Ident.text_of_id i  in
        Prims.op_Hat "layered_effect " uu____9086
    | Polymonadic_bind (l1,l2,l3,uu____9092) ->
        let uu____9093 = FStar_Ident.string_of_lid l1  in
        let uu____9095 = FStar_Ident.string_of_lid l2  in
        let uu____9097 = FStar_Ident.string_of_lid l3  in
        FStar_Util.format3 "polymonadic_bind (%s, %s) |> %s" uu____9093
          uu____9095 uu____9097
    | Splice (ids,t) ->
        let uu____9106 =
          let uu____9108 =
            let uu____9110 =
              FStar_List.map (fun i  -> FStar_Ident.text_of_id i) ids  in
            FStar_All.pipe_left (FStar_String.concat ";") uu____9110  in
          let uu____9122 =
            let uu____9124 =
              let uu____9126 = term_to_string t  in
              Prims.op_Hat uu____9126 ")"  in
            Prims.op_Hat "] (" uu____9124  in
          Prims.op_Hat uu____9108 uu____9122  in
        Prims.op_Hat "splice[" uu____9106
    | SubEffect uu____9131 -> "sub_effect"
    | Pragma uu____9133 -> "pragma"
  
let (modul_to_string : modul -> Prims.string) =
  fun m  ->
    match m with
    | Module (uu____9143,decls) ->
        let uu____9149 =
          FStar_All.pipe_right decls (FStar_List.map decl_to_string)  in
        FStar_All.pipe_right uu____9149 (FStar_String.concat "\n")
    | Interface (uu____9164,decls,uu____9166) ->
        let uu____9173 =
          FStar_All.pipe_right decls (FStar_List.map decl_to_string)  in
        FStar_All.pipe_right uu____9173 (FStar_String.concat "\n")
  
let (decl_is_val : FStar_Ident.ident -> decl -> Prims.bool) =
  fun id  ->
    fun decl1  ->
      match decl1.d with
      | Val (id',uu____9202) -> FStar_Ident.ident_equals id id'
      | uu____9203 -> false
  
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
              | Annotated (i,uu____9241) -> i
              | TAnnotated (i,uu____9243) -> i
              | NoName uu____9244 ->
                  FStar_Errors.raise_error
                    (FStar_Errors.Fatal_MissingQuantifierBinder,
                      "Wildcard binders in quantifiers are not allowed") r))
  