open Prims
type level =
  | Un 
  | Expr 
  | Type_level 
  | Kind 
  | Formula 
let (uu___is_Un : level -> Prims.bool) =
  fun projectee  -> match projectee with | Un  -> true | uu____6 -> false 
let (uu___is_Expr : level -> Prims.bool) =
  fun projectee  -> match projectee with | Expr  -> true | uu____12 -> false 
let (uu___is_Type_level : level -> Prims.bool) =
  fun projectee  ->
    match projectee with | Type_level  -> true | uu____18 -> false
  
let (uu___is_Kind : level -> Prims.bool) =
  fun projectee  -> match projectee with | Kind  -> true | uu____24 -> false 
let (uu___is_Formula : level -> Prims.bool) =
  fun projectee  ->
    match projectee with | Formula  -> true | uu____30 -> false
  
type let_qualifier =
  | NoLetQualifier 
  | Rec 
let (uu___is_NoLetQualifier : let_qualifier -> Prims.bool) =
  fun projectee  ->
    match projectee with | NoLetQualifier  -> true | uu____36 -> false
  
let (uu___is_Rec : let_qualifier -> Prims.bool) =
  fun projectee  -> match projectee with | Rec  -> true | uu____42 -> false 
type quote_kind =
  | Static 
  | Dynamic 
let (uu___is_Static : quote_kind -> Prims.bool) =
  fun projectee  ->
    match projectee with | Static  -> true | uu____48 -> false
  
let (uu___is_Dynamic : quote_kind -> Prims.bool) =
  fun projectee  ->
    match projectee with | Dynamic  -> true | uu____54 -> false
  
type term' =
  | Wild 
  | Const of FStar_Const.sconst 
  | Op of (FStar_Ident.ident,term Prims.list) FStar_Pervasives_Native.tuple2
  
  | Tvar of FStar_Ident.ident 
  | Uvar of FStar_Ident.ident 
  | Var of FStar_Ident.lid 
  | Name of FStar_Ident.lid 
  | Projector of (FStar_Ident.lid,FStar_Ident.ident)
  FStar_Pervasives_Native.tuple2 
  | Construct of
  (FStar_Ident.lid,(term,imp) FStar_Pervasives_Native.tuple2 Prims.list)
  FStar_Pervasives_Native.tuple2 
  | Abs of (pattern Prims.list,term) FStar_Pervasives_Native.tuple2 
  | App of (term,term,imp) FStar_Pervasives_Native.tuple3 
  | Let of
  (let_qualifier,(term Prims.list FStar_Pervasives_Native.option,(pattern,
                                                                   term)
                                                                   FStar_Pervasives_Native.tuple2)
                   FStar_Pervasives_Native.tuple2 Prims.list,term)
  FStar_Pervasives_Native.tuple3 
  | LetOpen of (FStar_Ident.lid,term) FStar_Pervasives_Native.tuple2 
  | Seq of (term,term) FStar_Pervasives_Native.tuple2 
  | Bind of (FStar_Ident.ident,term,term) FStar_Pervasives_Native.tuple3 
  | If of (term,term,term) FStar_Pervasives_Native.tuple3 
  | Match of
  (term,(pattern,term FStar_Pervasives_Native.option,term)
          FStar_Pervasives_Native.tuple3 Prims.list)
  FStar_Pervasives_Native.tuple2 
  | TryWith of
  (term,(pattern,term FStar_Pervasives_Native.option,term)
          FStar_Pervasives_Native.tuple3 Prims.list)
  FStar_Pervasives_Native.tuple2 
  | Ascribed of (term,term,term FStar_Pervasives_Native.option)
  FStar_Pervasives_Native.tuple3 
  | Record of
  (term FStar_Pervasives_Native.option,(FStar_Ident.lid,term)
                                         FStar_Pervasives_Native.tuple2
                                         Prims.list)
  FStar_Pervasives_Native.tuple2 
  | Project of (term,FStar_Ident.lid) FStar_Pervasives_Native.tuple2 
  | Product of (binder Prims.list,term) FStar_Pervasives_Native.tuple2 
  | Sum of ((binder,term) FStar_Util.either Prims.list,term)
  FStar_Pervasives_Native.tuple2 
  | QForall of (binder Prims.list,term Prims.list Prims.list,term)
  FStar_Pervasives_Native.tuple3 
  | QExists of (binder Prims.list,term Prims.list Prims.list,term)
  FStar_Pervasives_Native.tuple3 
  | Refine of (binder,term) FStar_Pervasives_Native.tuple2 
  | NamedTyp of (FStar_Ident.ident,term) FStar_Pervasives_Native.tuple2 
  | Paren of term 
  | Requires of (term,Prims.string FStar_Pervasives_Native.option)
  FStar_Pervasives_Native.tuple2 
  | Ensures of (term,Prims.string FStar_Pervasives_Native.option)
  FStar_Pervasives_Native.tuple2 
  | Labeled of (term,Prims.string,Prims.bool) FStar_Pervasives_Native.tuple3
  
  | Discrim of FStar_Ident.lid 
  | Attributes of term Prims.list 
  | Antiquote of term 
  | Quote of (term,quote_kind) FStar_Pervasives_Native.tuple2 
  | VQuote of term 
and term = {
  tm: term' ;
  range: FStar_Range.range ;
  level: level }
and binder' =
  | Variable of FStar_Ident.ident 
  | TVariable of FStar_Ident.ident 
  | Annotated of (FStar_Ident.ident,term) FStar_Pervasives_Native.tuple2 
  | TAnnotated of (FStar_Ident.ident,term) FStar_Pervasives_Native.tuple2 
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
  | PatApp of (pattern,pattern Prims.list) FStar_Pervasives_Native.tuple2 
  | PatVar of
  (FStar_Ident.ident,arg_qualifier FStar_Pervasives_Native.option)
  FStar_Pervasives_Native.tuple2 
  | PatName of FStar_Ident.lid 
  | PatTvar of
  (FStar_Ident.ident,arg_qualifier FStar_Pervasives_Native.option)
  FStar_Pervasives_Native.tuple2 
  | PatList of pattern Prims.list 
  | PatTuple of (pattern Prims.list,Prims.bool)
  FStar_Pervasives_Native.tuple2 
  | PatRecord of (FStar_Ident.lid,pattern) FStar_Pervasives_Native.tuple2
  Prims.list 
  | PatAscribed of
  (pattern,(term,term FStar_Pervasives_Native.option)
             FStar_Pervasives_Native.tuple2)
  FStar_Pervasives_Native.tuple2 
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
  | Nothing 
let (uu___is_Wild : term' -> Prims.bool) =
  fun projectee  -> match projectee with | Wild  -> true | uu____627 -> false 
let (uu___is_Const : term' -> Prims.bool) =
  fun projectee  ->
    match projectee with | Const _0 -> true | uu____634 -> false
  
let (__proj__Const__item___0 : term' -> FStar_Const.sconst) =
  fun projectee  -> match projectee with | Const _0 -> _0 
let (uu___is_Op : term' -> Prims.bool) =
  fun projectee  -> match projectee with | Op _0 -> true | uu____654 -> false 
let (__proj__Op__item___0 :
  term' -> (FStar_Ident.ident,term Prims.list) FStar_Pervasives_Native.tuple2)
  = fun projectee  -> match projectee with | Op _0 -> _0 
let (uu___is_Tvar : term' -> Prims.bool) =
  fun projectee  ->
    match projectee with | Tvar _0 -> true | uu____686 -> false
  
let (__proj__Tvar__item___0 : term' -> FStar_Ident.ident) =
  fun projectee  -> match projectee with | Tvar _0 -> _0 
let (uu___is_Uvar : term' -> Prims.bool) =
  fun projectee  ->
    match projectee with | Uvar _0 -> true | uu____700 -> false
  
let (__proj__Uvar__item___0 : term' -> FStar_Ident.ident) =
  fun projectee  -> match projectee with | Uvar _0 -> _0 
let (uu___is_Var : term' -> Prims.bool) =
  fun projectee  ->
    match projectee with | Var _0 -> true | uu____714 -> false
  
let (__proj__Var__item___0 : term' -> FStar_Ident.lid) =
  fun projectee  -> match projectee with | Var _0 -> _0 
let (uu___is_Name : term' -> Prims.bool) =
  fun projectee  ->
    match projectee with | Name _0 -> true | uu____728 -> false
  
let (__proj__Name__item___0 : term' -> FStar_Ident.lid) =
  fun projectee  -> match projectee with | Name _0 -> _0 
let (uu___is_Projector : term' -> Prims.bool) =
  fun projectee  ->
    match projectee with | Projector _0 -> true | uu____746 -> false
  
let (__proj__Projector__item___0 :
  term' -> (FStar_Ident.lid,FStar_Ident.ident) FStar_Pervasives_Native.tuple2)
  = fun projectee  -> match projectee with | Projector _0 -> _0 
let (uu___is_Construct : term' -> Prims.bool) =
  fun projectee  ->
    match projectee with | Construct _0 -> true | uu____782 -> false
  
let (__proj__Construct__item___0 :
  term' ->
    (FStar_Ident.lid,(term,imp) FStar_Pervasives_Native.tuple2 Prims.list)
      FStar_Pervasives_Native.tuple2)
  = fun projectee  -> match projectee with | Construct _0 -> _0 
let (uu___is_Abs : term' -> Prims.bool) =
  fun projectee  ->
    match projectee with | Abs _0 -> true | uu____832 -> false
  
let (__proj__Abs__item___0 :
  term' -> (pattern Prims.list,term) FStar_Pervasives_Native.tuple2) =
  fun projectee  -> match projectee with | Abs _0 -> _0 
let (uu___is_App : term' -> Prims.bool) =
  fun projectee  ->
    match projectee with | App _0 -> true | uu____870 -> false
  
let (__proj__App__item___0 :
  term' -> (term,term,imp) FStar_Pervasives_Native.tuple3) =
  fun projectee  -> match projectee with | App _0 -> _0 
let (uu___is_Let : term' -> Prims.bool) =
  fun projectee  ->
    match projectee with | Let _0 -> true | uu____922 -> false
  
let (__proj__Let__item___0 :
  term' ->
    (let_qualifier,(term Prims.list FStar_Pervasives_Native.option,(pattern,
                                                                    term)
                                                                    FStar_Pervasives_Native.tuple2)
                     FStar_Pervasives_Native.tuple2 Prims.list,term)
      FStar_Pervasives_Native.tuple3)
  = fun projectee  -> match projectee with | Let _0 -> _0 
let (uu___is_LetOpen : term' -> Prims.bool) =
  fun projectee  ->
    match projectee with | LetOpen _0 -> true | uu____1000 -> false
  
let (__proj__LetOpen__item___0 :
  term' -> (FStar_Ident.lid,term) FStar_Pervasives_Native.tuple2) =
  fun projectee  -> match projectee with | LetOpen _0 -> _0 
let (uu___is_Seq : term' -> Prims.bool) =
  fun projectee  ->
    match projectee with | Seq _0 -> true | uu____1030 -> false
  
let (__proj__Seq__item___0 :
  term' -> (term,term) FStar_Pervasives_Native.tuple2) =
  fun projectee  -> match projectee with | Seq _0 -> _0 
let (uu___is_Bind : term' -> Prims.bool) =
  fun projectee  ->
    match projectee with | Bind _0 -> true | uu____1062 -> false
  
let (__proj__Bind__item___0 :
  term' -> (FStar_Ident.ident,term,term) FStar_Pervasives_Native.tuple3) =
  fun projectee  -> match projectee with | Bind _0 -> _0 
let (uu___is_If : term' -> Prims.bool) =
  fun projectee  ->
    match projectee with | If _0 -> true | uu____1100 -> false
  
let (__proj__If__item___0 :
  term' -> (term,term,term) FStar_Pervasives_Native.tuple3) =
  fun projectee  -> match projectee with | If _0 -> _0 
let (uu___is_Match : term' -> Prims.bool) =
  fun projectee  ->
    match projectee with | Match _0 -> true | uu____1146 -> false
  
let (__proj__Match__item___0 :
  term' ->
    (term,(pattern,term FStar_Pervasives_Native.option,term)
            FStar_Pervasives_Native.tuple3 Prims.list)
      FStar_Pervasives_Native.tuple2)
  = fun projectee  -> match projectee with | Match _0 -> _0 
let (uu___is_TryWith : term' -> Prims.bool) =
  fun projectee  ->
    match projectee with | TryWith _0 -> true | uu____1216 -> false
  
let (__proj__TryWith__item___0 :
  term' ->
    (term,(pattern,term FStar_Pervasives_Native.option,term)
            FStar_Pervasives_Native.tuple3 Prims.list)
      FStar_Pervasives_Native.tuple2)
  = fun projectee  -> match projectee with | TryWith _0 -> _0 
let (uu___is_Ascribed : term' -> Prims.bool) =
  fun projectee  ->
    match projectee with | Ascribed _0 -> true | uu____1280 -> false
  
let (__proj__Ascribed__item___0 :
  term' ->
    (term,term,term FStar_Pervasives_Native.option)
      FStar_Pervasives_Native.tuple3)
  = fun projectee  -> match projectee with | Ascribed _0 -> _0 
let (uu___is_Record : term' -> Prims.bool) =
  fun projectee  ->
    match projectee with | Record _0 -> true | uu____1330 -> false
  
let (__proj__Record__item___0 :
  term' ->
    (term FStar_Pervasives_Native.option,(FStar_Ident.lid,term)
                                           FStar_Pervasives_Native.tuple2
                                           Prims.list)
      FStar_Pervasives_Native.tuple2)
  = fun projectee  -> match projectee with | Record _0 -> _0 
let (uu___is_Project : term' -> Prims.bool) =
  fun projectee  ->
    match projectee with | Project _0 -> true | uu____1384 -> false
  
let (__proj__Project__item___0 :
  term' -> (term,FStar_Ident.lid) FStar_Pervasives_Native.tuple2) =
  fun projectee  -> match projectee with | Project _0 -> _0 
let (uu___is_Product : term' -> Prims.bool) =
  fun projectee  ->
    match projectee with | Product _0 -> true | uu____1416 -> false
  
let (__proj__Product__item___0 :
  term' -> (binder Prims.list,term) FStar_Pervasives_Native.tuple2) =
  fun projectee  -> match projectee with | Product _0 -> _0 
let (uu___is_Sum : term' -> Prims.bool) =
  fun projectee  ->
    match projectee with | Sum _0 -> true | uu____1458 -> false
  
let (__proj__Sum__item___0 :
  term' ->
    ((binder,term) FStar_Util.either Prims.list,term)
      FStar_Pervasives_Native.tuple2)
  = fun projectee  -> match projectee with | Sum _0 -> _0 
let (uu___is_QForall : term' -> Prims.bool) =
  fun projectee  ->
    match projectee with | QForall _0 -> true | uu____1514 -> false
  
let (__proj__QForall__item___0 :
  term' ->
    (binder Prims.list,term Prims.list Prims.list,term)
      FStar_Pervasives_Native.tuple3)
  = fun projectee  -> match projectee with | QForall _0 -> _0 
let (uu___is_QExists : term' -> Prims.bool) =
  fun projectee  ->
    match projectee with | QExists _0 -> true | uu____1576 -> false
  
let (__proj__QExists__item___0 :
  term' ->
    (binder Prims.list,term Prims.list Prims.list,term)
      FStar_Pervasives_Native.tuple3)
  = fun projectee  -> match projectee with | QExists _0 -> _0 
let (uu___is_Refine : term' -> Prims.bool) =
  fun projectee  ->
    match projectee with | Refine _0 -> true | uu____1630 -> false
  
let (__proj__Refine__item___0 :
  term' -> (binder,term) FStar_Pervasives_Native.tuple2) =
  fun projectee  -> match projectee with | Refine _0 -> _0 
let (uu___is_NamedTyp : term' -> Prims.bool) =
  fun projectee  ->
    match projectee with | NamedTyp _0 -> true | uu____1660 -> false
  
let (__proj__NamedTyp__item___0 :
  term' -> (FStar_Ident.ident,term) FStar_Pervasives_Native.tuple2) =
  fun projectee  -> match projectee with | NamedTyp _0 -> _0 
let (uu___is_Paren : term' -> Prims.bool) =
  fun projectee  ->
    match projectee with | Paren _0 -> true | uu____1686 -> false
  
let (__proj__Paren__item___0 : term' -> term) =
  fun projectee  -> match projectee with | Paren _0 -> _0 
let (uu___is_Requires : term' -> Prims.bool) =
  fun projectee  ->
    match projectee with | Requires _0 -> true | uu____1706 -> false
  
let (__proj__Requires__item___0 :
  term' ->
    (term,Prims.string FStar_Pervasives_Native.option)
      FStar_Pervasives_Native.tuple2)
  = fun projectee  -> match projectee with | Requires _0 -> _0 
let (uu___is_Ensures : term' -> Prims.bool) =
  fun projectee  ->
    match projectee with | Ensures _0 -> true | uu____1744 -> false
  
let (__proj__Ensures__item___0 :
  term' ->
    (term,Prims.string FStar_Pervasives_Native.option)
      FStar_Pervasives_Native.tuple2)
  = fun projectee  -> match projectee with | Ensures _0 -> _0 
let (uu___is_Labeled : term' -> Prims.bool) =
  fun projectee  ->
    match projectee with | Labeled _0 -> true | uu____1782 -> false
  
let (__proj__Labeled__item___0 :
  term' -> (term,Prims.string,Prims.bool) FStar_Pervasives_Native.tuple3) =
  fun projectee  -> match projectee with | Labeled _0 -> _0 
let (uu___is_Discrim : term' -> Prims.bool) =
  fun projectee  ->
    match projectee with | Discrim _0 -> true | uu____1814 -> false
  
let (__proj__Discrim__item___0 : term' -> FStar_Ident.lid) =
  fun projectee  -> match projectee with | Discrim _0 -> _0 
let (uu___is_Attributes : term' -> Prims.bool) =
  fun projectee  ->
    match projectee with | Attributes _0 -> true | uu____1830 -> false
  
let (__proj__Attributes__item___0 : term' -> term Prims.list) =
  fun projectee  -> match projectee with | Attributes _0 -> _0 
let (uu___is_Antiquote : term' -> Prims.bool) =
  fun projectee  ->
    match projectee with | Antiquote _0 -> true | uu____1850 -> false
  
let (__proj__Antiquote__item___0 : term' -> term) =
  fun projectee  -> match projectee with | Antiquote _0 -> _0 
let (uu___is_Quote : term' -> Prims.bool) =
  fun projectee  ->
    match projectee with | Quote _0 -> true | uu____1868 -> false
  
let (__proj__Quote__item___0 :
  term' -> (term,quote_kind) FStar_Pervasives_Native.tuple2) =
  fun projectee  -> match projectee with | Quote _0 -> _0 
let (uu___is_VQuote : term' -> Prims.bool) =
  fun projectee  ->
    match projectee with | VQuote _0 -> true | uu____1894 -> false
  
let (__proj__VQuote__item___0 : term' -> term) =
  fun projectee  -> match projectee with | VQuote _0 -> _0 
let (__proj__Mkterm__item__tm : term -> term') =
  fun projectee  -> match projectee with | { tm; range; level;_} -> tm 
let (__proj__Mkterm__item__range : term -> FStar_Range.range) =
  fun projectee  -> match projectee with | { tm; range; level;_} -> range 
let (__proj__Mkterm__item__level : term -> level) =
  fun projectee  -> match projectee with | { tm; range; level;_} -> level 
let (uu___is_Variable : binder' -> Prims.bool) =
  fun projectee  ->
    match projectee with | Variable _0 -> true | uu____1932 -> false
  
let (__proj__Variable__item___0 : binder' -> FStar_Ident.ident) =
  fun projectee  -> match projectee with | Variable _0 -> _0 
let (uu___is_TVariable : binder' -> Prims.bool) =
  fun projectee  ->
    match projectee with | TVariable _0 -> true | uu____1946 -> false
  
let (__proj__TVariable__item___0 : binder' -> FStar_Ident.ident) =
  fun projectee  -> match projectee with | TVariable _0 -> _0 
let (uu___is_Annotated : binder' -> Prims.bool) =
  fun projectee  ->
    match projectee with | Annotated _0 -> true | uu____1964 -> false
  
let (__proj__Annotated__item___0 :
  binder' -> (FStar_Ident.ident,term) FStar_Pervasives_Native.tuple2) =
  fun projectee  -> match projectee with | Annotated _0 -> _0 
let (uu___is_TAnnotated : binder' -> Prims.bool) =
  fun projectee  ->
    match projectee with | TAnnotated _0 -> true | uu____1994 -> false
  
let (__proj__TAnnotated__item___0 :
  binder' -> (FStar_Ident.ident,term) FStar_Pervasives_Native.tuple2) =
  fun projectee  -> match projectee with | TAnnotated _0 -> _0 
let (uu___is_NoName : binder' -> Prims.bool) =
  fun projectee  ->
    match projectee with | NoName _0 -> true | uu____2020 -> false
  
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
    match projectee with | PatWild _0 -> true | uu____2084 -> false
  
let (__proj__PatWild__item___0 :
  pattern' -> arg_qualifier FStar_Pervasives_Native.option) =
  fun projectee  -> match projectee with | PatWild _0 -> _0 
let (uu___is_PatConst : pattern' -> Prims.bool) =
  fun projectee  ->
    match projectee with | PatConst _0 -> true | uu____2104 -> false
  
let (__proj__PatConst__item___0 : pattern' -> FStar_Const.sconst) =
  fun projectee  -> match projectee with | PatConst _0 -> _0 
let (uu___is_PatApp : pattern' -> Prims.bool) =
  fun projectee  ->
    match projectee with | PatApp _0 -> true | uu____2124 -> false
  
let (__proj__PatApp__item___0 :
  pattern' -> (pattern,pattern Prims.list) FStar_Pervasives_Native.tuple2) =
  fun projectee  -> match projectee with | PatApp _0 -> _0 
let (uu___is_PatVar : pattern' -> Prims.bool) =
  fun projectee  ->
    match projectee with | PatVar _0 -> true | uu____2162 -> false
  
let (__proj__PatVar__item___0 :
  pattern' ->
    (FStar_Ident.ident,arg_qualifier FStar_Pervasives_Native.option)
      FStar_Pervasives_Native.tuple2)
  = fun projectee  -> match projectee with | PatVar _0 -> _0 
let (uu___is_PatName : pattern' -> Prims.bool) =
  fun projectee  ->
    match projectee with | PatName _0 -> true | uu____2194 -> false
  
let (__proj__PatName__item___0 : pattern' -> FStar_Ident.lid) =
  fun projectee  -> match projectee with | PatName _0 -> _0 
let (uu___is_PatTvar : pattern' -> Prims.bool) =
  fun projectee  ->
    match projectee with | PatTvar _0 -> true | uu____2214 -> false
  
let (__proj__PatTvar__item___0 :
  pattern' ->
    (FStar_Ident.ident,arg_qualifier FStar_Pervasives_Native.option)
      FStar_Pervasives_Native.tuple2)
  = fun projectee  -> match projectee with | PatTvar _0 -> _0 
let (uu___is_PatList : pattern' -> Prims.bool) =
  fun projectee  ->
    match projectee with | PatList _0 -> true | uu____2248 -> false
  
let (__proj__PatList__item___0 : pattern' -> pattern Prims.list) =
  fun projectee  -> match projectee with | PatList _0 -> _0 
let (uu___is_PatTuple : pattern' -> Prims.bool) =
  fun projectee  ->
    match projectee with | PatTuple _0 -> true | uu____2274 -> false
  
let (__proj__PatTuple__item___0 :
  pattern' -> (pattern Prims.list,Prims.bool) FStar_Pervasives_Native.tuple2)
  = fun projectee  -> match projectee with | PatTuple _0 -> _0 
let (uu___is_PatRecord : pattern' -> Prims.bool) =
  fun projectee  ->
    match projectee with | PatRecord _0 -> true | uu____2312 -> false
  
let (__proj__PatRecord__item___0 :
  pattern' ->
    (FStar_Ident.lid,pattern) FStar_Pervasives_Native.tuple2 Prims.list)
  = fun projectee  -> match projectee with | PatRecord _0 -> _0 
let (uu___is_PatAscribed : pattern' -> Prims.bool) =
  fun projectee  ->
    match projectee with | PatAscribed _0 -> true | uu____2354 -> false
  
let (__proj__PatAscribed__item___0 :
  pattern' ->
    (pattern,(term,term FStar_Pervasives_Native.option)
               FStar_Pervasives_Native.tuple2)
      FStar_Pervasives_Native.tuple2)
  = fun projectee  -> match projectee with | PatAscribed _0 -> _0 
let (uu___is_PatOr : pattern' -> Prims.bool) =
  fun projectee  ->
    match projectee with | PatOr _0 -> true | uu____2400 -> false
  
let (__proj__PatOr__item___0 : pattern' -> pattern Prims.list) =
  fun projectee  -> match projectee with | PatOr _0 -> _0 
let (uu___is_PatOp : pattern' -> Prims.bool) =
  fun projectee  ->
    match projectee with | PatOp _0 -> true | uu____2420 -> false
  
let (__proj__PatOp__item___0 : pattern' -> FStar_Ident.ident) =
  fun projectee  -> match projectee with | PatOp _0 -> _0 
let (__proj__Mkpattern__item__pat : pattern -> pattern') =
  fun projectee  -> match projectee with | { pat; prange;_} -> pat 
let (__proj__Mkpattern__item__prange : pattern -> FStar_Range.range) =
  fun projectee  -> match projectee with | { pat; prange;_} -> prange 
let (uu___is_Implicit : arg_qualifier -> Prims.bool) =
  fun projectee  ->
    match projectee with | Implicit  -> true | uu____2447 -> false
  
let (uu___is_Equality : arg_qualifier -> Prims.bool) =
  fun projectee  ->
    match projectee with | Equality  -> true | uu____2453 -> false
  
let (uu___is_Meta : arg_qualifier -> Prims.bool) =
  fun projectee  ->
    match projectee with | Meta _0 -> true | uu____2460 -> false
  
let (__proj__Meta__item___0 : arg_qualifier -> term) =
  fun projectee  -> match projectee with | Meta _0 -> _0 
let (uu___is_FsTypApp : imp -> Prims.bool) =
  fun projectee  ->
    match projectee with | FsTypApp  -> true | uu____2473 -> false
  
let (uu___is_Hash : imp -> Prims.bool) =
  fun projectee  ->
    match projectee with | Hash  -> true | uu____2479 -> false
  
let (uu___is_UnivApp : imp -> Prims.bool) =
  fun projectee  ->
    match projectee with | UnivApp  -> true | uu____2485 -> false
  
let (uu___is_HashBrace : imp -> Prims.bool) =
  fun projectee  ->
    match projectee with | HashBrace _0 -> true | uu____2492 -> false
  
let (__proj__HashBrace__item___0 : imp -> term) =
  fun projectee  -> match projectee with | HashBrace _0 -> _0 
let (uu___is_Nothing : imp -> Prims.bool) =
  fun projectee  ->
    match projectee with | Nothing  -> true | uu____2505 -> false
  
type attributes_ = term Prims.list
type branch =
  (pattern,term FStar_Pervasives_Native.option,term)
    FStar_Pervasives_Native.tuple3
type aqual = arg_qualifier FStar_Pervasives_Native.option
type knd = term
type typ = term
type expr = term
type fsdoc =
  (Prims.string,(Prims.string,Prims.string) FStar_Pervasives_Native.tuple2
                  Prims.list)
    FStar_Pervasives_Native.tuple2
type tycon =
  | TyconAbstract of
  (FStar_Ident.ident,binder Prims.list,knd FStar_Pervasives_Native.option)
  FStar_Pervasives_Native.tuple3 
  | TyconAbbrev of
  (FStar_Ident.ident,binder Prims.list,knd FStar_Pervasives_Native.option,
  term) FStar_Pervasives_Native.tuple4 
  | TyconRecord of
  (FStar_Ident.ident,binder Prims.list,knd FStar_Pervasives_Native.option,
  (FStar_Ident.ident,term,fsdoc FStar_Pervasives_Native.option)
    FStar_Pervasives_Native.tuple3 Prims.list)
  FStar_Pervasives_Native.tuple4 
  | TyconVariant of
  (FStar_Ident.ident,binder Prims.list,knd FStar_Pervasives_Native.option,
  (FStar_Ident.ident,term FStar_Pervasives_Native.option,fsdoc
                                                           FStar_Pervasives_Native.option,
    Prims.bool) FStar_Pervasives_Native.tuple4 Prims.list)
  FStar_Pervasives_Native.tuple4 
let (uu___is_TyconAbstract : tycon -> Prims.bool) =
  fun projectee  ->
    match projectee with | TyconAbstract _0 -> true | uu____2634 -> false
  
let (__proj__TyconAbstract__item___0 :
  tycon ->
    (FStar_Ident.ident,binder Prims.list,knd FStar_Pervasives_Native.option)
      FStar_Pervasives_Native.tuple3)
  = fun projectee  -> match projectee with | TyconAbstract _0 -> _0 
let (uu___is_TyconAbbrev : tycon -> Prims.bool) =
  fun projectee  ->
    match projectee with | TyconAbbrev _0 -> true | uu____2690 -> false
  
let (__proj__TyconAbbrev__item___0 :
  tycon ->
    (FStar_Ident.ident,binder Prims.list,knd FStar_Pervasives_Native.option,
      term) FStar_Pervasives_Native.tuple4)
  = fun projectee  -> match projectee with | TyconAbbrev _0 -> _0 
let (uu___is_TyconRecord : tycon -> Prims.bool) =
  fun projectee  ->
    match projectee with | TyconRecord _0 -> true | uu____2762 -> false
  
let (__proj__TyconRecord__item___0 :
  tycon ->
    (FStar_Ident.ident,binder Prims.list,knd FStar_Pervasives_Native.option,
      (FStar_Ident.ident,term,fsdoc FStar_Pervasives_Native.option)
        FStar_Pervasives_Native.tuple3 Prims.list)
      FStar_Pervasives_Native.tuple4)
  = fun projectee  -> match projectee with | TyconRecord _0 -> _0 
let (uu___is_TyconVariant : tycon -> Prims.bool) =
  fun projectee  ->
    match projectee with | TyconVariant _0 -> true | uu____2868 -> false
  
let (__proj__TyconVariant__item___0 :
  tycon ->
    (FStar_Ident.ident,binder Prims.list,knd FStar_Pervasives_Native.option,
      (FStar_Ident.ident,term FStar_Pervasives_Native.option,fsdoc
                                                               FStar_Pervasives_Native.option,
        Prims.bool) FStar_Pervasives_Native.tuple4 Prims.list)
      FStar_Pervasives_Native.tuple4)
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
    match projectee with | Private  -> true | uu____2959 -> false
  
let (uu___is_Abstract : qualifier -> Prims.bool) =
  fun projectee  ->
    match projectee with | Abstract  -> true | uu____2965 -> false
  
let (uu___is_Noeq : qualifier -> Prims.bool) =
  fun projectee  ->
    match projectee with | Noeq  -> true | uu____2971 -> false
  
let (uu___is_Unopteq : qualifier -> Prims.bool) =
  fun projectee  ->
    match projectee with | Unopteq  -> true | uu____2977 -> false
  
let (uu___is_Assumption : qualifier -> Prims.bool) =
  fun projectee  ->
    match projectee with | Assumption  -> true | uu____2983 -> false
  
let (uu___is_DefaultEffect : qualifier -> Prims.bool) =
  fun projectee  ->
    match projectee with | DefaultEffect  -> true | uu____2989 -> false
  
let (uu___is_TotalEffect : qualifier -> Prims.bool) =
  fun projectee  ->
    match projectee with | TotalEffect  -> true | uu____2995 -> false
  
let (uu___is_Effect_qual : qualifier -> Prims.bool) =
  fun projectee  ->
    match projectee with | Effect_qual  -> true | uu____3001 -> false
  
let (uu___is_New : qualifier -> Prims.bool) =
  fun projectee  -> match projectee with | New  -> true | uu____3007 -> false 
let (uu___is_Inline : qualifier -> Prims.bool) =
  fun projectee  ->
    match projectee with | Inline  -> true | uu____3013 -> false
  
let (uu___is_Visible : qualifier -> Prims.bool) =
  fun projectee  ->
    match projectee with | Visible  -> true | uu____3019 -> false
  
let (uu___is_Unfold_for_unification_and_vcgen : qualifier -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | Unfold_for_unification_and_vcgen  -> true
    | uu____3025 -> false
  
let (uu___is_Inline_for_extraction : qualifier -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | Inline_for_extraction  -> true
    | uu____3031 -> false
  
let (uu___is_Irreducible : qualifier -> Prims.bool) =
  fun projectee  ->
    match projectee with | Irreducible  -> true | uu____3037 -> false
  
let (uu___is_NoExtract : qualifier -> Prims.bool) =
  fun projectee  ->
    match projectee with | NoExtract  -> true | uu____3043 -> false
  
let (uu___is_Reifiable : qualifier -> Prims.bool) =
  fun projectee  ->
    match projectee with | Reifiable  -> true | uu____3049 -> false
  
let (uu___is_Reflectable : qualifier -> Prims.bool) =
  fun projectee  ->
    match projectee with | Reflectable  -> true | uu____3055 -> false
  
let (uu___is_Opaque : qualifier -> Prims.bool) =
  fun projectee  ->
    match projectee with | Opaque  -> true | uu____3061 -> false
  
let (uu___is_Logic : qualifier -> Prims.bool) =
  fun projectee  ->
    match projectee with | Logic  -> true | uu____3067 -> false
  
type qualifiers = qualifier Prims.list
type decoration =
  | Qualifier of qualifier 
  | DeclAttributes of term Prims.list 
  | Doc of fsdoc 
let (uu___is_Qualifier : decoration -> Prims.bool) =
  fun projectee  ->
    match projectee with | Qualifier _0 -> true | uu____3093 -> false
  
let (__proj__Qualifier__item___0 : decoration -> qualifier) =
  fun projectee  -> match projectee with | Qualifier _0 -> _0 
let (uu___is_DeclAttributes : decoration -> Prims.bool) =
  fun projectee  ->
    match projectee with | DeclAttributes _0 -> true | uu____3109 -> false
  
let (__proj__DeclAttributes__item___0 : decoration -> term Prims.list) =
  fun projectee  -> match projectee with | DeclAttributes _0 -> _0 
let (uu___is_Doc : decoration -> Prims.bool) =
  fun projectee  ->
    match projectee with | Doc _0 -> true | uu____3129 -> false
  
let (__proj__Doc__item___0 : decoration -> fsdoc) =
  fun projectee  -> match projectee with | Doc _0 -> _0 
type lift_op =
  | NonReifiableLift of term 
  | ReifiableLift of (term,term) FStar_Pervasives_Native.tuple2 
  | LiftForFree of term 
let (uu___is_NonReifiableLift : lift_op -> Prims.bool) =
  fun projectee  ->
    match projectee with | NonReifiableLift _0 -> true | uu____3162 -> false
  
let (__proj__NonReifiableLift__item___0 : lift_op -> term) =
  fun projectee  -> match projectee with | NonReifiableLift _0 -> _0 
let (uu___is_ReifiableLift : lift_op -> Prims.bool) =
  fun projectee  ->
    match projectee with | ReifiableLift _0 -> true | uu____3180 -> false
  
let (__proj__ReifiableLift__item___0 :
  lift_op -> (term,term) FStar_Pervasives_Native.tuple2) =
  fun projectee  -> match projectee with | ReifiableLift _0 -> _0 
let (uu___is_LiftForFree : lift_op -> Prims.bool) =
  fun projectee  ->
    match projectee with | LiftForFree _0 -> true | uu____3206 -> false
  
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
    match projectee with | SetOptions _0 -> true | uu____3278 -> false
  
let (__proj__SetOptions__item___0 : pragma -> Prims.string) =
  fun projectee  -> match projectee with | SetOptions _0 -> _0 
let (uu___is_ResetOptions : pragma -> Prims.bool) =
  fun projectee  ->
    match projectee with | ResetOptions _0 -> true | uu____3294 -> false
  
let (__proj__ResetOptions__item___0 :
  pragma -> Prims.string FStar_Pervasives_Native.option) =
  fun projectee  -> match projectee with | ResetOptions _0 -> _0 
let (uu___is_PushOptions : pragma -> Prims.bool) =
  fun projectee  ->
    match projectee with | PushOptions _0 -> true | uu____3316 -> false
  
let (__proj__PushOptions__item___0 :
  pragma -> Prims.string FStar_Pervasives_Native.option) =
  fun projectee  -> match projectee with | PushOptions _0 -> _0 
let (uu___is_PopOptions : pragma -> Prims.bool) =
  fun projectee  ->
    match projectee with | PopOptions  -> true | uu____3335 -> false
  
let (uu___is_LightOff : pragma -> Prims.bool) =
  fun projectee  ->
    match projectee with | LightOff  -> true | uu____3341 -> false
  
type decl' =
  | TopLevelModule of FStar_Ident.lid 
  | Open of FStar_Ident.lid 
  | Friend of FStar_Ident.lid 
  | Include of FStar_Ident.lid 
  | ModuleAbbrev of (FStar_Ident.ident,FStar_Ident.lid)
  FStar_Pervasives_Native.tuple2 
  | TopLevelLet of
  (let_qualifier,(pattern,term) FStar_Pervasives_Native.tuple2 Prims.list)
  FStar_Pervasives_Native.tuple2 
  | Main of term 
  | Tycon of
  (Prims.bool,Prims.bool,(tycon,fsdoc FStar_Pervasives_Native.option)
                           FStar_Pervasives_Native.tuple2 Prims.list)
  FStar_Pervasives_Native.tuple3 
  | Val of (FStar_Ident.ident,term) FStar_Pervasives_Native.tuple2 
  | Exception of (FStar_Ident.ident,term FStar_Pervasives_Native.option)
  FStar_Pervasives_Native.tuple2 
  | NewEffect of effect_decl 
  | SubEffect of lift 
  | Pragma of pragma 
  | Fsdoc of fsdoc 
  | Assume of (FStar_Ident.ident,term) FStar_Pervasives_Native.tuple2 
  | Splice of (FStar_Ident.ident Prims.list,term)
  FStar_Pervasives_Native.tuple2 
and decl =
  {
  d: decl' ;
  drange: FStar_Range.range ;
  doc: fsdoc FStar_Pervasives_Native.option ;
  quals: qualifiers ;
  attrs: attributes_ }
and effect_decl =
  | DefineEffect of
  (FStar_Ident.ident,binder Prims.list,term,decl Prims.list)
  FStar_Pervasives_Native.tuple4 
  | RedefineEffect of (FStar_Ident.ident,binder Prims.list,term)
  FStar_Pervasives_Native.tuple3 
let (uu___is_TopLevelModule : decl' -> Prims.bool) =
  fun projectee  ->
    match projectee with | TopLevelModule _0 -> true | uu____3533 -> false
  
let (__proj__TopLevelModule__item___0 : decl' -> FStar_Ident.lid) =
  fun projectee  -> match projectee with | TopLevelModule _0 -> _0 
let (uu___is_Open : decl' -> Prims.bool) =
  fun projectee  ->
    match projectee with | Open _0 -> true | uu____3547 -> false
  
let (__proj__Open__item___0 : decl' -> FStar_Ident.lid) =
  fun projectee  -> match projectee with | Open _0 -> _0 
let (uu___is_Friend : decl' -> Prims.bool) =
  fun projectee  ->
    match projectee with | Friend _0 -> true | uu____3561 -> false
  
let (__proj__Friend__item___0 : decl' -> FStar_Ident.lid) =
  fun projectee  -> match projectee with | Friend _0 -> _0 
let (uu___is_Include : decl' -> Prims.bool) =
  fun projectee  ->
    match projectee with | Include _0 -> true | uu____3575 -> false
  
let (__proj__Include__item___0 : decl' -> FStar_Ident.lid) =
  fun projectee  -> match projectee with | Include _0 -> _0 
let (uu___is_ModuleAbbrev : decl' -> Prims.bool) =
  fun projectee  ->
    match projectee with | ModuleAbbrev _0 -> true | uu____3593 -> false
  
let (__proj__ModuleAbbrev__item___0 :
  decl' -> (FStar_Ident.ident,FStar_Ident.lid) FStar_Pervasives_Native.tuple2)
  = fun projectee  -> match projectee with | ModuleAbbrev _0 -> _0 
let (uu___is_TopLevelLet : decl' -> Prims.bool) =
  fun projectee  ->
    match projectee with | TopLevelLet _0 -> true | uu____3629 -> false
  
let (__proj__TopLevelLet__item___0 :
  decl' ->
    (let_qualifier,(pattern,term) FStar_Pervasives_Native.tuple2 Prims.list)
      FStar_Pervasives_Native.tuple2)
  = fun projectee  -> match projectee with | TopLevelLet _0 -> _0 
let (uu___is_Main : decl' -> Prims.bool) =
  fun projectee  ->
    match projectee with | Main _0 -> true | uu____3673 -> false
  
let (__proj__Main__item___0 : decl' -> term) =
  fun projectee  -> match projectee with | Main _0 -> _0 
let (uu___is_Tycon : decl' -> Prims.bool) =
  fun projectee  ->
    match projectee with | Tycon _0 -> true | uu____3701 -> false
  
let (__proj__Tycon__item___0 :
  decl' ->
    (Prims.bool,Prims.bool,(tycon,fsdoc FStar_Pervasives_Native.option)
                             FStar_Pervasives_Native.tuple2 Prims.list)
      FStar_Pervasives_Native.tuple3)
  = fun projectee  -> match projectee with | Tycon _0 -> _0 
let (uu___is_Val : decl' -> Prims.bool) =
  fun projectee  ->
    match projectee with | Val _0 -> true | uu____3761 -> false
  
let (__proj__Val__item___0 :
  decl' -> (FStar_Ident.ident,term) FStar_Pervasives_Native.tuple2) =
  fun projectee  -> match projectee with | Val _0 -> _0 
let (uu___is_Exception : decl' -> Prims.bool) =
  fun projectee  ->
    match projectee with | Exception _0 -> true | uu____3793 -> false
  
let (__proj__Exception__item___0 :
  decl' ->
    (FStar_Ident.ident,term FStar_Pervasives_Native.option)
      FStar_Pervasives_Native.tuple2)
  = fun projectee  -> match projectee with | Exception _0 -> _0 
let (uu___is_NewEffect : decl' -> Prims.bool) =
  fun projectee  ->
    match projectee with | NewEffect _0 -> true | uu____3825 -> false
  
let (__proj__NewEffect__item___0 : decl' -> effect_decl) =
  fun projectee  -> match projectee with | NewEffect _0 -> _0 
let (uu___is_SubEffect : decl' -> Prims.bool) =
  fun projectee  ->
    match projectee with | SubEffect _0 -> true | uu____3839 -> false
  
let (__proj__SubEffect__item___0 : decl' -> lift) =
  fun projectee  -> match projectee with | SubEffect _0 -> _0 
let (uu___is_Pragma : decl' -> Prims.bool) =
  fun projectee  ->
    match projectee with | Pragma _0 -> true | uu____3853 -> false
  
let (__proj__Pragma__item___0 : decl' -> pragma) =
  fun projectee  -> match projectee with | Pragma _0 -> _0 
let (uu___is_Fsdoc : decl' -> Prims.bool) =
  fun projectee  ->
    match projectee with | Fsdoc _0 -> true | uu____3867 -> false
  
let (__proj__Fsdoc__item___0 : decl' -> fsdoc) =
  fun projectee  -> match projectee with | Fsdoc _0 -> _0 
let (uu___is_Assume : decl' -> Prims.bool) =
  fun projectee  ->
    match projectee with | Assume _0 -> true | uu____3885 -> false
  
let (__proj__Assume__item___0 :
  decl' -> (FStar_Ident.ident,term) FStar_Pervasives_Native.tuple2) =
  fun projectee  -> match projectee with | Assume _0 -> _0 
let (uu___is_Splice : decl' -> Prims.bool) =
  fun projectee  ->
    match projectee with | Splice _0 -> true | uu____3917 -> false
  
let (__proj__Splice__item___0 :
  decl' -> (FStar_Ident.ident Prims.list,term) FStar_Pervasives_Native.tuple2)
  = fun projectee  -> match projectee with | Splice _0 -> _0 
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
    match projectee with | DefineEffect _0 -> true | uu____4025 -> false
  
let (__proj__DefineEffect__item___0 :
  effect_decl ->
    (FStar_Ident.ident,binder Prims.list,term,decl Prims.list)
      FStar_Pervasives_Native.tuple4)
  = fun projectee  -> match projectee with | DefineEffect _0 -> _0 
let (uu___is_RedefineEffect : effect_decl -> Prims.bool) =
  fun projectee  ->
    match projectee with | RedefineEffect _0 -> true | uu____4083 -> false
  
let (__proj__RedefineEffect__item___0 :
  effect_decl ->
    (FStar_Ident.ident,binder Prims.list,term) FStar_Pervasives_Native.tuple3)
  = fun projectee  -> match projectee with | RedefineEffect _0 -> _0 
type modul =
  | Module of (FStar_Ident.lid,decl Prims.list)
  FStar_Pervasives_Native.tuple2 
  | Interface of (FStar_Ident.lid,decl Prims.list,Prims.bool)
  FStar_Pervasives_Native.tuple3 
let (uu___is_Module : modul -> Prims.bool) =
  fun projectee  ->
    match projectee with | Module _0 -> true | uu____4151 -> false
  
let (__proj__Module__item___0 :
  modul -> (FStar_Ident.lid,decl Prims.list) FStar_Pervasives_Native.tuple2)
  = fun projectee  -> match projectee with | Module _0 -> _0 
let (uu___is_Interface : modul -> Prims.bool) =
  fun projectee  ->
    match projectee with | Interface _0 -> true | uu____4191 -> false
  
let (__proj__Interface__item___0 :
  modul ->
    (FStar_Ident.lid,decl Prims.list,Prims.bool)
      FStar_Pervasives_Native.tuple3)
  = fun projectee  -> match projectee with | Interface _0 -> _0 
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
      (let uu____4241 =
         let uu____4246 =
           FStar_Util.format1
             "Invalid identifer '%s'; expected a symbol that begins with a lower-case character"
             id1.FStar_Ident.idText
            in
         (FStar_Errors.Fatal_InvalidIdentifier, uu____4246)  in
       FStar_Errors.raise_error uu____4241 id1.FStar_Ident.idRange)
  
let at_most_one :
  'Auu____4255 .
    Prims.string ->
      FStar_Range.range ->
        'Auu____4255 Prims.list ->
          'Auu____4255 FStar_Pervasives_Native.option
  =
  fun s  ->
    fun r  ->
      fun l  ->
        match l with
        | x::[] -> FStar_Pervasives_Native.Some x
        | [] -> FStar_Pervasives_Native.None
        | uu____4278 ->
            let uu____4281 =
              let uu____4286 =
                FStar_Util.format1
                  "At most one %s is allowed on declarations" s
                 in
              (FStar_Errors.Fatal_MoreThanOneDeclaration, uu____4286)  in
            FStar_Errors.raise_error uu____4281 r
  
let (mk_decl : decl' -> FStar_Range.range -> decoration Prims.list -> decl) =
  fun d  ->
    fun r  ->
      fun decorations  ->
        let doc1 =
          let uu____4311 =
            FStar_List.choose
              (fun uu___93_4316  ->
                 match uu___93_4316 with
                 | Doc d1 -> FStar_Pervasives_Native.Some d1
                 | uu____4320 -> FStar_Pervasives_Native.None) decorations
             in
          at_most_one "fsdoc" r uu____4311  in
        let attributes_ =
          let uu____4326 =
            FStar_List.choose
              (fun uu___94_4335  ->
                 match uu___94_4335 with
                 | DeclAttributes a -> FStar_Pervasives_Native.Some a
                 | uu____4345 -> FStar_Pervasives_Native.None) decorations
             in
          at_most_one "attribute set" r uu____4326  in
        let attributes_1 = FStar_Util.dflt [] attributes_  in
        let qualifiers =
          FStar_List.choose
            (fun uu___95_4360  ->
               match uu___95_4360 with
               | Qualifier q -> FStar_Pervasives_Native.Some q
               | uu____4364 -> FStar_Pervasives_Native.None) decorations
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
                     ((Prims.strcat "-" s),
                       (FStar_Pervasives_Native.Some
                          (FStar_Const.Signed, width))))
            | uu____4447 ->
                let uu____4448 =
                  let uu____4455 = FStar_Ident.mk_ident ("-", rminus)  in
                  (uu____4455, [t])  in
                Op uu____4448
             in
          mk_term t1 r l
  
let (mk_pattern : pattern' -> FStar_Range.range -> pattern) =
  fun p  -> fun r  -> { pat = p; prange = r } 
let (un_curry_abs : pattern Prims.list -> term -> term') =
  fun ps  ->
    fun body  ->
      match body.tm with
      | Abs (p',body') -> Abs ((FStar_List.append ps p'), body')
      | uu____4490 -> Abs (ps, body)
  
let (mk_function :
  (pattern,term FStar_Pervasives_Native.option,term)
    FStar_Pervasives_Native.tuple3 Prims.list ->
    FStar_Range.range -> FStar_Range.range -> term)
  =
  fun branches  ->
    fun r1  ->
      fun r2  ->
        let x = let i = FStar_Parser_Const.next_id ()  in FStar_Ident.gen r1
           in
        let uu____4530 =
          let uu____4531 =
            let uu____4538 =
              let uu____4539 =
                let uu____4540 =
                  let uu____4555 =
                    let uu____4556 =
                      let uu____4557 = FStar_Ident.lid_of_ids [x]  in
                      Var uu____4557  in
                    mk_term uu____4556 r1 Expr  in
                  (uu____4555, branches)  in
                Match uu____4540  in
              mk_term uu____4539 r2 Expr  in
            ([mk_pattern (PatVar (x, FStar_Pervasives_Native.None)) r1],
              uu____4538)
             in
          Abs uu____4531  in
        mk_term uu____4530 r2 Expr
  
let (un_function :
  pattern ->
    term ->
      (pattern,term) FStar_Pervasives_Native.tuple2
        FStar_Pervasives_Native.option)
  =
  fun p  ->
    fun tm  ->
      match ((p.pat), (tm.tm)) with
      | (PatVar uu____4594,Abs (pats,body)) ->
          FStar_Pervasives_Native.Some
            ((mk_pattern (PatApp (p, pats)) p.prange), body)
      | uu____4613 -> FStar_Pervasives_Native.None
  
let (lid_with_range :
  FStar_Ident.lident -> FStar_Range.range -> FStar_Ident.lident) =
  fun lid  ->
    fun r  ->
      let uu____4632 = FStar_Ident.path_of_lid lid  in
      FStar_Ident.lid_of_path uu____4632 r
  
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
  
let (mkApp :
  term ->
    (term,imp) FStar_Pervasives_Native.tuple2 Prims.list ->
      FStar_Range.range -> term)
  =
  fun t  ->
    fun args  ->
      fun r  ->
        match args with
        | [] -> t
        | uu____4819 ->
            (match t.tm with
             | Name s -> mk_term (Construct (s, args)) r Un
             | uu____4833 ->
                 FStar_List.fold_left
                   (fun t1  ->
                      fun uu____4843  ->
                        match uu____4843 with
                        | (a,imp) -> mk_term (App (t1, a, imp)) r Un) t args)
  
let (mkRefSet : FStar_Range.range -> term Prims.list -> term) =
  fun r  ->
    fun elts  ->
      let uu____4864 =
        (FStar_Parser_Const.set_empty, FStar_Parser_Const.set_singleton,
          FStar_Parser_Const.set_union, FStar_Parser_Const.heap_addr_of_lid)
         in
      match uu____4864 with
      | (empty_lid,singleton_lid,union_lid,addr_of_lid) ->
          let empty1 =
            let uu____4878 =
              let uu____4879 = FStar_Ident.set_lid_range empty_lid r  in
              Var uu____4879  in
            mk_term uu____4878 r Expr  in
          let addr_of =
            let uu____4881 =
              let uu____4882 = FStar_Ident.set_lid_range addr_of_lid r  in
              Var uu____4882  in
            mk_term uu____4881 r Expr  in
          let singleton1 =
            let uu____4884 =
              let uu____4885 = FStar_Ident.set_lid_range singleton_lid r  in
              Var uu____4885  in
            mk_term uu____4884 r Expr  in
          let union1 =
            let uu____4887 =
              let uu____4888 = FStar_Ident.set_lid_range union_lid r  in
              Var uu____4888  in
            mk_term uu____4887 r Expr  in
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
        | uu____4944 ->
            (match t.tm with
             | Name s ->
                 let uu____4948 =
                   let uu____4949 =
                     let uu____4960 =
                       FStar_List.map (fun a  -> (a, Nothing)) args  in
                     (s, uu____4960)  in
                   Construct uu____4949  in
                 mk_term uu____4948 r Un
             | uu____4979 ->
                 FStar_List.fold_left
                   (fun t1  -> fun a  -> mk_term (App (t1, a, Nothing)) r Un)
                   t args)
  
let (mkAdmitMagic : FStar_Range.range -> term) =
  fun r  ->
    let unit_const = mk_term (Const FStar_Const.Const_unit) r Expr  in
    let admit1 =
      let admit_name =
        let uu____4992 =
          let uu____4993 =
            FStar_Ident.set_lid_range FStar_Parser_Const.admit_lid r  in
          Var uu____4993  in
        mk_term uu____4992 r Expr  in
      mkExplicitApp admit_name [unit_const] r  in
    let magic1 =
      let magic_name =
        let uu____4996 =
          let uu____4997 =
            FStar_Ident.set_lid_range FStar_Parser_Const.magic_lid r  in
          Var uu____4997  in
        mk_term uu____4996 r Expr  in
      mkExplicitApp magic_name [unit_const] r  in
    let admit_magic = mk_term (Seq (admit1, magic1)) r Expr  in admit_magic
  
let mkWildAdmitMagic :
  'Auu____5003 .
    FStar_Range.range ->
      (pattern,'Auu____5003 FStar_Pervasives_Native.option,term)
        FStar_Pervasives_Native.tuple3
  =
  fun r  ->
    let uu____5017 = mkAdmitMagic r  in
    ((mk_pattern (PatWild FStar_Pervasives_Native.None) r),
      FStar_Pervasives_Native.None, uu____5017)
  
let focusBranches :
  'Auu____5026 .
    (Prims.bool,(pattern,'Auu____5026 FStar_Pervasives_Native.option,
                  term) FStar_Pervasives_Native.tuple3)
      FStar_Pervasives_Native.tuple2 Prims.list ->
      FStar_Range.range ->
        (pattern,'Auu____5026 FStar_Pervasives_Native.option,term)
          FStar_Pervasives_Native.tuple3 Prims.list
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
            let uu____5118 =
              FStar_List.filter FStar_Pervasives_Native.fst branches  in
            FStar_All.pipe_right uu____5118
              (FStar_List.map FStar_Pervasives_Native.snd)
             in
          let uu____5205 =
            let uu____5216 = mkWildAdmitMagic r  in [uu____5216]  in
          FStar_List.append focussed uu____5205))
      else
        FStar_All.pipe_right branches
          (FStar_List.map FStar_Pervasives_Native.snd)
  
let focusLetBindings :
  'Auu____5308 .
    (Prims.bool,('Auu____5308,term) FStar_Pervasives_Native.tuple2)
      FStar_Pervasives_Native.tuple2 Prims.list ->
      FStar_Range.range ->
        ('Auu____5308,term) FStar_Pervasives_Native.tuple2 Prims.list
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
           (fun uu____5380  ->
              match uu____5380 with
              | (f,lb) ->
                  if f
                  then lb
                  else
                    (let uu____5408 = mkAdmitMagic r  in
                     ((FStar_Pervasives_Native.fst lb), uu____5408))) lbs)
      else
        FStar_All.pipe_right lbs (FStar_List.map FStar_Pervasives_Native.snd)
  
let focusAttrLetBindings :
  'Auu____5450 'Auu____5451 .
    ('Auu____5450,(Prims.bool,('Auu____5451,term)
                                FStar_Pervasives_Native.tuple2)
                    FStar_Pervasives_Native.tuple2)
      FStar_Pervasives_Native.tuple2 Prims.list ->
      FStar_Range.range ->
        ('Auu____5450,('Auu____5451,term) FStar_Pervasives_Native.tuple2)
          FStar_Pervasives_Native.tuple2 Prims.list
  =
  fun lbs  ->
    fun r  ->
      let should_filter =
        FStar_Util.for_some
          (fun uu____5517  ->
             match uu____5517 with | (attr,(focus,uu____5532)) -> focus) lbs
         in
      if should_filter
      then
        (FStar_Errors.log_issue r
           (FStar_Errors.Warning_Filtered,
             "Focusing on only some cases in this (mutually) recursive definition");
         FStar_List.map
           (fun uu____5584  ->
              match uu____5584 with
              | (attr,(f,lb)) ->
                  if f
                  then (attr, lb)
                  else
                    (let uu____5637 =
                       let uu____5642 = mkAdmitMagic r  in
                       ((FStar_Pervasives_Native.fst lb), uu____5642)  in
                     (attr, uu____5637))) lbs)
      else
        FStar_All.pipe_right lbs
          (FStar_List.map
             (fun uu____5696  ->
                match uu____5696 with | (attr,(uu____5718,lb)) -> (attr, lb)))
  
let (mkFsTypApp : term -> term Prims.list -> FStar_Range.range -> term) =
  fun t  ->
    fun args  ->
      fun r  ->
        let uu____5759 = FStar_List.map (fun a  -> (a, FsTypApp)) args  in
        mkApp t uu____5759 r
  
let (mkTuple : term Prims.list -> FStar_Range.range -> term) =
  fun args  ->
    fun r  ->
      let cons1 =
        FStar_Parser_Const.mk_tuple_data_lid (FStar_List.length args) r  in
      let uu____5787 = FStar_List.map (fun x  -> (x, Nothing)) args  in
      mkApp (mk_term (Name cons1) r Expr) uu____5787 r
  
let (mkDTuple : term Prims.list -> FStar_Range.range -> term) =
  fun args  ->
    fun r  ->
      let cons1 =
        FStar_Parser_Const.mk_dtuple_data_lid (FStar_List.length args) r  in
      let uu____5815 = FStar_List.map (fun x  -> (x, Nothing)) args  in
      mkApp (mk_term (Name cons1) r Expr) uu____5815 r
  
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
                       | PatVar (x,uu____5908) ->
                           mk_term
                             (Refine
                                ((mk_binder (Annotated (x, t)) t_range
                                    Type_level FStar_Pervasives_Native.None),
                                  phi)) range Type_level
                       | uu____5913 ->
                           let x = FStar_Ident.gen t_range  in
                           let phi1 =
                             let x_var =
                               let uu____5917 =
                                 let uu____5918 = FStar_Ident.lid_of_ids [x]
                                    in
                                 Var uu____5918  in
                               mk_term uu____5917 phi.range Formula  in
                             let pat_branch =
                               (pat, FStar_Pervasives_Native.None, phi)  in
                             let otherwise_branch =
                               let uu____5939 =
                                 let uu____5940 =
                                   let uu____5941 =
                                     FStar_Ident.lid_of_path ["False"]
                                       phi.range
                                      in
                                   Name uu____5941  in
                                 mk_term uu____5940 phi.range Formula  in
                               ((mk_pattern
                                   (PatWild FStar_Pervasives_Native.None)
                                   phi.range), FStar_Pervasives_Native.None,
                                 uu____5939)
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
    (FStar_Ident.ident,term,term FStar_Pervasives_Native.option)
      FStar_Pervasives_Native.tuple3 FStar_Pervasives_Native.option)
  =
  fun t1  ->
    match t1.tm with
    | NamedTyp (x,t) ->
        FStar_Pervasives_Native.Some (x, t, FStar_Pervasives_Native.None)
    | Refine
        ({ b = Annotated (x,t); brange = uu____6027; blevel = uu____6028;
           aqual = uu____6029;_},t')
        ->
        FStar_Pervasives_Native.Some
          (x, t, (FStar_Pervasives_Native.Some t'))
    | Paren t -> extract_named_refinement t
    | uu____6044 -> FStar_Pervasives_Native.None
  
let rec (as_mlist :
  ((FStar_Ident.lid,decl) FStar_Pervasives_Native.tuple2,decl Prims.list)
    FStar_Pervasives_Native.tuple2 -> decl Prims.list -> modul)
  =
  fun cur  ->
    fun ds  ->
      let uu____6087 = cur  in
      match uu____6087 with
      | ((m_name,m_decl),cur1) ->
          (match ds with
           | [] -> Module (m_name, (m_decl :: (FStar_List.rev cur1)))
           | d::ds1 ->
               (match d.d with
                | TopLevelModule m' ->
                    FStar_Errors.raise_error
                      (FStar_Errors.Fatal_UnexpectedModuleDeclaration,
                        "Unexpected module declaration") d.drange
                | uu____6116 -> as_mlist ((m_name, m_decl), (d :: cur1)) ds1))
  
let (as_frag :
  Prims.bool -> FStar_Range.range -> decl Prims.list -> inputFragment) =
  fun is_light  ->
    fun light_range  ->
      fun ds  ->
        let uu____6142 =
          match ds with
          | d::ds1 -> (d, ds1)
          | [] -> FStar_Exn.raise FStar_Errors.Empty_frag  in
        match uu____6142 with
        | (d,ds1) ->
            (match d.d with
             | TopLevelModule m ->
                 let ds2 =
                   if is_light
                   then
                     let uu____6179 =
                       mk_decl (Pragma LightOff) light_range []  in
                     uu____6179 :: ds1
                   else ds1  in
                 let m1 = as_mlist ((m, d), []) ds2  in FStar_Util.Inl m1
             | uu____6190 ->
                 let ds2 = d :: ds1  in
                 (FStar_List.iter
                    (fun uu___96_6201  ->
                       match uu___96_6201 with
                       | { d = TopLevelModule uu____6202; drange = r;
                           doc = uu____6204; quals = uu____6205;
                           attrs = uu____6206;_} ->
                           FStar_Errors.raise_error
                             (FStar_Errors.Fatal_UnexpectedModuleDeclaration,
                               "Unexpected module declaration") r
                       | uu____6209 -> ()) ds2;
                  FStar_Util.Inr ds2))
  
let (compile_op :
  Prims.int -> Prims.string -> FStar_Range.range -> Prims.string) =
  fun arity  ->
    fun s  ->
      fun r  ->
        let name_of_char uu___97_6233 =
          match uu___97_6233 with
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
                  (Prims.strcat "Unexpected operator symbol: '"
                     (Prims.strcat (FStar_Util.string_of_char c) "'"))) r
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
        | uu____6258 ->
            let uu____6259 =
              let uu____6260 =
                let uu____6263 = FStar_String.list_of_string s  in
                FStar_List.map name_of_char uu____6263  in
              FStar_String.concat "_" uu____6260  in
            Prims.strcat "op_" uu____6259
  
let (compile_op' : Prims.string -> FStar_Range.range -> Prims.string) =
  fun s  -> fun r  -> compile_op (~- (Prims.parse_int "1")) s r 
let (string_of_fsdoc :
  (Prims.string,(Prims.string,Prims.string) FStar_Pervasives_Native.tuple2
                  Prims.list)
    FStar_Pervasives_Native.tuple2 -> Prims.string)
  =
  fun uu____6292  ->
    match uu____6292 with
    | (comment,keywords) ->
        let uu____6317 =
          let uu____6318 =
            FStar_List.map
              (fun uu____6328  ->
                 match uu____6328 with
                 | (k,v1) -> Prims.strcat k (Prims.strcat "->" v1)) keywords
             in
          FStar_String.concat "," uu____6318  in
        Prims.strcat comment uu____6317
  
let (string_of_let_qualifier : let_qualifier -> Prims.string) =
  fun uu___98_6339  ->
    match uu___98_6339 with | NoLetQualifier  -> "" | Rec  -> "rec"
  
let to_string_l :
  'Auu____6348 .
    Prims.string ->
      ('Auu____6348 -> Prims.string) ->
        'Auu____6348 Prims.list -> Prims.string
  =
  fun sep  ->
    fun f  ->
      fun l  ->
        let uu____6373 = FStar_List.map f l  in
        FStar_String.concat sep uu____6373
  
let (imp_to_string : imp -> Prims.string) =
  fun uu___99_6380  ->
    match uu___99_6380 with | Hash  -> "#" | uu____6381 -> ""
  
let rec (term_to_string : term -> Prims.string) =
  fun x  ->
    match x.tm with
    | Wild  -> "_"
    | Requires (t,uu____6410) ->
        let uu____6415 = term_to_string t  in
        FStar_Util.format1 "(requires %s)" uu____6415
    | Ensures (t,uu____6417) ->
        let uu____6422 = term_to_string t  in
        FStar_Util.format1 "(ensures %s)" uu____6422
    | Labeled (t,l,uu____6425) ->
        let uu____6426 = term_to_string t  in
        FStar_Util.format2 "(labeled %s %s)" l uu____6426
    | Const c -> FStar_Parser_Const.const_to_string c
    | Op (s,xs) ->
        let uu____6434 = FStar_Ident.text_of_id s  in
        let uu____6435 =
          let uu____6436 =
            FStar_List.map
              (fun x1  -> FStar_All.pipe_right x1 term_to_string) xs
             in
          FStar_String.concat ", " uu____6436  in
        FStar_Util.format2 "%s(%s)" uu____6434 uu____6435
    | Tvar id1 -> id1.FStar_Ident.idText
    | Uvar id1 -> id1.FStar_Ident.idText
    | Var l -> l.FStar_Ident.str
    | Name l -> l.FStar_Ident.str
    | Construct (l,args) ->
        let uu____6459 =
          to_string_l " "
            (fun uu____6468  ->
               match uu____6468 with
               | (a,imp) ->
                   let uu____6475 = term_to_string a  in
                   FStar_Util.format2 "%s%s" (imp_to_string imp) uu____6475)
            args
           in
        FStar_Util.format2 "(%s %s)" l.FStar_Ident.str uu____6459
    | Abs (pats,t) ->
        let uu____6482 = to_string_l " " pat_to_string pats  in
        let uu____6483 = FStar_All.pipe_right t term_to_string  in
        FStar_Util.format2 "(fun %s -> %s)" uu____6482 uu____6483
    | App (t1,t2,imp) ->
        let uu____6487 = FStar_All.pipe_right t1 term_to_string  in
        let uu____6488 = FStar_All.pipe_right t2 term_to_string  in
        FStar_Util.format3 "%s %s%s" uu____6487 (imp_to_string imp)
          uu____6488
    | Let (Rec ,(a,(p,b))::lbs,body) ->
        let uu____6546 = attrs_opt_to_string a  in
        let uu____6547 =
          let uu____6548 = FStar_All.pipe_right p pat_to_string  in
          let uu____6549 = FStar_All.pipe_right b term_to_string  in
          FStar_Util.format2 "%s=%s" uu____6548 uu____6549  in
        let uu____6550 =
          to_string_l " "
            (fun uu____6570  ->
               match uu____6570 with
               | (a1,(p1,b1)) ->
                   let uu____6598 = attrs_opt_to_string a1  in
                   let uu____6599 = FStar_All.pipe_right p1 pat_to_string  in
                   let uu____6600 = FStar_All.pipe_right b1 term_to_string
                      in
                   FStar_Util.format3 "%sand %s=%s" uu____6598 uu____6599
                     uu____6600) lbs
           in
        let uu____6601 = FStar_All.pipe_right body term_to_string  in
        FStar_Util.format4 "%slet rec %s%s in %s" uu____6546 uu____6547
          uu____6550 uu____6601
    | Let (q,(attrs,(pat,tm))::[],body) ->
        let uu____6657 = attrs_opt_to_string attrs  in
        let uu____6658 = FStar_All.pipe_right pat pat_to_string  in
        let uu____6659 = FStar_All.pipe_right tm term_to_string  in
        let uu____6660 = FStar_All.pipe_right body term_to_string  in
        FStar_Util.format5 "%slet %s %s = %s in %s" uu____6657
          (string_of_let_qualifier q) uu____6658 uu____6659 uu____6660
    | Seq (t1,t2) ->
        let uu____6663 = FStar_All.pipe_right t1 term_to_string  in
        let uu____6664 = FStar_All.pipe_right t2 term_to_string  in
        FStar_Util.format2 "%s; %s" uu____6663 uu____6664
    | If (t1,t2,t3) ->
        let uu____6668 = FStar_All.pipe_right t1 term_to_string  in
        let uu____6669 = FStar_All.pipe_right t2 term_to_string  in
        let uu____6670 = FStar_All.pipe_right t3 term_to_string  in
        FStar_Util.format3 "if %s then %s else %s" uu____6668 uu____6669
          uu____6670
    | Match (t,branches) ->
        let uu____6693 = FStar_All.pipe_right t term_to_string  in
        let uu____6694 =
          to_string_l " | "
            (fun uu____6710  ->
               match uu____6710 with
               | (p,w,e) ->
                   let uu____6726 = FStar_All.pipe_right p pat_to_string  in
                   let uu____6727 =
                     match w with
                     | FStar_Pervasives_Native.None  -> ""
                     | FStar_Pervasives_Native.Some e1 ->
                         let uu____6729 = term_to_string e1  in
                         FStar_Util.format1 "when %s" uu____6729
                      in
                   let uu____6730 = FStar_All.pipe_right e term_to_string  in
                   FStar_Util.format3 "%s %s -> %s" uu____6726 uu____6727
                     uu____6730) branches
           in
        FStar_Util.format2 "match %s with %s" uu____6693 uu____6694
    | Ascribed (t1,t2,FStar_Pervasives_Native.None ) ->
        let uu____6735 = FStar_All.pipe_right t1 term_to_string  in
        let uu____6736 = FStar_All.pipe_right t2 term_to_string  in
        FStar_Util.format2 "(%s : %s)" uu____6735 uu____6736
    | Ascribed (t1,t2,FStar_Pervasives_Native.Some tac) ->
        let uu____6742 = FStar_All.pipe_right t1 term_to_string  in
        let uu____6743 = FStar_All.pipe_right t2 term_to_string  in
        let uu____6744 = FStar_All.pipe_right tac term_to_string  in
        FStar_Util.format3 "(%s : %s by %s)" uu____6742 uu____6743 uu____6744
    | Record (FStar_Pervasives_Native.Some e,fields) ->
        let uu____6761 = FStar_All.pipe_right e term_to_string  in
        let uu____6762 =
          to_string_l " "
            (fun uu____6771  ->
               match uu____6771 with
               | (l,e1) ->
                   let uu____6778 = FStar_All.pipe_right e1 term_to_string
                      in
                   FStar_Util.format2 "%s=%s" l.FStar_Ident.str uu____6778)
            fields
           in
        FStar_Util.format2 "{%s with %s}" uu____6761 uu____6762
    | Record (FStar_Pervasives_Native.None ,fields) ->
        let uu____6794 =
          to_string_l " "
            (fun uu____6803  ->
               match uu____6803 with
               | (l,e) ->
                   let uu____6810 = FStar_All.pipe_right e term_to_string  in
                   FStar_Util.format2 "%s=%s" l.FStar_Ident.str uu____6810)
            fields
           in
        FStar_Util.format1 "{%s}" uu____6794
    | Project (e,l) ->
        let uu____6813 = FStar_All.pipe_right e term_to_string  in
        FStar_Util.format2 "%s.%s" uu____6813 l.FStar_Ident.str
    | Product ([],t) -> term_to_string t
    | Product (b::hd1::tl1,t) ->
        term_to_string
          (mk_term
             (Product
                ([b], (mk_term (Product ((hd1 :: tl1), t)) x.range x.level)))
             x.range x.level)
    | Product (b::[],t) when x.level = Type_level ->
        let uu____6833 = FStar_All.pipe_right b binder_to_string  in
        let uu____6834 = FStar_All.pipe_right t term_to_string  in
        FStar_Util.format2 "%s -> %s" uu____6833 uu____6834
    | Product (b::[],t) when x.level = Kind ->
        let uu____6839 = FStar_All.pipe_right b binder_to_string  in
        let uu____6840 = FStar_All.pipe_right t term_to_string  in
        FStar_Util.format2 "%s => %s" uu____6839 uu____6840
    | Sum (binders,t) ->
        let uu____6855 =
          FStar_All.pipe_right (FStar_List.append binders [FStar_Util.Inr t])
            (FStar_List.map
               (fun uu___100_6884  ->
                  match uu___100_6884 with
                  | FStar_Util.Inl b -> binder_to_string b
                  | FStar_Util.Inr t1 -> term_to_string t1))
           in
        FStar_All.pipe_right uu____6855 (FStar_String.concat " & ")
    | QForall (bs,pats,t) ->
        let uu____6908 = to_string_l " " binder_to_string bs  in
        let uu____6909 =
          to_string_l " \\/ " (to_string_l "; " term_to_string) pats  in
        let uu____6912 = FStar_All.pipe_right t term_to_string  in
        FStar_Util.format3 "forall %s.{:pattern %s} %s" uu____6908 uu____6909
          uu____6912
    | QExists (bs,pats,t) ->
        let uu____6928 = to_string_l " " binder_to_string bs  in
        let uu____6929 =
          to_string_l " \\/ " (to_string_l "; " term_to_string) pats  in
        let uu____6932 = FStar_All.pipe_right t term_to_string  in
        FStar_Util.format3 "exists %s.{:pattern %s} %s" uu____6928 uu____6929
          uu____6932
    | Refine (b,t) ->
        let uu____6935 = FStar_All.pipe_right b binder_to_string  in
        let uu____6936 = FStar_All.pipe_right t term_to_string  in
        FStar_Util.format2 "%s:{%s}" uu____6935 uu____6936
    | NamedTyp (x1,t) ->
        let uu____6939 = FStar_All.pipe_right t term_to_string  in
        FStar_Util.format2 "%s:%s" x1.FStar_Ident.idText uu____6939
    | Paren t ->
        let uu____6941 = FStar_All.pipe_right t term_to_string  in
        FStar_Util.format1 "(%s)" uu____6941
    | Product (bs,t) ->
        let uu____6948 =
          let uu____6949 =
            FStar_All.pipe_right bs (FStar_List.map binder_to_string)  in
          FStar_All.pipe_right uu____6949 (FStar_String.concat ",")  in
        let uu____6958 = FStar_All.pipe_right t term_to_string  in
        FStar_Util.format2 "Unidentified product: [%s] %s" uu____6948
          uu____6958
    | t -> "_"

and (binder_to_string : binder -> Prims.string) =
  fun x  ->
    let s =
      match x.b with
      | Variable i -> i.FStar_Ident.idText
      | TVariable i -> FStar_Util.format1 "%s:_" i.FStar_Ident.idText
      | TAnnotated (i,t) ->
          let uu____6966 = FStar_All.pipe_right t term_to_string  in
          FStar_Util.format2 "%s:%s" i.FStar_Ident.idText uu____6966
      | Annotated (i,t) ->
          let uu____6969 = FStar_All.pipe_right t term_to_string  in
          FStar_Util.format2 "%s:%s" i.FStar_Ident.idText uu____6969
      | NoName t -> FStar_All.pipe_right t term_to_string  in
    let uu____6971 = aqual_to_string x.aqual  in
    FStar_Util.format2 "%s%s" uu____6971 s

and (aqual_to_string :
  arg_qualifier FStar_Pervasives_Native.option -> Prims.string) =
  fun uu___101_6972  ->
    match uu___101_6972 with
    | FStar_Pervasives_Native.Some (Equality ) -> "$"
    | FStar_Pervasives_Native.Some (Implicit ) -> "#"
    | uu____6975 -> ""

and (pat_to_string : pattern -> Prims.string) =
  fun x  ->
    match x.pat with
    | PatWild (FStar_Pervasives_Native.None ) -> "_"
    | PatWild uu____6979 -> "#_"
    | PatConst c -> FStar_Parser_Const.const_to_string c
    | PatApp (p,ps) ->
        let uu____6989 = FStar_All.pipe_right p pat_to_string  in
        let uu____6990 = to_string_l " " pat_to_string ps  in
        FStar_Util.format2 "(%s %s)" uu____6989 uu____6990
    | PatTvar (i,aq) ->
        let uu____6997 = aqual_to_string aq  in
        FStar_Util.format2 "%s%s" uu____6997 i.FStar_Ident.idText
    | PatVar (i,aq) ->
        let uu____7004 = aqual_to_string aq  in
        FStar_Util.format2 "%s%s" uu____7004 i.FStar_Ident.idText
    | PatName l -> l.FStar_Ident.str
    | PatList l ->
        let uu____7009 = to_string_l "; " pat_to_string l  in
        FStar_Util.format1 "[%s]" uu____7009
    | PatTuple (l,false ) ->
        let uu____7015 = to_string_l ", " pat_to_string l  in
        FStar_Util.format1 "(%s)" uu____7015
    | PatTuple (l,true ) ->
        let uu____7021 = to_string_l ", " pat_to_string l  in
        FStar_Util.format1 "(|%s|)" uu____7021
    | PatRecord l ->
        let uu____7029 =
          to_string_l "; "
            (fun uu____7038  ->
               match uu____7038 with
               | (f,e) ->
                   let uu____7045 = FStar_All.pipe_right e pat_to_string  in
                   FStar_Util.format2 "%s=%s" f.FStar_Ident.str uu____7045) l
           in
        FStar_Util.format1 "{%s}" uu____7029
    | PatOr l -> to_string_l "|\n " pat_to_string l
    | PatOp op ->
        let uu____7050 = FStar_Ident.text_of_id op  in
        FStar_Util.format1 "(%s)" uu____7050
    | PatAscribed (p,(t,FStar_Pervasives_Native.None )) ->
        let uu____7061 = FStar_All.pipe_right p pat_to_string  in
        let uu____7062 = FStar_All.pipe_right t term_to_string  in
        FStar_Util.format2 "(%s:%s)" uu____7061 uu____7062
    | PatAscribed (p,(t,FStar_Pervasives_Native.Some tac)) ->
        let uu____7074 = FStar_All.pipe_right p pat_to_string  in
        let uu____7075 = FStar_All.pipe_right t term_to_string  in
        let uu____7076 = FStar_All.pipe_right tac term_to_string  in
        FStar_Util.format3 "(%s:%s by %s)" uu____7074 uu____7075 uu____7076

and (attrs_opt_to_string :
  term Prims.list FStar_Pervasives_Native.option -> Prims.string) =
  fun uu___102_7077  ->
    match uu___102_7077 with
    | FStar_Pervasives_Native.None  -> ""
    | FStar_Pervasives_Native.Some attrs ->
        let uu____7089 =
          let uu____7090 = FStar_List.map term_to_string attrs  in
          FStar_All.pipe_right uu____7090 (FStar_String.concat "; ")  in
        FStar_Util.format1 "[@ %s]" uu____7089

let rec (head_id_of_pat : pattern -> FStar_Ident.lident Prims.list) =
  fun p  ->
    match p.pat with
    | PatName l -> [l]
    | PatVar (i,uu____7106) ->
        let uu____7111 = FStar_Ident.lid_of_ids [i]  in [uu____7111]
    | PatApp (p1,uu____7113) -> head_id_of_pat p1
    | PatAscribed (p1,uu____7119) -> head_id_of_pat p1
    | uu____7132 -> []
  
let lids_of_let :
  'Auu____7137 .
    (pattern,'Auu____7137) FStar_Pervasives_Native.tuple2 Prims.list ->
      FStar_Ident.lident Prims.list
  =
  fun defs  ->
    FStar_All.pipe_right defs
      (FStar_List.collect
         (fun uu____7172  ->
            match uu____7172 with | (p,uu____7180) -> head_id_of_pat p))
  
let (id_of_tycon : tycon -> Prims.string) =
  fun uu___103_7185  ->
    match uu___103_7185 with
    | TyconAbstract (i,uu____7187,uu____7188) -> i.FStar_Ident.idText
    | TyconAbbrev (i,uu____7198,uu____7199,uu____7200) ->
        i.FStar_Ident.idText
    | TyconRecord (i,uu____7210,uu____7211,uu____7212) ->
        i.FStar_Ident.idText
    | TyconVariant (i,uu____7242,uu____7243,uu____7244) ->
        i.FStar_Ident.idText
  
let (decl_to_string : decl -> Prims.string) =
  fun d  ->
    match d.d with
    | TopLevelModule l -> Prims.strcat "module " l.FStar_Ident.str
    | Open l -> Prims.strcat "open " l.FStar_Ident.str
    | Friend l -> Prims.strcat "friend " l.FStar_Ident.str
    | Include l -> Prims.strcat "include " l.FStar_Ident.str
    | ModuleAbbrev (i,l) ->
        FStar_Util.format2 "module %s = %s" i.FStar_Ident.idText
          l.FStar_Ident.str
    | TopLevelLet (uu____7292,pats) ->
        let uu____7306 =
          let uu____7307 =
            let uu____7310 = lids_of_let pats  in
            FStar_All.pipe_right uu____7310
              (FStar_List.map (fun l  -> l.FStar_Ident.str))
             in
          FStar_All.pipe_right uu____7307 (FStar_String.concat ", ")  in
        Prims.strcat "let " uu____7306
    | Main uu____7321 -> "main ..."
    | Assume (i,uu____7323) -> Prims.strcat "assume " i.FStar_Ident.idText
    | Tycon (uu____7324,uu____7325,tys) ->
        let uu____7343 =
          let uu____7344 =
            FStar_All.pipe_right tys
              (FStar_List.map
                 (fun uu____7366  ->
                    match uu____7366 with | (x,uu____7374) -> id_of_tycon x))
             in
          FStar_All.pipe_right uu____7344 (FStar_String.concat ", ")  in
        Prims.strcat "type " uu____7343
    | Val (i,uu____7382) -> Prims.strcat "val " i.FStar_Ident.idText
    | Exception (i,uu____7384) ->
        Prims.strcat "exception " i.FStar_Ident.idText
    | NewEffect (DefineEffect (i,uu____7390,uu____7391,uu____7392)) ->
        Prims.strcat "new_effect " i.FStar_Ident.idText
    | NewEffect (RedefineEffect (i,uu____7402,uu____7403)) ->
        Prims.strcat "new_effect " i.FStar_Ident.idText
    | Splice (ids,t) ->
        let uu____7414 =
          let uu____7415 =
            let uu____7416 =
              FStar_List.map (fun i  -> i.FStar_Ident.idText) ids  in
            FStar_All.pipe_left (FStar_String.concat ";") uu____7416  in
          let uu____7423 =
            let uu____7424 =
              let uu____7425 = term_to_string t  in
              Prims.strcat uu____7425 ")"  in
            Prims.strcat "] (" uu____7424  in
          Prims.strcat uu____7415 uu____7423  in
        Prims.strcat "splice[" uu____7414
    | SubEffect uu____7426 -> "sub_effect"
    | Pragma uu____7427 -> "pragma"
    | Fsdoc uu____7428 -> "fsdoc"
  
let (modul_to_string : modul -> Prims.string) =
  fun m  ->
    match m with
    | Module (uu____7434,decls) ->
        let uu____7440 =
          FStar_All.pipe_right decls (FStar_List.map decl_to_string)  in
        FStar_All.pipe_right uu____7440 (FStar_String.concat "\n")
    | Interface (uu____7449,decls,uu____7451) ->
        let uu____7456 =
          FStar_All.pipe_right decls (FStar_List.map decl_to_string)  in
        FStar_All.pipe_right uu____7456 (FStar_String.concat "\n")
  