open Prims
type level =
<<<<<<< HEAD
  | Un 
  | Expr 
  | Type_level 
  | Kind 
  | Formula 
let uu___is_Un : level -> Prims.bool =
  fun projectee  -> match projectee with | Un  -> true | uu____5 -> false 
let uu___is_Expr : level -> Prims.bool =
  fun projectee  -> match projectee with | Expr  -> true | uu____10 -> false 
let uu___is_Type_level : level -> Prims.bool =
  fun projectee  ->
    match projectee with | Type_level  -> true | uu____15 -> false
  
let uu___is_Kind : level -> Prims.bool =
  fun projectee  -> match projectee with | Kind  -> true | uu____20 -> false 
let uu___is_Formula : level -> Prims.bool =
=======
  | Un
  | Expr
  | Type_level
  | Kind
  | Formula
let (uu___is_Un :level -> Prims.bool)=
  fun projectee  -> match projectee with | Un  -> true | uu____5 -> false
let (uu___is_Expr :level -> Prims.bool)=
  fun projectee  -> match projectee with | Expr  -> true | uu____10 -> false
let (uu___is_Type_level :level -> Prims.bool)=
  fun projectee  ->
    match projectee with | Type_level  -> true | uu____15 -> false
let (uu___is_Kind :level -> Prims.bool)=
  fun projectee  -> match projectee with | Kind  -> true | uu____20 -> false
let (uu___is_Formula :level -> Prims.bool)=
>>>>>>> taramana_pointers_with_codes_modifies
  fun projectee  ->
    match projectee with | Formula  -> true | uu____25 -> false
  
type imp =
<<<<<<< HEAD
  | FsTypApp 
  | Hash 
  | UnivApp 
  | Nothing 
let uu___is_FsTypApp : imp -> Prims.bool =
  fun projectee  ->
    match projectee with | FsTypApp  -> true | uu____30 -> false
  
let uu___is_Hash : imp -> Prims.bool =
  fun projectee  -> match projectee with | Hash  -> true | uu____35 -> false 
let uu___is_UnivApp : imp -> Prims.bool =
  fun projectee  ->
    match projectee with | UnivApp  -> true | uu____40 -> false
  
let uu___is_Nothing : imp -> Prims.bool =
=======
  | FsTypApp
  | Hash
  | UnivApp
  | Nothing
let (uu___is_FsTypApp :imp -> Prims.bool)=
  fun projectee  ->
    match projectee with | FsTypApp  -> true | uu____30 -> false
let (uu___is_Hash :imp -> Prims.bool)=
  fun projectee  -> match projectee with | Hash  -> true | uu____35 -> false
let (uu___is_UnivApp :imp -> Prims.bool)=
  fun projectee  ->
    match projectee with | UnivApp  -> true | uu____40 -> false
let (uu___is_Nothing :imp -> Prims.bool)=
>>>>>>> taramana_pointers_with_codes_modifies
  fun projectee  ->
    match projectee with | Nothing  -> true | uu____45 -> false
  
type arg_qualifier =
<<<<<<< HEAD
  | Implicit 
  | Equality 
let uu___is_Implicit : arg_qualifier -> Prims.bool =
  fun projectee  ->
    match projectee with | Implicit  -> true | uu____50 -> false
  
let uu___is_Equality : arg_qualifier -> Prims.bool =
=======
  | Implicit
  | Equality
let (uu___is_Implicit :arg_qualifier -> Prims.bool)=
  fun projectee  ->
    match projectee with | Implicit  -> true | uu____50 -> false
let (uu___is_Equality :arg_qualifier -> Prims.bool)=
>>>>>>> taramana_pointers_with_codes_modifies
  fun projectee  ->
    match projectee with | Equality  -> true | uu____55 -> false
  
type aqual = arg_qualifier FStar_Pervasives_Native.option
type let_qualifier =
<<<<<<< HEAD
  | NoLetQualifier 
  | Rec 
  | Mutable 
let uu___is_NoLetQualifier : let_qualifier -> Prims.bool =
  fun projectee  ->
    match projectee with | NoLetQualifier  -> true | uu____62 -> false
  
let uu___is_Rec : let_qualifier -> Prims.bool =
  fun projectee  -> match projectee with | Rec  -> true | uu____67 -> false 
let uu___is_Mutable : let_qualifier -> Prims.bool =
=======
  | NoLetQualifier
  | Rec
  | Mutable
let (uu___is_NoLetQualifier :let_qualifier -> Prims.bool)=
  fun projectee  ->
    match projectee with | NoLetQualifier  -> true | uu____62 -> false
let (uu___is_Rec :let_qualifier -> Prims.bool)=
  fun projectee  -> match projectee with | Rec  -> true | uu____67 -> false
let (uu___is_Mutable :let_qualifier -> Prims.bool)=
>>>>>>> taramana_pointers_with_codes_modifies
  fun projectee  ->
    match projectee with | Mutable  -> true | uu____72 -> false
  
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
  (let_qualifier,(pattern,term) FStar_Pervasives_Native.tuple2 Prims.list,
  term) FStar_Pervasives_Native.tuple3 
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
  | Sum of (binder Prims.list,term) FStar_Pervasives_Native.tuple2 
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
  
  | Assign of (FStar_Ident.ident,term) FStar_Pervasives_Native.tuple2 
  | Discrim of FStar_Ident.lid 
  | Attributes of term Prims.list 
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
  aqual: aqual }
and pattern' =
  | PatWild 
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
  | PatAscribed of (pattern,term) FStar_Pervasives_Native.tuple2 
  | PatOr of pattern Prims.list 
  | PatOp of FStar_Ident.ident 
and pattern = {
<<<<<<< HEAD
  pat: pattern' ;
  prange: FStar_Range.range }
let uu___is_Wild : term' -> Prims.bool =
  fun projectee  -> match projectee with | Wild  -> true | uu____539 -> false 
let uu___is_Const : term' -> Prims.bool =
  fun projectee  ->
    match projectee with | Const _0 -> true | uu____545 -> false
  
let __proj__Const__item___0 : term' -> FStar_Const.sconst =
  fun projectee  -> match projectee with | Const _0 -> _0 
let uu___is_Op : term' -> Prims.bool =
  fun projectee  -> match projectee with | Op _0 -> true | uu____565 -> false 
let __proj__Op__item___0 :
  term' -> (FStar_Ident.ident,term Prims.list) FStar_Pervasives_Native.tuple2
  = fun projectee  -> match projectee with | Op _0 -> _0 
let uu___is_Tvar : term' -> Prims.bool =
  fun projectee  ->
    match projectee with | Tvar _0 -> true | uu____597 -> false
  
let __proj__Tvar__item___0 : term' -> FStar_Ident.ident =
  fun projectee  -> match projectee with | Tvar _0 -> _0 
let uu___is_Uvar : term' -> Prims.bool =
  fun projectee  ->
    match projectee with | Uvar _0 -> true | uu____611 -> false
  
let __proj__Uvar__item___0 : term' -> FStar_Ident.ident =
  fun projectee  -> match projectee with | Uvar _0 -> _0 
let uu___is_Var : term' -> Prims.bool =
  fun projectee  ->
    match projectee with | Var _0 -> true | uu____625 -> false
  
let __proj__Var__item___0 : term' -> FStar_Ident.lid =
  fun projectee  -> match projectee with | Var _0 -> _0 
let uu___is_Name : term' -> Prims.bool =
  fun projectee  ->
    match projectee with | Name _0 -> true | uu____639 -> false
  
let __proj__Name__item___0 : term' -> FStar_Ident.lid =
  fun projectee  -> match projectee with | Name _0 -> _0 
let uu___is_Projector : term' -> Prims.bool =
  fun projectee  ->
    match projectee with | Projector _0 -> true | uu____657 -> false
  
let __proj__Projector__item___0 :
  term' -> (FStar_Ident.lid,FStar_Ident.ident) FStar_Pervasives_Native.tuple2
  = fun projectee  -> match projectee with | Projector _0 -> _0 
let uu___is_Construct : term' -> Prims.bool =
  fun projectee  ->
    match projectee with | Construct _0 -> true | uu____693 -> false
  
let __proj__Construct__item___0 :
  term' ->
    (FStar_Ident.lid,(term,imp) FStar_Pervasives_Native.tuple2 Prims.list)
      FStar_Pervasives_Native.tuple2
  = fun projectee  -> match projectee with | Construct _0 -> _0 
let uu___is_Abs : term' -> Prims.bool =
  fun projectee  ->
    match projectee with | Abs _0 -> true | uu____743 -> false
  
let __proj__Abs__item___0 :
  term' -> (pattern Prims.list,term) FStar_Pervasives_Native.tuple2 =
  fun projectee  -> match projectee with | Abs _0 -> _0 
let uu___is_App : term' -> Prims.bool =
  fun projectee  ->
    match projectee with | App _0 -> true | uu____781 -> false
  
let __proj__App__item___0 :
  term' -> (term,term,imp) FStar_Pervasives_Native.tuple3 =
  fun projectee  -> match projectee with | App _0 -> _0 
let uu___is_Let : term' -> Prims.bool =
  fun projectee  ->
    match projectee with | Let _0 -> true | uu____825 -> false
  
let __proj__Let__item___0 :
  term' ->
    (let_qualifier,(pattern,term) FStar_Pervasives_Native.tuple2 Prims.list,
      term) FStar_Pervasives_Native.tuple3
  = fun projectee  -> match projectee with | Let _0 -> _0 
let uu___is_LetOpen : term' -> Prims.bool =
  fun projectee  ->
    match projectee with | LetOpen _0 -> true | uu____879 -> false
  
let __proj__LetOpen__item___0 :
  term' -> (FStar_Ident.lid,term) FStar_Pervasives_Native.tuple2 =
  fun projectee  -> match projectee with | LetOpen _0 -> _0 
let uu___is_Seq : term' -> Prims.bool =
  fun projectee  ->
    match projectee with | Seq _0 -> true | uu____909 -> false
  
let __proj__Seq__item___0 :
  term' -> (term,term) FStar_Pervasives_Native.tuple2 =
  fun projectee  -> match projectee with | Seq _0 -> _0 
let uu___is_Bind : term' -> Prims.bool =
  fun projectee  ->
    match projectee with | Bind _0 -> true | uu____941 -> false
  
let __proj__Bind__item___0 :
  term' -> (FStar_Ident.ident,term,term) FStar_Pervasives_Native.tuple3 =
  fun projectee  -> match projectee with | Bind _0 -> _0 
let uu___is_If : term' -> Prims.bool =
  fun projectee  -> match projectee with | If _0 -> true | uu____979 -> false 
let __proj__If__item___0 :
  term' -> (term,term,term) FStar_Pervasives_Native.tuple3 =
  fun projectee  -> match projectee with | If _0 -> _0 
let uu___is_Match : term' -> Prims.bool =
  fun projectee  ->
    match projectee with | Match _0 -> true | uu____1025 -> false
  
let __proj__Match__item___0 :
  term' ->
    (term,(pattern,term FStar_Pervasives_Native.option,term)
            FStar_Pervasives_Native.tuple3 Prims.list)
      FStar_Pervasives_Native.tuple2
  = fun projectee  -> match projectee with | Match _0 -> _0 
let uu___is_TryWith : term' -> Prims.bool =
  fun projectee  ->
    match projectee with | TryWith _0 -> true | uu____1095 -> false
  
let __proj__TryWith__item___0 :
  term' ->
    (term,(pattern,term FStar_Pervasives_Native.option,term)
            FStar_Pervasives_Native.tuple3 Prims.list)
      FStar_Pervasives_Native.tuple2
  = fun projectee  -> match projectee with | TryWith _0 -> _0 
let uu___is_Ascribed : term' -> Prims.bool =
  fun projectee  ->
    match projectee with | Ascribed _0 -> true | uu____1159 -> false
  
let __proj__Ascribed__item___0 :
  term' ->
    (term,term,term FStar_Pervasives_Native.option)
      FStar_Pervasives_Native.tuple3
  = fun projectee  -> match projectee with | Ascribed _0 -> _0 
let uu___is_Record : term' -> Prims.bool =
  fun projectee  ->
    match projectee with | Record _0 -> true | uu____1209 -> false
  
let __proj__Record__item___0 :
  term' ->
    (term FStar_Pervasives_Native.option,(FStar_Ident.lid,term)
                                           FStar_Pervasives_Native.tuple2
                                           Prims.list)
      FStar_Pervasives_Native.tuple2
  = fun projectee  -> match projectee with | Record _0 -> _0 
let uu___is_Project : term' -> Prims.bool =
  fun projectee  ->
    match projectee with | Project _0 -> true | uu____1263 -> false
  
let __proj__Project__item___0 :
  term' -> (term,FStar_Ident.lid) FStar_Pervasives_Native.tuple2 =
  fun projectee  -> match projectee with | Project _0 -> _0 
let uu___is_Product : term' -> Prims.bool =
  fun projectee  ->
    match projectee with | Product _0 -> true | uu____1295 -> false
  
let __proj__Product__item___0 :
  term' -> (binder Prims.list,term) FStar_Pervasives_Native.tuple2 =
  fun projectee  -> match projectee with | Product _0 -> _0 
let uu___is_Sum : term' -> Prims.bool =
  fun projectee  ->
    match projectee with | Sum _0 -> true | uu____1333 -> false
  
let __proj__Sum__item___0 :
  term' -> (binder Prims.list,term) FStar_Pervasives_Native.tuple2 =
  fun projectee  -> match projectee with | Sum _0 -> _0 
let uu___is_QForall : term' -> Prims.bool =
  fun projectee  ->
    match projectee with | QForall _0 -> true | uu____1377 -> false
  
let __proj__QForall__item___0 :
  term' ->
    (binder Prims.list,term Prims.list Prims.list,term)
      FStar_Pervasives_Native.tuple3
  = fun projectee  -> match projectee with | QForall _0 -> _0 
let uu___is_QExists : term' -> Prims.bool =
  fun projectee  ->
    match projectee with | QExists _0 -> true | uu____1439 -> false
  
let __proj__QExists__item___0 :
  term' ->
    (binder Prims.list,term Prims.list Prims.list,term)
      FStar_Pervasives_Native.tuple3
  = fun projectee  -> match projectee with | QExists _0 -> _0 
let uu___is_Refine : term' -> Prims.bool =
  fun projectee  ->
    match projectee with | Refine _0 -> true | uu____1493 -> false
  
let __proj__Refine__item___0 :
  term' -> (binder,term) FStar_Pervasives_Native.tuple2 =
  fun projectee  -> match projectee with | Refine _0 -> _0 
let uu___is_NamedTyp : term' -> Prims.bool =
  fun projectee  ->
    match projectee with | NamedTyp _0 -> true | uu____1523 -> false
  
let __proj__NamedTyp__item___0 :
  term' -> (FStar_Ident.ident,term) FStar_Pervasives_Native.tuple2 =
  fun projectee  -> match projectee with | NamedTyp _0 -> _0 
let uu___is_Paren : term' -> Prims.bool =
  fun projectee  ->
    match projectee with | Paren _0 -> true | uu____1549 -> false
  
let __proj__Paren__item___0 : term' -> term =
  fun projectee  -> match projectee with | Paren _0 -> _0 
let uu___is_Requires : term' -> Prims.bool =
  fun projectee  ->
    match projectee with | Requires _0 -> true | uu____1569 -> false
  
let __proj__Requires__item___0 :
  term' ->
    (term,Prims.string FStar_Pervasives_Native.option)
      FStar_Pervasives_Native.tuple2
  = fun projectee  -> match projectee with | Requires _0 -> _0 
let uu___is_Ensures : term' -> Prims.bool =
  fun projectee  ->
    match projectee with | Ensures _0 -> true | uu____1607 -> false
  
let __proj__Ensures__item___0 :
  term' ->
    (term,Prims.string FStar_Pervasives_Native.option)
      FStar_Pervasives_Native.tuple2
  = fun projectee  -> match projectee with | Ensures _0 -> _0 
let uu___is_Labeled : term' -> Prims.bool =
  fun projectee  ->
    match projectee with | Labeled _0 -> true | uu____1645 -> false
  
let __proj__Labeled__item___0 :
  term' -> (term,Prims.string,Prims.bool) FStar_Pervasives_Native.tuple3 =
  fun projectee  -> match projectee with | Labeled _0 -> _0 
let uu___is_Assign : term' -> Prims.bool =
  fun projectee  ->
    match projectee with | Assign _0 -> true | uu____1681 -> false
  
let __proj__Assign__item___0 :
  term' -> (FStar_Ident.ident,term) FStar_Pervasives_Native.tuple2 =
  fun projectee  -> match projectee with | Assign _0 -> _0 
let uu___is_Discrim : term' -> Prims.bool =
  fun projectee  ->
    match projectee with | Discrim _0 -> true | uu____1707 -> false
  
let __proj__Discrim__item___0 : term' -> FStar_Ident.lid =
  fun projectee  -> match projectee with | Discrim _0 -> _0 
let uu___is_Attributes : term' -> Prims.bool =
  fun projectee  ->
    match projectee with | Attributes _0 -> true | uu____1723 -> false
  
let __proj__Attributes__item___0 : term' -> term Prims.list =
  fun projectee  -> match projectee with | Attributes _0 -> _0 
let __proj__Mkterm__item__tm : term -> term' =
=======
  pat: pattern';
  prange: FStar_Range.range;}
let (uu___is_Wild :term' -> Prims.bool)=
  fun projectee  -> match projectee with | Wild  -> true | uu____539 -> false
let (uu___is_Const :term' -> Prims.bool)=
  fun projectee  ->
    match projectee with | Const _0 -> true | uu____545 -> false
let (__proj__Const__item___0 :term' -> FStar_Const.sconst)=
  fun projectee  -> match projectee with | Const _0 -> _0
let (uu___is_Op :term' -> Prims.bool)=
  fun projectee  -> match projectee with | Op _0 -> true | uu____565 -> false
let (__proj__Op__item___0
  :term' ->
     (FStar_Ident.ident,term Prims.list) FStar_Pervasives_Native.tuple2)=
  fun projectee  -> match projectee with | Op _0 -> _0
let (uu___is_Tvar :term' -> Prims.bool)=
  fun projectee  ->
    match projectee with | Tvar _0 -> true | uu____597 -> false
let (__proj__Tvar__item___0 :term' -> FStar_Ident.ident)=
  fun projectee  -> match projectee with | Tvar _0 -> _0
let (uu___is_Uvar :term' -> Prims.bool)=
  fun projectee  ->
    match projectee with | Uvar _0 -> true | uu____611 -> false
let (__proj__Uvar__item___0 :term' -> FStar_Ident.ident)=
  fun projectee  -> match projectee with | Uvar _0 -> _0
let (uu___is_Var :term' -> Prims.bool)=
  fun projectee  ->
    match projectee with | Var _0 -> true | uu____625 -> false
let (__proj__Var__item___0 :term' -> FStar_Ident.lid)=
  fun projectee  -> match projectee with | Var _0 -> _0
let (uu___is_Name :term' -> Prims.bool)=
  fun projectee  ->
    match projectee with | Name _0 -> true | uu____639 -> false
let (__proj__Name__item___0 :term' -> FStar_Ident.lid)=
  fun projectee  -> match projectee with | Name _0 -> _0
let (uu___is_Projector :term' -> Prims.bool)=
  fun projectee  ->
    match projectee with | Projector _0 -> true | uu____657 -> false
let (__proj__Projector__item___0
  :term' ->
     (FStar_Ident.lid,FStar_Ident.ident) FStar_Pervasives_Native.tuple2)=
  fun projectee  -> match projectee with | Projector _0 -> _0
let (uu___is_Construct :term' -> Prims.bool)=
  fun projectee  ->
    match projectee with | Construct _0 -> true | uu____693 -> false
let (__proj__Construct__item___0
  :term' ->
     (FStar_Ident.lid,(term,imp) FStar_Pervasives_Native.tuple2 Prims.list)
       FStar_Pervasives_Native.tuple2)=
  fun projectee  -> match projectee with | Construct _0 -> _0
let (uu___is_Abs :term' -> Prims.bool)=
  fun projectee  ->
    match projectee with | Abs _0 -> true | uu____743 -> false
let (__proj__Abs__item___0
  :term' -> (pattern Prims.list,term) FStar_Pervasives_Native.tuple2)=
  fun projectee  -> match projectee with | Abs _0 -> _0
let (uu___is_App :term' -> Prims.bool)=
  fun projectee  ->
    match projectee with | App _0 -> true | uu____781 -> false
let (__proj__App__item___0
  :term' -> (term,term,imp) FStar_Pervasives_Native.tuple3)=
  fun projectee  -> match projectee with | App _0 -> _0
let (uu___is_Let :term' -> Prims.bool)=
  fun projectee  ->
    match projectee with | Let _0 -> true | uu____825 -> false
let (__proj__Let__item___0
  :term' ->
     (let_qualifier,(pattern,term) FStar_Pervasives_Native.tuple2 Prims.list,
       term) FStar_Pervasives_Native.tuple3)=
  fun projectee  -> match projectee with | Let _0 -> _0
let (uu___is_LetOpen :term' -> Prims.bool)=
  fun projectee  ->
    match projectee with | LetOpen _0 -> true | uu____879 -> false
let (__proj__LetOpen__item___0
  :term' -> (FStar_Ident.lid,term) FStar_Pervasives_Native.tuple2)=
  fun projectee  -> match projectee with | LetOpen _0 -> _0
let (uu___is_Seq :term' -> Prims.bool)=
  fun projectee  ->
    match projectee with | Seq _0 -> true | uu____909 -> false
let (__proj__Seq__item___0
  :term' -> (term,term) FStar_Pervasives_Native.tuple2)=
  fun projectee  -> match projectee with | Seq _0 -> _0
let (uu___is_Bind :term' -> Prims.bool)=
  fun projectee  ->
    match projectee with | Bind _0 -> true | uu____941 -> false
let (__proj__Bind__item___0
  :term' -> (FStar_Ident.ident,term,term) FStar_Pervasives_Native.tuple3)=
  fun projectee  -> match projectee with | Bind _0 -> _0
let (uu___is_If :term' -> Prims.bool)=
  fun projectee  -> match projectee with | If _0 -> true | uu____979 -> false
let (__proj__If__item___0
  :term' -> (term,term,term) FStar_Pervasives_Native.tuple3)=
  fun projectee  -> match projectee with | If _0 -> _0
let (uu___is_Match :term' -> Prims.bool)=
  fun projectee  ->
    match projectee with | Match _0 -> true | uu____1025 -> false
let (__proj__Match__item___0
  :term' ->
     (term,(pattern,term FStar_Pervasives_Native.option,term)
             FStar_Pervasives_Native.tuple3 Prims.list)
       FStar_Pervasives_Native.tuple2)=
  fun projectee  -> match projectee with | Match _0 -> _0
let (uu___is_TryWith :term' -> Prims.bool)=
  fun projectee  ->
    match projectee with | TryWith _0 -> true | uu____1095 -> false
let (__proj__TryWith__item___0
  :term' ->
     (term,(pattern,term FStar_Pervasives_Native.option,term)
             FStar_Pervasives_Native.tuple3 Prims.list)
       FStar_Pervasives_Native.tuple2)=
  fun projectee  -> match projectee with | TryWith _0 -> _0
let (uu___is_Ascribed :term' -> Prims.bool)=
  fun projectee  ->
    match projectee with | Ascribed _0 -> true | uu____1159 -> false
let (__proj__Ascribed__item___0
  :term' ->
     (term,term,term FStar_Pervasives_Native.option)
       FStar_Pervasives_Native.tuple3)=
  fun projectee  -> match projectee with | Ascribed _0 -> _0
let (uu___is_Record :term' -> Prims.bool)=
  fun projectee  ->
    match projectee with | Record _0 -> true | uu____1209 -> false
let (__proj__Record__item___0
  :term' ->
     (term FStar_Pervasives_Native.option,(FStar_Ident.lid,term)
                                            FStar_Pervasives_Native.tuple2
                                            Prims.list)
       FStar_Pervasives_Native.tuple2)=
  fun projectee  -> match projectee with | Record _0 -> _0
let (uu___is_Project :term' -> Prims.bool)=
  fun projectee  ->
    match projectee with | Project _0 -> true | uu____1263 -> false
let (__proj__Project__item___0
  :term' -> (term,FStar_Ident.lid) FStar_Pervasives_Native.tuple2)=
  fun projectee  -> match projectee with | Project _0 -> _0
let (uu___is_Product :term' -> Prims.bool)=
  fun projectee  ->
    match projectee with | Product _0 -> true | uu____1295 -> false
let (__proj__Product__item___0
  :term' -> (binder Prims.list,term) FStar_Pervasives_Native.tuple2)=
  fun projectee  -> match projectee with | Product _0 -> _0
let (uu___is_Sum :term' -> Prims.bool)=
  fun projectee  ->
    match projectee with | Sum _0 -> true | uu____1333 -> false
let (__proj__Sum__item___0
  :term' -> (binder Prims.list,term) FStar_Pervasives_Native.tuple2)=
  fun projectee  -> match projectee with | Sum _0 -> _0
let (uu___is_QForall :term' -> Prims.bool)=
  fun projectee  ->
    match projectee with | QForall _0 -> true | uu____1377 -> false
let (__proj__QForall__item___0
  :term' ->
     (binder Prims.list,term Prims.list Prims.list,term)
       FStar_Pervasives_Native.tuple3)=
  fun projectee  -> match projectee with | QForall _0 -> _0
let (uu___is_QExists :term' -> Prims.bool)=
  fun projectee  ->
    match projectee with | QExists _0 -> true | uu____1439 -> false
let (__proj__QExists__item___0
  :term' ->
     (binder Prims.list,term Prims.list Prims.list,term)
       FStar_Pervasives_Native.tuple3)=
  fun projectee  -> match projectee with | QExists _0 -> _0
let (uu___is_Refine :term' -> Prims.bool)=
  fun projectee  ->
    match projectee with | Refine _0 -> true | uu____1493 -> false
let (__proj__Refine__item___0
  :term' -> (binder,term) FStar_Pervasives_Native.tuple2)=
  fun projectee  -> match projectee with | Refine _0 -> _0
let (uu___is_NamedTyp :term' -> Prims.bool)=
  fun projectee  ->
    match projectee with | NamedTyp _0 -> true | uu____1523 -> false
let (__proj__NamedTyp__item___0
  :term' -> (FStar_Ident.ident,term) FStar_Pervasives_Native.tuple2)=
  fun projectee  -> match projectee with | NamedTyp _0 -> _0
let (uu___is_Paren :term' -> Prims.bool)=
  fun projectee  ->
    match projectee with | Paren _0 -> true | uu____1549 -> false
let (__proj__Paren__item___0 :term' -> term)=
  fun projectee  -> match projectee with | Paren _0 -> _0
let (uu___is_Requires :term' -> Prims.bool)=
  fun projectee  ->
    match projectee with | Requires _0 -> true | uu____1569 -> false
let (__proj__Requires__item___0
  :term' ->
     (term,Prims.string FStar_Pervasives_Native.option)
       FStar_Pervasives_Native.tuple2)=
  fun projectee  -> match projectee with | Requires _0 -> _0
let (uu___is_Ensures :term' -> Prims.bool)=
  fun projectee  ->
    match projectee with | Ensures _0 -> true | uu____1607 -> false
let (__proj__Ensures__item___0
  :term' ->
     (term,Prims.string FStar_Pervasives_Native.option)
       FStar_Pervasives_Native.tuple2)=
  fun projectee  -> match projectee with | Ensures _0 -> _0
let (uu___is_Labeled :term' -> Prims.bool)=
  fun projectee  ->
    match projectee with | Labeled _0 -> true | uu____1645 -> false
let (__proj__Labeled__item___0
  :term' -> (term,Prims.string,Prims.bool) FStar_Pervasives_Native.tuple3)=
  fun projectee  -> match projectee with | Labeled _0 -> _0
let (uu___is_Assign :term' -> Prims.bool)=
  fun projectee  ->
    match projectee with | Assign _0 -> true | uu____1681 -> false
let (__proj__Assign__item___0
  :term' -> (FStar_Ident.ident,term) FStar_Pervasives_Native.tuple2)=
  fun projectee  -> match projectee with | Assign _0 -> _0
let (uu___is_Discrim :term' -> Prims.bool)=
  fun projectee  ->
    match projectee with | Discrim _0 -> true | uu____1707 -> false
let (__proj__Discrim__item___0 :term' -> FStar_Ident.lid)=
  fun projectee  -> match projectee with | Discrim _0 -> _0
let (uu___is_Attributes :term' -> Prims.bool)=
  fun projectee  ->
    match projectee with | Attributes _0 -> true | uu____1723 -> false
let (__proj__Attributes__item___0 :term' -> term Prims.list)=
  fun projectee  -> match projectee with | Attributes _0 -> _0
let (__proj__Mkterm__item__tm :term -> term')=
>>>>>>> taramana_pointers_with_codes_modifies
  fun projectee  ->
    match projectee with
    | { tm = __fname__tm; range = __fname__range; level = __fname__level;_}
        -> __fname__tm
<<<<<<< HEAD
  
let __proj__Mkterm__item__range : term -> FStar_Range.range =
=======
let (__proj__Mkterm__item__range :term -> FStar_Range.range)=
>>>>>>> taramana_pointers_with_codes_modifies
  fun projectee  ->
    match projectee with
    | { tm = __fname__tm; range = __fname__range; level = __fname__level;_}
        -> __fname__range
<<<<<<< HEAD
  
let __proj__Mkterm__item__level : term -> level =
=======
let (__proj__Mkterm__item__level :term -> level)=
>>>>>>> taramana_pointers_with_codes_modifies
  fun projectee  ->
    match projectee with
    | { tm = __fname__tm; range = __fname__range; level = __fname__level;_}
        -> __fname__level
<<<<<<< HEAD
  
let uu___is_Variable : binder' -> Prims.bool =
  fun projectee  ->
    match projectee with | Variable _0 -> true | uu____1764 -> false
  
let __proj__Variable__item___0 : binder' -> FStar_Ident.ident =
  fun projectee  -> match projectee with | Variable _0 -> _0 
let uu___is_TVariable : binder' -> Prims.bool =
  fun projectee  ->
    match projectee with | TVariable _0 -> true | uu____1778 -> false
  
let __proj__TVariable__item___0 : binder' -> FStar_Ident.ident =
  fun projectee  -> match projectee with | TVariable _0 -> _0 
let uu___is_Annotated : binder' -> Prims.bool =
  fun projectee  ->
    match projectee with | Annotated _0 -> true | uu____1796 -> false
  
let __proj__Annotated__item___0 :
  binder' -> (FStar_Ident.ident,term) FStar_Pervasives_Native.tuple2 =
  fun projectee  -> match projectee with | Annotated _0 -> _0 
let uu___is_TAnnotated : binder' -> Prims.bool =
  fun projectee  ->
    match projectee with | TAnnotated _0 -> true | uu____1826 -> false
  
let __proj__TAnnotated__item___0 :
  binder' -> (FStar_Ident.ident,term) FStar_Pervasives_Native.tuple2 =
  fun projectee  -> match projectee with | TAnnotated _0 -> _0 
let uu___is_NoName : binder' -> Prims.bool =
  fun projectee  ->
    match projectee with | NoName _0 -> true | uu____1852 -> false
  
let __proj__NoName__item___0 : binder' -> term =
  fun projectee  -> match projectee with | NoName _0 -> _0 
let __proj__Mkbinder__item__b : binder -> binder' =
=======
let (uu___is_Variable :binder' -> Prims.bool)=
  fun projectee  ->
    match projectee with | Variable _0 -> true | uu____1764 -> false
let (__proj__Variable__item___0 :binder' -> FStar_Ident.ident)=
  fun projectee  -> match projectee with | Variable _0 -> _0
let (uu___is_TVariable :binder' -> Prims.bool)=
  fun projectee  ->
    match projectee with | TVariable _0 -> true | uu____1778 -> false
let (__proj__TVariable__item___0 :binder' -> FStar_Ident.ident)=
  fun projectee  -> match projectee with | TVariable _0 -> _0
let (uu___is_Annotated :binder' -> Prims.bool)=
  fun projectee  ->
    match projectee with | Annotated _0 -> true | uu____1796 -> false
let (__proj__Annotated__item___0
  :binder' -> (FStar_Ident.ident,term) FStar_Pervasives_Native.tuple2)=
  fun projectee  -> match projectee with | Annotated _0 -> _0
let (uu___is_TAnnotated :binder' -> Prims.bool)=
  fun projectee  ->
    match projectee with | TAnnotated _0 -> true | uu____1826 -> false
let (__proj__TAnnotated__item___0
  :binder' -> (FStar_Ident.ident,term) FStar_Pervasives_Native.tuple2)=
  fun projectee  -> match projectee with | TAnnotated _0 -> _0
let (uu___is_NoName :binder' -> Prims.bool)=
  fun projectee  ->
    match projectee with | NoName _0 -> true | uu____1852 -> false
let (__proj__NoName__item___0 :binder' -> term)=
  fun projectee  -> match projectee with | NoName _0 -> _0
let (__proj__Mkbinder__item__b :binder -> binder')=
>>>>>>> taramana_pointers_with_codes_modifies
  fun projectee  ->
    match projectee with
    | { b = __fname__b; brange = __fname__brange; blevel = __fname__blevel;
        aqual = __fname__aqual;_} -> __fname__b
<<<<<<< HEAD
  
let __proj__Mkbinder__item__brange : binder -> FStar_Range.range =
=======
let (__proj__Mkbinder__item__brange :binder -> FStar_Range.range)=
>>>>>>> taramana_pointers_with_codes_modifies
  fun projectee  ->
    match projectee with
    | { b = __fname__b; brange = __fname__brange; blevel = __fname__blevel;
        aqual = __fname__aqual;_} -> __fname__brange
<<<<<<< HEAD
  
let __proj__Mkbinder__item__blevel : binder -> level =
=======
let (__proj__Mkbinder__item__blevel :binder -> level)=
>>>>>>> taramana_pointers_with_codes_modifies
  fun projectee  ->
    match projectee with
    | { b = __fname__b; brange = __fname__brange; blevel = __fname__blevel;
        aqual = __fname__aqual;_} -> __fname__blevel
<<<<<<< HEAD
  
let __proj__Mkbinder__item__aqual : binder -> aqual =
=======
let (__proj__Mkbinder__item__aqual :binder -> aqual)=
>>>>>>> taramana_pointers_with_codes_modifies
  fun projectee  ->
    match projectee with
    | { b = __fname__b; brange = __fname__brange; blevel = __fname__blevel;
        aqual = __fname__aqual;_} -> __fname__aqual
<<<<<<< HEAD
  
let uu___is_PatWild : pattern' -> Prims.bool =
  fun projectee  ->
    match projectee with | PatWild  -> true | uu____1897 -> false
  
let uu___is_PatConst : pattern' -> Prims.bool =
  fun projectee  ->
    match projectee with | PatConst _0 -> true | uu____1903 -> false
  
let __proj__PatConst__item___0 : pattern' -> FStar_Const.sconst =
  fun projectee  -> match projectee with | PatConst _0 -> _0 
let uu___is_PatApp : pattern' -> Prims.bool =
  fun projectee  ->
    match projectee with | PatApp _0 -> true | uu____1923 -> false
  
let __proj__PatApp__item___0 :
  pattern' -> (pattern,pattern Prims.list) FStar_Pervasives_Native.tuple2 =
  fun projectee  -> match projectee with | PatApp _0 -> _0 
let uu___is_PatVar : pattern' -> Prims.bool =
  fun projectee  ->
    match projectee with | PatVar _0 -> true | uu____1961 -> false
  
let __proj__PatVar__item___0 :
  pattern' ->
    (FStar_Ident.ident,arg_qualifier FStar_Pervasives_Native.option)
      FStar_Pervasives_Native.tuple2
  = fun projectee  -> match projectee with | PatVar _0 -> _0 
let uu___is_PatName : pattern' -> Prims.bool =
  fun projectee  ->
    match projectee with | PatName _0 -> true | uu____1993 -> false
  
let __proj__PatName__item___0 : pattern' -> FStar_Ident.lid =
  fun projectee  -> match projectee with | PatName _0 -> _0 
let uu___is_PatTvar : pattern' -> Prims.bool =
  fun projectee  ->
    match projectee with | PatTvar _0 -> true | uu____2013 -> false
  
let __proj__PatTvar__item___0 :
  pattern' ->
    (FStar_Ident.ident,arg_qualifier FStar_Pervasives_Native.option)
      FStar_Pervasives_Native.tuple2
  = fun projectee  -> match projectee with | PatTvar _0 -> _0 
let uu___is_PatList : pattern' -> Prims.bool =
  fun projectee  ->
    match projectee with | PatList _0 -> true | uu____2047 -> false
  
let __proj__PatList__item___0 : pattern' -> pattern Prims.list =
  fun projectee  -> match projectee with | PatList _0 -> _0 
let uu___is_PatTuple : pattern' -> Prims.bool =
  fun projectee  ->
    match projectee with | PatTuple _0 -> true | uu____2073 -> false
  
let __proj__PatTuple__item___0 :
  pattern' -> (pattern Prims.list,Prims.bool) FStar_Pervasives_Native.tuple2
  = fun projectee  -> match projectee with | PatTuple _0 -> _0 
let uu___is_PatRecord : pattern' -> Prims.bool =
  fun projectee  ->
    match projectee with | PatRecord _0 -> true | uu____2111 -> false
  
let __proj__PatRecord__item___0 :
  pattern' ->
    (FStar_Ident.lid,pattern) FStar_Pervasives_Native.tuple2 Prims.list
  = fun projectee  -> match projectee with | PatRecord _0 -> _0 
let uu___is_PatAscribed : pattern' -> Prims.bool =
  fun projectee  ->
    match projectee with | PatAscribed _0 -> true | uu____2147 -> false
  
let __proj__PatAscribed__item___0 :
  pattern' -> (pattern,term) FStar_Pervasives_Native.tuple2 =
  fun projectee  -> match projectee with | PatAscribed _0 -> _0 
let uu___is_PatOr : pattern' -> Prims.bool =
  fun projectee  ->
    match projectee with | PatOr _0 -> true | uu____2175 -> false
  
let __proj__PatOr__item___0 : pattern' -> pattern Prims.list =
  fun projectee  -> match projectee with | PatOr _0 -> _0 
let uu___is_PatOp : pattern' -> Prims.bool =
  fun projectee  ->
    match projectee with | PatOp _0 -> true | uu____2195 -> false
  
let __proj__PatOp__item___0 : pattern' -> FStar_Ident.ident =
  fun projectee  -> match projectee with | PatOp _0 -> _0 
let __proj__Mkpattern__item__pat : pattern -> pattern' =
  fun projectee  ->
    match projectee with
    | { pat = __fname__pat; prange = __fname__prange;_} -> __fname__pat
  
let __proj__Mkpattern__item__prange : pattern -> FStar_Range.range =
=======
let (uu___is_PatWild :pattern' -> Prims.bool)=
  fun projectee  ->
    match projectee with | PatWild  -> true | uu____1897 -> false
let (uu___is_PatConst :pattern' -> Prims.bool)=
  fun projectee  ->
    match projectee with | PatConst _0 -> true | uu____1903 -> false
let (__proj__PatConst__item___0 :pattern' -> FStar_Const.sconst)=
  fun projectee  -> match projectee with | PatConst _0 -> _0
let (uu___is_PatApp :pattern' -> Prims.bool)=
  fun projectee  ->
    match projectee with | PatApp _0 -> true | uu____1923 -> false
let (__proj__PatApp__item___0
  :pattern' -> (pattern,pattern Prims.list) FStar_Pervasives_Native.tuple2)=
  fun projectee  -> match projectee with | PatApp _0 -> _0
let (uu___is_PatVar :pattern' -> Prims.bool)=
  fun projectee  ->
    match projectee with | PatVar _0 -> true | uu____1961 -> false
let (__proj__PatVar__item___0
  :pattern' ->
     (FStar_Ident.ident,arg_qualifier FStar_Pervasives_Native.option)
       FStar_Pervasives_Native.tuple2)=
  fun projectee  -> match projectee with | PatVar _0 -> _0
let (uu___is_PatName :pattern' -> Prims.bool)=
  fun projectee  ->
    match projectee with | PatName _0 -> true | uu____1993 -> false
let (__proj__PatName__item___0 :pattern' -> FStar_Ident.lid)=
  fun projectee  -> match projectee with | PatName _0 -> _0
let (uu___is_PatTvar :pattern' -> Prims.bool)=
  fun projectee  ->
    match projectee with | PatTvar _0 -> true | uu____2013 -> false
let (__proj__PatTvar__item___0
  :pattern' ->
     (FStar_Ident.ident,arg_qualifier FStar_Pervasives_Native.option)
       FStar_Pervasives_Native.tuple2)=
  fun projectee  -> match projectee with | PatTvar _0 -> _0
let (uu___is_PatList :pattern' -> Prims.bool)=
  fun projectee  ->
    match projectee with | PatList _0 -> true | uu____2047 -> false
let (__proj__PatList__item___0 :pattern' -> pattern Prims.list)=
  fun projectee  -> match projectee with | PatList _0 -> _0
let (uu___is_PatTuple :pattern' -> Prims.bool)=
  fun projectee  ->
    match projectee with | PatTuple _0 -> true | uu____2073 -> false
let (__proj__PatTuple__item___0
  :pattern' -> (pattern Prims.list,Prims.bool) FStar_Pervasives_Native.tuple2)=
  fun projectee  -> match projectee with | PatTuple _0 -> _0
let (uu___is_PatRecord :pattern' -> Prims.bool)=
  fun projectee  ->
    match projectee with | PatRecord _0 -> true | uu____2111 -> false
let (__proj__PatRecord__item___0
  :pattern' ->
     (FStar_Ident.lid,pattern) FStar_Pervasives_Native.tuple2 Prims.list)=
  fun projectee  -> match projectee with | PatRecord _0 -> _0
let (uu___is_PatAscribed :pattern' -> Prims.bool)=
  fun projectee  ->
    match projectee with | PatAscribed _0 -> true | uu____2147 -> false
let (__proj__PatAscribed__item___0
  :pattern' -> (pattern,term) FStar_Pervasives_Native.tuple2)=
  fun projectee  -> match projectee with | PatAscribed _0 -> _0
let (uu___is_PatOr :pattern' -> Prims.bool)=
  fun projectee  ->
    match projectee with | PatOr _0 -> true | uu____2175 -> false
let (__proj__PatOr__item___0 :pattern' -> pattern Prims.list)=
  fun projectee  -> match projectee with | PatOr _0 -> _0
let (uu___is_PatOp :pattern' -> Prims.bool)=
  fun projectee  ->
    match projectee with | PatOp _0 -> true | uu____2195 -> false
let (__proj__PatOp__item___0 :pattern' -> FStar_Ident.ident)=
  fun projectee  -> match projectee with | PatOp _0 -> _0
let (__proj__Mkpattern__item__pat :pattern -> pattern')=
  fun projectee  ->
    match projectee with
    | { pat = __fname__pat; prange = __fname__prange;_} -> __fname__pat
let (__proj__Mkpattern__item__prange :pattern -> FStar_Range.range)=
>>>>>>> taramana_pointers_with_codes_modifies
  fun projectee  ->
    match projectee with
    | { pat = __fname__pat; prange = __fname__prange;_} -> __fname__prange
  
type branch =
  (pattern,term FStar_Pervasives_Native.option,term)
    FStar_Pervasives_Native.tuple3
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
<<<<<<< HEAD
  FStar_Pervasives_Native.tuple4 
let uu___is_TyconAbstract : tycon -> Prims.bool =
  fun projectee  ->
    match projectee with | TyconAbstract _0 -> true | uu____2335 -> false
  
let __proj__TyconAbstract__item___0 :
  tycon ->
    (FStar_Ident.ident,binder Prims.list,knd FStar_Pervasives_Native.option)
      FStar_Pervasives_Native.tuple3
  = fun projectee  -> match projectee with | TyconAbstract _0 -> _0 
let uu___is_TyconAbbrev : tycon -> Prims.bool =
  fun projectee  ->
    match projectee with | TyconAbbrev _0 -> true | uu____2391 -> false
  
let __proj__TyconAbbrev__item___0 :
  tycon ->
    (FStar_Ident.ident,binder Prims.list,knd FStar_Pervasives_Native.option,
      term) FStar_Pervasives_Native.tuple4
  = fun projectee  -> match projectee with | TyconAbbrev _0 -> _0 
let uu___is_TyconRecord : tycon -> Prims.bool =
  fun projectee  ->
    match projectee with | TyconRecord _0 -> true | uu____2463 -> false
  
let __proj__TyconRecord__item___0 :
  tycon ->
    (FStar_Ident.ident,binder Prims.list,knd FStar_Pervasives_Native.option,
      (FStar_Ident.ident,term,fsdoc FStar_Pervasives_Native.option)
        FStar_Pervasives_Native.tuple3 Prims.list)
      FStar_Pervasives_Native.tuple4
  = fun projectee  -> match projectee with | TyconRecord _0 -> _0 
let uu___is_TyconVariant : tycon -> Prims.bool =
  fun projectee  ->
    match projectee with | TyconVariant _0 -> true | uu____2569 -> false
  
let __proj__TyconVariant__item___0 :
  tycon ->
    (FStar_Ident.ident,binder Prims.list,knd FStar_Pervasives_Native.option,
      (FStar_Ident.ident,term FStar_Pervasives_Native.option,fsdoc
                                                               FStar_Pervasives_Native.option,
        Prims.bool) FStar_Pervasives_Native.tuple4 Prims.list)
      FStar_Pervasives_Native.tuple4
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
let uu___is_Private : qualifier -> Prims.bool =
  fun projectee  ->
    match projectee with | Private  -> true | uu____2660 -> false
  
let uu___is_Abstract : qualifier -> Prims.bool =
  fun projectee  ->
    match projectee with | Abstract  -> true | uu____2665 -> false
  
let uu___is_Noeq : qualifier -> Prims.bool =
  fun projectee  ->
    match projectee with | Noeq  -> true | uu____2670 -> false
  
let uu___is_Unopteq : qualifier -> Prims.bool =
  fun projectee  ->
    match projectee with | Unopteq  -> true | uu____2675 -> false
  
let uu___is_Assumption : qualifier -> Prims.bool =
  fun projectee  ->
    match projectee with | Assumption  -> true | uu____2680 -> false
  
let uu___is_DefaultEffect : qualifier -> Prims.bool =
  fun projectee  ->
    match projectee with | DefaultEffect  -> true | uu____2685 -> false
  
let uu___is_TotalEffect : qualifier -> Prims.bool =
  fun projectee  ->
    match projectee with | TotalEffect  -> true | uu____2690 -> false
  
let uu___is_Effect_qual : qualifier -> Prims.bool =
  fun projectee  ->
    match projectee with | Effect_qual  -> true | uu____2695 -> false
  
let uu___is_New : qualifier -> Prims.bool =
  fun projectee  -> match projectee with | New  -> true | uu____2700 -> false 
let uu___is_Inline : qualifier -> Prims.bool =
  fun projectee  ->
    match projectee with | Inline  -> true | uu____2705 -> false
  
let uu___is_Visible : qualifier -> Prims.bool =
  fun projectee  ->
    match projectee with | Visible  -> true | uu____2710 -> false
  
let uu___is_Unfold_for_unification_and_vcgen : qualifier -> Prims.bool =
=======
  FStar_Pervasives_Native.tuple4
let (uu___is_TyconAbstract :tycon -> Prims.bool)=
  fun projectee  ->
    match projectee with | TyconAbstract _0 -> true | uu____2335 -> false
let (__proj__TyconAbstract__item___0
  :tycon ->
     (FStar_Ident.ident,binder Prims.list,knd FStar_Pervasives_Native.option)
       FStar_Pervasives_Native.tuple3)=
  fun projectee  -> match projectee with | TyconAbstract _0 -> _0
let (uu___is_TyconAbbrev :tycon -> Prims.bool)=
  fun projectee  ->
    match projectee with | TyconAbbrev _0 -> true | uu____2391 -> false
let (__proj__TyconAbbrev__item___0
  :tycon ->
     (FStar_Ident.ident,binder Prims.list,knd FStar_Pervasives_Native.option,
       term) FStar_Pervasives_Native.tuple4)=
  fun projectee  -> match projectee with | TyconAbbrev _0 -> _0
let (uu___is_TyconRecord :tycon -> Prims.bool)=
  fun projectee  ->
    match projectee with | TyconRecord _0 -> true | uu____2463 -> false
let (__proj__TyconRecord__item___0
  :tycon ->
     (FStar_Ident.ident,binder Prims.list,knd FStar_Pervasives_Native.option,
       (FStar_Ident.ident,term,fsdoc FStar_Pervasives_Native.option)
         FStar_Pervasives_Native.tuple3 Prims.list)
       FStar_Pervasives_Native.tuple4)=
  fun projectee  -> match projectee with | TyconRecord _0 -> _0
let (uu___is_TyconVariant :tycon -> Prims.bool)=
  fun projectee  ->
    match projectee with | TyconVariant _0 -> true | uu____2569 -> false
let (__proj__TyconVariant__item___0
  :tycon ->
     (FStar_Ident.ident,binder Prims.list,knd FStar_Pervasives_Native.option,
       (FStar_Ident.ident,term FStar_Pervasives_Native.option,fsdoc
                                                                FStar_Pervasives_Native.option,
         Prims.bool) FStar_Pervasives_Native.tuple4 Prims.list)
       FStar_Pervasives_Native.tuple4)=
  fun projectee  -> match projectee with | TyconVariant _0 -> _0
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
let (uu___is_Private :qualifier -> Prims.bool)=
  fun projectee  ->
    match projectee with | Private  -> true | uu____2660 -> false
let (uu___is_Abstract :qualifier -> Prims.bool)=
  fun projectee  ->
    match projectee with | Abstract  -> true | uu____2665 -> false
let (uu___is_Noeq :qualifier -> Prims.bool)=
  fun projectee  ->
    match projectee with | Noeq  -> true | uu____2670 -> false
let (uu___is_Unopteq :qualifier -> Prims.bool)=
  fun projectee  ->
    match projectee with | Unopteq  -> true | uu____2675 -> false
let (uu___is_Assumption :qualifier -> Prims.bool)=
  fun projectee  ->
    match projectee with | Assumption  -> true | uu____2680 -> false
let (uu___is_DefaultEffect :qualifier -> Prims.bool)=
  fun projectee  ->
    match projectee with | DefaultEffect  -> true | uu____2685 -> false
let (uu___is_TotalEffect :qualifier -> Prims.bool)=
  fun projectee  ->
    match projectee with | TotalEffect  -> true | uu____2690 -> false
let (uu___is_Effect_qual :qualifier -> Prims.bool)=
  fun projectee  ->
    match projectee with | Effect_qual  -> true | uu____2695 -> false
let (uu___is_New :qualifier -> Prims.bool)=
  fun projectee  -> match projectee with | New  -> true | uu____2700 -> false
let (uu___is_Inline :qualifier -> Prims.bool)=
  fun projectee  ->
    match projectee with | Inline  -> true | uu____2705 -> false
let (uu___is_Visible :qualifier -> Prims.bool)=
  fun projectee  ->
    match projectee with | Visible  -> true | uu____2710 -> false
let (uu___is_Unfold_for_unification_and_vcgen :qualifier -> Prims.bool)=
>>>>>>> taramana_pointers_with_codes_modifies
  fun projectee  ->
    match projectee with
    | Unfold_for_unification_and_vcgen  -> true
    | uu____2715 -> false
<<<<<<< HEAD
  
let uu___is_Inline_for_extraction : qualifier -> Prims.bool =
=======
let (uu___is_Inline_for_extraction :qualifier -> Prims.bool)=
>>>>>>> taramana_pointers_with_codes_modifies
  fun projectee  ->
    match projectee with
    | Inline_for_extraction  -> true
    | uu____2720 -> false
<<<<<<< HEAD
  
let uu___is_Irreducible : qualifier -> Prims.bool =
  fun projectee  ->
    match projectee with | Irreducible  -> true | uu____2725 -> false
  
let uu___is_NoExtract : qualifier -> Prims.bool =
  fun projectee  ->
    match projectee with | NoExtract  -> true | uu____2730 -> false
  
let uu___is_Reifiable : qualifier -> Prims.bool =
  fun projectee  ->
    match projectee with | Reifiable  -> true | uu____2735 -> false
  
let uu___is_Reflectable : qualifier -> Prims.bool =
  fun projectee  ->
    match projectee with | Reflectable  -> true | uu____2740 -> false
  
let uu___is_Opaque : qualifier -> Prims.bool =
  fun projectee  ->
    match projectee with | Opaque  -> true | uu____2745 -> false
  
let uu___is_Logic : qualifier -> Prims.bool =
=======
let (uu___is_Irreducible :qualifier -> Prims.bool)=
  fun projectee  ->
    match projectee with | Irreducible  -> true | uu____2725 -> false
let (uu___is_NoExtract :qualifier -> Prims.bool)=
  fun projectee  ->
    match projectee with | NoExtract  -> true | uu____2730 -> false
let (uu___is_Reifiable :qualifier -> Prims.bool)=
  fun projectee  ->
    match projectee with | Reifiable  -> true | uu____2735 -> false
let (uu___is_Reflectable :qualifier -> Prims.bool)=
  fun projectee  ->
    match projectee with | Reflectable  -> true | uu____2740 -> false
let (uu___is_Opaque :qualifier -> Prims.bool)=
  fun projectee  ->
    match projectee with | Opaque  -> true | uu____2745 -> false
let (uu___is_Logic :qualifier -> Prims.bool)=
>>>>>>> taramana_pointers_with_codes_modifies
  fun projectee  ->
    match projectee with | Logic  -> true | uu____2750 -> false
  
type qualifiers = qualifier Prims.list
type attributes_ = term Prims.list
type decoration =
<<<<<<< HEAD
  | Qualifier of qualifier 
  | DeclAttributes of term Prims.list 
  | Doc of fsdoc 
let uu___is_Qualifier : decoration -> Prims.bool =
  fun projectee  ->
    match projectee with | Qualifier _0 -> true | uu____2774 -> false
  
let __proj__Qualifier__item___0 : decoration -> qualifier =
  fun projectee  -> match projectee with | Qualifier _0 -> _0 
let uu___is_DeclAttributes : decoration -> Prims.bool =
  fun projectee  ->
    match projectee with | DeclAttributes _0 -> true | uu____2790 -> false
  
let __proj__DeclAttributes__item___0 : decoration -> term Prims.list =
  fun projectee  -> match projectee with | DeclAttributes _0 -> _0 
let uu___is_Doc : decoration -> Prims.bool =
  fun projectee  ->
    match projectee with | Doc _0 -> true | uu____2810 -> false
  
let __proj__Doc__item___0 : decoration -> fsdoc =
  fun projectee  -> match projectee with | Doc _0 -> _0 
type lift_op =
  | NonReifiableLift of term 
  | ReifiableLift of (term,term) FStar_Pervasives_Native.tuple2 
  | LiftForFree of term 
let uu___is_NonReifiableLift : lift_op -> Prims.bool =
  fun projectee  ->
    match projectee with | NonReifiableLift _0 -> true | uu____2840 -> false
  
let __proj__NonReifiableLift__item___0 : lift_op -> term =
  fun projectee  -> match projectee with | NonReifiableLift _0 -> _0 
let uu___is_ReifiableLift : lift_op -> Prims.bool =
  fun projectee  ->
    match projectee with | ReifiableLift _0 -> true | uu____2858 -> false
  
let __proj__ReifiableLift__item___0 :
  lift_op -> (term,term) FStar_Pervasives_Native.tuple2 =
  fun projectee  -> match projectee with | ReifiableLift _0 -> _0 
let uu___is_LiftForFree : lift_op -> Prims.bool =
  fun projectee  ->
    match projectee with | LiftForFree _0 -> true | uu____2884 -> false
  
let __proj__LiftForFree__item___0 : lift_op -> term =
  fun projectee  -> match projectee with | LiftForFree _0 -> _0 
type lift =
  {
  msource: FStar_Ident.lid ;
  mdest: FStar_Ident.lid ;
  lift_op: lift_op }
let __proj__Mklift__item__msource : lift -> FStar_Ident.lid =
=======
  | Qualifier of qualifier
  | DeclAttributes of term Prims.list
  | Doc of fsdoc
let (uu___is_Qualifier :decoration -> Prims.bool)=
  fun projectee  ->
    match projectee with | Qualifier _0 -> true | uu____2774 -> false
let (__proj__Qualifier__item___0 :decoration -> qualifier)=
  fun projectee  -> match projectee with | Qualifier _0 -> _0
let (uu___is_DeclAttributes :decoration -> Prims.bool)=
  fun projectee  ->
    match projectee with | DeclAttributes _0 -> true | uu____2790 -> false
let (__proj__DeclAttributes__item___0 :decoration -> term Prims.list)=
  fun projectee  -> match projectee with | DeclAttributes _0 -> _0
let (uu___is_Doc :decoration -> Prims.bool)=
  fun projectee  ->
    match projectee with | Doc _0 -> true | uu____2810 -> false
let (__proj__Doc__item___0 :decoration -> fsdoc)=
  fun projectee  -> match projectee with | Doc _0 -> _0
type lift_op =
  | NonReifiableLift of term
  | ReifiableLift of (term,term) FStar_Pervasives_Native.tuple2
  | LiftForFree of term
let (uu___is_NonReifiableLift :lift_op -> Prims.bool)=
  fun projectee  ->
    match projectee with | NonReifiableLift _0 -> true | uu____2840 -> false
let (__proj__NonReifiableLift__item___0 :lift_op -> term)=
  fun projectee  -> match projectee with | NonReifiableLift _0 -> _0
let (uu___is_ReifiableLift :lift_op -> Prims.bool)=
  fun projectee  ->
    match projectee with | ReifiableLift _0 -> true | uu____2858 -> false
let (__proj__ReifiableLift__item___0
  :lift_op -> (term,term) FStar_Pervasives_Native.tuple2)=
  fun projectee  -> match projectee with | ReifiableLift _0 -> _0
let (uu___is_LiftForFree :lift_op -> Prims.bool)=
  fun projectee  ->
    match projectee with | LiftForFree _0 -> true | uu____2884 -> false
let (__proj__LiftForFree__item___0 :lift_op -> term)=
  fun projectee  -> match projectee with | LiftForFree _0 -> _0
type lift =
  {
  msource: FStar_Ident.lid;
  mdest: FStar_Ident.lid;
  lift_op: lift_op;}
let (__proj__Mklift__item__msource :lift -> FStar_Ident.lid)=
>>>>>>> taramana_pointers_with_codes_modifies
  fun projectee  ->
    match projectee with
    | { msource = __fname__msource; mdest = __fname__mdest;
        lift_op = __fname__lift_op;_} -> __fname__msource
<<<<<<< HEAD
  
let __proj__Mklift__item__mdest : lift -> FStar_Ident.lid =
=======
let (__proj__Mklift__item__mdest :lift -> FStar_Ident.lid)=
>>>>>>> taramana_pointers_with_codes_modifies
  fun projectee  ->
    match projectee with
    | { msource = __fname__msource; mdest = __fname__mdest;
        lift_op = __fname__lift_op;_} -> __fname__mdest
<<<<<<< HEAD
  
let __proj__Mklift__item__lift_op : lift -> lift_op =
=======
let (__proj__Mklift__item__lift_op :lift -> lift_op)=
>>>>>>> taramana_pointers_with_codes_modifies
  fun projectee  ->
    match projectee with
    | { msource = __fname__msource; mdest = __fname__mdest;
        lift_op = __fname__lift_op;_} -> __fname__lift_op
  
type pragma =
<<<<<<< HEAD
  | SetOptions of Prims.string 
  | ResetOptions of Prims.string FStar_Pervasives_Native.option 
  | LightOff 
let uu___is_SetOptions : pragma -> Prims.bool =
  fun projectee  ->
    match projectee with | SetOptions _0 -> true | uu____2941 -> false
  
let __proj__SetOptions__item___0 : pragma -> Prims.string =
  fun projectee  -> match projectee with | SetOptions _0 -> _0 
let uu___is_ResetOptions : pragma -> Prims.bool =
  fun projectee  ->
    match projectee with | ResetOptions _0 -> true | uu____2957 -> false
  
let __proj__ResetOptions__item___0 :
  pragma -> Prims.string FStar_Pervasives_Native.option =
  fun projectee  -> match projectee with | ResetOptions _0 -> _0 
let uu___is_LightOff : pragma -> Prims.bool =
=======
  | SetOptions of Prims.string
  | ResetOptions of Prims.string FStar_Pervasives_Native.option
  | LightOff
let (uu___is_SetOptions :pragma -> Prims.bool)=
  fun projectee  ->
    match projectee with | SetOptions _0 -> true | uu____2941 -> false
let (__proj__SetOptions__item___0 :pragma -> Prims.string)=
  fun projectee  -> match projectee with | SetOptions _0 -> _0
let (uu___is_ResetOptions :pragma -> Prims.bool)=
  fun projectee  ->
    match projectee with | ResetOptions _0 -> true | uu____2957 -> false
let (__proj__ResetOptions__item___0
  :pragma -> Prims.string FStar_Pervasives_Native.option)=
  fun projectee  -> match projectee with | ResetOptions _0 -> _0
let (uu___is_LightOff :pragma -> Prims.bool)=
>>>>>>> taramana_pointers_with_codes_modifies
  fun projectee  ->
    match projectee with | LightOff  -> true | uu____2976 -> false
  
type decl' =
  | TopLevelModule of FStar_Ident.lid 
  | Open of FStar_Ident.lid 
  | Include of FStar_Ident.lid 
  | ModuleAbbrev of (FStar_Ident.ident,FStar_Ident.lid)
  FStar_Pervasives_Native.tuple2 
  | TopLevelLet of
  (let_qualifier,(pattern,term) FStar_Pervasives_Native.tuple2 Prims.list)
  FStar_Pervasives_Native.tuple2 
  | Main of term 
  | Tycon of
  (Prims.bool,(tycon,fsdoc FStar_Pervasives_Native.option)
                FStar_Pervasives_Native.tuple2 Prims.list)
  FStar_Pervasives_Native.tuple2 
  | Val of (FStar_Ident.ident,term) FStar_Pervasives_Native.tuple2 
  | Exception of (FStar_Ident.ident,term FStar_Pervasives_Native.option)
  FStar_Pervasives_Native.tuple2 
  | NewEffect of effect_decl 
  | SubEffect of lift 
  | Pragma of pragma 
  | Fsdoc of fsdoc 
  | Assume of (FStar_Ident.ident,term) FStar_Pervasives_Native.tuple2 
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
<<<<<<< HEAD
  FStar_Pervasives_Native.tuple3 
let uu___is_TopLevelModule : decl' -> Prims.bool =
  fun projectee  ->
    match projectee with | TopLevelModule _0 -> true | uu____3128 -> false
  
let __proj__TopLevelModule__item___0 : decl' -> FStar_Ident.lid =
  fun projectee  -> match projectee with | TopLevelModule _0 -> _0 
let uu___is_Open : decl' -> Prims.bool =
  fun projectee  ->
    match projectee with | Open _0 -> true | uu____3142 -> false
  
let __proj__Open__item___0 : decl' -> FStar_Ident.lid =
  fun projectee  -> match projectee with | Open _0 -> _0 
let uu___is_Include : decl' -> Prims.bool =
  fun projectee  ->
    match projectee with | Include _0 -> true | uu____3156 -> false
  
let __proj__Include__item___0 : decl' -> FStar_Ident.lid =
  fun projectee  -> match projectee with | Include _0 -> _0 
let uu___is_ModuleAbbrev : decl' -> Prims.bool =
  fun projectee  ->
    match projectee with | ModuleAbbrev _0 -> true | uu____3174 -> false
  
let __proj__ModuleAbbrev__item___0 :
  decl' -> (FStar_Ident.ident,FStar_Ident.lid) FStar_Pervasives_Native.tuple2
  = fun projectee  -> match projectee with | ModuleAbbrev _0 -> _0 
let uu___is_TopLevelLet : decl' -> Prims.bool =
  fun projectee  ->
    match projectee with | TopLevelLet _0 -> true | uu____3210 -> false
  
let __proj__TopLevelLet__item___0 :
  decl' ->
    (let_qualifier,(pattern,term) FStar_Pervasives_Native.tuple2 Prims.list)
      FStar_Pervasives_Native.tuple2
  = fun projectee  -> match projectee with | TopLevelLet _0 -> _0 
let uu___is_Main : decl' -> Prims.bool =
  fun projectee  ->
    match projectee with | Main _0 -> true | uu____3254 -> false
  
let __proj__Main__item___0 : decl' -> term =
  fun projectee  -> match projectee with | Main _0 -> _0 
let uu___is_Tycon : decl' -> Prims.bool =
  fun projectee  ->
    match projectee with | Tycon _0 -> true | uu____3280 -> false
  
let __proj__Tycon__item___0 :
  decl' ->
    (Prims.bool,(tycon,fsdoc FStar_Pervasives_Native.option)
                  FStar_Pervasives_Native.tuple2 Prims.list)
      FStar_Pervasives_Native.tuple2
  = fun projectee  -> match projectee with | Tycon _0 -> _0 
let uu___is_Val : decl' -> Prims.bool =
  fun projectee  ->
    match projectee with | Val _0 -> true | uu____3334 -> false
  
let __proj__Val__item___0 :
  decl' -> (FStar_Ident.ident,term) FStar_Pervasives_Native.tuple2 =
  fun projectee  -> match projectee with | Val _0 -> _0 
let uu___is_Exception : decl' -> Prims.bool =
  fun projectee  ->
    match projectee with | Exception _0 -> true | uu____3366 -> false
  
let __proj__Exception__item___0 :
  decl' ->
    (FStar_Ident.ident,term FStar_Pervasives_Native.option)
      FStar_Pervasives_Native.tuple2
  = fun projectee  -> match projectee with | Exception _0 -> _0 
let uu___is_NewEffect : decl' -> Prims.bool =
  fun projectee  ->
    match projectee with | NewEffect _0 -> true | uu____3398 -> false
  
let __proj__NewEffect__item___0 : decl' -> effect_decl =
  fun projectee  -> match projectee with | NewEffect _0 -> _0 
let uu___is_SubEffect : decl' -> Prims.bool =
  fun projectee  ->
    match projectee with | SubEffect _0 -> true | uu____3412 -> false
  
let __proj__SubEffect__item___0 : decl' -> lift =
  fun projectee  -> match projectee with | SubEffect _0 -> _0 
let uu___is_Pragma : decl' -> Prims.bool =
  fun projectee  ->
    match projectee with | Pragma _0 -> true | uu____3426 -> false
  
let __proj__Pragma__item___0 : decl' -> pragma =
  fun projectee  -> match projectee with | Pragma _0 -> _0 
let uu___is_Fsdoc : decl' -> Prims.bool =
  fun projectee  ->
    match projectee with | Fsdoc _0 -> true | uu____3440 -> false
  
let __proj__Fsdoc__item___0 : decl' -> fsdoc =
  fun projectee  -> match projectee with | Fsdoc _0 -> _0 
let uu___is_Assume : decl' -> Prims.bool =
  fun projectee  ->
    match projectee with | Assume _0 -> true | uu____3458 -> false
  
let __proj__Assume__item___0 :
  decl' -> (FStar_Ident.ident,term) FStar_Pervasives_Native.tuple2 =
  fun projectee  -> match projectee with | Assume _0 -> _0 
let __proj__Mkdecl__item__d : decl -> decl' =
=======
  FStar_Pervasives_Native.tuple3
let (uu___is_TopLevelModule :decl' -> Prims.bool)=
  fun projectee  ->
    match projectee with | TopLevelModule _0 -> true | uu____3128 -> false
let (__proj__TopLevelModule__item___0 :decl' -> FStar_Ident.lid)=
  fun projectee  -> match projectee with | TopLevelModule _0 -> _0
let (uu___is_Open :decl' -> Prims.bool)=
  fun projectee  ->
    match projectee with | Open _0 -> true | uu____3142 -> false
let (__proj__Open__item___0 :decl' -> FStar_Ident.lid)=
  fun projectee  -> match projectee with | Open _0 -> _0
let (uu___is_Include :decl' -> Prims.bool)=
  fun projectee  ->
    match projectee with | Include _0 -> true | uu____3156 -> false
let (__proj__Include__item___0 :decl' -> FStar_Ident.lid)=
  fun projectee  -> match projectee with | Include _0 -> _0
let (uu___is_ModuleAbbrev :decl' -> Prims.bool)=
  fun projectee  ->
    match projectee with | ModuleAbbrev _0 -> true | uu____3174 -> false
let (__proj__ModuleAbbrev__item___0
  :decl' ->
     (FStar_Ident.ident,FStar_Ident.lid) FStar_Pervasives_Native.tuple2)=
  fun projectee  -> match projectee with | ModuleAbbrev _0 -> _0
let (uu___is_TopLevelLet :decl' -> Prims.bool)=
  fun projectee  ->
    match projectee with | TopLevelLet _0 -> true | uu____3210 -> false
let (__proj__TopLevelLet__item___0
  :decl' ->
     (let_qualifier,(pattern,term) FStar_Pervasives_Native.tuple2 Prims.list)
       FStar_Pervasives_Native.tuple2)=
  fun projectee  -> match projectee with | TopLevelLet _0 -> _0
let (uu___is_Main :decl' -> Prims.bool)=
  fun projectee  ->
    match projectee with | Main _0 -> true | uu____3254 -> false
let (__proj__Main__item___0 :decl' -> term)=
  fun projectee  -> match projectee with | Main _0 -> _0
let (uu___is_Tycon :decl' -> Prims.bool)=
  fun projectee  ->
    match projectee with | Tycon _0 -> true | uu____3280 -> false
let (__proj__Tycon__item___0
  :decl' ->
     (Prims.bool,(tycon,fsdoc FStar_Pervasives_Native.option)
                   FStar_Pervasives_Native.tuple2 Prims.list)
       FStar_Pervasives_Native.tuple2)=
  fun projectee  -> match projectee with | Tycon _0 -> _0
let (uu___is_Val :decl' -> Prims.bool)=
  fun projectee  ->
    match projectee with | Val _0 -> true | uu____3334 -> false
let (__proj__Val__item___0
  :decl' -> (FStar_Ident.ident,term) FStar_Pervasives_Native.tuple2)=
  fun projectee  -> match projectee with | Val _0 -> _0
let (uu___is_Exception :decl' -> Prims.bool)=
  fun projectee  ->
    match projectee with | Exception _0 -> true | uu____3366 -> false
let (__proj__Exception__item___0
  :decl' ->
     (FStar_Ident.ident,term FStar_Pervasives_Native.option)
       FStar_Pervasives_Native.tuple2)=
  fun projectee  -> match projectee with | Exception _0 -> _0
let (uu___is_NewEffect :decl' -> Prims.bool)=
  fun projectee  ->
    match projectee with | NewEffect _0 -> true | uu____3398 -> false
let (__proj__NewEffect__item___0 :decl' -> effect_decl)=
  fun projectee  -> match projectee with | NewEffect _0 -> _0
let (uu___is_SubEffect :decl' -> Prims.bool)=
  fun projectee  ->
    match projectee with | SubEffect _0 -> true | uu____3412 -> false
let (__proj__SubEffect__item___0 :decl' -> lift)=
  fun projectee  -> match projectee with | SubEffect _0 -> _0
let (uu___is_Pragma :decl' -> Prims.bool)=
  fun projectee  ->
    match projectee with | Pragma _0 -> true | uu____3426 -> false
let (__proj__Pragma__item___0 :decl' -> pragma)=
  fun projectee  -> match projectee with | Pragma _0 -> _0
let (uu___is_Fsdoc :decl' -> Prims.bool)=
  fun projectee  ->
    match projectee with | Fsdoc _0 -> true | uu____3440 -> false
let (__proj__Fsdoc__item___0 :decl' -> fsdoc)=
  fun projectee  -> match projectee with | Fsdoc _0 -> _0
let (uu___is_Assume :decl' -> Prims.bool)=
  fun projectee  ->
    match projectee with | Assume _0 -> true | uu____3458 -> false
let (__proj__Assume__item___0
  :decl' -> (FStar_Ident.ident,term) FStar_Pervasives_Native.tuple2)=
  fun projectee  -> match projectee with | Assume _0 -> _0
let (__proj__Mkdecl__item__d :decl -> decl')=
>>>>>>> taramana_pointers_with_codes_modifies
  fun projectee  ->
    match projectee with
    | { d = __fname__d; drange = __fname__drange; doc = __fname__doc;
        quals = __fname__quals; attrs = __fname__attrs;_} -> __fname__d
<<<<<<< HEAD
  
let __proj__Mkdecl__item__drange : decl -> FStar_Range.range =
=======
let (__proj__Mkdecl__item__drange :decl -> FStar_Range.range)=
>>>>>>> taramana_pointers_with_codes_modifies
  fun projectee  ->
    match projectee with
    | { d = __fname__d; drange = __fname__drange; doc = __fname__doc;
        quals = __fname__quals; attrs = __fname__attrs;_} -> __fname__drange
<<<<<<< HEAD
  
let __proj__Mkdecl__item__doc : decl -> fsdoc FStar_Pervasives_Native.option
  =
=======
let (__proj__Mkdecl__item__doc
  :decl -> fsdoc FStar_Pervasives_Native.option)=
>>>>>>> taramana_pointers_with_codes_modifies
  fun projectee  ->
    match projectee with
    | { d = __fname__d; drange = __fname__drange; doc = __fname__doc;
        quals = __fname__quals; attrs = __fname__attrs;_} -> __fname__doc
<<<<<<< HEAD
  
let __proj__Mkdecl__item__quals : decl -> qualifiers =
=======
let (__proj__Mkdecl__item__quals :decl -> qualifiers)=
>>>>>>> taramana_pointers_with_codes_modifies
  fun projectee  ->
    match projectee with
    | { d = __fname__d; drange = __fname__drange; doc = __fname__doc;
        quals = __fname__quals; attrs = __fname__attrs;_} -> __fname__quals
<<<<<<< HEAD
  
let __proj__Mkdecl__item__attrs : decl -> attributes_ =
=======
let (__proj__Mkdecl__item__attrs :decl -> attributes_)=
>>>>>>> taramana_pointers_with_codes_modifies
  fun projectee  ->
    match projectee with
    | { d = __fname__d; drange = __fname__drange; doc = __fname__doc;
        quals = __fname__quals; attrs = __fname__attrs;_} -> __fname__attrs
<<<<<<< HEAD
  
let uu___is_DefineEffect : effect_decl -> Prims.bool =
  fun projectee  ->
    match projectee with | DefineEffect _0 -> true | uu____3555 -> false
  
let __proj__DefineEffect__item___0 :
  effect_decl ->
    (FStar_Ident.ident,binder Prims.list,term,decl Prims.list)
      FStar_Pervasives_Native.tuple4
  = fun projectee  -> match projectee with | DefineEffect _0 -> _0 
let uu___is_RedefineEffect : effect_decl -> Prims.bool =
  fun projectee  ->
    match projectee with | RedefineEffect _0 -> true | uu____3613 -> false
  
let __proj__RedefineEffect__item___0 :
  effect_decl ->
    (FStar_Ident.ident,binder Prims.list,term) FStar_Pervasives_Native.tuple3
  = fun projectee  -> match projectee with | RedefineEffect _0 -> _0 
=======
let (uu___is_DefineEffect :effect_decl -> Prims.bool)=
  fun projectee  ->
    match projectee with | DefineEffect _0 -> true | uu____3555 -> false
let (__proj__DefineEffect__item___0
  :effect_decl ->
     (FStar_Ident.ident,binder Prims.list,term,decl Prims.list)
       FStar_Pervasives_Native.tuple4)=
  fun projectee  -> match projectee with | DefineEffect _0 -> _0
let (uu___is_RedefineEffect :effect_decl -> Prims.bool)=
  fun projectee  ->
    match projectee with | RedefineEffect _0 -> true | uu____3613 -> false
let (__proj__RedefineEffect__item___0
  :effect_decl ->
     (FStar_Ident.ident,binder Prims.list,term)
       FStar_Pervasives_Native.tuple3)=
  fun projectee  -> match projectee with | RedefineEffect _0 -> _0
>>>>>>> taramana_pointers_with_codes_modifies
type modul =
  | Module of (FStar_Ident.lid,decl Prims.list)
  FStar_Pervasives_Native.tuple2 
  | Interface of (FStar_Ident.lid,decl Prims.list,Prims.bool)
<<<<<<< HEAD
  FStar_Pervasives_Native.tuple3 
let uu___is_Module : modul -> Prims.bool =
  fun projectee  ->
    match projectee with | Module _0 -> true | uu____3679 -> false
  
let __proj__Module__item___0 :
  modul -> (FStar_Ident.lid,decl Prims.list) FStar_Pervasives_Native.tuple2 =
  fun projectee  -> match projectee with | Module _0 -> _0 
let uu___is_Interface : modul -> Prims.bool =
  fun projectee  ->
    match projectee with | Interface _0 -> true | uu____3719 -> false
  
let __proj__Interface__item___0 :
  modul ->
    (FStar_Ident.lid,decl Prims.list,Prims.bool)
      FStar_Pervasives_Native.tuple3
  = fun projectee  -> match projectee with | Interface _0 -> _0 
type file = modul Prims.list
type inputFragment = (file,decl Prims.list) FStar_Util.either
let check_id : FStar_Ident.ident -> Prims.unit =
=======
  FStar_Pervasives_Native.tuple3
let (uu___is_Module :modul -> Prims.bool)=
  fun projectee  ->
    match projectee with | Module _0 -> true | uu____3679 -> false
let (__proj__Module__item___0
  :modul -> (FStar_Ident.lid,decl Prims.list) FStar_Pervasives_Native.tuple2)=
  fun projectee  -> match projectee with | Module _0 -> _0
let (uu___is_Interface :modul -> Prims.bool)=
  fun projectee  ->
    match projectee with | Interface _0 -> true | uu____3719 -> false
let (__proj__Interface__item___0
  :modul ->
     (FStar_Ident.lid,decl Prims.list,Prims.bool)
       FStar_Pervasives_Native.tuple3)=
  fun projectee  -> match projectee with | Interface _0 -> _0
type file = modul
type inputFragment = (file,decl Prims.list) FStar_Util.either
let (check_id :FStar_Ident.ident -> Prims.unit)=
>>>>>>> taramana_pointers_with_codes_modifies
  fun id  ->
    let first_char =
      FStar_String.substring id.FStar_Ident.idText (Prims.parse_int "0")
        (Prims.parse_int "1")
       in
    if (FStar_String.lowercase first_char) = first_char
    then ()
    else
      (let uu____3764 =
         let uu____3765 =
           let uu____3770 =
             FStar_Util.format1
               "Invalid identifer '%s'; expected a symbol that begins with a lower-case character"
<<<<<<< HEAD
               id.FStar_Ident.idText
              in
           (uu____3772, (id.FStar_Ident.idRange))  in
         FStar_Errors.Error uu____3767  in
       FStar_Exn.raise uu____3766)
  
let at_most_one :
  'Auu____3781 .
=======
               id.FStar_Ident.idText in
           (uu____3770, (id.FStar_Ident.idRange)) in
         FStar_Errors.Error uu____3765 in
       FStar_Exn.raise uu____3764)
let at_most_one :
  'Auu____3779 .
>>>>>>> taramana_pointers_with_codes_modifies
    Prims.string ->
      FStar_Range.range ->
        'Auu____3779 Prims.list ->
          'Auu____3779 FStar_Pervasives_Native.option=
  fun s  ->
    fun r  ->
      fun l  ->
        match l with
        | x::[] -> FStar_Pervasives_Native.Some x
        | [] -> FStar_Pervasives_Native.None
        | uu____3799 ->
            let uu____3802 =
              let uu____3803 =
                let uu____3808 =
                  FStar_Util.format1
<<<<<<< HEAD
                    "At most one %s is allowed on declarations" s
                   in
                (uu____3810, r)  in
              FStar_Errors.Error uu____3805  in
            FStar_Exn.raise uu____3804
  
let mk_decl : decl' -> FStar_Range.range -> decoration Prims.list -> decl =
=======
                    "At most one %s is allowed on declarations" s in
                (uu____3808, r) in
              FStar_Errors.Error uu____3803 in
            FStar_Exn.raise uu____3802
let (mk_decl :decl' -> FStar_Range.range -> decoration Prims.list -> decl)=
>>>>>>> taramana_pointers_with_codes_modifies
  fun d  ->
    fun r  ->
      fun decorations  ->
        let doc1 =
          let uu____3830 =
            FStar_List.choose
              (fun uu___73_3835  ->
                 match uu___73_3835 with
                 | Doc d1 -> FStar_Pervasives_Native.Some d1
<<<<<<< HEAD
                 | uu____3841 -> FStar_Pervasives_Native.None) decorations
             in
          at_most_one "fsdoc" r uu____3832  in
=======
                 | uu____3839 -> FStar_Pervasives_Native.None) decorations in
          at_most_one "fsdoc" r uu____3830 in
>>>>>>> taramana_pointers_with_codes_modifies
        let attributes_ =
          let uu____3845 =
            FStar_List.choose
              (fun uu___74_3854  ->
                 match uu___74_3854 with
                 | DeclAttributes a -> FStar_Pervasives_Native.Some a
<<<<<<< HEAD
                 | uu____3866 -> FStar_Pervasives_Native.None) decorations
             in
          at_most_one "attribute set" r uu____3847  in
        let attributes_1 = FStar_Util.dflt [] attributes_  in
=======
                 | uu____3864 -> FStar_Pervasives_Native.None) decorations in
          at_most_one "attribute set" r uu____3845 in
        let attributes_1 = FStar_Util.dflt [] attributes_ in
>>>>>>> taramana_pointers_with_codes_modifies
        let qualifiers =
          FStar_List.choose
            (fun uu___75_3879  ->
               match uu___75_3879 with
               | Qualifier q -> FStar_Pervasives_Native.Some q
<<<<<<< HEAD
               | uu____3885 -> FStar_Pervasives_Native.None) decorations
           in
        { d; drange = r; doc = doc1; quals = qualifiers; attrs = attributes_1
        }
  
let mk_binder : binder' -> FStar_Range.range -> level -> aqual -> binder =
  fun b  ->
    fun r  -> fun l  -> fun i  -> { b; brange = r; blevel = l; aqual = i }
  
let mk_term : term' -> FStar_Range.range -> level -> term =
  fun t  -> fun r  -> fun l  -> { tm = t; range = r; level = l } 
let mk_uminus :
  term -> FStar_Range.range -> FStar_Range.range -> level -> term =
=======
               | uu____3883 -> FStar_Pervasives_Native.None) decorations in
        { d; drange = r; doc = doc1; quals = qualifiers; attrs = attributes_1
        }
let (mk_binder :binder' -> FStar_Range.range -> level -> aqual -> binder)=
  fun b  ->
    fun r  -> fun l  -> fun i  -> { b; brange = r; blevel = l; aqual = i }
let (mk_term :term' -> FStar_Range.range -> level -> term)=
  fun t  -> fun r  -> fun l  -> { tm = t; range = r; level = l }
let (mk_uminus
  :term -> FStar_Range.range -> FStar_Range.range -> level -> term)=
>>>>>>> taramana_pointers_with_codes_modifies
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
<<<<<<< HEAD
            | uu____3953 -> Op ((FStar_Ident.mk_ident ("-", rminus)), [t])
             in
          mk_term t1 r l
  
let mk_pattern : pattern' -> FStar_Range.range -> pattern =
  fun p  -> fun r  -> { pat = p; prange = r } 
let un_curry_abs : pattern Prims.list -> term -> term' =
=======
            | uu____3951 -> Op ((FStar_Ident.mk_ident ("-", rminus)), [t]) in
          mk_term t1 r l
let (mk_pattern :pattern' -> FStar_Range.range -> pattern)=
  fun p  -> fun r  -> { pat = p; prange = r }
let (un_curry_abs :pattern Prims.list -> term -> term')=
>>>>>>> taramana_pointers_with_codes_modifies
  fun ps  ->
    fun body  ->
      match body.tm with
      | Abs (p',body') -> Abs ((FStar_List.append ps p'), body')
<<<<<<< HEAD
      | uu____3984 -> Abs (ps, body)
  
let mk_function :
  (pattern,term FStar_Pervasives_Native.option,term)
    FStar_Pervasives_Native.tuple3 Prims.list ->
    FStar_Range.range -> FStar_Range.range -> term
  =
  fun branches  ->
    fun r1  ->
      fun r2  ->
        let x = let i = FStar_Parser_Const.next_id ()  in FStar_Ident.gen r1
           in
        let uu____4021 =
          let uu____4022 =
            let uu____4029 =
              let uu____4030 =
                let uu____4031 =
                  let uu____4046 =
                    let uu____4047 =
                      let uu____4048 = FStar_Ident.lid_of_ids [x]  in
                      Var uu____4048  in
                    mk_term uu____4047 r1 Expr  in
                  (uu____4046, branches)  in
                Match uu____4031  in
              mk_term uu____4030 r2 Expr  in
            ([mk_pattern (PatVar (x, FStar_Pervasives_Native.None)) r1],
              uu____4029)
             in
          Abs uu____4022  in
        mk_term uu____4021 r2 Expr
  
let un_function :
  pattern ->
    term ->
      (pattern,term) FStar_Pervasives_Native.tuple2
        FStar_Pervasives_Native.option
  =
=======
      | uu____3982 -> Abs (ps, body)
let (mk_function
  :(pattern,term FStar_Pervasives_Native.option,term)
     FStar_Pervasives_Native.tuple3 Prims.list ->
     FStar_Range.range -> FStar_Range.range -> term)=
  fun branches  ->
    fun r1  ->
      fun r2  ->
        let x = let i = FStar_Parser_Const.next_id () in FStar_Ident.gen r1 in
        let uu____4019 =
          let uu____4020 =
            let uu____4027 =
              let uu____4028 =
                let uu____4029 =
                  let uu____4044 =
                    let uu____4045 =
                      let uu____4046 = FStar_Ident.lid_of_ids [x] in
                      Var uu____4046 in
                    mk_term uu____4045 r1 Expr in
                  (uu____4044, branches) in
                Match uu____4029 in
              mk_term uu____4028 r2 Expr in
            ([mk_pattern (PatVar (x, FStar_Pervasives_Native.None)) r1],
              uu____4027) in
          Abs uu____4020 in
        mk_term uu____4019 r2 Expr
let (un_function
  :pattern ->
     term ->
       (pattern,term) FStar_Pervasives_Native.tuple2
         FStar_Pervasives_Native.option)=
>>>>>>> taramana_pointers_with_codes_modifies
  fun p  ->
    fun tm  ->
      match ((p.pat), (tm.tm)) with
      | (PatVar uu____4081,Abs (pats,body)) ->
          FStar_Pervasives_Native.Some
            ((mk_pattern (PatApp (p, pats)) p.prange), body)
<<<<<<< HEAD
      | uu____4102 -> FStar_Pervasives_Native.None
  
let lid_with_range :
  FStar_Ident.lident -> FStar_Range.range -> FStar_Ident.lident =
  fun lid  ->
    fun r  ->
      let uu____4119 = FStar_Ident.path_of_lid lid  in
      FStar_Ident.lid_of_path uu____4119 r
  
let consPat : FStar_Range.range -> pattern -> pattern -> pattern' =
=======
      | uu____4100 -> FStar_Pervasives_Native.None
let (lid_with_range
  :FStar_Ident.lident -> FStar_Range.range -> FStar_Ident.lident)=
  fun lid  ->
    fun r  ->
      let uu____4117 = FStar_Ident.path_of_lid lid in
      FStar_Ident.lid_of_path uu____4117 r
let (consPat :FStar_Range.range -> pattern -> pattern -> pattern')=
>>>>>>> taramana_pointers_with_codes_modifies
  fun r  ->
    fun hd1  ->
      fun tl1  ->
        PatApp
          ((mk_pattern (PatName FStar_Parser_Const.cons_lid) r), [hd1; tl1])
<<<<<<< HEAD
  
let consTerm : FStar_Range.range -> term -> term -> term =
=======
let (consTerm :FStar_Range.range -> term -> term -> term)=
>>>>>>> taramana_pointers_with_codes_modifies
  fun r  ->
    fun hd1  ->
      fun tl1  ->
        mk_term
          (Construct
             (FStar_Parser_Const.cons_lid, [(hd1, Nothing); (tl1, Nothing)]))
          r Expr
<<<<<<< HEAD
  
let lexConsTerm : FStar_Range.range -> term -> term -> term =
=======
let (lexConsTerm :FStar_Range.range -> term -> term -> term)=
>>>>>>> taramana_pointers_with_codes_modifies
  fun r  ->
    fun hd1  ->
      fun tl1  ->
        mk_term
          (Construct
             (FStar_Parser_Const.lexcons_lid,
               [(hd1, Nothing); (tl1, Nothing)])) r Expr
<<<<<<< HEAD
  
let mkConsList : FStar_Range.range -> term Prims.list -> term =
=======
let (mkConsList :FStar_Range.range -> term Prims.list -> term)=
>>>>>>> taramana_pointers_with_codes_modifies
  fun r  ->
    fun elts  ->
      let nil = mk_term (Construct (FStar_Parser_Const.nil_lid, [])) r Expr
         in
      FStar_List.fold_right (fun e  -> fun tl1  -> consTerm r e tl1) elts nil
<<<<<<< HEAD
  
let mkLexList : FStar_Range.range -> term Prims.list -> term =
=======
let (mkLexList :FStar_Range.range -> term Prims.list -> term)=
>>>>>>> taramana_pointers_with_codes_modifies
  fun r  ->
    fun elts  ->
      let nil =
        mk_term (Construct (FStar_Parser_Const.lextop_lid, [])) r Expr  in
      FStar_List.fold_right (fun e  -> fun tl1  -> lexConsTerm r e tl1) elts
        nil
<<<<<<< HEAD
  
let ml_comp : term -> term =
  fun t  ->
    let ml = mk_term (Name FStar_Parser_Const.effect_ML_lid) t.range Expr  in
    let t1 = mk_term (App (ml, t, Nothing)) t.range Expr  in t1
  
let tot_comp : term -> term =
  fun t  ->
    let ml = mk_term (Name FStar_Parser_Const.effect_Tot_lid) t.range Expr
       in
    let t1 = mk_term (App (ml, t, Nothing)) t.range Expr  in t1
  
let mkApp :
  term ->
    (term,imp) FStar_Pervasives_Native.tuple2 Prims.list ->
      FStar_Range.range -> term
  =
=======
let (ml_comp :term -> term)=
  fun t  ->
    let ml = mk_term (Name FStar_Parser_Const.effect_ML_lid) t.range Expr in
    let t1 = mk_term (App (ml, t, Nothing)) t.range Expr in t1
let (tot_comp :term -> term)=
  fun t  ->
    let ml = mk_term (Name FStar_Parser_Const.effect_Tot_lid) t.range Expr in
    let t1 = mk_term (App (ml, t, Nothing)) t.range Expr in t1
let (mkApp
  :term ->
     (term,imp) FStar_Pervasives_Native.tuple2 Prims.list ->
       FStar_Range.range -> term)=
>>>>>>> taramana_pointers_with_codes_modifies
  fun t  ->
    fun args  ->
      fun r  ->
        match args with
        | [] -> t
        | uu____4288 ->
            (match t.tm with
             | Name s -> mk_term (Construct (s, args)) r Un
             | uu____4302 ->
                 FStar_List.fold_left
                   (fun t1  ->
                      fun uu____4312  ->
                        match uu____4312 with
                        | (a,imp) -> mk_term (App (t1, a, imp)) r Un) t args)
<<<<<<< HEAD
  
let mkRefSet : FStar_Range.range -> term Prims.list -> term =
=======
let (mkRefSet :FStar_Range.range -> term Prims.list -> term)=
>>>>>>> taramana_pointers_with_codes_modifies
  fun r  ->
    fun elts  ->
      let uu____4331 =
        (FStar_Parser_Const.set_empty, FStar_Parser_Const.set_singleton,
<<<<<<< HEAD
          FStar_Parser_Const.set_union, FStar_Parser_Const.heap_addr_of_lid)
         in
      match uu____4333 with
=======
          FStar_Parser_Const.set_union, FStar_Parser_Const.heap_addr_of_lid) in
      match uu____4331 with
>>>>>>> taramana_pointers_with_codes_modifies
      | (empty_lid,singleton_lid,union_lid,addr_of_lid) ->
          let empty1 =
            mk_term (Var (FStar_Ident.set_lid_range empty_lid r)) r Expr  in
          let addr_of1 =
            mk_term (Var (FStar_Ident.set_lid_range addr_of_lid r)) r Expr
             in
          let singleton1 =
            mk_term (Var (FStar_Ident.set_lid_range singleton_lid r)) r Expr
             in
          let union1 =
            mk_term (Var (FStar_Ident.set_lid_range union_lid r)) r Expr  in
          FStar_List.fold_right
            (fun e  ->
               fun tl1  ->
                 let e1 = mkApp addr_of1 [(e, Nothing)] r  in
                 let single_e = mkApp singleton1 [(e1, Nothing)] r  in
                 mkApp union1 [(single_e, Nothing); (tl1, Nothing)] r) elts
            empty1
<<<<<<< HEAD
  
let mkExplicitApp : term -> term Prims.list -> FStar_Range.range -> term =
=======
let (mkExplicitApp :term -> term Prims.list -> FStar_Range.range -> term)=
>>>>>>> taramana_pointers_with_codes_modifies
  fun t  ->
    fun args  ->
      fun r  ->
        match args with
        | [] -> t
        | uu____4400 ->
            (match t.tm with
             | Name s ->
<<<<<<< HEAD
                 let uu____4406 =
                   let uu____4407 =
                     let uu____4418 =
                       FStar_List.map (fun a  -> (a, Nothing)) args  in
                     (s, uu____4418)  in
                   Construct uu____4407  in
                 mk_term uu____4406 r Un
             | uu____4437 ->
                 FStar_List.fold_left
                   (fun t1  -> fun a  -> mk_term (App (t1, a, Nothing)) r Un)
                   t args)
  
let mkAdmitMagic : FStar_Range.range -> term =
=======
                 let uu____4404 =
                   let uu____4405 =
                     let uu____4416 =
                       FStar_List.map (fun a  -> (a, Nothing)) args in
                     (s, uu____4416) in
                   Construct uu____4405 in
                 mk_term uu____4404 r Un
             | uu____4435 ->
                 FStar_List.fold_left
                   (fun t1  -> fun a  -> mk_term (App (t1, a, Nothing)) r Un)
                   t args)
let (mkAdmitMagic :FStar_Range.range -> term)=
>>>>>>> taramana_pointers_with_codes_modifies
  fun r  ->
    let unit_const = mk_term (Const FStar_Const.Const_unit) r Expr  in
    let admit1 =
      let admit_name =
        mk_term
          (Var (FStar_Ident.set_lid_range FStar_Parser_Const.admit_lid r)) r
          Expr
         in
      mkExplicitApp admit_name [unit_const] r  in
    let magic1 =
      let magic_name =
        mk_term
          (Var (FStar_Ident.set_lid_range FStar_Parser_Const.magic_lid r)) r
<<<<<<< HEAD
          Expr
         in
      mkExplicitApp magic_name [unit_const] r  in
    let admit_magic = mk_term (Seq (admit1, magic1)) r Expr  in admit_magic
  
let mkWildAdmitMagic :
  'Auu____4456 .
=======
          Expr in
      mkExplicitApp magic_name [unit_const] r in
    let admit_magic = mk_term (Seq (admit1, magic1)) r Expr in admit_magic
let mkWildAdmitMagic :
  'Auu____4454 .
>>>>>>> taramana_pointers_with_codes_modifies
    FStar_Range.range ->
      (pattern,'Auu____4454 FStar_Pervasives_Native.option,term)
        FStar_Pervasives_Native.tuple3=
  fun r  ->
<<<<<<< HEAD
    let uu____4469 = mkAdmitMagic r  in
    ((mk_pattern PatWild r), FStar_Pervasives_Native.None, uu____4469)
  
let focusBranches :
  'Auu____4478 .
    (Prims.bool,(pattern,'Auu____4478 FStar_Pervasives_Native.option,
=======
    let uu____4467 = mkAdmitMagic r in
    ((mk_pattern PatWild r), FStar_Pervasives_Native.None, uu____4467)
let focusBranches :
  'Auu____4476 .
    (Prims.bool,(pattern,'Auu____4476 FStar_Pervasives_Native.option,
>>>>>>> taramana_pointers_with_codes_modifies
                  term) FStar_Pervasives_Native.tuple3)
      FStar_Pervasives_Native.tuple2 Prims.list ->
      FStar_Range.range ->
        (pattern,'Auu____4476 FStar_Pervasives_Native.option,term)
          FStar_Pervasives_Native.tuple3 Prims.list=
  fun branches  ->
    fun r  ->
      let should_filter =
        FStar_Util.for_some FStar_Pervasives_Native.fst branches  in
      if should_filter
      then
        (FStar_Errors.warn r "Focusing on only some cases";
         (let focussed =
<<<<<<< HEAD
            let uu____4568 =
              FStar_List.filter FStar_Pervasives_Native.fst branches  in
            FStar_All.pipe_right uu____4568
              (FStar_List.map FStar_Pervasives_Native.snd)
             in
          let uu____4655 =
            let uu____4666 = mkWildAdmitMagic r  in [uu____4666]  in
          FStar_List.append focussed uu____4655))
      else
        FStar_All.pipe_right branches
          (FStar_List.map FStar_Pervasives_Native.snd)
  
let focusLetBindings :
  'Auu____4758 .
    (Prims.bool,('Auu____4758,term) FStar_Pervasives_Native.tuple2)
=======
            let uu____4566 =
              FStar_List.filter FStar_Pervasives_Native.fst branches in
            FStar_All.pipe_right uu____4566
              (FStar_List.map FStar_Pervasives_Native.snd) in
          let uu____4653 =
            let uu____4664 = mkWildAdmitMagic r in [uu____4664] in
          FStar_List.append focussed uu____4653))
      else
        FStar_All.pipe_right branches
          (FStar_List.map FStar_Pervasives_Native.snd)
let focusLetBindings :
  'Auu____4756 .
    (Prims.bool,('Auu____4756,term) FStar_Pervasives_Native.tuple2)
>>>>>>> taramana_pointers_with_codes_modifies
      FStar_Pervasives_Native.tuple2 Prims.list ->
      FStar_Range.range ->
        ('Auu____4756,term) FStar_Pervasives_Native.tuple2 Prims.list=
  fun lbs  ->
    fun r  ->
      let should_filter = FStar_Util.for_some FStar_Pervasives_Native.fst lbs
         in
      if should_filter
      then
        (FStar_Errors.warn r
           "Focusing on only some cases in this (mutually) recursive definition";
         FStar_List.map
           (fun uu____4826  ->
              match uu____4826 with
              | (f,lb) ->
                  if f
                  then lb
                  else
<<<<<<< HEAD
                    (let uu____4856 = mkAdmitMagic r  in
                     ((FStar_Pervasives_Native.fst lb), uu____4856))) lbs)
      else
        FStar_All.pipe_right lbs (FStar_List.map FStar_Pervasives_Native.snd)
  
let mkFsTypApp : term -> term Prims.list -> FStar_Range.range -> term =
  fun t  ->
    fun args  ->
      fun r  ->
        let uu____4906 = FStar_List.map (fun a  -> (a, FsTypApp)) args  in
        mkApp t uu____4906 r
  
let mkTuple : term Prims.list -> FStar_Range.range -> term =
  fun args  ->
    fun r  ->
      let cons1 =
        FStar_Parser_Const.mk_tuple_data_lid (FStar_List.length args) r  in
      let uu____4932 = FStar_List.map (fun x  -> (x, Nothing)) args  in
      mkApp (mk_term (Name cons1) r Expr) uu____4932 r
  
let mkDTuple : term Prims.list -> FStar_Range.range -> term =
  fun args  ->
    fun r  ->
      let cons1 =
        FStar_Parser_Const.mk_dtuple_data_lid (FStar_List.length args) r  in
      let uu____4958 = FStar_List.map (fun x  -> (x, Nothing)) args  in
      mkApp (mk_term (Name cons1) r Expr) uu____4958 r
  
let mkRefinedBinder :
  FStar_Ident.ident ->
    term ->
      Prims.bool ->
        term FStar_Pervasives_Native.option ->
          FStar_Range.range -> aqual -> binder
  =
=======
                    (let uu____4854 = mkAdmitMagic r in
                     ((FStar_Pervasives_Native.fst lb), uu____4854))) lbs)
      else
        FStar_All.pipe_right lbs (FStar_List.map FStar_Pervasives_Native.snd)
let (mkFsTypApp :term -> term Prims.list -> FStar_Range.range -> term)=
  fun t  ->
    fun args  ->
      fun r  ->
        let uu____4904 = FStar_List.map (fun a  -> (a, FsTypApp)) args in
        mkApp t uu____4904 r
let (mkTuple :term Prims.list -> FStar_Range.range -> term)=
  fun args  ->
    fun r  ->
      let cons1 =
        FStar_Parser_Const.mk_tuple_data_lid (FStar_List.length args) r in
      let uu____4930 = FStar_List.map (fun x  -> (x, Nothing)) args in
      mkApp (mk_term (Name cons1) r Expr) uu____4930 r
let (mkDTuple :term Prims.list -> FStar_Range.range -> term)=
  fun args  ->
    fun r  ->
      let cons1 =
        FStar_Parser_Const.mk_dtuple_data_lid (FStar_List.length args) r in
      let uu____4956 = FStar_List.map (fun x  -> (x, Nothing)) args in
      mkApp (mk_term (Name cons1) r Expr) uu____4956 r
let (mkRefinedBinder
  :FStar_Ident.ident ->
     term ->
       Prims.bool ->
         term FStar_Pervasives_Native.option ->
           FStar_Range.range -> aqual -> binder)=
>>>>>>> taramana_pointers_with_codes_modifies
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
<<<<<<< HEAD
  
let mkRefinedPattern :
  pattern ->
    term ->
      Prims.bool ->
        term FStar_Pervasives_Native.option ->
          FStar_Range.range -> FStar_Range.range -> pattern
  =
=======
let (mkRefinedPattern
  :pattern ->
     term ->
       Prims.bool ->
         term FStar_Pervasives_Native.option ->
           FStar_Range.range -> FStar_Range.range -> pattern)=
>>>>>>> taramana_pointers_with_codes_modifies
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
                       | PatVar (x,uu____5033) ->
                           mk_term
                             (Refine
                                ((mk_binder (Annotated (x, t)) t_range
                                    Type_level FStar_Pervasives_Native.None),
                                  phi)) range Type_level
<<<<<<< HEAD
                       | uu____5040 ->
                           let x = FStar_Ident.gen t_range  in
                           let phi1 =
                             let x_var =
                               let uu____5044 =
                                 let uu____5045 = FStar_Ident.lid_of_ids [x]
                                    in
                                 Var uu____5045  in
                               mk_term uu____5044 phi.range Formula  in
=======
                       | uu____5038 ->
                           let x = FStar_Ident.gen t_range in
                           let phi1 =
                             let x_var =
                               let uu____5042 =
                                 let uu____5043 = FStar_Ident.lid_of_ids [x] in
                                 Var uu____5043 in
                               mk_term uu____5042 phi.range Formula in
>>>>>>> taramana_pointers_with_codes_modifies
                             let pat_branch =
                               (pat, FStar_Pervasives_Native.None, phi)  in
                             let otherwise_branch =
                               let uu____5064 =
                                 let uu____5065 =
                                   let uu____5066 =
                                     FStar_Ident.lid_of_path ["False"]
<<<<<<< HEAD
                                       phi.range
                                      in
                                   Name uu____5068  in
                                 mk_term uu____5067 phi.range Formula  in
                               ((mk_pattern PatWild phi.range),
                                 FStar_Pervasives_Native.None, uu____5066)
                                in
=======
                                       phi.range in
                                   Name uu____5066 in
                                 mk_term uu____5065 phi.range Formula in
                               ((mk_pattern PatWild phi.range),
                                 FStar_Pervasives_Native.None, uu____5064) in
>>>>>>> taramana_pointers_with_codes_modifies
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
              mk_pattern (PatAscribed (pat, t1)) range
<<<<<<< HEAD
  
let rec extract_named_refinement :
  term ->
    (FStar_Ident.ident,term,term FStar_Pervasives_Native.option)
      FStar_Pervasives_Native.tuple3 FStar_Pervasives_Native.option
  =
=======
let rec (extract_named_refinement
  :term ->
     (FStar_Ident.ident,term,term FStar_Pervasives_Native.option)
       FStar_Pervasives_Native.tuple3 FStar_Pervasives_Native.option)=
>>>>>>> taramana_pointers_with_codes_modifies
  fun t1  ->
    match t1.tm with
    | NamedTyp (x,t) ->
        FStar_Pervasives_Native.Some (x, t, FStar_Pervasives_Native.None)
    | Refine
        ({ b = Annotated (x,t); brange = uu____5143; blevel = uu____5144;
           aqual = uu____5145;_},t')
        ->
        FStar_Pervasives_Native.Some
          (x, t, (FStar_Pervasives_Native.Some t'))
    | Paren t -> extract_named_refinement t
<<<<<<< HEAD
    | uu____5160 -> FStar_Pervasives_Native.None
  
let rec as_mlist :
  modul Prims.list ->
    ((FStar_Ident.lid,decl) FStar_Pervasives_Native.tuple2,decl Prims.list)
      FStar_Pervasives_Native.tuple2 -> decl Prims.list -> modul Prims.list
  =
  fun out  ->
    fun cur  ->
      fun ds  ->
        let uu____5213 = cur  in
        match uu____5213 with
        | ((m_name,m_decl),cur1) ->
            (match ds with
             | [] ->
                 FStar_List.rev
                   ((Module (m_name, (m_decl :: (FStar_List.rev cur1)))) ::
                   out)
             | d::ds1 ->
                 (match d.d with
                  | TopLevelModule m' ->
                      as_mlist
                        ((Module (m_name, (m_decl :: (FStar_List.rev cur1))))
                        :: out) ((m', d), []) ds1
                  | uu____5256 ->
                      as_mlist out ((m_name, m_decl), (d :: cur1)) ds1))
  
let as_frag :
  Prims.bool ->
    FStar_Range.range ->
      decl Prims.list -> (modul Prims.list,decl Prims.list) FStar_Util.either
  =
=======
    | uu____5158 -> FStar_Pervasives_Native.None
let rec (as_mlist
  :((FStar_Ident.lid,decl) FStar_Pervasives_Native.tuple2,decl Prims.list)
     FStar_Pervasives_Native.tuple2 -> decl Prims.list -> modul)=
  fun cur  ->
    fun ds  ->
      let uu____5199 = cur in
      match uu____5199 with
      | ((m_name,m_decl),cur1) ->
          (match ds with
           | [] -> Module (m_name, (m_decl :: (FStar_List.rev cur1)))
           | d::ds1 ->
               (match d.d with
                | TopLevelModule m' ->
                    FStar_Exn.raise
                      (FStar_Errors.Error
                         ("Unexpected module declaration", (d.drange)))
                | uu____5228 -> as_mlist ((m_name, m_decl), (d :: cur1)) ds1))
let (as_frag
  :Prims.bool -> FStar_Range.range -> decl Prims.list -> inputFragment)=
>>>>>>> taramana_pointers_with_codes_modifies
  fun is_light  ->
    fun light_range  ->
      fun ds  ->
        let uu____5251 =
          match ds with
          | d::ds1 -> (d, ds1)
<<<<<<< HEAD
          | [] -> FStar_Exn.raise FStar_Errors.Empty_frag  in
        match uu____5295 with
=======
          | [] -> FStar_Exn.raise FStar_Errors.Empty_frag in
        match uu____5251 with
>>>>>>> taramana_pointers_with_codes_modifies
        | (d,ds1) ->
            (match d.d with
             | TopLevelModule m ->
                 let ds2 =
                   if is_light
                   then
<<<<<<< HEAD
                     let uu____5348 =
                       mk_decl (Pragma LightOff) light_range []  in
                     uu____5348 :: ds1
                   else ds1  in
                 let ms = as_mlist [] ((m, d), []) ds2  in
                 ((let uu____5360 = FStar_List.tl ms  in
                   match uu____5360 with
                   | (Module (m',uu____5364))::uu____5365 ->
                       let msg =
                         "Support for more than one module in a file is deprecated"
                          in
                       let uu____5373 =
                         FStar_Range.string_of_range
                           (FStar_Ident.range_of_lid m')
                          in
                       FStar_Util.print2_warning "%s (Warning): %s\n"
                         uu____5373 msg
                   | uu____5374 -> ());
                  FStar_Util.Inl ms)
             | uu____5381 ->
                 let ds2 = d :: ds1  in
=======
                     let uu____5288 =
                       mk_decl (Pragma LightOff) light_range [] in
                     uu____5288 :: ds1
                   else ds1 in
                 let m1 = as_mlist ((m, d), []) ds2 in FStar_Util.Inl m1
             | uu____5299 ->
                 let ds2 = d :: ds1 in
>>>>>>> taramana_pointers_with_codes_modifies
                 (FStar_List.iter
                    (fun uu___76_5310  ->
                       match uu___76_5310 with
                       | { d = TopLevelModule uu____5311; drange = r;
                           doc = uu____5313; quals = uu____5314;
                           attrs = uu____5315;_} ->
                           FStar_Exn.raise
                             (FStar_Errors.Error
                                ("Unexpected module declaration", r))
                       | uu____5318 -> ()) ds2;
                  FStar_Util.Inr ds2))
<<<<<<< HEAD
  
let compile_op :
  Prims.int -> Prims.string -> FStar_Range.range -> Prims.string =
=======
let (compile_op
  :Prims.int -> Prims.string -> FStar_Range.range -> Prims.string)=
>>>>>>> taramana_pointers_with_codes_modifies
  fun arity  ->
    fun s  ->
      fun r  ->
        let name_of_char uu___77_5336 =
          match uu___77_5336 with
          | '&' -> "Amp"
          | '@' -> "At"
          | '+' -> "Plus"
          | '-' when arity = (Prims.parse_int "1") -> "Minus"
          | '-' -> "Subtraction"
          | '~' -> "Tilde"
          | '/' -> "Slash"
          | '\\' -> "Backslash"
          | '<' -> "Less"
          | '=' -> "Equals"
          | '>' -> "Greater"
          | '_' -> "Underscore"
          | '|' -> "Bar"
          | '!' -> "Bang"
          | '^' -> "Hat"
          | '%' -> "Percent"
          | '*' -> "Star"
          | '?' -> "Question"
          | ':' -> "Colon"
          | '$' -> "Dollar"
          | '.' -> "Dot"
          | c ->
              FStar_Exn.raise
                (FStar_Errors.Error
                   ((Prims.strcat "Unexpected operator symbol: '"
                       (Prims.strcat (FStar_Util.string_of_char c) "'")), r))
           in
        match s with
        | ".[]<-" -> "op_String_Assignment"
        | ".()<-" -> "op_Array_Assignment"
        | ".[]" -> "op_String_Access"
        | ".()" -> "op_Array_Access"
<<<<<<< HEAD
        | uu____5422 ->
            let uu____5423 =
              let uu____5424 =
                let uu____5427 = FStar_String.list_of_string s  in
                FStar_List.map name_of_char uu____5427  in
              FStar_String.concat "_" uu____5424  in
            Prims.strcat "op_" uu____5423
  
let compile_op' : Prims.string -> FStar_Range.range -> Prims.string =
  fun s  -> fun r  -> compile_op (~- (Prims.parse_int "1")) s r 
let string_of_fsdoc :
  (Prims.string,(Prims.string,Prims.string) FStar_Pervasives_Native.tuple2
                  Prims.list)
    FStar_Pervasives_Native.tuple2 -> Prims.string
  =
  fun uu____5451  ->
    match uu____5451 with
=======
        | uu____5338 ->
            let uu____5339 =
              let uu____5340 =
                let uu____5343 = FStar_String.list_of_string s in
                FStar_List.map name_of_char uu____5343 in
              FStar_String.concat "_" uu____5340 in
            Prims.strcat "op_" uu____5339
let (compile_op' :Prims.string -> FStar_Range.range -> Prims.string)=
  fun s  -> fun r  -> compile_op (- (Prims.parse_int "1")) s r
let (string_of_fsdoc
  :(Prims.string,(Prims.string,Prims.string) FStar_Pervasives_Native.tuple2
                   Prims.list)
     FStar_Pervasives_Native.tuple2 -> Prims.string)=
  fun uu____5367  ->
    match uu____5367 with
>>>>>>> taramana_pointers_with_codes_modifies
    | (comment,keywords) ->
        let uu____5392 =
          let uu____5393 =
            FStar_List.map
<<<<<<< HEAD
              (fun uu____5487  ->
                 match uu____5487 with
                 | (k,v1) -> Prims.strcat k (Prims.strcat "->" v1)) keywords
             in
          FStar_String.concat "," uu____5477  in
        Prims.strcat comment uu____5476
  
let string_of_let_qualifier : let_qualifier -> Prims.string =
  fun uu___79_5497  ->
    match uu___79_5497 with
    | NoLetQualifier  -> ""
    | Rec  -> "rec"
    | Mutable  -> "mutable"
  
let to_string_l :
  'Auu____5506 .
=======
              (fun uu____5403  ->
                 match uu____5403 with
                 | (k,v1) -> Prims.strcat k (Prims.strcat "->" v1)) keywords in
          FStar_String.concat "," uu____5393 in
        Prims.strcat comment uu____5392
let (string_of_let_qualifier :let_qualifier -> Prims.string)=
  fun uu___78_5413  ->
    match uu___78_5413 with
    | NoLetQualifier  -> ""
    | Rec  -> "rec"
    | Mutable  -> "mutable"
let to_string_l :
  'Auu____5422 .
>>>>>>> taramana_pointers_with_codes_modifies
    Prims.string ->
      ('Auu____5422 -> Prims.string) ->
        'Auu____5422 Prims.list -> Prims.string=
  fun sep  ->
    fun f  ->
      fun l  ->
<<<<<<< HEAD
        let uu____5528 = FStar_List.map f l  in
        FStar_String.concat sep uu____5528
  
let imp_to_string : imp -> Prims.string =
  fun uu___80_5534  ->
    match uu___80_5534 with | Hash  -> "#" | uu____5535 -> ""
  
let rec term_to_string : term -> Prims.string =
  fun x  ->
    match x.tm with
    | Wild  -> "_"
    | Requires (t,uu____5546) ->
        let uu____5551 = term_to_string t  in
        FStar_Util.format1 "(requires %s)" uu____5551
    | Ensures (t,uu____5553) ->
        let uu____5558 = term_to_string t  in
        FStar_Util.format1 "(ensures %s)" uu____5558
    | Labeled (t,l,uu____5561) ->
        let uu____5562 = term_to_string t  in
        FStar_Util.format2 "(labeled %s %s)" l uu____5562
=======
        let uu____5444 = FStar_List.map f l in
        FStar_String.concat sep uu____5444
let (imp_to_string :imp -> Prims.string)=
  fun uu___79_5450  ->
    match uu___79_5450 with | Hash  -> "#" | uu____5451 -> ""
let rec (term_to_string :term -> Prims.string)=
  fun x  ->
    match x.tm with
    | Wild  -> "_"
    | Requires (t,uu____5462) ->
        let uu____5467 = term_to_string t in
        FStar_Util.format1 "(requires %s)" uu____5467
    | Ensures (t,uu____5469) ->
        let uu____5474 = term_to_string t in
        FStar_Util.format1 "(ensures %s)" uu____5474
    | Labeled (t,l,uu____5477) ->
        let uu____5478 = term_to_string t in
        FStar_Util.format2 "(labeled %s %s)" l uu____5478
>>>>>>> taramana_pointers_with_codes_modifies
    | Const c -> FStar_Parser_Const.const_to_string c
    | Op (s,xs) ->
        let uu____5486 =
          let uu____5487 =
            FStar_List.map
<<<<<<< HEAD
              (fun x1  -> FStar_All.pipe_right x1 term_to_string) xs
             in
          FStar_String.concat ", " uu____5571  in
        FStar_Util.format2 "%s(%s)" (FStar_Ident.text_of_id s) uu____5570
=======
              (fun x1  -> FStar_All.pipe_right x1 term_to_string) xs in
          FStar_String.concat ", " uu____5487 in
        FStar_Util.format2 "%s(%s)" (FStar_Ident.text_of_id s) uu____5486
>>>>>>> taramana_pointers_with_codes_modifies
    | Tvar id -> id.FStar_Ident.idText
    | Uvar id -> id.FStar_Ident.idText
    | Var l -> l.FStar_Ident.str
    | Name l -> l.FStar_Ident.str
    | Construct (l,args) ->
        let uu____5510 =
          to_string_l " "
            (fun uu____5519  ->
               match uu____5519 with
               | (a,imp) ->
<<<<<<< HEAD
                   let uu____5610 = term_to_string a  in
                   FStar_Util.format2 "%s%s" (imp_to_string imp) uu____5610)
            args
           in
        FStar_Util.format2 "(%s %s)" l.FStar_Ident.str uu____5594
    | Abs (pats,t) ->
        let uu____5617 = to_string_l " " pat_to_string pats  in
        let uu____5618 = FStar_All.pipe_right t term_to_string  in
        FStar_Util.format2 "(fun %s -> %s)" uu____5617 uu____5618
    | App (t1,t2,imp) ->
        let uu____5622 = FStar_All.pipe_right t1 term_to_string  in
        let uu____5623 = FStar_All.pipe_right t2 term_to_string  in
        FStar_Util.format3 "%s %s%s" uu____5622 (imp_to_string imp)
          uu____5623
=======
                   let uu____5526 = term_to_string a in
                   FStar_Util.format2 "%s%s" (imp_to_string imp) uu____5526)
            args in
        FStar_Util.format2 "(%s %s)" l.FStar_Ident.str uu____5510
    | Abs (pats,t) ->
        let uu____5533 = to_string_l " " pat_to_string pats in
        let uu____5534 = FStar_All.pipe_right t term_to_string in
        FStar_Util.format2 "(fun %s -> %s)" uu____5533 uu____5534
    | App (t1,t2,imp) ->
        let uu____5538 = FStar_All.pipe_right t1 term_to_string in
        let uu____5539 = FStar_All.pipe_right t2 term_to_string in
        FStar_Util.format3 "%s %s%s" uu____5538 (imp_to_string imp)
          uu____5539
>>>>>>> taramana_pointers_with_codes_modifies
    | Let (Rec ,lbs,body) ->
        let uu____5554 =
          to_string_l " and "
            (fun uu____5564  ->
               match uu____5564 with
               | (p,b) ->
<<<<<<< HEAD
                   let uu____5655 = FStar_All.pipe_right p pat_to_string  in
                   let uu____5656 = FStar_All.pipe_right b term_to_string  in
                   FStar_Util.format2 "%s=%s" uu____5655 uu____5656) lbs
           in
        let uu____5657 = FStar_All.pipe_right body term_to_string  in
        FStar_Util.format2 "let rec %s in %s" uu____5638 uu____5657
    | Let (q,(pat,tm)::[],body) ->
        let uu____5676 = FStar_All.pipe_right pat pat_to_string  in
        let uu____5677 = FStar_All.pipe_right tm term_to_string  in
        let uu____5678 = FStar_All.pipe_right body term_to_string  in
=======
                   let uu____5571 = FStar_All.pipe_right p pat_to_string in
                   let uu____5572 = FStar_All.pipe_right b term_to_string in
                   FStar_Util.format2 "%s=%s" uu____5571 uu____5572) lbs in
        let uu____5573 = FStar_All.pipe_right body term_to_string in
        FStar_Util.format2 "let rec %s in %s" uu____5554 uu____5573
    | Let (q,(pat,tm)::[],body) ->
        let uu____5592 = FStar_All.pipe_right pat pat_to_string in
        let uu____5593 = FStar_All.pipe_right tm term_to_string in
        let uu____5594 = FStar_All.pipe_right body term_to_string in
>>>>>>> taramana_pointers_with_codes_modifies
        FStar_Util.format4 "let %s %s = %s in %s" (string_of_let_qualifier q)
          uu____5592 uu____5593 uu____5594
    | Seq (t1,t2) ->
<<<<<<< HEAD
        let uu____5681 = FStar_All.pipe_right t1 term_to_string  in
        let uu____5682 = FStar_All.pipe_right t2 term_to_string  in
        FStar_Util.format2 "%s; %s" uu____5681 uu____5682
    | If (t1,t2,t3) ->
        let uu____5686 = FStar_All.pipe_right t1 term_to_string  in
        let uu____5687 = FStar_All.pipe_right t2 term_to_string  in
        let uu____5688 = FStar_All.pipe_right t3 term_to_string  in
        FStar_Util.format3 "if %s then %s else %s" uu____5686 uu____5687
          uu____5688
    | Match (t,branches) ->
        let uu____5711 = FStar_All.pipe_right t term_to_string  in
        let uu____5712 =
=======
        let uu____5597 = FStar_All.pipe_right t1 term_to_string in
        let uu____5598 = FStar_All.pipe_right t2 term_to_string in
        FStar_Util.format2 "%s; %s" uu____5597 uu____5598
    | If (t1,t2,t3) ->
        let uu____5602 = FStar_All.pipe_right t1 term_to_string in
        let uu____5603 = FStar_All.pipe_right t2 term_to_string in
        let uu____5604 = FStar_All.pipe_right t3 term_to_string in
        FStar_Util.format3 "if %s then %s else %s" uu____5602 uu____5603
          uu____5604
    | Match (t,branches) ->
        let uu____5627 = FStar_All.pipe_right t term_to_string in
        let uu____5628 =
>>>>>>> taramana_pointers_with_codes_modifies
          to_string_l " | "
            (fun uu____5644  ->
               match uu____5644 with
               | (p,w,e) ->
<<<<<<< HEAD
                   let uu____5744 = FStar_All.pipe_right p pat_to_string  in
                   let uu____5745 =
                     match w with
                     | FStar_Pervasives_Native.None  -> ""
                     | FStar_Pervasives_Native.Some e1 ->
                         let uu____5747 = term_to_string e1  in
                         FStar_Util.format1 "when %s" uu____5747
                      in
                   let uu____5748 = FStar_All.pipe_right e term_to_string  in
                   FStar_Util.format3 "%s %s -> %s" uu____5744 uu____5745
                     uu____5748) branches
           in
        FStar_Util.format2 "match %s with %s" uu____5711 uu____5712
    | Ascribed (t1,t2,FStar_Pervasives_Native.None ) ->
        let uu____5753 = FStar_All.pipe_right t1 term_to_string  in
        let uu____5754 = FStar_All.pipe_right t2 term_to_string  in
        FStar_Util.format2 "(%s : %s)" uu____5753 uu____5754
    | Ascribed (t1,t2,FStar_Pervasives_Native.Some tac) ->
        let uu____5760 = FStar_All.pipe_right t1 term_to_string  in
        let uu____5761 = FStar_All.pipe_right t2 term_to_string  in
        let uu____5762 = FStar_All.pipe_right tac term_to_string  in
        FStar_Util.format3 "(%s : %s by %s)" uu____5760 uu____5761 uu____5762
    | Record (FStar_Pervasives_Native.Some e,fields) ->
        let uu____5779 = FStar_All.pipe_right e term_to_string  in
        let uu____5780 =
=======
                   let uu____5660 = FStar_All.pipe_right p pat_to_string in
                   let uu____5661 =
                     match w with
                     | FStar_Pervasives_Native.None  -> ""
                     | FStar_Pervasives_Native.Some e1 ->
                         let uu____5663 = term_to_string e1 in
                         FStar_Util.format1 "when %s" uu____5663 in
                   let uu____5664 = FStar_All.pipe_right e term_to_string in
                   FStar_Util.format3 "%s %s -> %s" uu____5660 uu____5661
                     uu____5664) branches in
        FStar_Util.format2 "match %s with %s" uu____5627 uu____5628
    | Ascribed (t1,t2,FStar_Pervasives_Native.None ) ->
        let uu____5669 = FStar_All.pipe_right t1 term_to_string in
        let uu____5670 = FStar_All.pipe_right t2 term_to_string in
        FStar_Util.format2 "(%s : %s)" uu____5669 uu____5670
    | Ascribed (t1,t2,FStar_Pervasives_Native.Some tac) ->
        let uu____5676 = FStar_All.pipe_right t1 term_to_string in
        let uu____5677 = FStar_All.pipe_right t2 term_to_string in
        let uu____5678 = FStar_All.pipe_right tac term_to_string in
        FStar_Util.format3 "(%s : %s by %s)" uu____5676 uu____5677 uu____5678
    | Record (FStar_Pervasives_Native.Some e,fields) ->
        let uu____5695 = FStar_All.pipe_right e term_to_string in
        let uu____5696 =
>>>>>>> taramana_pointers_with_codes_modifies
          to_string_l " "
            (fun uu____5705  ->
               match uu____5705 with
               | (l,e1) ->
<<<<<<< HEAD
                   let uu____5796 = FStar_All.pipe_right e1 term_to_string
                      in
                   FStar_Util.format2 "%s=%s" l.FStar_Ident.str uu____5796)
            fields
           in
        FStar_Util.format2 "{%s with %s}" uu____5779 uu____5780
=======
                   let uu____5712 = FStar_All.pipe_right e1 term_to_string in
                   FStar_Util.format2 "%s=%s" l.FStar_Ident.str uu____5712)
            fields in
        FStar_Util.format2 "{%s with %s}" uu____5695 uu____5696
>>>>>>> taramana_pointers_with_codes_modifies
    | Record (FStar_Pervasives_Native.None ,fields) ->
        let uu____5728 =
          to_string_l " "
            (fun uu____5737  ->
               match uu____5737 with
               | (l,e) ->
<<<<<<< HEAD
                   let uu____5828 = FStar_All.pipe_right e term_to_string  in
                   FStar_Util.format2 "%s=%s" l.FStar_Ident.str uu____5828)
            fields
           in
        FStar_Util.format1 "{%s}" uu____5812
    | Project (e,l) ->
        let uu____5831 = FStar_All.pipe_right e term_to_string  in
        FStar_Util.format2 "%s.%s" uu____5831 l.FStar_Ident.str
=======
                   let uu____5744 = FStar_All.pipe_right e term_to_string in
                   FStar_Util.format2 "%s=%s" l.FStar_Ident.str uu____5744)
            fields in
        FStar_Util.format1 "{%s}" uu____5728
    | Project (e,l) ->
        let uu____5747 = FStar_All.pipe_right e term_to_string in
        FStar_Util.format2 "%s.%s" uu____5747 l.FStar_Ident.str
>>>>>>> taramana_pointers_with_codes_modifies
    | Product ([],t) -> term_to_string t
    | Product (b::hd1::tl1,t) ->
        term_to_string
          (mk_term
             (Product
                ([b], (mk_term (Product ((hd1 :: tl1), t)) x.range x.level)))
             x.range x.level)
    | Product (b::[],t) when x.level = Type_level ->
<<<<<<< HEAD
        let uu____5851 = FStar_All.pipe_right b binder_to_string  in
        let uu____5852 = FStar_All.pipe_right t term_to_string  in
        FStar_Util.format2 "%s -> %s" uu____5851 uu____5852
    | Product (b::[],t) when x.level = Kind ->
        let uu____5857 = FStar_All.pipe_right b binder_to_string  in
        let uu____5858 = FStar_All.pipe_right t term_to_string  in
        FStar_Util.format2 "%s => %s" uu____5857 uu____5858
    | Sum (binders,t) ->
        let uu____5865 =
          let uu____5866 =
            FStar_All.pipe_right binders (FStar_List.map binder_to_string)
             in
          FStar_All.pipe_right uu____5866 (FStar_String.concat " * ")  in
        let uu____5875 = FStar_All.pipe_right t term_to_string  in
        FStar_Util.format2 "%s * %s" uu____5865 uu____5875
    | QForall (bs,pats,t) ->
        let uu____5891 = to_string_l " " binder_to_string bs  in
        let uu____5892 =
          to_string_l " \\/ " (to_string_l "; " term_to_string) pats  in
        let uu____5895 = FStar_All.pipe_right t term_to_string  in
        FStar_Util.format3 "forall %s.{:pattern %s} %s" uu____5891 uu____5892
          uu____5895
    | QExists (bs,pats,t) ->
        let uu____5911 = to_string_l " " binder_to_string bs  in
        let uu____5912 =
          to_string_l " \\/ " (to_string_l "; " term_to_string) pats  in
        let uu____5915 = FStar_All.pipe_right t term_to_string  in
        FStar_Util.format3 "exists %s.{:pattern %s} %s" uu____5911 uu____5912
          uu____5915
    | Refine (b,t) ->
        let uu____5918 = FStar_All.pipe_right b binder_to_string  in
        let uu____5919 = FStar_All.pipe_right t term_to_string  in
        FStar_Util.format2 "%s:{%s}" uu____5918 uu____5919
    | NamedTyp (x1,t) ->
        let uu____5922 = FStar_All.pipe_right t term_to_string  in
        FStar_Util.format2 "%s:%s" x1.FStar_Ident.idText uu____5922
    | Paren t ->
        let uu____5924 = FStar_All.pipe_right t term_to_string  in
        FStar_Util.format1 "(%s)" uu____5924
    | Product (bs,t) ->
        let uu____5931 =
          let uu____5932 =
            FStar_All.pipe_right bs (FStar_List.map binder_to_string)  in
          FStar_All.pipe_right uu____5932 (FStar_String.concat ",")  in
        let uu____5941 = FStar_All.pipe_right t term_to_string  in
        FStar_Util.format2 "Unidentified product: [%s] %s" uu____5931
          uu____5941
    | t -> "_"

and binder_to_string : binder -> Prims.string =
=======
        let uu____5767 = FStar_All.pipe_right b binder_to_string in
        let uu____5768 = FStar_All.pipe_right t term_to_string in
        FStar_Util.format2 "%s -> %s" uu____5767 uu____5768
    | Product (b::[],t) when x.level = Kind ->
        let uu____5773 = FStar_All.pipe_right b binder_to_string in
        let uu____5774 = FStar_All.pipe_right t term_to_string in
        FStar_Util.format2 "%s => %s" uu____5773 uu____5774
    | Sum (binders,t) ->
        let uu____5781 =
          let uu____5782 =
            FStar_All.pipe_right binders (FStar_List.map binder_to_string) in
          FStar_All.pipe_right uu____5782 (FStar_String.concat " * ") in
        let uu____5791 = FStar_All.pipe_right t term_to_string in
        FStar_Util.format2 "%s * %s" uu____5781 uu____5791
    | QForall (bs,pats,t) ->
        let uu____5807 = to_string_l " " binder_to_string bs in
        let uu____5808 =
          to_string_l " \\/ " (to_string_l "; " term_to_string) pats in
        let uu____5811 = FStar_All.pipe_right t term_to_string in
        FStar_Util.format3 "forall %s.{:pattern %s} %s" uu____5807 uu____5808
          uu____5811
    | QExists (bs,pats,t) ->
        let uu____5827 = to_string_l " " binder_to_string bs in
        let uu____5828 =
          to_string_l " \\/ " (to_string_l "; " term_to_string) pats in
        let uu____5831 = FStar_All.pipe_right t term_to_string in
        FStar_Util.format3 "exists %s.{:pattern %s} %s" uu____5827 uu____5828
          uu____5831
    | Refine (b,t) ->
        let uu____5834 = FStar_All.pipe_right b binder_to_string in
        let uu____5835 = FStar_All.pipe_right t term_to_string in
        FStar_Util.format2 "%s:{%s}" uu____5834 uu____5835
    | NamedTyp (x1,t) ->
        let uu____5838 = FStar_All.pipe_right t term_to_string in
        FStar_Util.format2 "%s:%s" x1.FStar_Ident.idText uu____5838
    | Paren t ->
        let uu____5840 = FStar_All.pipe_right t term_to_string in
        FStar_Util.format1 "(%s)" uu____5840
    | Product (bs,t) ->
        let uu____5847 =
          let uu____5848 =
            FStar_All.pipe_right bs (FStar_List.map binder_to_string) in
          FStar_All.pipe_right uu____5848 (FStar_String.concat ",") in
        let uu____5857 = FStar_All.pipe_right t term_to_string in
        FStar_Util.format2 "Unidentified product: [%s] %s" uu____5847
          uu____5857
    | t -> "_"
and (binder_to_string :binder -> Prims.string)=
>>>>>>> taramana_pointers_with_codes_modifies
  fun x  ->
    let s =
      match x.b with
      | Variable i -> i.FStar_Ident.idText
      | TVariable i -> FStar_Util.format1 "%s:_" i.FStar_Ident.idText
      | TAnnotated (i,t) ->
<<<<<<< HEAD
          let uu____5949 = FStar_All.pipe_right t term_to_string  in
          FStar_Util.format2 "%s:%s" i.FStar_Ident.idText uu____5949
      | Annotated (i,t) ->
          let uu____5952 = FStar_All.pipe_right t term_to_string  in
          FStar_Util.format2 "%s:%s" i.FStar_Ident.idText uu____5952
      | NoName t -> FStar_All.pipe_right t term_to_string  in
    let uu____5954 = aqual_to_string x.aqual  in
    FStar_Util.format2 "%s%s" uu____5954 s

and aqual_to_string : aqual -> Prims.string =
  fun uu___81_5955  ->
    match uu___81_5955 with
    | FStar_Pervasives_Native.Some (Equality ) -> "$"
    | FStar_Pervasives_Native.Some (Implicit ) -> "#"
    | uu____5956 -> ""

and pat_to_string : pattern -> Prims.string =
=======
          let uu____5865 = FStar_All.pipe_right t term_to_string in
          FStar_Util.format2 "%s:%s" i.FStar_Ident.idText uu____5865
      | Annotated (i,t) ->
          let uu____5868 = FStar_All.pipe_right t term_to_string in
          FStar_Util.format2 "%s:%s" i.FStar_Ident.idText uu____5868
      | NoName t -> FStar_All.pipe_right t term_to_string in
    let uu____5870 = aqual_to_string x.aqual in
    FStar_Util.format2 "%s%s" uu____5870 s
and (aqual_to_string :aqual -> Prims.string)=
  fun uu___80_5871  ->
    match uu___80_5871 with
    | FStar_Pervasives_Native.Some (Equality ) -> "$"
    | FStar_Pervasives_Native.Some (Implicit ) -> "#"
    | uu____5872 -> ""
and (pat_to_string :pattern -> Prims.string)=
>>>>>>> taramana_pointers_with_codes_modifies
  fun x  ->
    match x.pat with
    | PatWild  -> "_"
    | PatConst c -> FStar_Parser_Const.const_to_string c
    | PatApp (p,ps) ->
<<<<<<< HEAD
        let uu____5965 = FStar_All.pipe_right p pat_to_string  in
        let uu____5966 = to_string_l " " pat_to_string ps  in
        FStar_Util.format2 "(%s %s)" uu____5965 uu____5966
    | PatTvar (i,aq) ->
        let uu____5973 = aqual_to_string aq  in
        FStar_Util.format2 "%s%s" uu____5973 i.FStar_Ident.idText
    | PatVar (i,aq) ->
        let uu____5980 = aqual_to_string aq  in
        FStar_Util.format2 "%s%s" uu____5980 i.FStar_Ident.idText
    | PatName l -> l.FStar_Ident.str
    | PatList l ->
        let uu____5985 = to_string_l "; " pat_to_string l  in
        FStar_Util.format1 "[%s]" uu____5985
    | PatTuple (l,false ) ->
        let uu____5991 = to_string_l ", " pat_to_string l  in
        FStar_Util.format1 "(%s)" uu____5991
    | PatTuple (l,true ) ->
        let uu____5997 = to_string_l ", " pat_to_string l  in
        FStar_Util.format1 "(|%s|)" uu____5997
=======
        let uu____5881 = FStar_All.pipe_right p pat_to_string in
        let uu____5882 = to_string_l " " pat_to_string ps in
        FStar_Util.format2 "(%s %s)" uu____5881 uu____5882
    | PatTvar (i,aq) ->
        let uu____5889 = aqual_to_string aq in
        FStar_Util.format2 "%s%s" uu____5889 i.FStar_Ident.idText
    | PatVar (i,aq) ->
        let uu____5896 = aqual_to_string aq in
        FStar_Util.format2 "%s%s" uu____5896 i.FStar_Ident.idText
    | PatName l -> l.FStar_Ident.str
    | PatList l ->
        let uu____5901 = to_string_l "; " pat_to_string l in
        FStar_Util.format1 "[%s]" uu____5901
    | PatTuple (l,false ) ->
        let uu____5907 = to_string_l ", " pat_to_string l in
        FStar_Util.format1 "(%s)" uu____5907
    | PatTuple (l,true ) ->
        let uu____5913 = to_string_l ", " pat_to_string l in
        FStar_Util.format1 "(|%s|)" uu____5913
>>>>>>> taramana_pointers_with_codes_modifies
    | PatRecord l ->
        let uu____5921 =
          to_string_l "; "
            (fun uu____5930  ->
               match uu____5930 with
               | (f,e) ->
<<<<<<< HEAD
                   let uu____6021 = FStar_All.pipe_right e pat_to_string  in
                   FStar_Util.format2 "%s=%s" f.FStar_Ident.str uu____6021) l
           in
        FStar_Util.format1 "{%s}" uu____6005
    | PatOr l -> to_string_l "|\n " pat_to_string l
    | PatOp op -> FStar_Util.format1 "(%s)" (FStar_Ident.text_of_id op)
    | PatAscribed (p,t) ->
        let uu____6028 = FStar_All.pipe_right p pat_to_string  in
        let uu____6029 = FStar_All.pipe_right t term_to_string  in
        FStar_Util.format2 "(%s:%s)" uu____6028 uu____6029

let rec head_id_of_pat : pattern -> FStar_Ident.lid Prims.list =
  fun p  ->
    match p.pat with
    | PatName l -> [l]
    | PatVar (i,uu____6040) ->
        let uu____6045 = FStar_Ident.lid_of_ids [i]  in [uu____6045]
    | PatApp (p1,uu____6047) -> head_id_of_pat p1
    | PatAscribed (p1,uu____6053) -> head_id_of_pat p1
    | uu____6054 -> []
  
let lids_of_let :
  'Auu____6059 .
    (pattern,'Auu____6059) FStar_Pervasives_Native.tuple2 Prims.list ->
      FStar_Ident.lid Prims.list
  =
  fun defs  ->
    FStar_All.pipe_right defs
      (FStar_List.collect
         (fun uu____6093  ->
            match uu____6093 with | (p,uu____6101) -> head_id_of_pat p))
  
let id_of_tycon : tycon -> Prims.string =
  fun uu___82_6105  ->
    match uu___82_6105 with
    | TyconAbstract (i,uu____6107,uu____6108) -> i.FStar_Ident.idText
    | TyconAbbrev (i,uu____6118,uu____6119,uu____6120) ->
=======
                   let uu____5937 = FStar_All.pipe_right e pat_to_string in
                   FStar_Util.format2 "%s=%s" f.FStar_Ident.str uu____5937) l in
        FStar_Util.format1 "{%s}" uu____5921
    | PatOr l -> to_string_l "|\n " pat_to_string l
    | PatOp op -> FStar_Util.format1 "(%s)" (FStar_Ident.text_of_id op)
    | PatAscribed (p,t) ->
        let uu____5944 = FStar_All.pipe_right p pat_to_string in
        let uu____5945 = FStar_All.pipe_right t term_to_string in
        FStar_Util.format2 "(%s:%s)" uu____5944 uu____5945
let rec (head_id_of_pat :pattern -> FStar_Ident.lid Prims.list)=
  fun p  ->
    match p.pat with
    | PatName l -> [l]
    | PatVar (i,uu____5956) ->
        let uu____5961 = FStar_Ident.lid_of_ids [i] in [uu____5961]
    | PatApp (p1,uu____5963) -> head_id_of_pat p1
    | PatAscribed (p1,uu____5969) -> head_id_of_pat p1
    | uu____5970 -> []
let lids_of_let :
  'Auu____5975 .
    (pattern,'Auu____5975) FStar_Pervasives_Native.tuple2 Prims.list ->
      FStar_Ident.lid Prims.list=
  fun defs  ->
    FStar_All.pipe_right defs
      (FStar_List.collect
         (fun uu____6009  ->
            match uu____6009 with | (p,uu____6017) -> head_id_of_pat p))
let (id_of_tycon :tycon -> Prims.string)=
  fun uu___81_6021  ->
    match uu___81_6021 with
    | TyconAbstract (i,uu____6023,uu____6024) -> i.FStar_Ident.idText
    | TyconAbbrev (i,uu____6034,uu____6035,uu____6036) ->
>>>>>>> taramana_pointers_with_codes_modifies
        i.FStar_Ident.idText
    | TyconRecord (i,uu____6046,uu____6047,uu____6048) ->
        i.FStar_Ident.idText
    | TyconVariant (i,uu____6078,uu____6079,uu____6080) ->
        i.FStar_Ident.idText
<<<<<<< HEAD
  
let decl_to_string : decl -> Prims.string =
=======
let (decl_to_string :decl -> Prims.string)=
>>>>>>> taramana_pointers_with_codes_modifies
  fun d  ->
    match d.d with
    | TopLevelModule l -> Prims.strcat "module " l.FStar_Ident.str
    | Open l -> Prims.strcat "open " l.FStar_Ident.str
    | Include l -> Prims.strcat "include " l.FStar_Ident.str
    | ModuleAbbrev (i,l) ->
        FStar_Util.format2 "module %s = %s" i.FStar_Ident.idText
          l.FStar_Ident.str
<<<<<<< HEAD
    | TopLevelLet (uu____6210,pats) ->
        let uu____6224 =
          let uu____6225 =
            let uu____6228 = lids_of_let pats  in
            FStar_All.pipe_right uu____6228
              (FStar_List.map (fun l  -> l.FStar_Ident.str))
             in
          FStar_All.pipe_right uu____6225 (FStar_String.concat ", ")  in
        Prims.strcat "let " uu____6224
    | Main uu____6239 -> "main ..."
    | Assume (i,uu____6241) -> Prims.strcat "assume " i.FStar_Ident.idText
    | Tycon (uu____6242,tys) ->
        let uu____6260 =
          let uu____6261 =
            FStar_All.pipe_right tys
              (FStar_List.map
                 (fun uu____6283  ->
                    match uu____6283 with | (x,uu____6291) -> id_of_tycon x))
             in
          FStar_All.pipe_right uu____6261 (FStar_String.concat ", ")  in
        Prims.strcat "type " uu____6260
    | Val (i,uu____6299) -> Prims.strcat "val " i.FStar_Ident.idText
    | Exception (i,uu____6301) ->
=======
    | TopLevelLet (uu____6126,pats) ->
        let uu____6140 =
          let uu____6141 =
            let uu____6144 = lids_of_let pats in
            FStar_All.pipe_right uu____6144
              (FStar_List.map (fun l  -> l.FStar_Ident.str)) in
          FStar_All.pipe_right uu____6141 (FStar_String.concat ", ") in
        Prims.strcat "let " uu____6140
    | Main uu____6155 -> "main ..."
    | Assume (i,uu____6157) -> Prims.strcat "assume " i.FStar_Ident.idText
    | Tycon (uu____6158,tys) ->
        let uu____6176 =
          let uu____6177 =
            FStar_All.pipe_right tys
              (FStar_List.map
                 (fun uu____6199  ->
                    match uu____6199 with | (x,uu____6207) -> id_of_tycon x)) in
          FStar_All.pipe_right uu____6177 (FStar_String.concat ", ") in
        Prims.strcat "type " uu____6176
    | Val (i,uu____6215) -> Prims.strcat "val " i.FStar_Ident.idText
    | Exception (i,uu____6217) ->
>>>>>>> taramana_pointers_with_codes_modifies
        Prims.strcat "exception " i.FStar_Ident.idText
    | NewEffect (DefineEffect (i,uu____6223,uu____6224,uu____6225)) ->
        Prims.strcat "new_effect " i.FStar_Ident.idText
    | NewEffect (RedefineEffect (i,uu____6235,uu____6236)) ->
        Prims.strcat "new_effect " i.FStar_Ident.idText
<<<<<<< HEAD
    | SubEffect uu____6325 -> "sub_effect"
    | Pragma uu____6326 -> "pragma"
    | Fsdoc uu____6327 -> "fsdoc"
  
let modul_to_string : modul -> Prims.string =
  fun m  ->
    match m with
    | Module (uu____6332,decls) ->
        let uu____6338 =
          FStar_All.pipe_right decls (FStar_List.map decl_to_string)  in
        FStar_All.pipe_right uu____6338 (FStar_String.concat "\n")
    | Interface (uu____6347,decls,uu____6349) ->
        let uu____6354 =
          FStar_All.pipe_right decls (FStar_List.map decl_to_string)  in
        FStar_All.pipe_right uu____6354 (FStar_String.concat "\n")
  
let error :
  'Auu____6371 . Prims.string -> term -> FStar_Range.range -> 'Auu____6371 =
=======
    | SubEffect uu____6241 -> "sub_effect"
    | Pragma uu____6242 -> "pragma"
    | Fsdoc uu____6243 -> "fsdoc"
let (modul_to_string :modul -> Prims.string)=
  fun m  ->
    match m with
    | Module (uu____6248,decls) ->
        let uu____6254 =
          FStar_All.pipe_right decls (FStar_List.map decl_to_string) in
        FStar_All.pipe_right uu____6254 (FStar_String.concat "\n")
    | Interface (uu____6263,decls,uu____6265) ->
        let uu____6270 =
          FStar_All.pipe_right decls (FStar_List.map decl_to_string) in
        FStar_All.pipe_right uu____6270 (FStar_String.concat "\n")
let error :
  'Auu____6287 . Prims.string -> term -> FStar_Range.range -> 'Auu____6287=
>>>>>>> taramana_pointers_with_codes_modifies
  fun msg  ->
    fun tm  ->
      fun r  ->
        let tm1 = FStar_All.pipe_right tm term_to_string  in
        let tm2 =
          if (FStar_String.length tm1) >= (Prims.parse_int "80")
          then
            let uu____6302 =
              FStar_Util.substring tm1 (Prims.parse_int "0")
<<<<<<< HEAD
                (Prims.parse_int "77")
               in
            Prims.strcat uu____6386 "..."
          else tm1  in
=======
                (Prims.parse_int "77") in
            Prims.strcat uu____6302 "..."
          else tm1 in
>>>>>>> taramana_pointers_with_codes_modifies
        FStar_Exn.raise
          (FStar_Errors.Error ((Prims.strcat msg (Prims.strcat "\n" tm2)), r))
  